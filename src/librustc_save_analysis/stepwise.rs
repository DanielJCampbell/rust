// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use syntax::ast;
use syntax::ext::base::{ExtCtxt, SyntaxExtension, NamedSyntaxExtension};
use syntax::ext::expand::{self, MacroExpander};
use syntax::ext::expand::MacroError::*;

use syntax::codemap::{Span, ExpnInfo, NO_EXPANSION};
use syntax::fold::{self, Folder};
use syntax::print::pprust;
use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;

use syntax_pos::{mk_sp, BytePos};

use std::collections::{HashSet, HashMap};

// A MacroExpansion consists of an expansion trace (mapped to a span in a HashMap),
// and a boolean marking whether or not expansion failed.
// The nth step of the trace is the pretty-printed text of the macro call
// after n expansions. If the expansion utltimately failed, failed == true,
// and the last element of the trace is an error message.

#[derive(Clone, Debug)]
pub struct MacroExpansion {
    pub trace: Vec<String>,
    pub failed: bool,
}

pub fn expand_crate(ecx: &mut ExtCtxt,
                    user_exts: Vec<NamedSyntaxExtension>,
                    c: ast::Crate)
                    -> (ast::Crate, HashMap<Span, MacroExpansion>) {
    // User extensions only need to be added once
    for (name, extension) in user_exts {
        ecx.syntax_env.insert(name, extension);
    }
    let data = ExpandData::new(ecx, c);
    let expander = StepwiseExpander::new(data);
    expander.expand()
}

struct ExpandData<'a, 'b:'a> {
    cx: &'a mut ExtCtxt<'b>,
    krate: ast::Crate,
    span_map: HashMap<Span, Span>,
    expansions: HashMap<Span, MacroExpansion>,
    // Used to ensure correct trace length
    span_set: HashSet<Span>,
}

impl<'a, 'b> ExpandData<'a, 'b> {
    fn new(cx: &'a mut ExtCtxt<'b>,
           init_crate: ast::Crate) -> ExpandData<'a, 'b> {

        ExpandData {
            cx: cx,
            krate: init_crate,
            span_map: HashMap::new(),
            expansions: HashMap::new(),
            span_set: HashSet::new(),
        }
    }

    // When stepwise expanding, generated span traces will only ever be one level deep,
    // as they have no way of storing results from a previous step.
    // So we manually maintain a mapping from span without expn_id to span with expn_id.
    fn insert(&mut self, span: Span) {
        if span.expn_id == NO_EXPANSION {
            unreachable!();
        }

        let key_sp = Span {
            lo: span.lo,
            hi: span.hi,
            expn_id: NO_EXPANSION
        };
        let callsite = self.cx.codemap().with_expn_info(span.expn_id,
                                                        |ei| ei.map(|ei| ei.call_site.clone()));
        if callsite.is_none() {
            unreachable!();
        }
        let mut callsite = callsite.unwrap();

        if !self.span_map.contains_key(&callsite) {
            self.span_map.insert(key_sp, span);
            return;
        }

        let callee = self.cx.codemap().with_expn_info(span.expn_id,
                                                      |ei| ei.map(|ei| ei.callee.clone()));
        if callee.is_none() {
            unreachable!();
        }
        let callee = callee.unwrap();

        // Get will return the supplied span if not in the map, to handle
        // the case where this is the first level of expansion.
        callsite = self.span_map.get(&callsite).unwrap().clone();
        let info = ExpnInfo {
            call_site: callsite,
            callee: callee
        };
        let new_id = self.cx.codemap().record_expansion(info);
        self.span_map.insert(key_sp, Span { expn_id: new_id, .. span });
    }

    fn get(&self, span: Span) -> Span {
        let key_sp = Span { expn_id: NO_EXPANSION, .. span };
        return self.span_map.get(&key_sp).unwrap_or(&span).clone();
    }

    fn step_expand(&mut self) {
        let mut krate = self.krate.clone();
        let mut errs = HashMap::new();
        self.span_set = HashSet::new();
        {
            let mut expander = MacroExpander::new(&mut self.cx, true, true);
            krate = expand::expand_crate_with_expander(&mut expander, Vec::new(), krate);
            for err in expander.mac_errors.iter() {
                match *err {
                    MacroInvokeError { callsite: sp, ref msg } => {errs.insert(sp, msg.clone());},
                    MacroMalformedError { callsite: sp, ref msg, .. } =>
                        {errs.insert(sp, msg.clone());},
                    _ => (),
                };
            }
        }
        // Update spans and MacroExpansion traces.
        self.krate = self.fold_crate(krate);

        // For every failed macro call, mark that MacroExpansion and remove its last (dummy) step.
        // Instead, the last element of the trace will be an error message
        let mapping: Vec<(&Span, &String)> = errs.iter().collect();
        for (sp, msg) in mapping {
            let callsite = self.cx.codemap().source_callsite(self.get(sp.clone()));
            let expn = self.expansions.get_mut(&callsite);
            if let Some(expn) = expn {
                expn.failed = true;
                expn.trace.pop();
                expn.trace.push(msg.clone())
            }
        }
    }
}

// Walk over AST of expanded crate to patch up spans and update expansion traces.
impl<'a, 'b> Folder for ExpandData<'a, 'b> {
    fn fold_crate(&mut self, krate: ast::Crate) -> ast::Crate {
        fold::noop_fold_crate(krate, self)
    }

    fn fold_pat(&mut self, pat: P<ast::Pat>) -> P<ast::Pat> {
        if pat.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_pat(pat, self);
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. pat.span }) == Some(&pat.span) {
            return fold::noop_fold_pat(pat, self);
        }
        self.insert(pat.span);

        let callsite = self.cx.codemap().source_callsite(self.get(pat.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::pat_to_string(&pat.clone()));
                self.span_set.insert(callsite);
            }
        }

        fold::noop_fold_pat(pat.map(|elt| ast::Pat { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_ty(&mut self, ty: P<ast::Ty>) -> P<ast::Ty> {
        if ty.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_ty(ty, self);
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. ty.span }) == Some(&ty.span) {
            return fold::noop_fold_ty(ty, self);
        }
        self.insert(ty.span);

        let callsite = self.cx.codemap().source_callsite(self.get(ty.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::ty_to_string(&ty.clone()));
                self.span_set.insert(callsite);
            }
        }
        fold::noop_fold_ty(ty.map(|elt| ast::Ty { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_expr(&mut self, expr: P<ast::Expr>) -> P<ast::Expr> {
        if expr.span.expn_id == NO_EXPANSION {
            return P(fold::noop_fold_expr(expr.unwrap(), self));
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. expr.span }) == Some(&expr.span) {
            return P(fold::noop_fold_expr(expr.unwrap(), self));
        }
        self.insert(expr.span.clone());

        let callsite = self.cx.codemap().source_callsite(self.get(expr.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::expr_to_string(&expr.clone()));
                self.span_set.insert(callsite);
            }
        }
        P(fold::noop_fold_expr(expr.map(|elt| ast::Expr { span: self.get(elt.span), .. elt })
                                   .unwrap(), self))
    }

    fn fold_opt_expr(&mut self, opt: P<ast::Expr>) -> Option<P<ast::Expr>> {
        if opt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_opt_expr(opt, self);
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. opt.span }) == Some(&opt.span) {
            return fold::noop_fold_opt_expr(opt, self);
        }
        self.insert(opt.span);

        let callsite = self.cx.codemap().source_callsite(self.get(opt.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::expr_to_string(&opt.clone()));
                self.span_set.insert(callsite);
            }
        }
        fold::noop_fold_opt_expr(opt.map(|elt| ast::Expr { span: self.get(elt.span), .. elt }),
                                 self)
    }

    fn fold_item(&mut self, item: P<ast::Item>) -> SmallVector<P<ast::Item>> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_item(item, self);
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. item.span }) == Some(&item.span) {
            return fold::noop_fold_item(item, self);
        }
        self.insert(item.span);

        let callsite = self.cx.codemap().source_callsite(self.get(item.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::item_to_string(&item.clone()));
                self.span_set.insert(callsite);
            }
        }
        fold::noop_fold_item(item.map(|elt| ast::Item { span: self.get(elt.span), .. elt }),
                             self)
    }

    fn fold_stmt(&mut self, stmt: ast::Stmt) -> SmallVector<ast::Stmt> {
        if stmt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_stmt(stmt, self);
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. stmt.span }) == Some(&stmt.span) {
            return fold::noop_fold_stmt(stmt, self);
        }
        self.insert(stmt.span);

        let callsite = self.cx.codemap().source_callsite(self.get(stmt.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::stmt_to_string(&stmt.clone()));
                self.span_set.insert(callsite);
            }
        }
        fold::noop_fold_stmt(ast::Stmt { span: self.get(stmt.span), .. stmt }, self)
    }

    fn fold_impl_item(&mut self, item: ast::ImplItem) -> SmallVector<ast::ImplItem> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_impl_item(item, self);
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. item.span }) == Some(&item.span) {
            return fold::noop_fold_impl_item(item, self);
        }
        self.insert(item.span);

        let callsite = self.cx.codemap().source_callsite(self.get(item.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::impl_item_to_string(&item.clone()));
                self.span_set.insert(callsite);
            }
        }
        fold::noop_fold_impl_item(ast::ImplItem { span: self.get(item.span), .. item },
                                  self)
    }

    fn fold_trait_item(&mut self, item: ast::TraitItem) -> SmallVector<ast::TraitItem> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_trait_item(item, self);
        }
        // This node has already been expanded to the maximum
        if self.span_map.get(&Span{ expn_id: NO_EXPANSION, .. item.span }) == Some(&item.span) {
            return fold::noop_fold_trait_item(item, self);
        }
        self.insert(item.span);

        let callsite = self.cx.codemap().source_callsite(self.get(item.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            if !self.span_set.contains(&callsite) {
                val.trace.push(pprust::trait_item_to_string(&item.clone()));
                self.span_set.insert(callsite);
            }
        }
        fold::noop_fold_trait_item(ast::TraitItem {span: self.get(item.span), .. item},
                                   self)
    }

    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {
        fold::noop_fold_mac(mac, self)
    }
}

// Struct for stepwise expansion - repeatedly expands a crate
// so long as it contains a (non macro-defining) macro invocation.
struct StepwiseExpander<'a, 'b:'a> {
    has_mac: bool,
    first: bool,
    data: ExpandData<'a, 'b>
}

impl<'a, 'b> StepwiseExpander<'a, 'b> {

    fn new(data: ExpandData<'a, 'b>) -> StepwiseExpander<'a, 'b> {
        StepwiseExpander { has_mac: false, first: true, data: data }
    }

    fn expand(mut self) -> (ast::Crate, HashMap<Span, MacroExpansion>) {
        while !self.check_finished() {
            self.data.step_expand();
        }
        (self.data.krate, self.data.expansions)
    }

    fn check_finished(&mut self) -> bool {
        self.has_mac = false;
        let krate = self.data.krate.clone();
        self.fold_crate(krate);
        if self.first {
            self.first = false;
        }
        !self.has_mac
    }
}

impl<'a, 'b> Folder for StepwiseExpander<'a, 'b> {
    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {

        if mac.node.path.segments == Vec::new() {
            // Placeholder macro showing a macro-rules expansion - ignored.
            return mac;
        }
        // Ignore macro definitions and attribute macros, we only care about macro calls.
        let extname = mac.node.path.segments[0].identifier.name.clone();
        if let Some(extension) = self.data.cx.syntax_env.find(extname) {
            if let SyntaxExtension::MacroRulesTT = *extension {
                return mac;
            }
            if let SyntaxExtension::MultiDecorator(_) = *extension {
                return mac;
            }
            if let SyntaxExtension::MultiModifier(_) = *extension {
                return mac;
            }
        }
        self.has_mac = true;

        // On the first expansion, want to store
        // macro calls as the root of their expansion traces.
        if self.first {
            // Dirty dirty dirty hack: Expr Macros do not have a semicolon in their span,
            // But if used in the statement position, the callsite spans will contain a semicolon
            // So we have to manually check if this is the case.
            let stmt_span = mk_sp(mac.span.lo, mac.span.hi + (BytePos(1)));
            let snippet = match self.data.cx.codemap().span_to_snippet(stmt_span.end_point()) {
                Ok(snip) => snip,
                Err(_) => "".to_owned()
            };
            if snippet == ";".to_owned() {
                self.data.expansions.insert(stmt_span, MacroExpansion {
                    trace: vec!(pprust::mac_to_string(&mac)),
                    failed: false,
                });
            }
            else {
                self.data.expansions.insert(mac.span, MacroExpansion {
                    trace: vec!(pprust::mac_to_string(&mac)),
                    failed: false,
                });
            }
        }
        mac
    }
}