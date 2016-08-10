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
use syntax::ext::expand;
use syntax::codemap::{Span, ExpnInfo, NO_EXPANSION, DUMMY_SP};
use syntax::fold::{self, Folder};
use syntax::print::pprust;
use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;

use std::collections::HashMap;

// Small macro to simplify setting the full-expansion closures to the identity closure.
macro_rules! set_expander_fns {
    ($expander:ident,
        $( $expand:ident ),*) => {{
        $( $expander.$expand = Rc::new(Box::new(|_, node| node )); )*
    }}
}

// A MacroExpansion consists of a callsite span and an expansion trace.
// The nth step of the trace is the pretty-printed text of the macro call
// after n expansions.
pub struct MacroExpansion {
    callsite: Span,
    trace: Vec<String>,
}

pub fn expand_crate(crate_name: String,
                    krate: ast::Crate,
                    ecx: ExtCtxt,
                    user_exts: Vec<NamedSyntaxExtension>) -> Vec<MacroExpansion> {
    // Add extensions to the ExtCtxt - don't pass to expander because only need adding once.
    for (name, extension) in user_exts {
        cx.syntax_env.insert(name, extension);
    }
    let data = ExpandData::new(crate_name, cx, krate);
    let expander = StepwiseExpander::new(data);

    expander.expand()
}

struct ExpandData<'a> {
    filename: String,
    cx: ExtCtxt<'a>,
    krates: Vec<ast::Crate>,
    index: usize,
    span_map: HashMap<Span, Span>,
    expansions: HashMap<Span, MacroExpansion>,
}

impl<'a> ExpandData<'a> {

    fn new(filename: String,
           cx: ExtCtxt<'a>,
           init_crate: ast::Crate) -> ExpandData<'a> {

        let mut krates = vec!();
        krates.push(init_crate);

        ExpandData {
            filename: filename,
            cx: cx,
            krates: krates,
            index: 0,
            span_map: HashMap::new(),
            expansions: HashMap::new(),
        }
    }

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

        callsite = self.span_map.get(&callsite).unwrap().clone();
        let info = ExpnInfo {
            call_site: callsite,
            callee: callee
        };
        let new_id = self.cx.codemap().record_expansion(info);
        self.span_map.insert(key_sp, Span { expn_id: new_id, .. span });
    }

    fn get(&mut self, span: Span) -> Span {
        let key_sp = Span { expn_id: NO_EXPANSION, .. span };
        return self.span_map.get(&key_sp).unwrap_or(&span).clone();
    }

    fn step_expand(&mut self) {
        let mut krate = self.krates[self.index].clone();
        {
            let mut expander = MacroExpander::new(&mut self.cx, true, true);
            krate = expand::expand_crate_with_expander(&mut expander,
                                                       Vec::new(),
                                                       krate).0;
        }

        krate = self.fold_crate(krate);

        self.krates.push(krate);
        self.index += 1;
    }
}

//Walk over AST of expanded crate to patch up spans
impl<'a> Folder for ExpandData<'a> {
    fn fold_crate(&mut self, krate: ast::Crate) -> ast::Crate {
        fold::noop_fold_crate(krate, self)
    }

    fn fold_pat(&mut self, pat: P<ast::Pat>) -> P<ast::Pat> {
        if pat.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_pat(pat, self);
        }

        self.insert(pat.span);

        let callsite = self.cx.codemap().source_callsite(self.get(pat.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::pat_to_string(&pat.clone()));

        fold::noop_fold_pat(pat.map(|elt| ast::Pat { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_ty(&mut self, ty: P<ast::Ty>) -> P<ast::Ty> {
        if ty.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_ty(ty, self);
        }

        self.insert(ty.span);

        let callsite = self.cx.codemap().source_callsite(self.get(ty.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::ty_to_string(&ty.clone()));

        fold::noop_fold_ty(ty.map(|elt| ast::Ty { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_expr(&mut self, expr: P<ast::Expr>) -> P<ast::Expr> {
        if expr.span.expn_id == NO_EXPANSION {
            return P(fold::noop_fold_expr(expr.unwrap(), self));
        }

        self.insert(expr.span.clone());

        let callsite = self.cx.codemap().source_callsite(self.get(expr.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::expr_to_string(&expr.clone().unwrap()));

        P(fold::noop_fold_expr(expr.map(|elt| ast::Expr { span: self.get(elt.span), .. elt })
                                        .unwrap(), self))
    }

    fn fold_opt_expr(&mut self, opt: P<ast::Expr>) -> Option<P<ast::Expr>> {
        if opt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_opt_expr(opt, self);
        }

        self.insert(opt.span);

        let callsite = self.cx.codemap().source_callsite(self.get(opt.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::expr_to_string(&opt.clone()));

        fold::noop_fold_opt_expr(opt.map(|elt| ast::Expr { span: self.get(elt.span), .. elt }),
                                 self)
    }

    fn fold_item(&mut self, item: P<ast::Item>) -> SmallVector<P<ast::Item>> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_item(item, self);
        }

        self.insert(item.span);

        let callsite = self.cx.codemap().source_callsite(self.get(item.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::item_to_string(&item.clone()));

        return fold::noop_fold_item(item.map(
            |elt| ast::Item { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_stmt(&mut self, stmt: ast::Stmt) -> SmallVector<ast::Stmt> {
        if stmt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_stmt(stmt, self);
        }

        self.insert(stmt.span);

        let callsite = self.cx.codemap().source_callsite(self.get(stmt.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::stmt_to_string(&stmt.clone()));

        return fold::noop_fold_stmt(ast::Stmt { span: self.get(stmt.span), .. stmt }, self)
    }

    fn fold_impl_item(&mut self, item: ast::ImplItem) -> SmallVector<ast::ImplItem> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_impl_item(item, self);
        }

        self.insert(item.span);

        let callsite = self.cx.codemap().source_callsite(self.get(item.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::impl_item_to_string(&item.clone()));

        return fold::noop_fold_impl_item(ast::ImplItem { span: self.get(item.span), .. item },
                                         self)
    }

    fn fold_trait_item(&mut self, item: ast::TraitItem) -> SmallVector<ast::TraitItem> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_trait_item(item, self);
        }

        self.insert(item.span);

        let callsite = self.cx.codemap().source_callsite(self.get(item.span.clone()));
        self.expansions.get_mut(&callsite).unwrap().trace
            .push(pprust::trait_item_to_string(&item.clone()));

        return fold::noop_fold_trait_item(ast::TraitItem {span: self.get(item.span), .. item},
                                          self)
    }

    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {
        fold::noop_fold_mac(mac, self)
    }
}

// Struct for stepwise expansion - repeatedly expands a crate
// so long as it contains a (non macro-defining) macro invocation.
struct StepwiseExpander<'a> {
    has_mac: bool,
    mac_span: Span,
    data: ExpandData<'a>
}

impl<'a> StepwiseExpander<'a> {

    fn new(data: ExpandData<'a>) -> StepwiseExpander<'a> {
        StepwiseExpander { has_mac: false, mac_span: DUMMY_SP, data: data }
    }

    fn expand(mut self) -> Vec<MacroExpansion> {
        while !self.check_finished() {
            self.data.step_expand();
        }
        self.data.expansions.into_iter().map(|(_, v)| v).collect()
    }

    fn check_finished(&mut self) -> bool {
        self.has_mac = false;
        let krate = self.data.krates[self.data.index].clone();
        self.fold_crate(krate);
        !self.has_mac
    }
}

impl<'a> Folder for StepwiseExpander<'a> {
    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {

        if mac.node.path.segments == Vec::new() {
            // Placeholder macro showing a macro-rules expansion - ignored.
            return mac;
        }

        // Ignore macro definitions, we only care about macro calls.
        let extname = mac.node.path.segments[0].identifier.name.clone();
        if let Some(extension) = self.data.cx.syntax_env.find(extname) {
            if let SyntaxExtension::MacroRulesTT = *extension {
                return mac;
            }
        }

        self.has_mac = true;
        self.mac_span = mac.span.clone();

        // On the first expansion, want to store
        // macro calls as the root of their expansion traces.
        if self.data.index == 0 {
            self.data.expansions.insert(mac.span.clone(), MacroExpansion {
                callsite: mac.span.clone(),
                trace: vec!(pprust::mac_to_string(&mac)),
            });
        }

        mac
    }
}