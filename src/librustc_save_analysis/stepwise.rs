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

use syntax::codemap::{Span, ExpnInfo, ExpnFormat, NameAndSpan, DUMMY_SP, NO_EXPANSION, COMMAND_LINE_EXPN};
use syntax::fold::{self, Folder};
use syntax::parse::token::keywords;
use syntax::print::pprust;
use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;

use syntax_pos::{mk_sp, BytePos};

use std::collections::HashMap;

// A MacroExpansion consists of an expansion trace (mapped to a span in a HashMap),
// and a boolean marking whether or not expansion failed.
// The nth step of the trace is the pretty-printed text of the macro call
// after n expansions. If the expansion utltimately failed, failed == true,
// and the last element of the trace is an error message.

#[derive(Clone, Debug)]
pub struct MacroExpansion {
    pub trace: Vec<String>,
    pub failed: bool,
    // The last step_count on which we added to this trace
    last_depth: usize,
    // If this trace can still be extended - hasn't failed or finished.
    can_add: bool,
}

enum FoldMode {
    CheckMac, UpdateSpan, AddTrace
}

pub fn expand_crate(ecx: &mut ExtCtxt,
                    user_exts: Vec<NamedSyntaxExtension>,
                    c: ast::Crate)
                    -> (ast::Crate, HashMap<Span, MacroExpansion>) {
    // User extensions only need to be added once
    for (name, extension) in user_exts {
        ecx.syntax_env.insert(name, extension);
    }
    let mut expander = StepwiseExpander::new(ecx, c);
    expander.expand()
}

struct StepwiseExpander<'a, 'b:'a> {
    cx: &'a mut ExtCtxt<'b>,
    krate: ast::Crate,
    step_count: usize,
    block_count: usize,
    span_map: HashMap<Span, Span>,
    err_spans: HashMap<Span, Span>,
    expansions: HashMap<Span, MacroExpansion>,
    mode: FoldMode,
    has_mac: bool,
    // True if the mac to expand is a stmt (requires `;` appended to span).
    stmt_mac: bool,
}

impl<'a, 'b> StepwiseExpander<'a, 'b> {
    fn new(cx: &'a mut ExtCtxt<'b>,
           init_crate: ast::Crate) -> StepwiseExpander<'a, 'b> {

        StepwiseExpander {
            cx: cx,
            krate: init_crate,
            step_count: 0,
            block_count: 0,
            span_map: HashMap::new(),
            err_spans: HashMap::new(),
            expansions: HashMap::new(),
            mode: FoldMode::CheckMac,
            has_mac: false,
            stmt_mac: false,
        }
    }

    // When stepwise expanding, generated span traces will only ever be one level deep,
    // as they have no way of storing results from a previous step.
    // So we manually maintain a mapping from span without expn_id to span with expn_id.
    fn insert(&mut self, span: Span) {
        if span.expn_id == NO_EXPANSION {
            return;
        }
        let key_sp = Span {
            lo: span.lo,
            hi: span.hi,
            expn_id: NO_EXPANSION
        };
        let callsite = self.cx.codemap().with_expn_info(span.expn_id,
                                                        |ei| ei.map(|ei| ei.call_site.clone()));
        if callsite.is_none() {
            return;
        }
        let mut callsite = callsite.unwrap();

        // This is the first level of expansion - just stores proper expn_id.
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

    fn get(&self, span: Span) -> Span {
        let key_sp = Span { expn_id: NO_EXPANSION, .. span };
        return self.span_map.get(&key_sp).unwrap_or(&span).clone();
    }

    fn expand(&mut self) -> (ast::Crate, HashMap<Span, MacroExpansion>) {
        while !self.check_finished() {
            self.step_expand();
        }
        (self.krate.clone(), self.expansions.clone())
    }

    fn check_finished(&mut self) -> bool {
        let krate = self.krate.clone();
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        self.fold_crate(krate);
        !self.has_mac
    }

    // Checks if the AST node with this span came from a failed macro expansion.
    // If it did, return an updated span pointing to the original trace.
    fn check_error(&mut self, span: Span) -> (bool, Span) {
        let callsite = self.cx.codemap().source_callsite(span);
        if let Some(val) = self.err_spans.get(&callsite) {
            // First time encountering this, make expninfo point to root callsite.
            let callee = self.cx.codemap().with_expn_info(span.expn_id,
                                                          |ei| ei.map(|ei| ei.callee.clone()));
            // No callee means this is the result of invoking a non-existant macro.
            // Make up a dummy callee in that case.
            // Note: we need to give it Some(DUMMY_SP) rather than None or it won't generate save_analysis data.
            let callee = callee.unwrap_or(NameAndSpan {
                format: ExpnFormat::MacroBang(ast::Name(0)),
                allow_internal_unstable: false,
                span: Some(DUMMY_SP)
            });
            let callsite = val.clone();
            let info = ExpnInfo {
                call_site: callsite,
                callee: callee
            };
            let new_id = self.cx.codemap().record_expansion(info);
            println!("Attached new callsite to span");
            println!("Callsite: {}", self.cx.codemap().span_to_expanded_string(callsite));
            return (true, Span { expn_id: new_id, .. span });
        }
        // Other case: we've fixed this span before but its been re-folded.
        if let Some(val) = self.expansions.get(&callsite) {
            if val.failed {
                return (true, span)
            }
        }
        (false, DUMMY_SP)
    }

    fn step_expand(&mut self) {
        let mut krate = self.krate.clone();
        {
            let mut expander = MacroExpander::new(&mut self.cx, true, true);

            // To ensure we do not get caught in a non-terminating macro expansion,
            // we manually set the ExtCtxt recursion count to the step count.
            expander.cx.recursion_count = self.step_count;
            krate = expand::expand_crate_with_expander(&mut expander, Vec::new(), krate);
            for err in expander.cx.mac_errors.iter() {
                // Special case: errors spawned from recursive macro calls will not have the correct
                // source span from source_callsite. Need to manually recurse up the callsite tree. 
                let mut callsite = err.callsite;
                while callsite.expn_id != NO_EXPANSION && callsite.expn_id != COMMAND_LINE_EXPN {
                    if let Some(span) = expander.cx.codemap().with_expn_info(callsite.expn_id,
                                               |ei| ei.map(|ei| ei.call_site)) {
                        callsite = span;
                    }
                    else {
                        break;
                    }
                }
                let key_sp = Span { expn_id: NO_EXPANSION, .. err.callsite };
                if !self.err_spans.contains_key(&key_sp) {
                    if let Some(val) = self.expansions.get_mut(&callsite) {
                        val.trace.push(err.msg.clone());
                        val.failed = true;
                        val.can_add = false;
                    }
                    self.err_spans.insert(key_sp, callsite);
                }
            }
        }
        self.step_count += 1;
        // Update spans and MacroExpansion traces.
        self.mode = FoldMode::UpdateSpan;
        krate = self.fold_crate(krate);
        self.mode = FoldMode::AddTrace;
        self.krate = self.fold_crate(krate);
    }
}

// Walk over AST of expanded crate to patch up spans and update expansion traces.
impl<'a, 'b> Folder for StepwiseExpander<'a, 'b> {
    fn fold_crate(&mut self, krate: ast::Crate) -> ast::Crate {
        fold::noop_fold_crate(krate, self)
    }

    // Keep track of current level of indentation for use in formatting the trace.
    fn fold_block(&mut self, block: P<ast::Block>) -> P<ast::Block> {
        self.block_count += 1;
        let res = fold::noop_fold_block(block, self);
        self.block_count -= 1;
        res
    }

    fn fold_pat(&mut self, pat: P<ast::Pat>) -> P<ast::Pat> {
        if let FoldMode::CheckMac = self.mode {
            return fold::noop_fold_pat(pat, self);
        }
        if let (true, sp) = self.check_error(pat.span) {
            return fold::noop_fold_pat(pat.map(|elt| ast::Pat { span: sp, .. elt }), self);
        }
        if pat.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_pat(pat, self);
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(pat.span);
            return fold::noop_fold_pat(pat.map(|elt| ast::Pat { span: self.get(elt.span),
                                                                .. elt }), self);
        }
        let callsite = self.cx.codemap().source_callsite(self.get(pat.span));
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_pat(pat.clone(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::pat_to_string(&pat));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return pat;
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                val.trace.push(pprust::pat_to_string(&pat));
            }
        }
        pat
    }

    fn fold_ty(&mut self, ty: P<ast::Ty>) -> P<ast::Ty> {
        if let FoldMode::CheckMac = self.mode {
            return fold::noop_fold_ty(ty, self);
        }
        if let (true, sp) = self.check_error(ty.span) {
            return fold::noop_fold_ty(ty.map(|elt| ast::Ty { span: sp, .. elt }), self);
        }
        if ty.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_ty(ty, self);
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(ty.span);
            return fold::noop_fold_ty(ty.map(|elt| ast::Ty { span: self.get(elt.span),
                                                             .. elt }), self);
        }
        let callsite = self.cx.codemap().source_callsite(self.get(ty.span));
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_ty(ty.clone(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::ty_to_string(&ty));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return ty;
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                self.mode = FoldMode::AddTrace;
                val.trace.push(pprust::ty_to_string(&ty));
            }
        }
        ty
    }

    fn fold_expr(&mut self, expr: P<ast::Expr>) -> P<ast::Expr> {
        if let FoldMode::CheckMac = self.mode {
            return P(fold::noop_fold_expr(expr.unwrap(), self));
        }
        if let (true, sp) = self.check_error(expr.span) {
            return P(fold::noop_fold_expr(expr.map(|elt| ast::Expr { span: sp, .. elt }).unwrap(),
                                          self))
        }
        if expr.span.expn_id == NO_EXPANSION {
            return P(fold::noop_fold_expr(expr.unwrap(), self));
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(expr.span.clone());
            return P(fold::noop_fold_expr(expr.map(|elt| ast::Expr { span: self.get(elt.span),
                                                                     .. elt }).unwrap(), self))
        }
        let callsite = self.cx.codemap().source_callsite(self.get(expr.span));
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_expr(expr.clone().unwrap(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::expr_to_string(&expr));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return expr;
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                val.trace.push(pprust::expr_to_string(&expr));
            }
        }
        expr
    }

    fn fold_opt_expr(&mut self, opt: P<ast::Expr>) -> Option<P<ast::Expr>> {
        if let FoldMode::CheckMac = self.mode {
            return fold::noop_fold_opt_expr(opt, self);
        }
        if let (true, sp) = self.check_error(opt.span) {
            return fold::noop_fold_opt_expr(opt.map(|elt| ast::Expr { span: sp, .. elt }), self);
        }
        if opt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_opt_expr(opt, self);
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(opt.span);
            return fold::noop_fold_opt_expr(opt.map(|elt| ast::Expr { span: self.get(elt.span),
                                                                      .. elt }), self);
        }
        let callsite = self.cx.codemap().source_callsite(self.get(opt.span));
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_opt_expr(opt.clone(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::expr_to_string(&opt));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return Some(opt);
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                val.trace.push(pprust::expr_to_string(&opt));
            }
        }
        Some(opt)
    }

    fn fold_item(&mut self, item: P<ast::Item>) -> SmallVector<P<ast::Item>> {
        if item.ident == keywords::Invalid.ident() {
            if let ast::ItemKind::Mac(ref mac) = item.node {
                if mac.node.path.segments == Vec::new() {
                    // Placeholder item showing a failed macro rules expansion
                    return SmallVector::zero();
                }
            }
        }
        if let FoldMode::CheckMac = self.mode {
            return fold::noop_fold_item(item, self);
        }
        if let (true, sp) = self.check_error(item.span) {
            return fold::noop_fold_item(item.map(|elt| ast::Item { span: sp, .. elt }), self);
        }
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_item(item, self);
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(item.span);
            return fold::noop_fold_item(item.map(|elt| ast::Item { span: self.get(elt.span),
                                                                   .. elt }), self);
        }
        let callsite = self.cx.codemap().source_callsite(self.get(item.span));
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_item(item.clone(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::item_to_string(&item));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return SmallVector::one(item);
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                val.trace.push(pprust::item_to_string(&item));
            }
        }
        SmallVector::one(item)
    }

    fn fold_stmt(&mut self, stmt: ast::Stmt) -> SmallVector<ast::Stmt> {
        if let FoldMode::CheckMac = self.mode {
            if let ast::StmtKind::Mac(val) = stmt.clone().node {
                if let (_, ast::MacStmtStyle::Semicolon, _) = *val {
                    self.stmt_mac = true;
                    let res = fold::noop_fold_stmt(stmt, self);
                    self.stmt_mac = false;
                    return res;
                }
            }
            return fold::noop_fold_stmt(stmt, self);
        }
        if let (true, sp) = self.check_error(stmt.span) {
            return fold::noop_fold_stmt(ast::Stmt { span: sp, .. stmt }, self);
        }
        if stmt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_stmt(stmt, self);
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(stmt.span);
            return fold::noop_fold_stmt(ast::Stmt { span: self.get(stmt.span), .. stmt }, self);
        }
        let callsite = self.cx.codemap().source_callsite(self.get(stmt.span));
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_stmt(stmt.clone(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::stmt_to_string(&stmt));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return SmallVector::one(stmt);
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                val.trace.push(pprust::stmt_to_string(&stmt));
            }
        }
        SmallVector::one(stmt)
    }

    fn fold_impl_item(&mut self, item: ast::ImplItem) -> SmallVector<ast::ImplItem> {
        if let FoldMode::CheckMac = self.mode {
            return fold::noop_fold_impl_item(item, self);
        }
        if let (true, sp) = self.check_error(item.span) {
            return fold::noop_fold_impl_item(ast::ImplItem { span: sp, .. item }, self);
        }
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_impl_item(item, self);
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(item.span);
            return fold::noop_fold_impl_item(ast::ImplItem { span: self.get(item.span), .. item },
                                             self);
        }
        let callsite = self.cx.codemap().source_callsite(self.get(item.span));
        // Check if this AST needs further expansion.
        // If not, disallow future adds (to account for other ongoing expansions).
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_impl_item(item.clone(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::impl_item_to_string(&item));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return SmallVector::one(item);
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                val.trace.push(pprust::impl_item_to_string(&item));
            }
        }
        SmallVector::one(item)
    }

    fn fold_trait_item(&mut self, item: ast::TraitItem) -> SmallVector<ast::TraitItem> {
        if let FoldMode::CheckMac = self.mode {
            return fold::noop_fold_trait_item(item, self);
        }
        if let (true, sp) = self.check_error(item.span) {
            return fold::noop_fold_trait_item(ast::TraitItem {span: sp, .. item}, self);
        }
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_trait_item(item, self);
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(item.span);
            return fold::noop_fold_trait_item(ast::TraitItem {span: self.get(item.span), .. item},
                                              self);
        }
        let callsite = self.cx.codemap().source_callsite(self.get(item.span));
        // Check if this AST needs further expansion.
        // If not, disallow future adds (to account for other ongoing expansions).
        self.has_mac = false;
        self.mode = FoldMode::CheckMac;
        fold::noop_fold_trait_item(item.clone(), self);
        self.mode = FoldMode::AddTrace;
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::trait_item_to_string(&item));
                val.trace.push(prev);
                // Can't be sure we're done with expansion until all expanded parts checked.
                if self.has_mac && val.can_add == false {
                    val.can_add = true;
                }
            }
            // Check that we can add to this trace.
            else { 
                if !val.can_add {
                    return SmallVector::one(item);
                }
                val.last_depth = index;
                if !self.has_mac {
                    val.can_add = false;
                }
                val.trace.push(pprust::trait_item_to_string(&item));
            }
        }
        SmallVector::one(item)
    }

    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {
        if mac.node.path.segments == Vec::new() {
            // Placeholder macro showing a macro-rules expansion - ignored.
            return mac;
        }
        // Ignore macro definitions and attribute macros, we only care about macro calls.
        let extname = mac.node.path.segments[0].identifier.name.clone();
        if let Some(extension) = self.cx.syntax_env.find(extname) {
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
        if let FoldMode::CheckMac = self.mode {
            if self.step_count == 0 {
                // Some stmt macros do not have a semicolon in their span.
                // However, the generated callsites do have a semicolon.
                // We manually append this semicolon when necessary.
                let stmt_span = mk_sp(mac.span.lo, mac.span.hi + (BytePos(1)));
                let snippet = match self.cx.codemap().span_to_snippet(stmt_span.end_point()) {
                    Ok(snip) => snip,
                    Err(_) => "".to_owned()
                };
                if snippet == ";".to_owned() && self.stmt_mac {
                    self.expansions.insert(stmt_span, MacroExpansion {
                        trace: vec!(pprust::mac_to_string(&mac)),
                        failed: false,
                        last_depth: 0,
                        can_add: true,
                    });
                }
                else {
                    self.expansions.insert(mac.span, MacroExpansion {
                        trace: vec!(pprust::mac_to_string(&mac)),
                        failed: false,
                        last_depth: 0,
                        can_add: true,
                    });
                }
            }
            return mac;
        }

        // Still need to update macro invocation spans and add them to trace as for any other AST.
        if let (true, sp) = self.check_error(mac.span) {
            return ast::Mac { span: sp, .. mac };
        }
        if mac.span.expn_id == NO_EXPANSION {
            return mac;
        }
        if let FoldMode::UpdateSpan = self.mode {
            self.insert(mac.span);
            return ast::Mac { span: self.get(mac.span), .. mac };
        }
        let callsite = self.cx.codemap().source_callsite(self.get(mac.span));
        if let Some(val) = self.expansions.get_mut(&callsite) {
            let index = self.step_count+1;
            // Continuing an add from this step, no checks required.
            if val.last_depth == index {
                let mut prev = val.trace.pop().unwrap();
                prev.push_str("\n");
                for _ in 0..self.block_count {
                    prev.push_str("    ");
                }
                prev.push_str(&pprust::mac_to_string(&mac));
                val.trace.push(prev);
            }
            else { 
                val.last_depth = index;
                // A mac call will always need future expansion.
                val.trace.push(pprust::mac_to_string(&mac));
            }
        }
        mac
    }
}
