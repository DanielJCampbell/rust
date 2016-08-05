// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::session::Session;
use rustc_metadata::cstore::CStore;
use rustc_metadata::macro_import;

use syntax::ast;
use syntax::attr;
use syntax::ext::base::{ExtCtxt, MacroLoader, SyntaxExtension};
use syntax::ext::expand;
use syntax::ext::expand::{ExpansionConfig, MacroExpander};
use syntax::codemap::{CodeMap, Span, ExpnInfo, NO_EXPANSION, DUMMY_SP};
use syntax::errors::Handler;
use syntax::errors::emitter::{ColorConfig};
use syntax::fold::{self, Folder};
use syntax::parse::{self, ParseSess};
use syntax::print::pprust::{print_crate, NoAnn};
use syntax::ptr::{self, P};
use syntax::util::small_vector::SmallVector;

use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::Error;
use std::path::Path;
use std::rc::Rc;

// Small macro to simplify setting the full-expansion closures to the identity closure.
macro_rules! set_expander_fns {
    ($expander:ident,
        $( $expand:ident ),*) => {{
        $( $expander.$expand = Rc::new(Box::new(|_, node| node )); )*
    }}
}

pub fn expand_crate(crate_name: String,
                    krate: ast::Crate,
                    sess: &'a Session) {

    let cfg = syntax::ext::expand::ExpansionConfig {
        crate_name: crate_name.clone(),
        features: Some(&sess.features.borrow()),
        recursion_limit: sess.recursion_limit.get(),
        trace_mac: sess.opts.debugging_opts.trace_macros,
        should_test: sess.opts.test,
    };

    let mut loader = macro_import::MacroLoader::new(sess, *sess.cstore.clone(), &crate_name);
    let data = ExpandData::new(crate_name, krate, cx);
    let expander = StepwiseExpander::new(data);

    expander.expand();

    //NOT YET COMPLETED
    unimplemented!();
}

struct ExpandData<'a> {
    filename: String,
    cx: ExtCtxt<'a>,
    krates: Vec<ast::Crate>,
    index: usize,
    span_map: HashMap<Span, Span>,
}

impl<'a> ExpandData<'a> {

    fn new(filename: String,
           cx: EcxCtxt<'a>,
           init_crate: ast::Crate) -> ExpandData<'a> {

        let mut krates = vec!();
        krates.push(init_crate);

        ExpandData {
            filename: filename,
            cx: ecx,
            krates: krates,
            index: 0,
            span_map: HashMap::new(),
        }
    }

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
            panic!("Callsite not found!");
        }
        let mut callsite = callsite.unwrap();

        if !self.span_map.contains_key(&callsite) {
            self.span_map.insert(key_sp, span);
            return;
        }

        let callee = self.cx.codemap().with_expn_info(span.expn_id,
                                                      |ei| ei.map(|ei| ei.callee.clone()));
        if callee.is_none() {
            panic!("Callee not found!");
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

    fn expand_crate(&mut self) {
        let mut krate = self.krates[self.index].clone();
        {
            let mut expander = MacroExpander::new(&mut self.cx, true);

            set_expander_fns!(expander,
                              expand_pat,
                              expand_ty,
                              expand_expr,
                              expand_stmt,
                              expand_item,
                              expand_impl_item,
                              expand_trait_item,
                              expand_opt_expr);


            krate = expand::expand_crate_with_expander(&mut expander,
                                                       Vec::new(),
                                                       krate).0;
        }



        krate = self.fold_crate(krate);

        self.krates.push(krate);
        self.index += 1;
    }

    fn write_file(&self) -> Result<(), Error> {
        let prefix = Path::new(&self.filename).file_stem()
                     .and_then(|stem| stem.to_str()).unwrap_or("");
        let parent = Path::new(&self.filename).parent()
                     .and_then(|path| path.to_str()).unwrap_or("");
        let file = try!(File::create(format!("{}/{}Output{}.rs", parent, prefix, self.index)));
        let ann = NoAnn;
        let handler = &self.cx.parse_sess().span_diagnostic;
        let mut src = try!(File::open(&self.filename.clone()));
        print_crate(self.cx.codemap(), handler, &self.krates[self.index],
                    self.filename.clone(), &mut src, Box::new(file), &ann, false).unwrap();
        Ok(())
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
        fold::noop_fold_pat(pat.map(|elt| ast::Pat { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_ty(&mut self, ty: P<ast::Ty>) -> P<ast::Ty> {
        if ty.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_ty(ty, self);
        }
        
        self.insert(ty.span);
        fold::noop_fold_ty(ty.map(|elt| ast::Ty { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_expr(&mut self, expr: P<ast::Expr>) -> P<ast::Expr> {
        if expr.span.expn_id == NO_EXPANSION {
            return ptr::P(fold::noop_fold_expr(expr.unwrap(), self));
        }
        
        self.insert(expr.span);
        ptr::P(fold::noop_fold_expr(expr.map(|elt| ast::Expr { span: self.get(elt.span), .. elt })
                                        .unwrap(), self))
    }

    fn fold_opt_expr(&mut self, opt: P<ast::Expr>) -> Option<P<ast::Expr>> {
        if opt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_opt_expr(opt, self);
        }
        
        self.insert(opt.span);
        fold::noop_fold_opt_expr(opt.map(|elt| ast::Expr { span: self.get(elt.span), .. elt }),
                                 self)
    }

    fn fold_item(&mut self, item: P<ast::Item>) -> SmallVector<P<ast::Item>> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_item(item, self);
        }
        
        self.insert(item.span);
        return fold::noop_fold_item(item.map(|elt| ast::Item { span: self.get(elt.span), .. elt }), self)
    }

    fn fold_stmt(&mut self, stmt: ast::Stmt) -> SmallVector<ast::Stmt> {
        if stmt.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_stmt(stmt, self);
        }

        self.insert(stmt.span);
        return fold::noop_fold_stmt(ast::Stmt { span: self.get(stmt.span), .. stmt }, self)
    }

    fn fold_impl_item(&mut self, item: ast::ImplItem) -> SmallVector<ast::ImplItem> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_impl_item(item, self);
        }
        
        self.insert(item.span);
        return fold::noop_fold_impl_item(ast::ImplItem { span: self.get(item.span), .. item }, self)
    }

    fn fold_trait_item(&mut self, item: ast::TraitItem) -> SmallVector<ast::TraitItem> {
        if item.span.expn_id == NO_EXPANSION {
            return fold::noop_fold_trait_item(item, self);
        }
        
        self.insert(item.span);
        return fold::noop_fold_trait_item(ast::TraitItem { span: self.get(item.span), .. item }, self)
    }

    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {
        fold::noop_fold_mac(mac, self)
    }
}

// Struct for checking if expansion is required.
// (Checking if AST contains macros)
struct StepwiseExpander<'a> {
    has_mac: bool,
    mac_span: Span,
    data: ExpandData<'a>
}

impl<'a> StepwiseExpander<'a> {

    fn new(data:ExpandData) -> MacChecker<'a, 'b> {
        MacChecker { has_mac: false, mac_span: DUMMY_SP, data: data }
    }

    fn expand() {
        unimplemented!();
    }

    fn check_finished(&mut self) -> bool {
        self.has_mac = false;
        let krate = self.data.krates[self.data.index].clone();
        self.fold_crate(krate);
        !self.has_mac
    }
}

impl<'a, 'b> Folder for MacChecker<'a, 'b> {
    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {

        if mac.node.path.segments == Vec::new() {
            //placeholder macro showing a macro-rules expansion - ignore
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
        mac //No need to expand further
    }
}