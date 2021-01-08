// use std::collections::HashMap;

// use ast::{FnBody, StatementKind};
// use liquid_rust_core::{
//     ast::{self, ContDef, Place, Statement},
//     names::ContId,
//     ty::{self, TyCtxt},
// };

// use crate::{env::Env, synth::Synth};

// pub struct RefineChecker<'a> {
//     cont_tys: &'a HashMap<ContId, ty::ContTy>,
//     tcx: &'a TyCtxt,
//     env: Env<'a>,
// }

// impl RefineChecker<'_> {
//     fn check_body<I>(&mut self, body: &FnBody<I>) {
//         match body {
//             FnBody::LetCont(defs, rest) => {
//                 for def in defs {
//                     let cont_ty = &self.cont_tys[&def.name];
//                     let snapshot = self.env.snapshot_without_locals();
//                     let locals = cont_ty.locals(&def.params);
//                     self.env.insert_locals(locals);
//                     self.env.insert_heap(&cont_ty.heap);
//                     self.check_cont_def(def);
//                     self.env.rollback_to(snapshot);
//                 }
//                 self.check_body(rest);
//             }
//             FnBody::Ite { discr, then, else_ } => {
//                 let snapshot = self.env.snapshot();
//                 self.check_body(then);
//                 self.env.rollback_to(snapshot);
//                 self.check_body(else_);
//             }
//             FnBody::Call { func, args, ret } => {}
//             FnBody::Jump { target, args } => {
//                 let cont_ty = &self.cont_tys[target];
//                 for (x, l) in cont_ty.locals(args) {
//                     let ty1 = self.env.lookup(&Place::from(x));
//                     let ty2 = &cont_ty.heap[&l];
//                 }
//             }
//             FnBody::Seq(stmnt, rest) => {
//                 self.check_stmnt(stmnt);
//                 self.check_body(rest);
//             }
//             FnBody::Abort => {}
//         }
//     }

//     fn check_cont_def<I>(&mut self, def: &ContDef<I>) {}

//     fn check_stmnt<I>(&mut self, stmnt: &Statement<I>) {
//         match &stmnt.kind {
//             StatementKind::Let(x, layout) => {
//                 self.env.alloc(*x, self.tcx.mk_ty_for_layout(layout));
//             }
//             StatementKind::Assign(place, rvalue) => {
//                 let ty = rvalue.synth(self.tcx, &mut self.env);
//                 self.env.update(place, ty);
//             }
//             StatementKind::Drop(x) => self.env.drop(x),
//         }
//     }
// }
