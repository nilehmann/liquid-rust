//! Implements a basic name-checking phase to check that no function names are
//! duplicated and no names are referenced without being defined first.

// TODOs:
// - Use actual error types
// - Propagate extra context at each level
// - Do smth with source info

use crate::{
    ast::{
        pred::{Pred, Var},
        *,
    },
    names::{ContId, Field, FnId, Local, Location},
};
use quickscope::ScopeSet;
use std::collections::HashSet;

pub struct NameChecker<S> {
    fns: HashSet<FnId<S>>,
    locals: ScopeSet<Local<S>>,
    locations: ScopeSet<Location<S>>,
    fields: ScopeSet<Field<S>>,
    conts: ScopeSet<ContId<S>>,
}

impl<S> NameChecker<S>
where
    S: Eq + Copy + std::hash::Hash + std::fmt::Debug,
{
    pub fn new() -> Self {
        Self {
            fns: HashSet::new(),
            locals: ScopeSet::new(),
            locations: ScopeSet::new(),
            fields: ScopeSet::new(),
            conts: ScopeSet::new(),
        }
    }

    pub fn check<I>(mut self, program: &Program<I, S>) {
        for (fn_id, def) in program.iter() {
            // We first check if the function has already been defined;
            // we error out if this is the case
            if !self.fns.insert(*fn_id) {
                panic!("NameChecker: duplicate function {:?} defined", fn_id);
            } else {
                self.check_fn_def(def);
            }
        }

        todo!()
    }

    pub fn push_fn_scope(&mut self) {
        self.locals.push_layer();
        self.locations.push_layer();
        self.fields.push_layer();
        self.conts.push_layer();
    }

    pub fn pop_fn_scope(&mut self) {
        self.locals.pop_layer();
        self.locations.pop_layer();
        self.fields.pop_layer();
        self.conts.pop_layer();
    }

    pub fn check_fn_def<I>(&mut self, def: &FnDef<I, S>) {
        self.push_fn_scope();

        // First, push the return continuation into our scope
        self.conts.define(def.ret);

        // First, check the type of the function
        self.check_fn_decl(&def.ty);

        // We then check the params of the function
        self.check_params(&def.params);

        // Finally, we check the body
        self.check_body(&def.body);

        // And pop our scope
        self.pop_fn_scope();
    }

    pub fn check_fn_decl(&mut self, ty: &FnDecl<S>) {
        // First, we check that each input corresponds to something in the
        // in_heap, and each output corresponds to something in the out_heap.
        // For now, we do this super inefficiently and for each item in the
        // input and output, we just search through the heaps for the
        // corresponding item.
        for (inl, inloc) in &ty.inputs {
            if !ty.in_heap.iter().find(|(x, _ty)| x == inloc).is_some() {
                // If we can't find the corresponding location of the input
                // local in the input heap, panic and complain
                panic!(
                    "NameChecker: local {:?} references undefined location {:?}",
                    inl, inloc
                );
            }

            // Record the local as defined
            self.locals.define(*inl);
        }

        for (outl, outloc) in &ty.outputs {
            if !ty.out_heap.iter().find(|(x, _ty)| x == outloc).is_some() {
                // Same with the outputs
                panic!(
                    "NameChecker: local {:?} references undefined location {:?}",
                    outl, outloc
                );
            }

            // For output locals, don't record them as defined
        }

        // We then go through the types defined in the heaps, checking each of
        // the types. We also record the locals we've seen so far so we know
        // if a local is defined.
        for (inloc, inty) in ty.in_heap.iter() {
            // We record the location as defined
            self.locations.define(*inloc);

            // and check the type
            self.check_ty(inty);
        }

        // We don't want the output locations and types to be in the scope of
        // the body
        self.locations.push_layer();

        for (outloc, outty) in ty.out_heap.iter() {
            self.locations.define(*outloc);
            self.check_ty(outty);
        }
    }

    fn check_params(&mut self, params: &[Local<S>]) {
        for param in params {
            self.check_local(*param);
        }
    }

    fn check_body<I>(&mut self, body: &FnBody<I, S>) {
        use FnBody::*;

        match body {
            LetCont(defs, box rest) => {
                self.conts.push_layer();
                for def in defs {
                    self.conts.define(def.name);
                    self.check_cont_def(def);
                }

                self.check_body(rest);
                self.conts.pop_layer();
            }
            Ite {
                discr,
                box then,
                box else_,
            } => {
                self.check_place(discr);
                self.check_body(then);
                self.check_body(else_);
            }
            Call {
                func,
                args,
                destination,
            } => {
                // We first check that the function is in our list of functions
                if !self.fns.contains(&func) {
                    panic!("NameChecker: function {:?} not defined", func);
                }

                // Then check the arguments
                self.check_params(args);

                for (place, ret) in destination {
                    self.check_place(place);
                    self.check_cont_id(*ret);
                }
            }
            Jump { target, args } => {
                self.check_cont_id(*target);
                self.check_params(args);
            }
            Seq(statement, box rest) => {
                self.locals.push_layer();
                self.check_statement(statement);
                self.check_body(rest);
                self.locals.pop_layer();
            }
            Abort => {}
        }
    }

    fn check_cont_def<I>(&mut self, cont: &ContDef<I, S>) {
        self.locals.push_layer();

        for local in &cont.params {
            self.locals.define(*local);
        }

        self.locations.push_layer();

        for (location, _) in &cont.ty.heap {
            self.locations.define(*location);
        }

        self.check_cont_id(cont.name);
        self.check_cont_ty(&cont.ty);
        self.check_params(&cont.params);
        self.check_body(&cont.body);

        self.locations.pop_layer();
        self.locals.pop_layer();
    }

    fn check_cont_ty(&mut self, cont_ty: &ContTy<S>) {
        for l in &cont_ty.inputs {
            self.check_location(*l);
        }

        // check the heap
        for (inloc, inty) in &cont_ty.heap {
            self.check_location(*inloc);
            self.check_ty(inty);
        }

        // and check our locals
        for (inl, inloc) in &cont_ty.locals {
            if !cont_ty.heap.iter().find(|(x, _ty)| x == inloc).is_some() {
                // If we can't find the corresponding location of the input
                // local in the input heap, panic and complain
                panic!(
                    "NameChecker: local {:?} references undefined location {:?}",
                    inl, inloc
                );
            }

            // Check the local
            self.check_local(*inl);
        }
    }

    fn check_statement<I>(&mut self, statement: &Statement<I, S>) {
        use StatementKind::*;

        match &statement.kind {
            StatementKind::Let(local, _layout) => {
                self.locals.define(*local);
            }
            StatementKind::Assign(place, value) => {
                self.check_place(&place);
                self.check_rvalue(&value);
            }
            Drop(place) => self.check_place(&place),
            Nop => {}
        }
    }

    fn check_rvalue(&mut self, rvalue: &Rvalue<S>) {
        use Rvalue::*;

        match rvalue {
            Use(op) => self.check_operand(op),
            Ref(_kind, place) => self.check_place(place),
            BinaryOp(_op, lhs, rhs) => {
                self.check_operand(lhs);
                self.check_operand(rhs);
            }
            CheckedBinaryOp(_op, lhs, rhs) => {
                self.check_operand(lhs);
                self.check_operand(rhs);
            }
            UnaryOp(_op, operand) => self.check_operand(&operand),
        }
    }

    fn check_operand(&mut self, operand: &Operand<S>) {
        use Operand::*;

        match operand {
            Copy(place) => self.check_place(&place),
            Move(place) => self.check_place(&place),
            Constant(_c) => {}
        }
    }

    pub fn check_ty(&mut self, ty: &Ty<S>) {
        use Ty::*;

        match ty {
            OwnRef(location) => self.check_location(*location),
            Ref(_kind, _reg, location) => self.check_location(*location),
            Tuple(tup) => {
                self.fields.push_layer();
                for (fld, fty) in tup {
                    self.fields.define(*fld);
                    self.check_ty(fty);
                }
                self.fields.pop_layer();
            }
            Uninit(_s) => {}
            Refine(_bty, refine) => self.check_refine(refine),
        }
    }

    fn check_refine(&mut self, refine: &Refine<S>) {
        match refine {
            Refine::Infer => {}
            Refine::Pred(pred) => self.check_pred(pred),
        }
    }

    fn check_pred(&mut self, pred: &Pred<S>) {
        use Pred::*;

        match pred {
            Constant(_c) => {}
            Place(pred::Place {
                base,
                projs: _projs,
            }) => self.check_var(*base),
            BinaryOp(_op, box lhs, box rhs) => {
                self.check_pred(lhs);
                self.check_pred(rhs);
            }
            UnaryOp(_op, box operand) => self.check_pred(operand),
        }
    }

    fn check_var(&mut self, var: Var<S>) {
        match var {
            Var::Nu => {}
            Var::Location(location) => self.check_location(location),
            Var::Field(field) => self.check_field(field),
        }
    }

    fn check_place(&mut self, place: &Place<S>) {
        self.check_local(place.base);
    }

    fn check_cont_id(&mut self, c: ContId<S>) {
        if !self.conts.contains(&c) {
            panic!("NameChecker: cont {:?} undefined", c);
        }
    }

    fn check_field(&mut self, f: Field<S>) {
        if !self.fields.contains(&f) {
            panic!("NameChecker: field {:?} undefined", f);
        }
    }

    fn check_local(&mut self, l: Local<S>) {
        if !self.locals.contains(&l) {
            panic!("NameChecker: local {:?} undefined", l);
        }
    }

    fn check_location(&mut self, l: Location<S>) {
        if !self.locations.contains(&l) {
            panic!("NameChecker: location {:?} undefined", l);
        }
    }
}
