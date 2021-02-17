//! Implements a basic name-checking phase to check that no function names are
//! duplicated and no names are referenced without being defined first.

use crate::{
    ast::*,
    names::{FnId, Local},
};
use quickscope::ScopeSet;
use std::collections::HashSet;

pub struct NameChecker<S> {
    fns: HashSet<FnId<S>>,
    vars: ScopeSet<Local<S>>,
}

impl<S> NameChecker<S>
where
    S: Eq + Copy + std::hash::Hash + std::fmt::Debug,
{
    pub fn new() -> Self {
        Self {
            fns: HashSet::new(),
            vars: ScopeSet::new(),
        }
    }

    pub fn check<I>(mut self, program: &Program<I, S>) {
        for (fn_id, def) in program.iter() {
            // self.check_

            // We first check if the function has already been defined;
            // we error out if this is the case
            if !self.fns.insert(*fn_id) {
                panic!("NameChecker: duplicate function {:?} defined", fn_id);
            } else {
            }
        }

        todo!()
    }

    pub fn check_fn_def<I>(&mut self, def: &FnDef<I, S>) {
        // When checking a function definition, we have to check four different
        // parts:

        // First, check the type of the function

        // We don't need to check the params since they're generated by us:
        // we can assume they're okay

        // We then check the body

        // Finally, we check that the return continuation (something)
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
        }

        for (outl, outloc) in &ty.outputs {
            if !ty.out_heap.iter().find(|(x, _ty)| x == outloc).is_some() {
                // Same with the outputs
                panic!(
                    "NameChecker: local {:?} references undefined location {:?}",
                    outl, outloc
                );
            }
        }

        // We then go through the types defined in the heaps, checking each of
        // the types. We also record the locals we've seen so far so we know
        // if a local is defined.
        for (inloc, inty) in ty.in_heap.iter() {

        }

        for (outloc, outty) in ty.out_heap.iter() {

        }
    }
}
