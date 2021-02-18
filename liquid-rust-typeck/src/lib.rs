#![feature(bindings_after_at)]
#![feature(box_syntax)]
#![feature(or_patterns)]

pub mod constraint;
pub mod env;
pub mod glob_env;
pub mod refineck;
pub mod region_inference;

use crate::{refineck::RefineChecker, region_inference::infer_regions};

use glob_env::GlobEnv;
use liquid_rust_core::{ast::Program, freshen::NameFreshener, lower::TypeLowerer, ty::TyCtxt};
pub use liquid_rust_fixpoint::solver::Safeness;

#[macro_use]
extern crate liquid_rust_common;

#[macro_use]
extern crate liquid_rust_core;

pub fn check_program<I>(program: Program<I>) {
    let tcx = TyCtxt::new();
    // println!("{}\n", program);
    let program = NameFreshener::new(&tcx).freshen(program);

    let mut glob_env = GlobEnv::new();
    for (fn_id, fn_def) in program.iter() {
        let (conts, fn_ty) = TypeLowerer::lower_fn_def(&tcx, &fn_def);
        // println!("{}\n", fn_def);
        let (conts, fn_ty) = infer_regions(&tcx, &fn_def, conts, fn_ty);
        glob_env.insert_fn(*fn_id, fn_ty, conts);
        // println!("{}\n", fn_def);
    }

    for (fn_id, fn_def) in program.iter() {
        println!("{}", fn_def);
        let constraint = RefineChecker::new(&tcx, &glob_env, *fn_id).check(fn_def);
        match constraint {
            Ok(constraint) => {
                // let safeness = constraint.lower().solve().unwrap().tag;
                // println!("{:?}", safeness);
                println!("{:?}", constraint.lower().solve());
            }
            Err(err) => {
                println!("{:?}", err)
            }
        }
    }
    // Ok(constraint.solve().unwrap().tag)
}
