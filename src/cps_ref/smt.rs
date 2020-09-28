use std::{collections::HashMap, path::Path};

use rsmt2::{self, print::Expr2Smt, print::Sort2Smt, print::Sym2Smt, SmtRes};

use super::ast::*;

pub struct ConstraintChecker {
    smt: rsmt2::Solver<()>,
}

// struct Var(u32);

// struct PredC {}

// impl ConstraintChecker {
//     pub fn new() -> Self {
//         let mut smt = rsmt2::Solver::default(()).expect("couldn't create solver");
//         let _ = smt.path_tee(Path::new("file.smt"));
//         Self { smt }
//     }

//     pub fn check(&mut self, constraint: &ConstraintP) -> SmtRes<()> {
//         match constraint {
//             ConstraintP::Implies(pred1, pred2) => {
//                 // self.smt
//                 //     .assert_with(&PredS::UnaryOp(UnOp::Not, pred), None)?;
//                 let a = self.smt.check_sat()?;
//                 // if a {
//                 //     println!("Cannot satisfy constraint {:?}", pred);
//                 // }
//             }
//             ConstraintP::Conj(cs) => {
//                 for c in cs {
//                     self.smt.push(1)?;
//                     self.check(c)?;
//                     self.smt.pop(1)?;
//                 }
//             }
//             ConstraintP::Binding { bind, typ, body } => {
//                 todo!();
//                 // self.embed(*bind, typ)?;
//                 // self.check(body)?;
//             }
//             Constraint::Guard(p, c) => {
//                 self.smt.assert_with(p, None)?;
//                 self.check(c)?;
//             }
//             Constraint::True => {}
//         }
//         Ok(())
//     }
// }

// impl Sort2Smt for BasicType {
//     fn sort_to_smt2<Writer>(&self, w: &mut Writer) -> SmtRes<()>
//     where
//         Writer: std::io::Write,
//     {
//         match self {
//             BasicType::Bool => write!(w, "Bool")?,
//             BasicType::Int => write!(w, "Int")?,
//         }
//         Ok(())
//     }
// }

// impl Sym2Smt<Option<Var>> for Var {
//     fn sym_to_smt2<Writer>(&self, w: &mut Writer, subst_nu: Option<Var>) -> SmtRes<()>
//     where
//         Writer: std::io::Write,
//     {
//         match self {
//             Var::Nu => {
//                 if let Some(x) = subst_nu {
//                     x.sym_to_smt2(w, None)?;
//                 } else {
//                     write!(w, "_v")?;
//                 }
//             }
//             Var::Location(l) => write!(w, "l${}", l.0)?,
//             Var::Field(f) => write!(w, "f${}", f.0)?,
//         }
//         Ok(())
//     }
// }

// impl Expr2Smt<Option<Var>> for PredS<'_> {
//     fn expr_to_smt2<Writer>(&self, w: &mut Writer, subst_nu: Option<Var>) -> SmtRes<()>
//     where
//         Writer: std::io::Write,
//     {
//         match self {
//             PredS::Constant(c) => c.expr_to_smt2(w, ())?,
//             PredS::Place { var, projection } => {
//                 var.sym_to_smt2(w, subst_nu)?;
//                 for p in projection {
//                     write!(w, ".{}", p)?;
//                 }
//             }
//             PredS::BinaryOp(op, lhs, rhs) => {
//                 write!(w, "({} ", bin_op_to_smt2(*op))?;
//                 lhs.expr_to_smt2(w, subst_nu)?;
//                 write!(w, " ")?;
//                 rhs.expr_to_smt2(w, subst_nu)?;
//                 write!(w, ")")?;
//             }
//             PredS::UnaryOp(UnOp::Not, operand) => {
//                 write!(w, "(not ")?;
//                 operand.expr_to_smt2(w, subst_nu)?;
//                 write!(w, ")")?;
//             }
//         }
//         Ok(())
//     }
// }

// impl Expr2Smt<()> for Constant {
//     fn expr_to_smt2<Writer>(&self, w: &mut Writer, _: ()) -> SmtRes<()>
//     where
//         Writer: std::io::Write,
//     {
//         match self {
//             Constant::Bool(b) => write!(w, "{}", b)?,
//             Constant::Int(i) => write!(w, "{}", i)?,
//         }
//         Ok(())
//     }
// }

// fn bin_op_to_smt2(op: BinOp) -> &'static str {
//     match op {
//         BinOp::Eq => "=",
//         BinOp::Lt => "<",
//         BinOp::Le => "<=",
//         BinOp::Gt => ">",
//         BinOp::Ge => ">=",
//         BinOp::Add => "+",
//         BinOp::Sub => "-",
//     }
// }
