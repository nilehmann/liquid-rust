use super::ast::*;
use super::constraint::*;

pub use rsmt2::errors::SmtRes;
pub use rsmt2::print::{Expr2Smt, Sym2Smt};
pub use rsmt2::Solver;

use std::io::Write;

impl Expr2Smt<()> for Pred {
    fn expr_to_smt2<Writer: Write>(&self, w: &mut Writer, info: ()) -> SmtRes<()> {
        match self {
            Pred::Op(o) => {
                write!(w, "{}", o)?;
            },
            Pred::Unary(PredUnOp::Not, p) => {
                write!(w, "(not ")?;
                p.expr_to_smt2(w, info)?;
                write!(w, ")")?;
            },
            Pred::Binary(b, p1, p2) => {
                if *b == PredBinOp::And {
                    write!(w, "(and ")?;
                } else {
                    write!(w, "{} ", b)?;
                }

                p1.expr_to_smt2(w, info)?;
                write!(w, " ")?;
                p2.expr_to_smt2(w, info)?;
                write!(w, ")")?;
            },
        }

        Ok(())
    }
}

impl Expr2Smt<()> for Constraint {
    fn expr_to_smt2<Writer: Write>(&self, w: &mut Writer, info: ()) -> SmtRes<()> {
        match self {
            Constraint::Pred(p) => {
                p.expr_to_smt2(w, info)?;
            },
            Constraint::Conj(c1, c2) => {
                write!(w, "(and ")?;
                c1.expr_to_smt2(w, info)?;
                write!(w, " ")?;
                c2.expr_to_smt2(w, info)?;
                write!(w, ")")?;
            },
            Constraint::Forall { ident, ty, hyp, con } => {
                // (forall ((x Nat)) (implies (p (pred x)) (p x)))
                write!(w, "(forall (({} {})) ", ident, ty)?;
                hyp.expr_to_smt2(w, info)?;
                write!(w, " ")?;
                con.expr_to_smt2(w, info)?;
                write!(w, ")")?;
            },
            Constraint::Implies(p, c) => {
                write!(w, "(=> ")?;
                p.expr_to_smt2(w, info)?;
                write!(w, " ")?;
                c.expr_to_smt2(w, info)?;
                write!(w, ")")?;
            }
        }

        Ok(())
    }
}
