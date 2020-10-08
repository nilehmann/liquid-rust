use std::path::Path;

use rsmt2::{
    self,
    print::{Expr2Smt, Sort2Smt},
    SmtRes,
};

use super::{ast::*, constraint::Constraint, constraint::PredC};

pub struct ConstraintChecker {
    smt: rsmt2::Solver<()>,
}

impl ConstraintChecker {
    pub fn new() -> Self {
        let mut smt = rsmt2::Solver::default(()).expect("couldn't create solver");
        let _ = smt.path_tee(Path::new("file.smt"));
        Self { smt }
    }

    pub fn check(&mut self, constraint: &Constraint) -> SmtRes<()> {
        match constraint {
            Constraint::Pred(pred) => {
                self.smt.assert_with(&pred, true)?;
                if self.smt.check_sat()? {
                    todo!("Cannot satisfy constraint");
                }
            }
            Constraint::Conj(cs) => {
                for c in cs {
                    self.smt.push(1)?;
                    self.check(c)?;
                    self.smt.pop(1)?;
                }
            }
            Constraint::Forall {
                bind,
                ty,
                hyp,
                body,
            } => {
                self.smt.declare_const(&*bind.as_str(), &ty)?;
                self.smt.assert(&hyp)?;
                self.check(body)?;
            }
            Constraint::Guard(p, c) => {
                self.smt.assert(&p)?;
                self.check(c)?;
            }
            Constraint::True => {}
            Constraint::Err => bug!(),
        }
        Ok(())
    }
}

impl Sort2Smt for BasicType {
    fn sort_to_smt2<Writer>(&self, w: &mut Writer) -> SmtRes<()>
    where
        Writer: std::io::Write,
    {
        match self {
            BasicType::Bool => write!(w, "Bool")?,
            BasicType::Int => write!(w, "Int")?,
        }
        Ok(())
    }
}

impl Expr2Smt<()> for PredC {
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, _: ()) -> SmtRes<()>
    where
        Writer: std::io::Write,
    {
        match self {
            PredC::Constant(c) => c.expr_to_smt2(w, ())?,
            PredC::Var(s) => write!(w, "{}", &*s.as_str())?,
            PredC::BinaryOp(op, lhs, rhs) => {
                write!(w, "({} ", bin_op_to_smt2(*op))?;
                lhs.expr_to_smt2(w, ())?;
                write!(w, " ")?;
                rhs.expr_to_smt2(w, ())?;
                write!(w, ")")?;
            }
            PredC::UnaryOp(UnOp::Not, operand) => {
                write!(w, "(not ")?;
                operand.expr_to_smt2(w, ())?;
                write!(w, ")")?;
            }
        }
        Ok(())
    }
}

impl Expr2Smt<bool> for PredC {
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, negate: bool) -> SmtRes<()>
    where
        Writer: std::io::Write,
    {
        if negate {
            write!(w, "(not ")?;
        }
        Expr2Smt::expr_to_smt2(self, w, ())?;
        if negate {
            write!(w, ")")?;
        }
        Ok(())
    }
}

impl Expr2Smt<()> for Constant {
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, _: ()) -> SmtRes<()>
    where
        Writer: std::io::Write,
    {
        match self {
            Constant::Bool(b) => write!(w, "{}", b)?,
            Constant::Int(i) => write!(w, "{}", i)?,
        }
        Ok(())
    }
}

fn bin_op_to_smt2(op: BinOp) -> &'static str {
    match op {
        BinOp::Eq => "=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Add => "+",
        BinOp::Sub => "-",
    }
}
