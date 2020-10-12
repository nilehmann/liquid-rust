use std::{
    fs::File,
    io::{self, BufWriter, Write},
    path::Path,
    process::{Command, Stdio},
};

use ast::BasicType;

use super::{
    ast,
    constraint::{Constraint, PredC},
};

pub struct LiquidSolver {
    buf: BufWriter<File>,
}

impl LiquidSolver {
    pub fn new() -> io::Result<Self> {
        use std::fs::OpenOptions;
        let path = Path::new("file.smt2");
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;
        let buf = BufWriter::with_capacity(1000, file);

        Ok(Self { buf })
    }

    pub fn check(mut self, c: &Constraint) -> io::Result<bool> {
        write!(self.buf, "(constraint ")?;
        self.write_constraint(c)?;
        write!(self.buf, ")")?;
        self.buf.flush()?;
        let st = Command::new("fixpoint")
            .arg("file.smt2")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .status()?;
        Ok(st.success())
    }

    fn write_constraint(&mut self, c: &Constraint) -> io::Result<()> {
        match c {
            Constraint::Pred(p) => {
                write!(self.buf, "(")?;
                self.write_pred(p)?;
                write!(self.buf, ")")?;
            }
            Constraint::Conj(cs) => match cs.len() {
                0 => write!(self.buf, "true")?,
                1 => self.write_constraint(&cs[0])?,
                _ => {
                    write!(self.buf, "(and ")?;
                    for c in cs {
                        self.write_constraint(c)?;
                        write!(self.buf, "")?;
                    }
                    write!(self.buf, ")")?;
                }
            },
            Constraint::Forall {
                bind,
                ty,
                hyp,
                body,
            } => {
                write!(self.buf, "(forall (({} ", bind)?;
                match ty {
                    BasicType::Bool => write!(self.buf, "bool")?,
                    BasicType::Int => write!(self.buf, "int")?,
                }
                write!(self.buf, ") (")?;
                self.write_pred(hyp)?;
                write!(self.buf, ")) ")?;
                self.write_constraint(body)?;
                write!(self.buf, ")")?;
            }
            Constraint::Guard(p, c) => {
                write!(self.buf, "(forall ((_ int) (")?;
                self.write_pred(p)?;
                write!(self.buf, ")) ")?;
                self.write_constraint(c)?;
                write!(self.buf, ")")?;
            }
            Constraint::True => write!(self.buf, "true")?,
            Constraint::Err => bug!(),
        }
        Ok(())
    }

    fn write_pred(&mut self, p: &PredC) -> io::Result<()> {
        match p {
            PredC::Var(v) => {
                write!(self.buf, "{}", &*v.as_str())?;
            }
            PredC::Constant(c) => {
                write!(self.buf, "{:?}", c)?;
            }
            PredC::BinaryOp(op, lhs, rhs) => {
                write!(self.buf, "(")?;
                self.write_pred(lhs)?;
                write!(self.buf, " {:?} ", op)?;
                self.write_pred(rhs)?;
                write!(self.buf, ")")?;
            }
            PredC::UnaryOp(op, operand) => match op {
                ast::UnOp::Not => {
                    write!(self.buf, "(not ")?;
                    self.write_pred(operand)?;
                    write!(self.buf, ")")?;
                }
            },
            PredC::Iff(lhs, rhs) => {
                write!(self.buf, "(")?;
                self.write_pred(lhs)?;
                write!(self.buf, " <=> ")?;
                self.write_pred(rhs)?;
                write!(self.buf, ")")?;
            }
        }
        Ok(())
    }
}
