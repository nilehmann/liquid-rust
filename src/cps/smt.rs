use super::ast::*;
use super::constraint::*;

pub use rsmt2::errors::SmtRes;
pub use rsmt2::print::{Expr2Smt, Sym2Smt};
pub use rsmt2::Solver;

use std::io::Write;

enum Token<'a, T, U> {
    Expr(&'a T),
    Alt(&'a U),
    Space,
    Paren,
}

impl Expr2Smt<()> for Pred {
    fn expr_to_smt2<Writer: Write>(&self, w: &mut Writer, info: ()) -> SmtRes<()> {
        let mut stack = vec![Token::Expr(self)];
        while let Some(token) = stack.pop() {
            match token {
                Token::Expr(Pred::Op(o)) => {
                    write!(w, "{}", o)?;
                }
                Token::Expr(Pred::Unary(PredUnOp::Not, p)) => {
                    write!(w, "(not ")?;
                    stack.push(Token::Paren);
                    stack.push(Token::Expr(p));
                }
                Token::Expr(Pred::Binary(b, p1, p2)) => {
                    if *b == PredBinOp::And {
                        write!(w, "(and ")?;
                    } else {
                        write!(w, "({} ", b)?;
                    }

                    stack.push(Token::Paren);
                    stack.push(Token::Expr(p2));
                    stack.push(Token::Space);
                    stack.push(Token::Expr(p1));
                }
                Token::Alt(()) => {},
                Token::Space => write!(w, " ")?,
                Token::Paren => write!(w, ")")?,
            }
        }

        Ok(())
    }
}

impl Expr2Smt<()> for Constraint {
    fn expr_to_smt2<Writer: Write>(&self, w: &mut Writer, info: ()) -> SmtRes<()> {
        let mut stack: Vec<Token<Constraint, Pred>> = vec![Token::Expr(self)];
        while let Some(token) = stack.pop() {
            match token {
                Token::Expr(Constraint::Pred(p)) => {
                    p.expr_to_smt2(w, info)?;
                }
                Token::Alt(bp) => {
                    bp.expr_to_smt2(w, info)?;
                }
                Token::Expr(Constraint::Conj(c1, c2)) => {
                    write!(w, "(and ")?;
                    stack.push(Token::Paren);
                    stack.push(Token::Expr(c2));
                    stack.push(Token::Space);
                    stack.push(Token::Expr(c1));
                }
                Token::Expr(Constraint::Forall {
                    ident,
                    ty,
                    hyp,
                    con,
                }) => {
                    // (forall ((ident ty)) (=> hyp con))
                    write!(w, "(forall (({} {})) (=> ", ident, ty)?;
                    stack.push(Token::Paren);
                    stack.push(Token::Paren);
                    stack.push(Token::Expr(con));
                    stack.push(Token::Space);
                    stack.push(Token::Alt(&*hyp));
                }
                Token::Expr(Constraint::Implies(hyp, con)) => {
                    write!(w, "(=> ")?;
                    stack.push(Token::Paren);
                    stack.push(Token::Expr(con));
                    stack.push(Token::Space);
                    stack.push(Token::Alt(&*hyp));
                }
                Token::Space => write!(w, " ")?,
                Token::Paren => write!(w, ")")?,
            }
        }

        Ok(())
    }
}
