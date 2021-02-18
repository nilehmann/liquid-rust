#![allow(clippy::clippy::unused_self)]
use crate::{ast, names::*};
use std::fmt;

macro_rules! indent {
    ($formatter:expr, $indent:expr) => {
        ::std::write!($formatter, "\n{:>1$}", "", $indent)
    };
}

macro_rules! join {
    ($f:expr, $sep:literal, $it:expr) => {{
        join!($f, $sep, x in $it => write!($f, "{}", x)?)
    }};
    ($f:expr, $sep:literal, $pat:pat in $it:expr => $block:expr) => {{
        for (i, $pat) in IntoIterator::into_iter($it).enumerate() {
            if i > 0 {
                write!($f, $sep)?;
            }
            $block;
        }
    }};
}

impl<I> fmt::Display for ast::Program<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_program(self, f, 0)
    }
}

impl<I> fmt::Display for ast::FnDef<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_fn_def(self, f, 0)
    }
}

impl<I> fmt::Display for ast::FnBody<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_fn_body(self, f, 0)
    }
}

impl<I> fmt::Display for ast::Statement<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_statement(self, f)
    }
}

impl fmt::Display for ast::Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_operand(self, f)
    }
}

impl fmt::Display for ast::Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_ty(self, f)
    }
}

impl fmt::Debug for ast::Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for ast::Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_pred(self, f)
    }
}

impl fmt::Debug for ast::Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for ast::pred::Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_pred_place(self, f)
    }
}

impl fmt::Debug for ast::pred::Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for ast::Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_rvalue(self, f)
    }
}

impl fmt::Display for ast::Heap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        PrettyPrinter.print_heap(self, f)?;
        write!(f, "(")
    }
}

impl fmt::Debug for ast::Heap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub struct PrettyPrinter;

impl PrettyPrinter {
    fn print_program<I>(
        &mut self,
        program: &ast::Program<I>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        for (_, def) in program.iter() {
            self.print_fn_def(def, f, indent)?;
            writeln!(f, "\n")?;
        }
        Ok(())
    }

    fn print_fn_def<I>(
        &mut self,
        func: &ast::FnDef<I>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        write!(f, "fn {}", func.name)?;
        indent!(f, indent + 2)?;
        write!(f, "( ")?;
        self.print_heap(&func.ty.in_heap, f)?;
        indent!(f, indent + 2)?;
        write!(f, "; ")?;
        self.print_locals(
            func.params
                .iter()
                .zip(&func.ty.inputs)
                .map(|(x, (_, ty))| (x, ty)),
            f,
        )?;
        indent!(f, indent + 2)?;
        write!(f, ") ret {}(", func.ret)?;
        self.print_heap(&func.ty.out_heap, f)?;
        write!(f, "; ")?;
        self.print_locals(func.ty.outputs.iter().map(|(x, y)| (x, y)), f)?;
        write!(f, "; own({})) = ", &func.ty.output)?;
        self.print_fn_body(&func.body, f, indent + 2)?;
        Ok(())
    }

    fn print_fn_body<I>(
        &mut self,
        fn_body: &ast::FnBody<I>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        match fn_body {
            ast::FnBody::LetCont(defs, rest) => {
                indent!(f, indent)?;
                write!(f, "letcont ")?;
                for (i, def) in defs.iter().enumerate() {
                    if i > 0 {
                        indent!(f, indent)?;
                        write!(f, "and ")?;
                    }
                    self.print_cont_def(def, f, indent + 2)?
                }
                indent!(f, indent)?;
                write!(f, "in")?;
                self.print_fn_body(rest, f, indent)?;
            }
            ast::FnBody::Ite { discr, then, else_ } => {
                indent!(f, indent)?;
                write!(f, "if {} then", discr)?;
                self.print_fn_body(then, f, indent + 2)?;
                indent!(f, indent)?;
                write!(f, "else")?;
                self.print_fn_body(else_, f, indent + 2)?;
            }
            ast::FnBody::Call {
                func,
                args,
                destination,
            } => {
                indent!(f, indent)?;
                if let Some((place, ret)) = destination {
                    write!(f, "call {} := {}(", place, func)?;
                    join!(f, ", ", args);
                    write!(f, ") ret {}", ret)?;
                } else {
                    write!(f, "call {}(", func)?;
                    join!(f, ", ", args);
                    write!(f, ")")?;
                }
            }
            ast::FnBody::Jump { target, args } => {
                indent!(f, indent)?;
                write!(f, "jump {}(", target)?;
                join!(f, ", ", args);
                write!(f, ")")?;
            }
            ast::FnBody::Seq(stmnt, rest) => {
                if !matches!(stmnt.kind, ast::StatementKind::Nop) {
                    indent!(f, indent)?;
                    self.print_statement(stmnt, f)?;
                    write!(f, ";")?;
                }
                self.print_fn_body(rest, f, indent)?;
            }
            ast::FnBody::Abort => {
                indent!(f, indent)?;
                write!(f, "abort")?;
            }
        }
        Ok(())
    }

    fn print_statement<I>(
        &mut self,
        stmnt: &ast::Statement<I>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match &stmnt.kind {
            ast::StatementKind::Let(x, layout) => {
                write!(f, "let {} = alloc(", x)?;
                self.print_type_layout(layout, f)?;
                write!(f, ")")?;
            }
            ast::StatementKind::Assign(place, rvalue) => {
                write!(f, "{} := ", place)?;
                self.print_rvalue(rvalue, f)?;
            }
            ast::StatementKind::Drop(place) => {
                write!(f, "drop({})", place)?;
            }
            ast::StatementKind::Nop => {
                write!(f, "Nop")?;
            }
        };
        Ok(())
    }

    fn print_rvalue(&mut self, rvalue: &ast::Rvalue, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match rvalue {
            ast::Rvalue::Use(op) => {
                self.print_operand(op, f)?;
            }
            ast::Rvalue::Ref(bk, place) => {
                let bk = match bk {
                    ast::BorrowKind::Shared => "",
                    ast::BorrowKind::Mut => "mut",
                };
                write!(f, "&{} {}", bk, place)?;
            }
            ast::Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.print_operand(op1, f)?;
                write!(f, " ")?;
                self.print_bin_op(*bin_op, f)?;
                write!(f, " ")?;
                self.print_operand(op2, f)?;
            }
            ast::Rvalue::CheckedBinaryOp(bin_op, op1, op2) => {
                write!(f, "Checked(")?;
                self.print_operand(op1, f)?;
                write!(f, " ")?;
                self.print_bin_op(*bin_op, f)?;
                write!(f, " ")?;
                self.print_operand(op2, f)?;
                write!(f, ")")?;
            }
            ast::Rvalue::UnaryOp(un_op, op) => {
                let un_op = match un_op {
                    ast::UnOp::Not => "!",
                    ast::UnOp::Neg => "-",
                };
                write!(f, "{}", un_op)?;
                self.print_operand(op, f)?;
            }
        };
        Ok(())
    }

    fn print_bin_op(&mut self, bin_op: ast::BinOp, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match bin_op {
            ast::BinOp::Add => write!(f, "+"),
            ast::BinOp::Sub => write!(f, "-"),
            ast::BinOp::Lt => write!(f, "<"),
            ast::BinOp::Le => write!(f, "<="),
            ast::BinOp::Eq => write!(f, "=="),
            ast::BinOp::Ge => write!(f, ">="),
            ast::BinOp::Gt => write!(f, ">"),
        }
    }

    fn print_operand(&mut self, op: &ast::Operand, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match op {
            ast::Operand::Copy(place) => write!(f, "{}", place),
            ast::Operand::Move(place) => write!(f, "move {}", place),
            ast::Operand::Constant(c) => self.print_constant(c, f),
        }
    }

    fn print_constant(&mut self, c: &ast::Constant, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match c {
            ast::Constant::Bool(b) => write!(f, "{}", b),
            ast::Constant::Int(n) => write!(f, "{}", n),
            ast::Constant::Unit => write!(f, "()"),
        }
    }

    fn print_cont_def<I>(
        &mut self,
        def: &ast::ContDef<I>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        write!(f, "{}", def.name)?;
        indent!(f, indent + 2)?;
        write!(f, "( ")?;
        self.print_heap(&def.ty.heap, f)?;
        indent!(f, indent + 2)?;
        write!(f, "; ")?;
        self.print_locals(def.ty.locals.iter().map(|(x, l)| (x, l)), f)?;
        // indent!(f, indent + 2)?;
        // write!(f, "; ")?;
        // self.print_locals(def.params.iter().zip(&def.ty.inputs), f)?;
        indent!(f, indent + 2)?;
        write!(f, ") =")?;
        self.print_fn_body(&def.body, f, indent)?;
        Ok(())
    }

    fn print_locals<'a, I: IntoIterator<Item = (&'a Local, &'a Location)>>(
        &mut self,
        params: I,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        join!(f, ", ", (x, l) in params => {
            write!(f, "{}: own({})", x, l)?;
        });
        Ok(())
    }
    fn print_heap(&mut self, heap: &ast::Heap, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        join!(f, ", ", (l, ty) in heap => {
            write!(f, "{}: {}", l, ty)?;
        });
        Ok(())
    }

    fn print_ty(&mut self, ty: &ast::Ty, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match ty {
            ast::Ty::OwnRef(l) => {
                write!(f, "own({})", l)?;
            }
            ast::Ty::Ref(bk, r, l) => {
                write!(f, "&")?;
                match r {
                    ast::Region::Infer => write!(f, "{{ _ }}")?,
                    ast::Region::Universal(urid) => write!(f, "'{}", urid.as_usize())?,
                    ast::Region::Concrete(places) => {
                        write!(f, "{{")?;
                        join!(f, ", ", places);
                        write!(f, "}}")?;
                    }
                }
                match bk {
                    ast::BorrowKind::Shared => write!(f, " ")?,
                    ast::BorrowKind::Mut => write!(f, " mut ")?,
                };
                write!(f, "{}", l)?;
            }
            ast::Ty::Tuple(tup) => {
                write!(f, "(")?;
                join!(f, ", ", (fld, ty) in tup => {
                    write!(f, "{}: {}", fld, ty)?;
                });
                write!(f, ")")?;
            }
            ast::Ty::Uninit(size) => {
                write!(f, "uninit({})", size)?;
            }
            ast::Ty::Refine(
                bty,
                ast::Refine::Pred(ast::pred::Pred::Constant(ast::pred::Constant::Bool(true))),
            ) => {
                write!(f, "{}", bty)?;
            }
            ast::Ty::Refine(bty, refine) => {
                write!(f, "{{ {} | ", bty)?;
                match refine {
                    ast::Refine::Infer => write!(f, "_")?,
                    ast::Refine::Pred(pred) => self.print_pred(pred, f)?,
                }
                write!(f, " }}")?;
            }
        }
        Ok(())
    }

    fn print_pred(&mut self, pred: &ast::Pred, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match pred {
            ast::Pred::Constant(ast::pred::Constant::Bool(b)) => {
                write!(f, "{}", b)?;
            }
            ast::Pred::Constant(ast::pred::Constant::Int(n)) => {
                write!(f, "{}", n)?;
            }
            ast::Pred::Constant(ast::pred::Constant::Unit) => {
                write!(f, "()")?;
            }
            ast::Pred::Place(place) => {
                self.print_pred_place(place, f)?;
            }
            ast::Pred::BinaryOp(bin_op, op1, op2) => {
                write!(f, "({} {} {})", op1, bin_op, op2)?;
            }
            ast::Pred::UnaryOp(un_op, op) => {
                write!(f, "{}{}", un_op, op)?;
            }
        }
        Ok(())
    }

    fn print_pred_place(
        &mut self,
        place: &ast::pred::Place,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        write!(f, "{}", place.base)?;
        for proj in &place.projs {
            write!(f, ".{}", proj)?;
        }
        Ok(())
    }

    fn print_type_layout(
        &mut self,
        layout: &ast::TypeLayout,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match layout {
            ast::TypeLayout::Tuple(tup) => {
                write!(f, "(")?;
                join!(f, ", ", layout in tup => self.print_type_layout(layout, f)?);
                write!(f, ")")?;
            }
            ast::TypeLayout::Block(size) => {
                write!(f, "{}", size)?;
            }
        }
        Ok(())
    }
}
