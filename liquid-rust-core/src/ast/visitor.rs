use super::*;

pub trait Visitor<I>: Sized {
    fn visit_fn_body(&mut self, fn_body: &FnBody<I>) {
        walk_fn_body(self, fn_body);
    }

    fn visit_stmnt(&mut self, stmnt: &Statement<I>) {
        walk_stmnt(self, stmnt);
    }

    fn visit_cont_def(&mut self, def: &ContDef<I>) {
        walk_cont_def(self, def);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue) {
        walk_rvalue(self, rvalue);
    }

    fn visit_operand(&mut self, operand: &Operand) {
        walk_operand(self, operand);
    }

    fn visit_local(&mut self, _local: &Local) {}

    fn visit_constant(&mut self, _constant: &Constant) {}

    fn visit_place(&mut self, _place: &Place) {}

    fn visit_cont_id(&mut self, _const_id: &ContId) {}

    fn visit_fn_id(&mut self, _fn_id: &FnId) {}
}

#[macro_export]
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
    ($visitor: expr, $method: ident, $list: expr, $($extra_args: expr),*) => {
        for elem in $list {
            $visitor.$method(elem, $($extra_args,)*)
        }
    }
}

pub fn walk_fn_body<I, V: Visitor<I>>(visitor: &mut V, fn_body: &FnBody<I>) {
    match fn_body {
        FnBody::LetCont(defs, rest) => {
            walk_list!(visitor, visit_cont_def, defs);
            visitor.visit_fn_body(rest);
        }
        FnBody::Ite { discr, then, else_ } => {
            visitor.visit_place(discr);
            visitor.visit_fn_body(then);
            visitor.visit_fn_body(else_);
        }
        FnBody::Call {
            func,
            args,
            destination,
        } => {
            visitor.visit_fn_id(func);
            walk_list!(visitor, visit_local, args);
            if let Some((place, ret)) = destination {
                visitor.visit_cont_id(ret);
                visitor.visit_place(place);
            }
        }
        FnBody::Jump { target, args } => {
            visitor.visit_cont_id(target);
            walk_list!(visitor, visit_local, args);
        }
        FnBody::Seq(st, rest) => {
            visitor.visit_stmnt(st);
            visitor.visit_fn_body(rest);
        }
        FnBody::Abort => {}
    }
}

pub fn walk_cont_def<I, V: Visitor<I>>(visitor: &mut V, def: &ContDef<I>) {
    visitor.visit_fn_body(&def.body);
    visitor.visit_cont_id(&def.name);
    walk_list!(visitor, visit_local, &def.params);
}

pub fn walk_stmnt<I, V: Visitor<I>>(visitor: &mut V, stmnt: &Statement<I>) {
    match &stmnt.kind {
        StatementKind::Let(local, _) => {
            visitor.visit_local(local);
        }
        StatementKind::Assign(place, rvalue) => {
            visitor.visit_place(place);
            visitor.visit_rvalue(rvalue);
        }
        StatementKind::Drop(place) => {
            visitor.visit_place(place);
        }
        StatementKind::Nop => {}
    }
}

pub fn walk_rvalue<I, V: Visitor<I>>(visitor: &mut V, rvalue: &Rvalue) {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::UnaryOp(_, operand) => {
            visitor.visit_operand(operand);
        }
        Rvalue::Ref(_, place) => {
            visitor.visit_place(place);
        }
        Rvalue::CheckedBinaryOp(_, lhs, rhs) | Rvalue::BinaryOp(_, lhs, rhs) => {
            visitor.visit_operand(lhs);
            visitor.visit_operand(rhs);
        }
    }
}

pub fn walk_operand<I, V: Visitor<I>>(visitor: &mut V, operand: &Operand) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => visitor.visit_place(place),
        Operand::Constant(c) => visitor.visit_constant(c),
    }
}
