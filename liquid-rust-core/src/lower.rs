use crate::{
    ast,
    ty::{self, TyCtxt, Var},
};

pub struct TypeLowerer<'a> {
    tcx: &'a TyCtxt,
    vars_in_scope: Vec<Var>,
}

impl<'a> TypeLowerer<'a> {
    pub fn new(tcx: &'a TyCtxt, vars_in_scope: Vec<Var>) -> Self {
        Self { tcx, vars_in_scope }
    }

    pub fn lower_ty(&mut self, ty: &ast::Ty) -> ty::Ty {
        match ty {
            ast::Ty::OwnRef(location) => self.tcx.mk_own_ref(*location),
            ast::Ty::Ref(bk, region, location) => {
                self.tcx.mk_ref(*bk, self.lower_region(region), *location)
            }
            ast::Ty::Tuple(tup) => {
                let mut vec = Vec::new();
                for (f, ty) in tup {
                    self.vars_in_scope.push(Var::Field(*f));
                    vec.push((*f, self.lower_ty(ty)));
                    self.vars_in_scope.pop();
                }
                self.tcx.mk_tuple(ty::Tuple::from(vec))
            }
            ast::Ty::Uninit(n) => self.tcx.mk_uninit(*n),
            ast::Ty::Refine { bty: ty, refine } => {
                self.tcx.mk_refine(*ty, self.lower_refine(refine))
            }
        }
    }

    pub fn lower_cont_ty(&mut self, cont_ty: &ast::ContTy) -> ty::ContTy {
        ty::ContTy::new(
            self.lower_heap(&cont_ty.heap),
            cont_ty.locals.iter().copied().collect(),
            cont_ty.inputs.clone(),
        )
    }

    pub fn lower_fn_ty(&mut self, fn_ty: &ast::FnTy) -> ty::FnTy {
        ty::FnTy {
            in_heap: self.lower_heap(&fn_ty.in_heap),
            inputs: fn_ty.inputs.clone(),
            out_heap: self.lower_heap(&fn_ty.out_heap),
            output: fn_ty.output.clone(),
        }
    }

    pub fn lower_heap(&mut self, heap: &ast::Heap) -> ty::Heap {
        heap.into_iter()
            .map(|(l, ty)| {
                let r = (*l, self.lower_ty(ty));
                self.vars_in_scope.push(Var::from(*l));
                r
            })
            .collect()
    }

    fn lower_region(&mut self, region: &ast::Region) -> ty::Region {
        match region {
            ast::Region::Concrete(places) => ty::Region::Concrete(places.clone()),
            ast::Region::Infer => ty::Region::Infer(self.tcx.fresh_region_vid()),
        }
    }

    fn lower_refine(&self, refine: &ast::Refine) -> ty::Refine {
        match refine {
            ast::Refine::Pred(pred) => ty::Refine::Pred(self.lower_pred(pred)),
            ast::Refine::Infer => {
                let mut vars_in_scope = vec![Var::Nu];
                vars_in_scope.extend(&self.vars_in_scope);
                ty::Refine::Infer(ty::Kvar(self.tcx.fresh_kvar(), vars_in_scope))
            }
        }
    }

    fn lower_pred(&self, pred: &ast::Pred) -> ty::Pred {
        match pred {
            ast::Pred::Constant(c) => self.tcx.mk_constant(*c),
            ast::Pred::Place(place) => self.tcx.mk_pred_place(place.clone()),
            ast::Pred::BinaryOp(bin_op, op1, op2) => {
                self.tcx
                    .mk_bin_op(*bin_op, self.lower_pred(op1), self.lower_pred(op2))
            }
            ast::Pred::UnaryOp(un_op, op) => self.tcx.mk_un_op(*un_op, self.lower_pred(op)),
        }
    }
}
