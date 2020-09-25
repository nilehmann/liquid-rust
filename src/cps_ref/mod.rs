pub mod ast;
pub mod context;
pub mod parser;
pub mod smt;
pub mod typeck;

#[cfg(test)]
mod tests {
    use super::{ast::FnDef, parser::FnParser, smt::ConstraintChecker, typeck::Constraint};
    use super::{
        context::{Arena, LiquidRustCtxt},
        typeck::TypeCk,
    };
    use rustc_ast::attr::with_default_session_globals;

    struct Session<'lr> {
        cx: &'lr LiquidRustCtxt<'lr>,
    }

    impl<'lr> Session<'lr> {
        fn run(act: impl for<'a> FnOnce(Session<'a>)) {
            with_default_session_globals(|| {
                let arena = Arena::default();
                let cx = LiquidRustCtxt::new(&arena);
                act(Session { cx: &cx });
            })
        }

        fn parse(&self, string: &str) -> Option<FnDef<'lr>> {
            dbg!(FnParser::new().parse(self.cx, string)).ok()
        }

        fn check_parse(&self, string: &str) {
            assert!(self.parse(string).is_some());
        }

        fn check(&self, string: &str) -> Constraint<'lr> {
            TypeCk::cgen(self.cx, &self.parse(string).unwrap())
        }
    }

    #[test]
    fn abs() {
        Session::run(|sess| {
            let c = sess.check(
                r####"
fn abs(n0: {int | true}; n: own(n0)) ret k(r: {int | _v >= 0}; own(r)) =
  let b = new(1);
  b := *n <= 0;
  if *b then
    n := 0 - *n;
    jump k(n)
  else
    jump k(n)
"####,
            );
            println!("{:#?}", c);
            let mut checker = ConstraintChecker::new();
            let a = checker.check(&c);
            println!("{:?}", a);
        });
    }

    #[test]
    fn sum() {
        Session::run(|sess| {
            let c = sess.check(
                r####"
    fn sum(n0: {int | _v >= 0}; n: own(n0)) ret k(r: {int | _v >= n0}; own(r)) =
      letcont loop( n1: {int | _v == n0}, i1: {int | _v >= 0}, r1: {int | _v >= i1}
                  ; i: own(i1), r: own(r1), n: own(n1);) =
        let t0 = new(1);
        t0 := *i <= *n;
        if *t0 then
          i := *i + 1;
          r := *r + *i;
          jump loop()
        else
          jump k(r)
      in
      let i = new(1);
      let r = new(1);
      i := 0;
      r := 0;
      jump loop()
    "####,
            );
            println!("{:#?}", c);
            let a = ConstraintChecker::new().check(&c);
            println!("{:?}", a);
        })
    }

    #[test]
    fn count_zeros() {
        Session::run(|sess| {
            sess.check(
                r####"
    fn count_zeros(n0: {int | _v >= 0}; n: own(n0)) ret k(r: {int | _v >= 0}; own(r))=
      letcont b0( n1: {int | _v >= 0}, i1: {int | _v >= 0}, c1: {int | _v >= 0}
                ; i: own(i1), c: own(c1), n: own(n1); ) =
        let t0 = new(1);
        t0 := *i < *n;
        if *t0 then
          letcont b1( n2: {int | _v >= 0}, i2: {int | _v >= 0}, c2: {int | _v >= 0}, x0: {int | true}
                    ; i: own(i2), c: own(c2), n: own(n2)
                    ; x: own(x0)
                    ) =
            let t1 = new(1);
            t1 := *x == 0;
            if *t1 then
              c := *c + 1;
              jump b0()
            else
              jump b0()
          in
          call f(i) ret b1
        else
          jump k(c)
      in
      let i = new(1);
      let c = new(1);
      i := 0;
      c := 0;
      jump b0()
    "####,
            );
        });
    }

    #[test]
    fn alloc_pair() {
        Session::run(|sess| {
            sess.check(
                r####"
    fn alloc_pair(;) ret k(r: {int | true}; own(r))=
      let p = new((1, 1));
      p.0 := 1;
      p.1 := 2;
      let r = new(1);
      r := *p.0;
      jump k(r)
    "####,
            );
        });
    }

    #[test]
    fn length() {
        Session::run(|sess| {
            sess.check(
            r####"
    fn length(p0: (@x: {int | true}, @y: {int | _v >= @x}); p: own(p0)) ret k(r: {int | _v >= 0}; own(r))=
      let t = new(1);
      t := *p.1 - *p.0;
      jump k(t)
    "####,
        );
        });
    }
}
