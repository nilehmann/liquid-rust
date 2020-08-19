pub mod ast;
pub mod constraint;
pub mod parser;
pub mod smt;

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_ast::attr::with_default_session_globals;

    const CPS_COUNT_ZEROS_TEXT: &str = r"
fn f(n: {i32 | n >= 0}) ret k(v: i32) = jump k(n)

fn count_zeros(limit: {i32 | limit >= 0}) ret k(v: {i32 | v >= 0}) =
  letcont b0(i1: {i32 | i1 >= 0}, c1: {i32 | c1 >= 0}) =
    let t0 = i1 < limit in
    if t0 then
      letcont b1(x: i32) =
        letcont b2(c3: {i32 | c3 >= 0}) =
          let t3 = i1 + 1 in
          let a1 = t3.0 in
          let b1 = t3.1 in
          if b1 then jump b0(a1, c3) else abort
        in
        let t1 = x == 0 in
        if t1 then
          let t2 = c1 + 1 in
          let a1 = t2.1 in
          let a2 = t2.0 in
          if a1 then jump b2(a2) else abort
        else
          jump b2(c1)
      in
      call f(i1) ret b1
    else
      jump k(c1)
  in
  let i0 = 0 in
  let c0 = 0 in
  jump b0(i0, c0)
";

    #[test]
    fn cps_smt_count_zeros() {
        with_default_session_globals(|| {
            let fns = parser::FnsParser::new().parse(CPS_COUNT_ZEROS_TEXT).unwrap();
            let mut cgen = constraint::ConstraintGen::new();
            cgen.check_fns(fns).expect("cgen failed");
        });
    }
}
