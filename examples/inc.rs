#![feature(register_tool)]
#![register_tool(liquid)]

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

#[liquid::ty("fn(n: int) -> int")]
fn inc(n: u32) -> u32 {
    n + 1
}

fn main() {}
