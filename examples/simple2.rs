#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

/**@ (n:{n >= 0}) -> v:{v >= n} @*/
fn sum(n: u32) -> u32 {
    let mut i = 0;
    let mut r = 0;

    while (i < n) {
        i += 1;
        r += i;
    }

    return r;
}

fn main() {}
