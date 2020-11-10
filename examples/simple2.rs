#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

/**@ (n:{n >= 0}) -> v:{v >= n} @*/
fn sum(mut n: u32) -> u32 {
    //     let mut i = 0;
    //     let mut r = 0;
    //
    //     while (i < n) {
    //         i += 1;
    //         r += i;
    //     }
    //
    //     return r;

    if n < 0 {
        n = 0 - n;
    }
    return n;
}

fn main() {}
