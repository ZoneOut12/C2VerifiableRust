#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn matcher_begin_a(x0: &String) -> (result: i32)
    requires
        (((((x0)@.len() - 1)) >= 0) && ((forall|i: int|
            0 <= i < x0@.len() - 1 ==> (x0@[(i) as int] != '\0')) && x0@[x0@.len() - 1] == '\0')),
{
    let x2: char = x0.chars().next().unwrap_or('\0');
    let x3: i32 = if x2 == '\0' {
        1
    } else {
        0
    };
    let x6: i32;
    if x3 != 0 {
        x6 = 0;
    } else {
        let x5: i32 = if 'a' == x2 {
            1
        } else {
            0
        };
        x6 = x5;
    }
    let x8: i32 = if x6 != 0 {
        1
    } else {
        0
    };
    x8
}

fn main() {
}

} // verus!
