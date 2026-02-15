#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max(a: i32, b: i32) -> (result: i32)
    ensures
        result >= a && result >= b,
        result == a || result == b,
{
    if a > b {
        a
    } else {
        b
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo() {
    let a: i32 = 42;
    let b: i32 = 37;
    let c: i32 = max(a, b);
    assert(c == 42);
}

fn main() {
}

} // verus!
