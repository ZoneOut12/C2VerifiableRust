#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fun(x: i32, y: i32) -> (result: i32)
    requires
        x >= 0 && y > 0,
    ensures
        result == x / y,
{
    let mut r: i32 = x;
    let mut d: i32 = 0;

    while r >= y
        invariant
            r >= 0,
            r + d * y == x,
        decreases r - y,
    {
        r = r - y;
        d = d + 1;
    }
    d
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let res: i32 = fun(10, 2);
    assert(res == 5);
}

} // verus!
