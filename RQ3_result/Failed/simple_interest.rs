#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn simple(p: i32, n: i32, r: i32) -> (result: i32)
    requires
        p >= 5000,
        r > 0 && r < 15,
        n > 0 && n < 5,
        p * n * r <= i32::MAX,
    ensures
        result <= 2 * p && result > 0,
        p * n * r <= 200 * p * n * r,
{
    let si: i32 = p * n * r / 100;
    si
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let s: i32 = simple(10000, 3, 10);
}

} // verus!
