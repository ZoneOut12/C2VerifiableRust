#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn diff(x: i32, y: i32) -> (result: i32)
    requires
        i32::MIN <= x - y <= i32::MAX,
    ensures
        y == x - result,
{
    x - y
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let t: i32 = diff(10, 5);
    assert(t == 5);
}

} // verus!
