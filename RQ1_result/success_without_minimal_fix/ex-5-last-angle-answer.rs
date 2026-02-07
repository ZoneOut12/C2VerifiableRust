#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn last_angle(first: i32, second: i32) -> (result: i32)
    requires
        0 <= first <= 180,
        0 <= second <= 180,
        first + second <= 180,
    ensures
        180 == first + second + result,
        0 <= result <= 180,
{
    180 - first - second
}

fn main() {
}

} // verus!
