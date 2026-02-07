#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn abs(x: i32) -> (result: i32)
    requires
        x > i32::MIN,
    ensures
        result >= 0,
{
    if x < 0 {
        -x
    } else {
        x
    }
}

fn main() {
}

} // verus!
