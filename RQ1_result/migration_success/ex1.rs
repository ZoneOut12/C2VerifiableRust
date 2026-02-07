#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max(x: i32, y: i32) -> (result: i32)
    ensures
        result >= x && result >= y,
        result == x || result == y,
{
    if x > y {
        x
    } else {
        y
    }
}

fn main() {
}

} // verus!
