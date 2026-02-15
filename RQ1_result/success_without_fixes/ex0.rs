#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn inc(x: i32) -> (result: i32)
    requires
        x < i32::MAX,
    ensures
        result > x,
{
    x + 1
}

fn main() {
}

} // verus!
