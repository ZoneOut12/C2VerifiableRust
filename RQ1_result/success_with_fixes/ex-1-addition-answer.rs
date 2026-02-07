#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(x: i32, y: i32) -> (result: i32)
    requires
        i32::MIN <= x + y <= i32::MAX,
    ensures
        result == x + y,
{
    x + y
}

fn main() {
}

} // verus!
