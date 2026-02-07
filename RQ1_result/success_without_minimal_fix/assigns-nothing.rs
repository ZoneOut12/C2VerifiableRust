#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn plus_5(a: &i32) -> (result: i32)
    requires
        true,
        ((a)@) <= i32::MAX - 5,
    ensures
        result == ((a)@) + 5,
{
    *a + 5
}

fn main() {
}

} // verus!
