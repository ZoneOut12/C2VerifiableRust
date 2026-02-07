#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn is_pos(x: i32) -> bool {
    x > 0
}

pub open spec fn is_nat(x: i32) -> bool {
    x >= 0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn minus1(x: i32) -> (result: i32)
    requires
        (is_pos(x as i32)),
    ensures
        (is_nat(result as i32)),
{
    x - 1
}

fn main() {
}

} // verus!
