#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn is_pos(x0: i32) -> bool {
    (x0 > 0)
}

pub open spec fn is_nat(x3: i32) -> bool {
    (x3 >= 0)
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_pos(x0: i32) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((is_pos(x0 as i32))) as int != 0,
{
    let x2: i32 = (x0 > 0) as i32;
    x2
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_nat(x3: i32) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((is_nat(x3 as i32))) as int != 0,
{
    let x5: i32 = (x3 >= 0) as i32;
    x5
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn minus1(x6: i32) -> (result: i32)
    requires
        (is_pos(x6 as i32)),
    ensures
        (is_nat(result as i32)),
{
    let x8: i32 = x6 - 1;
    x8
}

fn main() {
}

} // verus!
