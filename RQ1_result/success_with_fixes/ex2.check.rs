#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_index(x0: i32) -> (result: i32)
    requires
        (x0 > 0),
    ensures
        ((0 <= result) && (result < x0)),
{
    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_element(x6: &[i32], x7: i32) -> (result: i32)
    requires
        ((x7 > 0) && x6@.len() >= x7 - 1 + 1),
{
    let x9: i32 = pick_index(x7);
    let x10: i32 = x6[x9 as usize];
    x10
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_first(x15: &[i32]) -> (result: i32)
    requires
        (x15)@.len() >= 1,
    ensures
        (result == x15@[(0) as int]),
{
    let x17: i32 = x15[0];
    x17
}

fn main() {
}

} // verus!
