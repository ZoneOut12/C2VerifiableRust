#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_index(n: i32) -> (result: i32)
    requires
        n > 0,
    ensures
        0 <= result && result < n,
{
    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_element(p: &[i32], n: i32) -> (result: i32)
    requires
        n > 0,
        p@.len() >= n - 1 + 1,
{
    let i: i32 = pick_index(n);
    assert((0 <= i && i < n));
    assert(p@.len() >= n - 1 + 1);
    p[i as usize]
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_first(p: &[i32]) -> (result: i32)
    requires
        p@.len() >= 0 + 1,
    ensures
        result == p@[(0) as int],
{
    p[0]
}

fn main() {
}

} // verus!
