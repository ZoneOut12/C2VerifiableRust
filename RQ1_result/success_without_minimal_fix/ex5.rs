#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_swap(p: &mut [i32])
    requires
        old(p)@.len() >= 1 + 1,
    ensures
        p@[(0) as int] == old(p)@[(1) as int],
        p@[(1) as int] == old(p)@[(0) as int],
{
    let tmp: i32 = p[0];
    p[0] = p[1];
    p[1] = tmp;
}

fn main() {
}

} // verus!
