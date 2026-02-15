#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_swap(x0: &mut [i32])
    requires
        old(x0)@.len() >= 1 + 1,
    ensures
        ((x0@[(0) as int] == old(x0)@[(1) as int]) && (x0@[(1) as int] == old(x0)@[(0) as int])),
{
    let x2: i32 = x0[0];
    let x3: i32 = x0[1];
    x0[0] = x3;
    x0[1] = x2;
}

fn main() {
}

} // verus!
