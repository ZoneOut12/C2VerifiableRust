#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

const LARGE_INT: i32 = 10;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(mut k: i32) -> (result: i32)
    requires
        0 <= k && k <= 1,
{
    let mut i: i32;
    let mut j: i32;
    i = 1;
    let tmp: i32 = k;
    while i < LARGE_INT
        invariant
            i == k + 2 * (i - 1) || i == k + 1 + 2 * (i - 1),
            i + k <= 2,
            1 <= i,
            1 <= i + k,
        decreases LARGE_INT - i,
    {
        i = i + 1;
        k = k - 1;
        assert(1 <= i + k && i + k <= 2 && i >= 1);
    }
    0
}

fn main() {
}

} // verus!
