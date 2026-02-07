#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sum_42(n: i32) -> (result: i32)
    requires
        n * 42 <= i32::MAX,
{
    let mut x: i32 = 0;
    let r: i32 = 42;

    let mut i: i32 = 0;
    while i < n
        invariant
            x == i * r,
    {
        x += r;
        i += 1;
    }
    x
}

fn main() {
}

} // verus!
