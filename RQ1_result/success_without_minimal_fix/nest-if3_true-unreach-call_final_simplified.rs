#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown1() -> (result: i32) {
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32, mut l: i32)
    requires
        l > 0,
        l < i32::MAX,
        n < i32::MAX,
{
    let mut k: i32;
    let mut i: i32;

    k = 1;
    while k < n
        invariant
            1 <= l,
            1 <= k,
        decreases n - k,
    {
        i = l;
        while i < n
            invariant
                1 <= i,
            decreases n - i,
        {
            assert(1 <= i);
            i += 1;
        }
        if unknown1() != 0 && l < 2147483647 {
            l = l + 1;
        }
        k += 1;
    }
}

fn main() {
}

} // verus!
