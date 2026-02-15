#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32, l: i32)
    requires
        l > 0,
        n > l,
{
    let mut i: i32;
    let mut k: i32;

    k = 1;
    while k < n
        invariant
            1 <= k <= n,
        decreases n - k,
    {
        i = l;
        while i < n
            invariant
                l <= i <= n,
            decreases n - i,
        {
            i += 1;
        }

        i = l;
        while i < n
            invariant
                l <= i <= n,
            decreases n - i,
        {
            assert(1 <= i);
            i += 1;
        }

        k += 1;
    }
}

fn main() {
}

} // verus!
