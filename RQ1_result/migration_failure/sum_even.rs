#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn func(n: i32) -> (result: i32)
    requires
        n >= 0,
        n / 2 * (n / 2 + 1) <= i32::MAX,
    ensures
        result == n / 2 * (n / 2 + 1),
{
    let mut sum: i32 = 0;
    let mut i: i32 = 0;

    while i <= n / 2
        invariant
            i <= n / 2 + 1,
            (sum == i * (i - 1)),
        decreases n / 2 - i,
    {
        sum = sum + 2 * i;
        i += 1;
    }
    assert(i == n / 2 + 1);
    sum
}

fn main() {
}

} // verus!
