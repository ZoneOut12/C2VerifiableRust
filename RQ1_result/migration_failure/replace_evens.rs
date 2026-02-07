#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn func(a: &mut [i32], n: i32)
    requires
        n > 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        forall|k: int|
            ((0 <= k < n) && (k % 2 == 0)) as int != 0 ==> ((a@[(k) as int] == 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                ((0 <= k < i) && (k % 2 == 0)) as int != 0 ==> (a@[(k) as int] == 0) as int != 0,
            forall|k: int|
                ((0 <= k < i) && (k % 2 == 1)) as int != 0 ==> (a@[(k) as int] == a@[(
                k) as int]) as int != 0,
        decreases n - i,
    {
        if i % 2 == 0 {
            a[i as usize] = 0;
        }
        i += 1;
    }
}

fn main() {
}

} // verus!
