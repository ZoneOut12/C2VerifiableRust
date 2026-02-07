#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn arrayDouble(a: &mut [i32], n: i32)
    requires
        n > 0,
        old(a)@.len() >= n - 1 + 1,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (old(a)@[(k) as int] == k && 2 * k <= i32::MAX) as int
                != 0,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] == 2 * k) as int != 0,
{
    let mut p: i32 = 0;
    while p < n
        invariant
            0 <= p <= n,
            forall|k: int| (p <= k < n) as int != 0 ==> (a@[(k) as int] == k) as int != 0,
            forall|k: int| (0 <= k < p) as int != 0 ==> (a@[(k) as int] == 2 * k) as int != 0,
        decreases n - p,
    {
        a[p as usize] = a[p as usize] * 2;
        p = p + 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut arr: [i32; 6] = [0, 1, 2, 3, 4, 5];
    arrayDouble(&mut arr, 6);
}

} // verus!
