#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn areElementsEven(a: &[i32], n: i32) -> (result: i32)
    requires
        n > 0,
        a@.len() >= (n - 1) + 1,
    ensures
        (forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] % 2 == 0) as int != 0) ==> (
        result == 1),
        (exists|k: int| 0 <= k < n && a@[(k) as int] % 2 != 0) ==> (result == 0),
{
    let mut p: i32 = 0;
    while p < n
        invariant
            0 <= p <= n,
            forall|k: int| (0 <= k < p) as int != 0 ==> (a@[(k) as int] % 2 == 0) as int != 0,
        decreases n - p,
    {
        if a[p as usize] % 2 != 0 {
            return 0;
        }
        p += 1;
    }
    return 1;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let arr: [i32; 5] = [2, 4, 6, 8, 10];
    let res: i32 = areElementsEven(&arr, 5);
    assert(res == 1);
}

} // verus!
