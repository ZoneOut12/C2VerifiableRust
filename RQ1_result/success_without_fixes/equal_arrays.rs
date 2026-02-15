#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn check(a: &[i32], b: &[i32], n: i32) -> (result: i32)
    requires
        n > 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
    ensures
        (forall|k: int| (0 <= k < n) as int != 0 ==> (b@[(k) as int] == a@[(k) as int]) as int != 0)
            ==> (result == 1),
        (exists|k: int| 0 <= k < n && b@[(k) as int] != a@[(k) as int]) ==> (result == 0),
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] == b@[(k) as int]) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != b[i as usize] {
            return 0;
        }
        i += 1;
    }
    return 1;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let a: [i32; 5] = [1, 2, 3, 4, 5];
    let b: [i32; 5] = [1, 2, 3, 4, 5];
    check(&a, &b, 5);
}

} // verus!
