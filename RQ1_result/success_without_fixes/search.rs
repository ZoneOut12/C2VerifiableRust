#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn arraysearch(a: &[i32], x: i32, n: i32) -> (result: i32)
    requires
        n > 0,
        a@.len() >= n - 1 + 1,
    ensures
        (exists|k: int| 0 <= k < n && x == a@[(k) as int]) ==> (result == 1),
        (forall|k: int| (0 <= k < n) as int != 0 ==> (x != a@[(k) as int]) as int != 0) ==> (result
            == 0),
{
    let mut p: i32 = 0;
    while p < n
        invariant
            0 <= p <= n,
            forall|k: int| (0 <= k < p) as int != 0 ==> (x != a@[(k) as int]) as int != 0,
        decreases n - p,
    {
        if a[p as usize] == x {
            return 1;
        }
        p += 1;
    }
    0
}

fn main() {
}

} // verus!
