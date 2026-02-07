#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn arraymax(a: &[i32], n: i32) -> (result: i32)
    requires
        a@.len() >= n - 1 + 1,
        n > 0,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (result >= a@[(k) as int]) as int != 0,
        exists|k: int| 0 <= k < n && result == a@[(k) as int],
{
    let mut i: i32 = 1;
    let mut max: i32 = a[0];

    while i < n
        invariant
            exists|k: int| 0 <= k < i && max == a@[(k) as int],
            forall|k: int| (0 <= k < i) as int != 0 ==> (max >= a@[(k) as int]) as int != 0,
            0 <= i <= n,
        decreases n - i,
    {
        if max < a[i as usize] {
            max = a[i as usize];
            assert(exists|k: int| 0 <= k < i + 1 && max == a@[(k) as int]);
        }
        i = i + 1;
    }
    max
}

fn main() {
}

} // verus!
