#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_find(arr: &[i32], n: i32, x: i32) -> (result: i32)
    requires
        n >= 0,
        arr@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (0 <= result < n) as int != 0 ==> (arr@[(result) as int] == x) as int != 0,
        ((result == -1)) as int != 0 ==> ((forall|i: int|
            (0 <= i < n) as int != 0 ==> (arr@[(i) as int] != x) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (arr@[(k) as int] != x) as int != 0,
        decreases n - i,
    {
        if arr[i as usize] == x {
            return i;
        }
        i += 1;
    }
    -1
}

fn main() {
}

} // verus!
