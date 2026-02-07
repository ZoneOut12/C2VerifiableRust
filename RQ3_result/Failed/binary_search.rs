#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn binsearch(base: &[i32], n: i32, key: i32) -> (result: i32)
    requires
        n >= 0,
        base@.len() >= n - 1 + 1,
        forall|k1: int, k2: int|
            (0 <= k1 < k2 < n) as int != 0 ==> (base@[(k1) as int] <= base@[(k2) as int]) as int
                != 0,
    ensures
        result >= -1 && result < n,
        (exists|k: int| 0 <= k < n && base@[(k) as int] == key) ==> (base@[(result) as int] == key),
        (forall|k: int| (0 <= k < n) as int != 0 ==> (base@[(k) as int] != key) as int != 0) ==> (
        result == -1),
{
    let mut l: i32 = 0;
    let mut h: i32 = n - 1;

    while l <= h
        invariant
            0 <= l,
            h < n,
            forall|i: int|
                (0 <= i < n && base@[(i) as int] == key) as int != 0 ==> (l <= i <= h) as int != 0,
        decreases h - l,
    {
        let m: i32 = l + (h - l) / 2;
        let val: i32 = base[m as usize];

        if val < key {
            l = m + 1;
            assert(forall|k1: int, k2: int|
                (0 <= k1 < k2 < l) as int != 0 ==> (base@[(k1) as int] <= base@[(k2) as int]) as int
                    != 0);
            assert(base@[(m) as int] < key && m == l - 1);
        } else if val > key {
            h = m - 1;
        } else {
            assert(forall|i: int|
                (0 <= i < n && base@[(i) as int] == key) as int != 0 ==> (l <= i <= h) as int != 0);
            return m;
        }
    }

    -1
}

fn main() {
}

} // verus!
