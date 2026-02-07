#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn predicate(v: i32) -> (result: bool)
    ensures
        result == 0 || result == 1,
{
    v % 2 == 0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn index_where(v: &[i32], n: i32, o: &mut [i32]) -> (result: i32)
    requires
        n > 0,
        v@.len() >= n - 1 + 1,
        old(o)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|i: i32| (0 <= i < result) as int != 0 ==> (0 <= o@[(i) as int] < n) as int != 0,
        forall|i: i32|
            (0 < i < result) as int != 0 ==> (o@[(i - 1) as int] < o@[(i) as int]) as int != 0,
{
    let mut r: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= r <= i,
            forall|j: i32| (0 <= j < r) as int != 0 ==> (0 <= o@[(j) as int] < i) as int != 0,
            forall|j: i32|
                (0 < j < r) as int != 0 ==> (o@[(j - 1) as int] < o@[(j) as int]) as int != 0,
        decreases n - i,
    {
        if predicate(v[i as usize]) {
            o[r as usize] = i;
            r += 1;
        }
        i += 1;
    }
    r
}

fn main() {
}

} // verus!
