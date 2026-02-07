#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn sorted(arr: &[i32], end: int) -> bool {
    forall|i: int, j: int|
        (0 <= i <= j < end) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0
}

pub open spec fn element_level_sorted(array: &[i32], end: int) -> bool {
    forall|i: int|
        (0 <= i < end - 1) as int != 0 ==> (array@[(i) as int] <= array@[(i + 1) as int]) as int
            != 0
}

#[verifier::external_body]
fn bsearch(arr: &[i32], len: usize, value: i32) -> (result: usize)
    requires
        arr@.len() >= len - 1 + 1,
        (sorted(arr, len as int)),
{
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn element_level_sorted_implies_sorted(arr: &[i32], len: usize)
    requires
        forall|i: int|
            (0 <= i < len - 1) as int != 0 ==> (arr@[(i) as int] <= arr@[(i + 1) as int]) as int
                != 0,
    ensures
        forall|i: int, j: int|
            (0 <= i <= j < len) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0,
{
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            (sorted(arr, i as int)),
        decreases len - i,
    {
        assert((0 < i) as int != 0 ==> (arr@[(i - 1) as int] <= arr@[(i) as int]) as int != 0);
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn element_level_sorted_implies_greater(arr: &[i32], len: usize, i: usize, j: usize)
    requires
        forall|i: int|
            (0 <= i < len - 1) as int != 0 ==> (arr@[(i) as int] <= arr@[(i + 1) as int]) as int
                != 0,
    ensures
        (0 <= i <= j < len) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0,
{
    element_level_sorted_implies_sorted(arr, len);
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn element_level_sorted_implies_greater_2(arr: &[i32], len: usize, i: usize, j: usize)
    requires
        forall|i: int|
            (0 <= i < len - 1) as int != 0 ==> (arr@[(i) as int] <= arr@[(i + 1) as int]) as int
                != 0,
        0 <= i <= j < len,
    ensures
        arr@[(i) as int] <= arr@[(j) as int],
{
    element_level_sorted_implies_sorted(arr, len);
}

fn main() {
}

} // verus!
