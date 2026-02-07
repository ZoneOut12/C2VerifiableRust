#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn sorted(a: &[i32], b: int, e: int) -> bool {
    forall|i: int, j: int|
        (b <= i <= j < e) as int != 0 ==> (a@[(i) as int] <= a@[(j) as int]) as int != 0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fail_sort(a: &mut [i32], beg: usize, end: usize)
    requires
        old(a)@.len() >= end - 1 + 1,
        beg < end,
    ensures
        (sorted(a, beg as int, end as int)),
{
    let mut i: usize = beg;
    while i < end
        invariant
            beg <= i <= end,
            forall|j: int| (beg <= j < i) as int != 0 ==> (a@[(j) as int] == 0) as int != 0,
        decreases end - i,
    {
        a[i] = 0;
        i += 1;
    }
}

fn main() {
}

} // verus!
