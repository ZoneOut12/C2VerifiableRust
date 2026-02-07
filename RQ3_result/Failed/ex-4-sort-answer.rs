#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn min_idx_in(a: &[i32], beg: usize, end: usize) -> (result: usize)
    requires
        beg < end,
        a@.len() >= end - 1 + 1,
    ensures
        beg <= result < end,
{
    let mut min_i: usize = beg;
    let mut i: usize = beg + 1;
    while i < end
        invariant
            beg + 1 <= i <= end,
            beg <= min_i < end,
        decreases end - i,
    {
        if a[i] < a[min_i] {
            min_i = i;
        }
        i += 1;
    }
    min_i
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn swap(p: &mut i32, q: &mut i32)
    requires
        true && true,
{
    let tmp: i32 = *p;
    *p = *q;
    *q = tmp;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sort(a: &mut [i32], beg: usize, end: usize)
    requires
        beg <= end,
        old(a)@.len() >= end - 1 + 1,
{
    let mut i: usize = beg;
    while i < end
        invariant
            beg <= i <= end,
        decreases end - i,
    {
        let imin: usize = min_idx_in(a, i, end);
        if i != imin {
            let (left, right) = a.split_at_mut(imin);
            swap(&mut left[i], &mut right[0]);
        }
        i += 1;
    }
}

fn main() {
}

} // verus!
