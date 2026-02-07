#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn swap(a: &mut i32, b: &mut i32)
    requires
        true && true,
{
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn reverse(array: &mut [i32], len: usize)
    requires
        old(array)@.len() >= len - 1 + 1,
{
    let mut i: usize = 0;
    while i < len / 2
        invariant
            0 <= i <= len / 2,
        decreases len - i,
    {
        let right_i = len - i - 1;
        let (left, right) = array.split_at_mut(right_i);
        swap(&mut left[i], &mut right[0]);
        i += 1;
    }
}

fn main() {
}

} // verus!
