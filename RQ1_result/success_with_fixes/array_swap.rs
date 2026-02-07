#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_swap(arr: &mut [i32], n: i32, n1: i32, n2: i32)
    requires
        n >= 0,
        0 <= n1 < n && 0 <= n2 < n,
        old(arr)@.len() >= n - 1 + 1,
    ensures
        (arr@[(n2) as int] == old(arr)@[(n1) as int]) && (arr@[(n2) as int] == old(arr)@[(
        n1) as int]),
{
    let temp = arr[n1 as usize];
    arr[n1 as usize] = arr[n2 as usize];
    arr[n2 as usize] = temp;
}

fn main() {
}

} // verus!
