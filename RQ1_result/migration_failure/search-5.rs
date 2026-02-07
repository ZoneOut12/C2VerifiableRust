#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn search(array: &mut [i32], length: usize, element: i32) -> (result: Option<&mut i32>)
    requires
        old(array)@.len() >= length - 1 + 1,
    ensures
        (result).is_none() || (exists|i: int| 0 <= i < length && array + i == result),
{
    let mut i: usize = 0;
    while i < length
        invariant
            0 <= i <= length,
        decreases length - i,
    {
        if array[i] == element {
            return Some(&mut array[i]);
        }
        i += 1;
    }
    None
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(array: &mut [i32], length: usize)
    requires
        forall|i: int|
            (0 <= i < length) as int != 0 ==> (old(array)@[(i) as int] < i32::MAX) as int != 0,
        old(array)@.len() >= length - 1 + 1,
{
    let p: Option<&mut i32> = search(array, length, 0);
    if let Some(p_ref) = p {
        *p_ref += 1;
    }
}

fn main() {
}

} // verus!
