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
        (forall|off: u32|
            (0 <= off < length) as int != 0 ==> (old(array)@[(off) as int] != element) as int != 0)
            ==> ((result).is_none()),
        (exists|off: u32| 0 <= off < length && old(array)@[(off) as int] == element) ==> (array
            <= result < array + length && ((result).unwrap()@) == element),
{
    let mut i: usize = 0;
    while i < length
        invariant
            0 <= i <= length,
            forall|j: u32| (0 <= j < i) as int != 0 ==> (array@[(j) as int] != element) as int != 0,
        decreases length - i,
    {
        if array[i] == element {
            return Some(&mut array[i]);
        }
        i += 1;
    }
    None
}

fn main() {
}

} // verus!
