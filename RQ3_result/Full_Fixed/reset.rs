#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn reset(array: &mut [i32], length: usize)
    requires
        old(array)@.len() >= length - 1 + 1,
    ensures
        forall|j: u32| (0 <= j < length) as int != 0 ==> (array@[(j) as int] == 0) as int != 0,
{
    let mut i: usize = 0;
    while i < length
        invariant
            (array)@.len() >= length - 1 + 1, //2C
            0 <= i <= length,
            forall|j: u32| (0 <= j < i) as int != 0 ==> (array@[(j) as int] == 0) as int != 0,
        decreases length - i,
    {
        array[i] = 0;
        i += 1;
    }
}

fn main() {
}

} // verus!
