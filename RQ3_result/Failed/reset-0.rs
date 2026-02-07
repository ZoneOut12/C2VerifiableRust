#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn zeroed(a: &[i32], b: int, e: int) -> bool;

#[verifier::external_body]
pub broadcast proof fn zeroed_inductive()
    ensures
        forall|a: &[i32], b: int, e: int|
            (b >= e) as int != 0 ==> ((zeroed(a, b as int, e as int))) as int != 0,
        forall|a: &[i32], b: int, e: int|
            (b < e) as int != 0 ==> (((zeroed(a, b as int, e - 1 as int)) && a@[(e - 1) as int]
                == 0) as int != 0 ==> ((zeroed(a, b as int, e as int))) as int != 0) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn reset(array: &mut [i32], length: usize)
    requires
        old(array)@.len() >= length - 1 + 1,
    ensures
        (zeroed(array, 0 as int, length as int)),
{
    broadcast use zeroed_inductive;

    let mut i: usize = 0;
    while i < length
        invariant
            0 <= i <= length,
            (zeroed(array, 0 as int, i as int)),
        decreases length - i,
    {
        array[i] = 0;
        i += 1;
    }
}

fn main() {
}

} // verus!
