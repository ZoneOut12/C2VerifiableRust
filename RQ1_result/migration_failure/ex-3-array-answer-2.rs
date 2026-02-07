#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn copy(original: &[i32], copy: &mut [i32], length: i32)
    requires
        0 <= length,
        original@.len() >= length - 1 + 1,
        old(copy)@.len() >= length - 1 + 1,
        true,
    ensures
        forall|j: int|
            (0 <= j < length) as int != 0 ==> (original@[(j) as int] == copy@[(j) as int]) as int
                != 0,
{
    let mut i: i32 = 0;
    while i < length
        invariant
            0 <= i <= length,
            forall|j: int|
                (0 <= j < i) as int != 0 ==> (original@[(j) as int] == copy@[(j) as int]) as int
                    != 0,
        decreases length - i,
    {
        copy[i as usize] = original[i as usize];
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(a: &mut [i32])
    requires
        old(a)@.len() >= 9 + 1,
    ensures
        forall|j: int|
            (0 <= j < 10) as int != 0 ==> (a@[(j) as int] == old(a)@[(j) as int]) as int != 0,
{
    let mut g: [i32; 10] = [0;10];
    copy(a, &mut g, 10);

    let mut i: i32 = 0;
    while i < 10
        invariant
            0 <= i <= 10,
            forall|j: int|
                (0 <= j < 10) as int != 0 ==> (a@[(j) as int] == g@[(j) as int]) as int != 0,
        decreases 10 - i,
    {
        i += 1;
    }
}

fn main() {
}

} // verus!
