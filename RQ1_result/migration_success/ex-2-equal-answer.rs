#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn equal(a_1: &[i32], a_2: &[i32], len: usize) -> (result: i32)
    requires
        a_1@.len() >= len - 1 + 1,
        a_2@.len() >= len - 1 + 1,
    ensures
        (result) as int != 0 <==> ((forall|j: int|
            (0 <= j < len) as int != 0 ==> (a_1@[(j) as int] == a_2@[(j) as int]) as int
                != 0)) as int != 0,
{
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall|j: int|
                (0 <= j < i) as int != 0 ==> (a_1@[(j) as int] == a_2@[(j) as int]) as int != 0,
        decreases len - i,
    {
        if a_1[i] != a_2[i] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn different(a_1: &[i32], a_2: &[i32], len: usize) -> (result: i32)
    requires
        a_1@.len() >= len - 1 + 1,
        a_2@.len() >= len - 1 + 1,
    ensures
        (result) as int != 0 <==> ((exists|j: int|
            0 <= j < len && a_1@[(j) as int] != a_2@[(j) as int])) as int != 0,
{
    if equal(a_1, a_2, len) == 0 {
        1
    } else {
        0
    }
}

fn main() {
}

} // verus!
