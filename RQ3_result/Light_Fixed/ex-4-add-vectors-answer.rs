#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add_vectors(v_res: &mut [i32], v1: &[i32], v2: &[i32], len: usize)
    requires
        old(v_res)@.len() >= len - 1 + 1,
        v1@.len() >= len - 1 + 1,
        v2@.len() >= len - 1 + 1,
        true,
        true,
        forall|i: int|
            (0 <= i < len) as int != 0 ==> (i32::MIN <= #[trigger] v1@[(i) as int] + v2@[(i) as int] //2b
                <= i32::MAX) as int != 0,
    ensures
        forall|i: int|
            (0 <= i < len) as int != 0 ==> (v_res@[(i) as int] == v1@[(i) as int] + v2@[(
            i) as int]) as int != 0,
        forall|i: int|
            (0 <= i < len) as int != 0 ==> (v1@[(i) as int] == v1@[(i) as int]) as int != 0,
        forall|i: int|
            (0 <= i < len) as int != 0 ==> (v2@[(i) as int] == v2@[(i) as int]) as int != 0,
{
    let mut i: usize = 0;
    while i < len
        invariant
            (v_res)@.len() >= len - 1 + 1,//2c
            0 <= i <= len,
            forall|j: int|
                (0 <= j < i) as int != 0 ==> (v_res@[(j) as int] == v1@[(j) as int] + v2@[(
                j) as int]) as int != 0,
        decreases len - i,
    {
        v_res[i] = v1[i] + v2[i];
        i += 1;
    }
}

fn main() {
}

} // verus!
