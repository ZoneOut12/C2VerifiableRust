#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn inc(x: int) -> int {
    x + 1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn iota(array: &mut [i32], len: usize, value: i32)
    requires
        old(array)@.len() >= len + 1,
        value + len - 1 <= i32::MAX,
    ensures
        (len > 0) as int != 0 ==> (array@[(0) as int] == value) as int != 0,
        forall|j: int|
            (1 <= j < len) as int != 0 ==> (array@[(j) as int] == (inc(
                array@[(j - 1) as int] as int,
            ))) as int != 0,
{
    if len > 0 {
        array[0] = value;

        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                forall|j: int|
                    (1 <= j < i) as int != 0 ==> (array@[(j) as int] == (inc(
                        array@[(j - 1) as int] as int,
                    ))) as int != 0,
                array@[(i - 1) as int] == value + (i - 1),
            decreases len - i,
        {
            array[i] = array[i - 1] + 1;
            i += 1;
        }
    }
}

fn main() {
}

} // verus!
