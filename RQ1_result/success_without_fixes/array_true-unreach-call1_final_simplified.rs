#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut A: [i32; 2048] = [0;2048];
    let mut i: i32 = 0;
    while i < 1024
        invariant
            forall|j: int| (0 <= j < i) as int != 0 ==> (A@[(j) as int] == j) as int != 0,
            0 <= i <= 1024,
        decreases 1024 - i,
    {
        A[i as usize] = i;
        i += 1;
    }
    assert(A@[(1023) as int] == 1023);
}

} // verus!
