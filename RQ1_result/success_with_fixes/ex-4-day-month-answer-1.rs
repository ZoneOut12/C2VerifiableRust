#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn day_of(m: i32) -> (result: i32)
    requires
        1 <= m <= 12,
    ensures
        (m == 2) as int != 0 ==> (result == 28) as int != 0,
        ((m == 1 || m == 3 || m == 5 || m == 7 || m == 8 || m == 10 || m == 12)) as int != 0 ==> (
        result == 31) as int != 0,
        ((m == 4 || m == 6 || m == 9 || m == 11)) as int != 0 ==> (result == 30) as int != 0,
{
    let days: [i32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    days[(m - 1) as usize]
}

fn main() {
}

} // verus!
