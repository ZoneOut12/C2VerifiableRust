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
        (set!{2}.contains(m)) ==> (result == 28),
        (set!{4,6,9,11}.contains(m)) ==> (result == 30),
        (set!{1,3,5,7,8,10,12}.contains(m)) ==> (result == 31),
{
    let days: &[i32] = &[31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    days[(m - 1) as usize]
}

fn main() {
}

} // verus!
