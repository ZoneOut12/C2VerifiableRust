#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn leap(y: i32) -> (result: i32)
    ensures
        (result) as int != 0 <==> (((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0)) as int != 0,
{
    (((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0)) as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn day_of(m: i32, y: i32) -> (result: i32)
    requires
        1 <= m <= 12,
    ensures
        (set!{2}.contains(m)) && (((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0)) ==> (result
            == 29),
        (set!{2}.contains(m)) && ((!(((((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0))) as int
            != 0))) ==> (result == 28),
        (set!{4,6,9,11}.contains(m)) ==> (result == 30),
        (set!{1,3,5,7,8,10,12}.contains(m)) ==> (result == 31),
{
    let days: [i32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    let n: i32 = days[(m - 1) as usize];
    if n == 28 {
        if leap(y) != 0 {
            return 29;
        } else {
            return 28;
        }
    }
    return n;
}

fn main() {
}

} // verus!
