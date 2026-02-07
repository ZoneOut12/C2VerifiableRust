#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn distance(a: i32, b: i32) -> (result: i32)
    requires
        (a < b) as int != 0 ==> (b - a <= i32::MAX) as int != 0,
        (b <= a) as int != 0 ==> (a - b <= i32::MAX) as int != 0,
    ensures
        (a < b) as int != 0 ==> (a + result == b) as int != 0,
        (b <= a) as int != 0 ==> (a - result == b) as int != 0,
{
    if a < b {
        b - a
    } else {
        a - b
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn reset_1st_if_2nd_is_true(a: &mut i32, b: &i32)
    requires
        true && true,
        true,
    ensures
        (((b)@)) as int != 0 ==> (((a)@) == 0) as int != 0,
        ((!((((b)@)) as int != 0))) as int != 0 ==> (((a)@) == ((old(a))@)) as int != 0,
        ((b)@) == ((b)@),
{
    if *b != 0 {
        *a = 0;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn day_of(m: i32) -> (result: i32)
    requires
        1 <= m <= 12,
    ensures
        (set!{2}.contains(m)) as int != 0 ==> (result == 28) as int != 0,
        (set!{1,3,5,7,8,10,12}.contains(m)) as int != 0 ==> (result == 31) as int != 0,
        (set!{4,6,9,11}.contains(m)) as int != 0 ==> (result == 30) as int != 0,
{
    let days: [i32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    days[(m - 1) as usize]
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_ptr(a: &mut i32, b: &mut i32)
    requires
        true && true,
    ensures
        (((old(a))@) < ((old(b))@)) as int != 0 ==> (((a)@) == ((old(b))@) && ((b)@) == ((old(
            a,
        ))@)) as int != 0,
        (((old(a))@) >= ((old(b))@)) as int != 0 ==> (((a)@) == ((old(a))@) && ((b)@) == ((old(
            b,
        ))@)) as int != 0,
{
    if *a < *b {
        let tmp: i32 = *b;
        *b = *a;
        *a = tmp;
    }
}

fn main() {
}

} // verus!
