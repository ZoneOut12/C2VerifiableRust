#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn reset_1st_if_2nd_is_true(a: &mut i32, b: &i32)
    requires
        true && true,
        true,
    ensures
        ((b)@) == ((b)@),
        (((b)@)) ==> (((a)@) == 0),
        ((!((((b)@)) as int != 0))) ==> (((a)@) == ((old(a))@)),
{
    if *b != 0 {
        *a = 0;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut a: i32 = 5;
    let mut x: i32 = 0;

    reset_1st_if_2nd_is_true(&mut a, &x);
    assert(a == 5);
    assert(x == 0);

    let b: i32 = 1;

    reset_1st_if_2nd_is_true(&mut a, &b);
    assert(a == 0);
    assert(b == 1);
}

} // verus!
