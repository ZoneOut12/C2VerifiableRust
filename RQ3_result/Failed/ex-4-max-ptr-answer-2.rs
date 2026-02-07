#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

exec static mut h: i32 = 0;

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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    unsafe {
        h = 42;
    }
    let mut a: i32 = 24;
    let mut b: i32 = 42;
    max_ptr(&mut a, &mut b);
    assert(a == 42 && b == 24);
    assert(h == 42);
}

} // verus!
