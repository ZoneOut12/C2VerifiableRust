#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

exec static mut h: i32 = 0;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_ptr(a: &i32, b: &i32) -> (result: i32)
    requires
        true && true,
    ensures
        result == ((a)@) || result == ((b)@),
        (((a)@) < ((b)@)) ==> (result == ((b)@)),
        (((a)@) > ((b)@)) ==> (result == ((a)@)),
        (((a)@) == ((b)@)) ==> (result == ((a)@) == ((b)@)),
{
    if *a < *b {
        *b
    } else {
        *a
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    unsafe {
        h = 42;
    }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(&a, &b);
    assert(x == 42);
    assert(h == 42);
}

} // verus!
