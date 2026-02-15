#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(a: &i32, b: &i32, r: &i32) -> (result: i32)
    requires
        true && true && true,
        true,
        ((a)@) + ((b)@) <= i32::MAX,
        ((a)@) + ((b)@) >= i32::MIN,
        ((a)@) + ((b)@) + ((r)@) <= i32::MAX,
        ((a)@) + ((b)@) + ((r)@) >= i32::MIN,
    ensures
        result == ((a)@) + ((b)@) + ((r)@),
{
    *a + *b + *r
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut a: i32 = 24;
    let mut b: i32 = 32;
    let mut r: i32 = 12;
    let mut x: i32;
    x = add(&a, &b, &r);
    assert(x == a + b + r);
    assert(x == 68);
}

} // verus!
