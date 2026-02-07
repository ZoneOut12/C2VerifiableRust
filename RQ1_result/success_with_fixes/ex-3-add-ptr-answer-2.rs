#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(p: &i32, q: &i32, r: &mut i32)
    requires
        i32::MIN <= ((p)@) + ((q)@) <= i32::MAX,
        true && true && true,
        true,
        true,
    ensures
        ((r)@) == ((p)@) + ((q)@),
{
    *r = *p + *q;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let a: i32 = 24;
    let b: i32 = 42;
    let mut x: i32 = 0;
    add(&a, &b, &mut x);
    assert(x == a + b);
    assert(x == 66);
    add(&a, &a, &mut x);
    assert(x == a + a);
    assert(x == 48);
}

} // verus!
