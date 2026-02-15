#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(p: &i32, q: &i32) -> (result: i32)
    requires
        i32::MIN <= ((p)@) + ((q)@) <= i32::MAX,
        true && true,
    ensures
        result == ((p)@) + ((q)@),
{
    *p + *q
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let a: i32 = 24;
    let b: i32 = 42;
    let mut x: i32;
    x = add(&a, &b);
    assert(x == a + b);
    assert(x == 66);
    x = add(&a, &a);
    assert(x == a + a);
    assert(x == 48);
}

} // verus!
