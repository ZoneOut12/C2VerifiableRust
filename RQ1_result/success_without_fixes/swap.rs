#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn swap(a: &mut i32, b: &mut i32)
    requires
        true && true,
    ensures
        ((a)@) == ((old(b))@) && ((b)@) == ((old(a))@),
{
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut a: i32 = 37;
    let mut b: i32 = 91;
    swap(&mut a, &mut b);
}

} // verus!
