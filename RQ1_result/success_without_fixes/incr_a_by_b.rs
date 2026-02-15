#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn incr_a_by_b(a: &mut i32, b: &i32) -> (result: i32)
    requires
        i32::MIN <= ((old(a))@) + ((b)@) <= i32::MAX,
        true && true,
        true,
    ensures
        ((a)@) == ((old(a))@) + ((b)@),
        ((b)@) == ((b)@),
{
    *a += *b;
    *a
}

fn main() {
}

} // verus!
