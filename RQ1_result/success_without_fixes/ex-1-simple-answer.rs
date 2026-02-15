#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_ptr(a: &mut i32, b: &mut i32)
    requires
        true && true,
{
    if *a < *b {
        let tmp: i32 = *b;
        *b = *a;
        *a = tmp;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn min_ptr(a: &mut i32, b: &mut i32)
    requires
        true && true,
{
    max_ptr(b, a);
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn order_3_inc_min(a: &mut i32, b: &mut i32, c: &mut i32)
    requires
        true && true && true,
{
    min_ptr(a, b);
    min_ptr(a, c);
    min_ptr(b, c);
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn incr_a_by_b(a: &mut i32, b: &i32)
    requires
        true && true,
        i32::MIN <= ((old(a))@) + ((b)@) <= i32::MAX,
{
    *a += *b;
}

fn main() {
}

} // verus!
