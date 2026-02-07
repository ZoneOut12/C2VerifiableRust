#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn abs(val: i32) -> (result: i32)
    requires
        val > i32::MIN,
    ensures
        result >= 0,
        ((val >= 0) as int != 0 ==> (result == val) as int != 0) && ((val < 0) as int != 0 ==> (
        result == -val) as int != 0),
{
    if val < 0 {
        -val
    } else {
        val
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(a: i32)
    requires
        a > i32::MIN,
{
    let b: i32 = abs(-42);
    let c: i32 = abs(42);
    let d: i32 = abs(a);
}

fn main() {
}

} // verus!
