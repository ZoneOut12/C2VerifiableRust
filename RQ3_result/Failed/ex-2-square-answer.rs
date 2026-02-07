#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn square(n: int) -> int {
    n * n
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn abs(x: i32) -> (result: i32)
    requires
        i32::MIN < x,
    ensures
        (x >= 0) as int != 0 ==> (result == x) as int != 0,
        (x < 0) as int != 0 ==> (result == -x) as int != 0,
{
    if x < 0 {
        -x
    } else {
        x
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn square(x: i32) -> (result: u32)
    requires
        x * x <= u32::MAX,
    ensures
        result == (square(x as int)),
{
    let v: u32 = abs(x) as u32;
    v * v
}

fn main() {
}

} // verus!
