#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn function(mut x: i32, mut y: i32) -> (result: i32)
    requires
        -10 <= x <= 0,
        0 <= y <= 5,
    ensures
        -10 <= result <= 10,
{
    let res: i32;
    y += 10;
    x -= 5;
    res = x + y;
    assert(-5 <= res <= 10);
    res
}

fn main() {
}

} // verus!
