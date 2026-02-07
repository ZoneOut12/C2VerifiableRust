#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown() -> (result: i32) {
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(mut x: i32, mut y: i32)
    requires
        0 <= x <= 10,
        0 <= y <= 10,
{
    while unknown() != 0
        invariant
            (x == 20) as int != 0 ==> (y != 0) as int != 0,
            0 <= y,
            0 <= x,
    {
        if x > i32::MAX - 10 || y > i32::MAX - 10 {
            break ;
        }
        x = x + 10;
        y = y + 10;
    }
    if x == 20 {
        assert(y != 0);
    }
}

fn main() {
}

} // verus!
