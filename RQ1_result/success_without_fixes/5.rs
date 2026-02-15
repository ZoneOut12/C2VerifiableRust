#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fun(x: i32, y: i32, r: &mut i32) -> (result: i32)
    requires
        x >= y && x > 0 && y > 0,
        true,
    ensures
        ((r)@) < y,
        x == result * y + ((r)@),
{
    *r = x;
    let mut d: i32 = 0;
    while *r >= y
        invariant
            ((r)@) == x - y * d,
        decreases ((r)@),
    {
        *r = *r - y;
        d = d + 1;
    }
    d
}

fn main() {
}

} // verus!
