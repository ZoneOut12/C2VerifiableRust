#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn func(c: i32) -> (result: i32)
    requires
        c > 0,
    ensures
        result == c,
{
    let mut x: i32 = c;
    let mut y: i32 = 0;
    while x > 0
        invariant
            c == x + y && x >= 0,
        decreases x,
    {
        x = x - 1;
        y = y + 1;
    }
    y
}

fn main() {
}

} // verus!
