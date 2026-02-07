#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(mut x: i32)
    requires
        (x == 10000),
{
    while x > 0
        invariant
            x <= 10000,
            0 <= x,
        decreases x,
    {
        x = x - 1;
    }
    assert((x == 0));
}

fn main() {
}

} // verus!
