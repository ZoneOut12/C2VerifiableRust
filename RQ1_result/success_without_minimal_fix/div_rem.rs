#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn div_rem(x: u32, y: u32, q: &mut u32, r: &mut u32)
    requires
        true && true,
        true,
        y != 0,
    ensures
        x == ((q)@) * y + ((r)@),
        ((r)@) < y,
{
    *q = x / y;
    *r = x % y;
}

fn main() {
}

} // verus!
