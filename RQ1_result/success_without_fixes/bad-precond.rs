#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(a: i32)
    requires
        a < 0 && a > 0,
    ensures
        false,
{
}

fn main() {
}

} // verus!
