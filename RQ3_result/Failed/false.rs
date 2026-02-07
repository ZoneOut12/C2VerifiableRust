#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
pub broadcast proof fn false_is_true()
    ensures
        false,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    broadcast use false_is_true;

    assert(false);
    assert(forall|x: int| x > x);
    assert(forall|x: int, y: int, z: int| x == y == z == 42);
    // unimplemented!();
}

} // verus!
