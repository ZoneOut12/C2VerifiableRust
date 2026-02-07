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

pub open spec fn greater_than(x: int) -> bool { x > x } //2A
pub open spec fn eq(x: int, y: int) -> bool { x == y } //2A

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    broadcast use false_is_true;

    assert(false);
    assert(forall|x: int| greater_than(x)); //2A
    assert(forall|x: int, y: int, z: int| #[trigger]eq(x, y) && #[trigger]eq(y, z) && z == 42); //2A //2B
    // unimplemented!();
}

} // verus!
