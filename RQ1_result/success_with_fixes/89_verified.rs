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
        x == y,
{
    let mut lock: i32 = 1;
    while x != y
        invariant
            x == y,
            lock == 1,
            lock == 1 || lock == 0,
            lock == 0 || lock == 1,
            (lock != 1) as int != 0 ==> (x == y) as int != 0,
            (lock == 1) || (lock == 0),
    {
        if unknown() != 0 {
            lock = 1;
            x = y;
        } else {
            lock = 0;
            x = y;
            y = y + 1;
        }
    }
    assert(lock == 1);
}

fn main() {
}

} // verus!
