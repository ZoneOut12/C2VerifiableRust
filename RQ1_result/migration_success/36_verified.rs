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
fn main() {
    let mut c: i32 = 0;
    while unknown() != 0
        invariant
            c <= 40,
            (c != 40) as int != 0 ==> (c <= 40) as int != 0,
            exists|k: int| 0 <= k <= c && k != 40,
            0 <= c,
            ((c != 40)) as int != 0 ==> ((c < 40)) as int != 0,
    {
        if unknown() != 0 {
            if c != 40 {
                c = c + 1;
            }
        } else {
            if c == 40 {
                c = 1;
            }
        }
    }
    if c != 40 {
        assert(c <= 40);
    }
}

} // verus!
