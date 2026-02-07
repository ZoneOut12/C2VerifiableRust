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
fn foo(n: i32)
    requires
        n > 0,
{
    let mut c: i32 = 0;
    while unknown() != 0
        invariant
            c <= n,
            0 <= c,
            ((c == n)) as int != 0 ==> ((c >= 0 && c <= n)) as int != 0,
    {
        if c == n {
            c = 1;
        } else {
            c = c + 1;
        }
    }
    if c == n {
        assert(c >= 0);
    }
}

fn main() {
}

} // verus!
