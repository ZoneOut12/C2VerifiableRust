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
            (c == n) as int != 0 ==> (forall|k: int|
                (0 <= k < c) as int != 0 ==> (k != n) as int != 0) as int != 0,
            c != n || c <= n,
            0 <= c,
            ((c == n)) as int != 0 ==> ((n > -1)) as int != 0,
    {
        if unknown() != 0 {
            if c != n {
                if c >= 2147483647 {
                    break ;
                }
                c += 1;
            }
        } else {
            if c == n {
                c = 1;
            }
        }
    }
    if c == n {
        assert(n > -1);
    }
}

fn main() {
}

} // verus!
