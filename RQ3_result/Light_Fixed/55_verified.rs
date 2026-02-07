#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown() -> (result: i32) {
    unimplemented!();
}

spec fn assist(i: int) -> bool{ 1 <= i } //2a

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32)
    requires
        n > 0,
{
    let mut c: i32 = 0;
    while unknown() != 0
        invariant
            n != c,
            c >= 0 && c <= n,
            (c > n) as int != 0 ==> (c == n) as int != 0,
            (c > n) as int != 0 ==> (c == n + 1) as int != 0,
            c <= n,
            forall|k: int|
                (#[trigger] assist(k) && k <= c) as int != 0 ==> ((exists|i: int| #[trigger] assist(i) && i <= n && i == c)) as int != 0,//2b
            0 <= c,
    {
        if unknown() != 0 {
            if c > n {
                c += 1;
            }
        } else {
            if c == n {
                c = 1;
            }
        }
    }
    if c < 0 {
        if c > n {
            assert(c == n);
        }
    }
}

fn main() {
}

} // verus!
