#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo() {
    let mut i: i32 = 0;
    let mut x: i32 = 0;

    while i < 20
        invariant
            0 <= i <= 19,
        decreases 19 - i,
    {
        if i == 19 {
            x += 1;
            break ;
        }
        i += 1;
    }
    assert(x == 1);
    assert(i == 19);
}

fn main() {
}

} // verus!
