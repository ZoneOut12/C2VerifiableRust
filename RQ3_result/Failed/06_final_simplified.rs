#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown1() -> (result: i32) {
    unimplemented!();
}

#[verifier::external_body]
fn unknown2() -> (result: i32) {
    unimplemented!();
}

#[verifier::external_body]
fn unknown3() -> (result: i32) {
    unimplemented!();
}

#[verifier::external_body]
fn unknown4() -> (result: i32) {
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut w: i32 = 1;
    let mut z: i32 = 0;
    let mut x: i32 = 0;
    let mut y: i32 = 0;

    while unknown1() != 0
        invariant
            x == y,
            w == z + 1,
            1 <= w,
            0 <= x,
    {
        while unknown2() != 0
            invariant
                x == y,
                0 <= x,
        {
            if w % 2 == 1 {
                if x == 2147483647 {
                    break ;
                }
                x += 1;
            }
            if z % 2 == 0 {
                if y == 2147483647 {
                    break ;
                }
                y += 1;
            }
        }
        if x <= (2147483647 - 1) / 2 {
            z = x + y;
            w = z + 1;
        }
    }

    assert(x == y);
}

} // verus!
