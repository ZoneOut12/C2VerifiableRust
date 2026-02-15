#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn member(x0: &[i32], x1: i32, x2: i32) -> (result: i32)
    requires
        ((x1 > 0) && x0@.len() >= x1 - 1 + 1),
    ensures
        ((((result == -1)) as int != 0 ==> ((!(((exists|x56: i32|
            (((0 <= x56) && (x56 < x1)) && (x0@[(x56) as int] == x2)))) as int != 0))) as int != 0)
            && (((result != -1)) as int != 0 ==> ((((0 <= result) && (result < x1)) && (x0@[(
        result) as int] == x2))) as int != 0)),
{
    let mut x4: i32 = -1;
    let mut x6: i32 = 0;
    while x6 < x1
        invariant
            ((((0 <= x6) && (x6 <= x1)) && (((x4 == -1)) as int != 0 ==> ((!(((exists|x22: i32|
                (((0 <= x22) && (x22 < x6)) && (x0@[(x22) as int] == x2)))) as int != 0))) as int
                != 0)) && (((x4 != -1)) as int != 0 ==> ((((0 <= x4) && (x4 < x6)) && (x0@[(
            x4) as int] == x2))) as int != 0)),
        decreases (x1 - x6),
    {
        let x7: i32 = x4;
        let x8: i32 = if x7 == -1 {
            1
        } else {
            0
        };
        let x11: i32;
        if x8 != 0 {
            let x9: i32 = x0[x6 as usize];
            let x10: i32 = if x9 == x2 {
                1
            } else {
                0
            };
            x11 = x10;
        } else {
            x11 = 0;
        }
        if x11 != 0 {
            x4 = x6;
        }
        x6 += 1;
    }
    let x50: i32 = x4;
    x50
}

fn main() {
}

} // verus!
