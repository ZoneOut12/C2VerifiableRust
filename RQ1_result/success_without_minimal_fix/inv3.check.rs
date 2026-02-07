#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn inv_vec_Int(x0: &[i32], x1: int) -> bool {
    ((x1 == 0) || ((x1 > 0) && x0@.len() >= x1 - 1 + 1))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_pos(x15: &[i32], x16: i32) -> (result: i32)
    requires
        (inv_vec_Int(x15, x16 as int)),
    ensures
        (inv_vec_Int(x15, x16 as int)),
{
    let mut x18: i32 = 0;
    let mut x20: i32 = 0;
    while x20 < x16
        invariant
            0 <= x20 <= x16,
            ((0 <= x18) && (x18 <= x20)),
        decreases x16 - x20,
    {
        let x22: i32 = x18;
        let x21: i32 = x15[x20 as usize];
        let x26: bool = x21 > 0;
        let x27: i32;
        if x26 {
            x27 = 1;
        } else {
            x27 = 0;
        }
        let x28: i32 = x22 + x27;
        x18 = x28;
        x20 += 1;
    }
    let x32: i32 = x18;
    x32
}

fn main() {
}

} // verus!
