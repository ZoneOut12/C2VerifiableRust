#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn inv_matrix_Boolean(x26: &[i32], x27: int, x28: int) -> bool {
    (((((x27 < 100) && (x28 < 100)) && (0 < x27)) && (0 < x28)) && (((x27 * x28) > 0) && x26@.len()
        >= (x27 * x28) - 1 + 1))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> (result: i32)
    requires
        ((((((((0 < x0) && (x0 < 100)) && (0 < x1)) && (x1 < 100)) && (0 <= x2)) && (0 <= x3)) && (
        x2 < x0)) && (x3 < x1)),
    ensures
        ((0 <= result) && (result < (x0 * x1))),
{
    let x5: i32 = x2 * x1;
    let x6: i32 = x5 + x3;
    x6
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mult(
    x63: &[i32],
    x64: i32,
    x65: i32,
    x66: &[i32],
    x67: i32,
    x68: i32,
    x69: &mut [i32],
    x70: i32,
    x71: i32,
)
    requires
        ((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(old(x69), x70 as int, x71 as int))) && (((x65 == x67) && (x64
            == x70)) && (x68 == x71))),
    ensures
        (((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(x69, x70 as int, x71 as int))),
{
    let mut x76: i32 = 0;
    while x76 < x64
        invariant
            0 <= x76 <= x64,
        decreases x64 - x76,
    {
        let mut x78: i32 = 0;
        while x78 < x68
            invariant
                0 <= x78 <= x68,
            decreases x68 - x78,
        {
            let x79: i32 = index_(x70, x71, x76, x78);
            x69[x79 as usize] = 0;
            let mut x82: i32 = 0;
            while x82 < x65
                invariant
                    0 <= x82 <= x65,
                decreases x65 - x82,
            {
                let x83: i32 = x69[x79 as usize];
                let x84: i32 = index_(x64, x65, x76, x82);
                let x85: i32 = x63[x84 as usize];
                let x88: i32;
                if x85 != 0 {
                    let x86: i32 = index_(x67, x68, x82, x78);
                    let x87: i32 = x66[x86 as usize];
                    x88 = x87;
                } else {
                    x88 = 0;
                }
                let x89: i32 = if (x83 != 0) || (x88 != 0) {
                    1
                } else {
                    0
                };
                x69[x79 as usize] = x89;
                x82 += 1;
            }
            x78 += 1;
        }
        x76 += 1;
    }
}

fn main() {
}

} // verus!
