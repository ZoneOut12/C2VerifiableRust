#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn inv_vec_Int(x0: &[i32], x1: int) -> bool {
    ((x1 == 0) || ((x1 > 0) && x0@.len() >= x1 - 1 + 1))
}

pub open spec fn eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32) -> bool {
    ((x16 == x18) && (forall|x22: i32|
        ((0 <= x22 < x16)) as int != 0 ==> ((x15@[(x22) as int] == x17@[(x22) as int])) as int
            != 0))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32) -> (result: i32)
    requires
        ((inv_vec_Int(x15, x16 as int)) && (inv_vec_Int(x17, x18 as int))),
    ensures
        ((inv_vec_Int(x15, x16 as int)) && (inv_vec_Int(x17, x18 as int))),
        (result) as int != 0 <==> ((eq_vec_Int(x15, x16 as i32, x17, x18 as i32))) as int != 0,
{
    let x20: i32 = if x16 == x18 {
        1
    } else {
        0
    };
    let x31: i32;
    if x20 != 0 {
        let mut x30: i32 = 1;
        let mut x23: i32 = 0;
        while x23 < x16
            invariant
                (0 <= x23 <= x16),
                forall|x22: i32|
                    ((0 <= x22 < x23)) as int != 0 ==> ((x15@[(x22) as int] == x17@[(
                    x22) as int])) as int != 0,
                x30 == 1,
            decreases (x16 - x23),
        {
            let x27: i32 = x15[x23 as usize];
            let x28: i32 = x17[x23 as usize];
            let x29: i32 = if x27 == x28 {
                1
            } else {
                0
            };
            if x29 == 0 {
                x30 = 0;
                break ;
            }
            x23 += 1;
        }
        x31 = x30;
    } else {
        x31 = 0;
    }
    x31
}

fn main() {
}

} // verus!
