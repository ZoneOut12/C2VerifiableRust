#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn matcher_a(x0: &str) -> (result: i32)
    requires
        (((((x0)@.len() - 1)) >= 0) && ((forall|i: int|
            0 <= i < x0@.len() - 1 ==> (x0@[(i) as int] != '\0')) && x0@[x0@.len() - 1] == '\0')),
{
    let mut x2: i32 = 0;
    let mut x3: i32 = 1;
    let mut x4: usize = 0;
    while true
        invariant
            (((((x4)@.len() - 1)) >= 0) && x4@.len() >= (((x4)@.len() - 1)) + 1),
        decreases
                (((((x4)@.len() - 1)) + (if (x2) {
                    (0)
                } else {
                    (1)
                })) + (if (x3) {
                    (1)
                } else {
                    (0)
                })),
    {
        let x5: i32 = x2;
        let x9: i32 = if x5 != 0 {
            0
        } else {
            x3
        };
        if x9 == 0 {
            break ;
        }
        let x12: char = match x0.as_bytes().get(x4) {
            Some(&b) => b as char,
            None => '\0',
        };
        let x13: i32 = if x12 == '\0' {
            1
        } else {
            0
        };
        let x16: i32 = if x13 != 0 {
            0
        } else {
            if x12 == 'a' {
                1
            } else {
                0
            }
        };
        let x18: i32 = if x16 != 0 {
            1
        } else {
            0
        };
        x2 = x18;
        let x20: i32 = x2;
        if x20 != 0 {
        } else {
            let x14: i32 = if x13 == 0 {
                1
            } else {
                0
            };
            x3 = x14;
            let x23: i32 = x3;
            if x23 != 0 {
                x4 += 1;
            }
        }
    }
    x2
}

fn main() {
}

} // verus!
