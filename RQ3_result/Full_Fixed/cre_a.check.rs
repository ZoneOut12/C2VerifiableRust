#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
use vstd::string::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn matcher_a(x0: &str) -> (result: i32) 
    requires
        ((((x0)@.len())-1 >= 0) && true) && (forall|i: int| 0 <= i < (x0)@.len() - 1 ==> (x0@[(i) as int] != '\0')) && x0@[(x0)@.len()-1]=='\0',
{
    let mut x2: i32 = 0;
    let mut x3: i32 = 1;
    // let mut x4: usize = 0;
    let mut x4: &str = x0.substring_char(0, x0.unicode_len()); //0
    while true
        invariant
            ((((x4)@.len())-1 >= 0) && true) && (forall|i: int| 0 <= i < (x4)@.len() - 1 ==> (x4@[(i) as int] != '\0')) && x4@[(x4)@.len()-1]=='\0', //2A
        decreases
                ((((x4)@.len()) + (if (x2 != 0) { //1
                    (0) as int //1
                } else {
                    (1) as int //1
                })) + (if (x3 != 0) { //1
                    (1) as int //1
                } else {
                    (0) as int //1
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
        // let x12: char = match x0.as_bytes().get(x4) {
        //     Some(&b) => b as char,
        //     None => '\0',
        // }; 
        let x12 = x4.get_char(0) as char; //0
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
                // x4 += 1;
                x4 = x4.substring_char(1, x4.unicode_len()); //0
            }
        }
    }
    x2
}

fn main() {
}

} // verus!
