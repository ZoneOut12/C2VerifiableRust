#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn dfa_aab(input: &str) -> (result: i32)
    requires
        (((input)@.len() - 1)) >= 0 && ((forall|i: int|
            0 <= i < input@.len() - 1 ==> (input@[(i) as int] != '\0')) && input@[input@.len() - 1]
            == '\0'),
    ensures
        result == 0 || result == 1,
{
    if input.is_empty() {
        return 0;
    }
    let mut id: i32 = 0;
    let len: usize = input.len();
    let mut pos: usize = 0;

    while pos + 1 < len
        invariant
            (((input)@.len() - 1)) > 0 && input@.len() >= (((input)@.len() - 1)) + 1,
            id == 6 || id == 3 || id == 0,
        decreases (((input)@.len() - 1)),
    {
        let c: char = input.as_bytes()[pos] as char;
        if id == 0 {
            let x1: char = c;
            let x2: i32 = if x1 == 'A' {
                1
            } else {
                0
            };
            let x16: i32;
            if x2 != 0 {
                x16 = 3;
            } else {
                x16 = 0;
            }
            id = x16;
        } else if id == 6 {
            let x7: char = c;
            let x8: i32 = if x7 == 'A' {
                1
            } else {
                0
            };
            let x13: i32;
            if x8 != 0 {
                x13 = 6;
            } else {
                x13 = 0;
            }
            id = x13;
        } else if id == 3 {
            let x4: char = c;
            let x5: i32 = if x4 == 'A' {
                1
            } else {
                0
            };
            let x14: i32;
            if x5 != 0 {
                x14 = 6;
            } else {
                x14 = 0;
            }
            id = x14;
        } else {
            return -1;
        }
        pos += 1;
    }

    if pos < len {
        let c: char = input.as_bytes()[pos] as char;
        if id == 0 {
            let x1: char = c;
            let x2: i32 = if x1 == 'A' {
                1
            } else {
                0
            };
            let x16: i32;
            if x2 != 0 {
                x16 = 0;
            } else {
                x16 = 0;
            }
            id = x16;
        } else if id == 6 {
            let x7: char = c;
            let x8: i32 = if x7 == 'A' {
                1
            } else {
                0
            };
            let x13: i32;
            if x8 != 0 {
                x13 = 0;
            } else {
                x13 = 1;
            }
            id = x13;
        } else if id == 3 {
            let x4: char = c;
            let x5: i32 = if x4 == 'A' {
                1
            } else {
                0
            };
            let x14: i32;
            if x5 != 0 {
                x14 = 0;
            } else {
                x14 = 0;
            }
            id = x14;
        } else {
            return -1;
        }
    }
    id
}

fn main() {
}

} // verus!
