#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn dfa_aabany(input: &str) -> (result: i32)
    requires
        (((input)@.len() - 1)) >= 0 && ((forall|i: int|
            0 <= i < input@.len() - 1 ==> (input@[(i) as int] != '\0')) && input@[input@.len() - 1]
            == '\0'),
    ensures
        result == 0 || result == 1,
{
    let chars: Vec<char> = input.chars().collect();
    let len = chars.len();
    if len == 0 {
        return 0;
    }
    let mut id: i32 = 0;
    let mut index: usize = 0;
    while index + 1 < len
        invariant
            (((input)@.len() - 1)) > 0 && input@.len() >= (((input)@.len() - 1)) + 1,
            id == 17 || id == 14 || id == 11 || id == 6 || id == 3 || id == 0,
        decreases (((input)@.len() - 1)),
    {
        let c = chars[index];
        index += 1;
        if id == 17 {
            let x18 = c;
            let x19 = (x18 == 'A') as i32;
            let x23: i32;
            if x19 != 0 {
                x23 = 1;
                return 1;
            } else {
                x23 = 1;
                return 1;
            }
            id = x23;
        } else if id == 14 {
            let x15 = c;
            let x16 = (x15 == 'A') as i32;
            let x24: i32;
            if x16 != 0 {
                x24 = 1;
                return 1;
            } else {
                x24 = 1;
                return 1;
            }
            id = x24;
        } else if id == 11 {
            let x12 = c;
            let x13 = (x12 == 'A') as i32;
            let x26: i32;
            if x13 != 0 {
                x26 = 1;
                return 1;
            } else {
                x26 = 1;
                return 1;
            }
            id = x26;
        } else if id == 6 {
            let x7 = c;
            let x8 = (x7 == 'A') as i32;
            if x8 != 0 {
                id = 6;
            } else {
                let x10 = (x7 == 'B') as i32;
                let x28: i32;
                if x10 != 0 {
                    x28 = 1;
                    return 1;
                } else {
                    x28 = 0;
                }
                id = x28;
            }
        } else if id == 3 {
            let x4 = c;
            let x5 = (x4 == 'A') as i32;
            let x30: i32;
            if x5 != 0 {
                x30 = 6;
            } else {
                x30 = 0;
            }
            id = x30;
        } else if id == 0 {
            let x1 = c;
            let x2 = (x1 == 'A') as i32;
            let x32: i32;
            if x2 != 0 {
                x32 = 3;
            } else {
                x32 = 0;
            }
            id = x32;
        } else {
            return -1;
        }
    }
    if index < len {
        let c = chars[index];
        if id == 17 {
            let x18 = c;
            let x19 = (x18 == 'A') as i32;
            let x23: i32;
            if x19 != 0 {
                x23 = 1;
            } else {
                x23 = 1;
            }
            id = x23;
        } else if id == 14 {
            let x15 = c;
            let x16 = (x15 == 'A') as i32;
            let x24: i32;
            if x16 != 0 {
                x24 = 1;
            } else {
                x24 = 1;
            }
            id = x24;
        } else if id == 11 {
            let x12 = c;
            let x13 = (x12 == 'A') as i32;
            let x26: i32;
            if x13 != 0 {
                x26 = 1;
            } else {
                x26 = 1;
            }
            id = x26;
        } else if id == 6 {
            let x7 = c;
            let x8 = (x7 == 'A') as i32;
            let x29: i32;
            if x8 != 0 {
                x29 = 0;
            } else {
                let x10 = (x7 == 'B') as i32;
                let x28: i32;
                if x10 != 0 {
                    x28 = 1;
                } else {
                    x28 = 0;
                }
                x29 = x28;
            }
            id = x29;
        } else if id == 3 {
            let x4 = c;
            let x5 = (x4 == 'A') as i32;
            let x30: i32;
            if x5 != 0 {
                x30 = 0;
            } else {
                x30 = 0;
            }
            id = x30;
        } else if id == 0 {
            let x1 = c;
            let x2 = (x1 == 'A') as i32;
            let x32: i32;
            if x2 != 0 {
                x32 = 0;
            } else {
                x32 = 0;
            }
            id = x32;
        } else {
            return -1;
        }
    }
    id
}

fn main() {
}

} // verus!
