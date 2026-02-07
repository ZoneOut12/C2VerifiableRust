#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn my_atoi(a: &String) -> (result: i32)
    requires
        ((a)@.len()) >= 0 && true,
    ensures
        0 <= result || result == -1,
{
    let m: i32 = (i32::MAX / 10) - 10;
    let mut r: i32 = 0;
    let mut index: usize = 0;
    let s = a.as_bytes(); //0

    while index < s.len() && s[index] >= b'0' && s[index] <= b'9' //0
        invariant
            ((s)@.len()) >= 0 && s@.len() >= ((s)@.len()) + 1,
            0 <= r,
        decreases ((s)@.len()),
    {
        if r > m {
            return -1;
        }
        r = 10 * r + (s[index] as i32 - b'0' as i32); //0
        index += 1;
    }
    r
}

fn main() {
}

} // verus!
