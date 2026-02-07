#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn matcher(x0: &String) -> (result: i32)
    requires
        (((((x0)@.len() - 1)) >= 0) && ((forall|i: int|
            0 <= i < x0@.len() - 1 ==> (x0@[(i) as int] != '\0')) && x0@[x0@.len() - 1] == '\0')),
{
    let x2: i32 = x0.len() as i32;
    let x3: i32 = (0 < x2) as i32;
    let x6: i32;
    if x3 != 0 {
        let x4: u8 = x0.as_bytes()[0];
        let x5: i32 = (x4 == b'a') as i32;
        x6 = x5;
    } else {
        x6 = 0;
    }
    let x7: i32;
    if x6 != 0 {
        x7 = 1;
    } else {
        x7 = 0;
    }
    x7
}

fn main() {
}

} // verus!
