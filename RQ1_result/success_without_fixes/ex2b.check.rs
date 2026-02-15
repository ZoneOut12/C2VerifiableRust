#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn picker_first(x0: i32) -> (result: i32)
    requires
        (x0 > 0),
    ensures
        ((0 <= result) && (result < x0)),
{
    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_first_element(x6: &[i32], x7: i32) -> (result: i32)
    requires
        ((x7 > 0) && x6@.len() >= x7 - 1 + 1),
{
    let x9: i32 = picker_first(x7);
    let x10: i32 = x6[x9 as usize];
    x10
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_first_directly(x15: &[i32], x16: i32) -> (result: i32)
    requires
        ((x16 > 0) && x15@.len() >= x16 - 1 + 1),
{
    let x18: i32 = x15[0];
    x18
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn picker_last(x23: i32) -> (result: i32)
    requires
        (x23 > 0),
    ensures
        ((0 <= result) && (result < x23)),
{
    let x25: i32 = x23 - 1;
    x25
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_last_element(x30: &[i32], x31: i32) -> (result: i32)
    requires
        ((x31 > 0) && x30@.len() >= x31 - 1 + 1),
{
    let x33: i32 = picker_last(x31);
    let x34: i32 = x30[x33 as usize];
    x34
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_last_directly(x39: &[i32], x40: i32) -> (result: i32)
    requires
        ((x40 > 0) && x39@.len() >= x40 - 1 + 1),
{
    let x42: i32 = x40 - 1;
    let x43: i32 = x39[x42 as usize];
    x43
}

fn main() {
}

} // verus!
