#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_lower_alpha(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> ('a' <= c <= 'z') as int != 0,
{
    ('a' <= c && c <= 'z') as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_upper_alpha(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> ('A' <= c <= 'Z') as int != 0,
{
    ('A' <= c && c <= 'Z') as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_digit(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> ('0' <= c <= '9') as int != 0,
{
    ('0' <= c && c <= '9') as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_alpha_num(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c
            <= '9'))) as int != 0,
{
    (is_lower_alpha(c) != 0 || is_upper_alpha(c) != 0 || is_digit(c) != 0) as i32
}

fn main() {
}

} // verus!
