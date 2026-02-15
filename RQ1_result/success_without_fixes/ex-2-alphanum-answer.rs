#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn lower(c: char) -> bool {
    'a' <= c <= 'z'
}

pub open spec fn upper(c: char) -> bool {
    'A' <= c <= 'Z'
}

pub open spec fn digit(c: char) -> bool {
    '0' <= c <= '9'
}

enum Kind {
    LOWER,
    UPPER,
    DIGIT,
    OTHER,
}

use Kind::*;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_lower_alpha(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((lower(c as char))) as int != 0,
{
    (c >= 'a' && c <= 'z') as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_upper_alpha(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((upper(c as char))) as int != 0,
{
    (c >= 'A' && c <= 'Z') as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_digit(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((digit(c as char))) as int != 0,
{
    (c >= '0' && c <= '9') as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn character_kind(c: char) -> (result: Kind)
    ensures
        ((lower(c as char))) ==> (result == LOWER),
        ((upper(c as char))) ==> (result == UPPER),
        ((digit(c as char))) ==> (result == DIGIT),
        ((!((((lower(c as char)) || (upper(c as char)) || (digit(c as char)))) as int != 0))) ==> (
        result == OTHER),
{
    if is_lower_alpha(c) != 0 {
        return LOWER;
    }
    if is_upper_alpha(c) != 0 {
        return UPPER;
    }
    if is_digit(c) != 0 {
        return DIGIT;
    }
    OTHER
}

fn main() {
}

} // verus!
