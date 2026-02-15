#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[derive(PartialEq)]
enum Kind {
    LOWER,
    UPPER,
    DIGIT,
    OTHER,
}

use Kind::*;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_lower_alpha(c: char) -> (result: bool)
    ensures
        (result) as int != 0 <==> ('a' <= c <= 'z') as int != 0,
{
    'a' <= c && c <= 'z'
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_upper_alpha(c: char) -> (result: bool)
    ensures
        (result) as int != 0 <==> ('A' <= c <= 'Z') as int != 0,
{
    'A' <= c && c <= 'Z'
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_digit(c: char) -> (result: bool)
    ensures
        (result) as int != 0 <==> ('0' <= c <= '9') as int != 0,
{
    '0' <= c && c <= '9'
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn character_kind(c: char) -> (result: Kind)
    ensures
        ('a' <= c <= 'z') ==> (result == LOWER),
        ('A' <= c <= 'Z') ==> (result == UPPER),
        ('0' <= c <= '9') ==> (result == DIGIT),
        ((!((('a' <= c <= 'z')) as int != 0))) && ((!((('A' <= c <= 'Z')) as int != 0))) && ((!(((
        '0' <= c <= '9')) as int != 0))) ==> (result == OTHER),
{
    if is_lower_alpha(c) {
        LOWER
    } else if is_upper_alpha(c) {
        UPPER
    } else if is_digit(c) {
        DIGIT
    } else {
        OTHER
    }
}

fn main() {
}

} // verus!
