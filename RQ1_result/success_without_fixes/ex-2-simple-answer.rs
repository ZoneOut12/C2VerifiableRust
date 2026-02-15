#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[derive(PartialEq)]
enum Kind {
    VOWEL,
    CONSONANT,
}

use Kind::*;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn kind_of_letter(c: char) -> (result: Kind)
    requires
        'a' <= c <= 'z',
    ensures
        (set!{'a','e','i','o','u','y'}.contains(c)) ==> (result == VOWEL),
        ((!(((set!{'a','e','i','o','u','y'}.contains(c))) as int != 0))) ==> (result == CONSONANT),
{
    if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y' {
        VOWEL
    } else {
        CONSONANT
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn quadrant(x: i32, y: i32) -> (result: i32)
    ensures
        1 <= result <= 4,
        (x >= 0 && y >= 0) ==> (result == 1),
        (x < 0 && y >= 0) ==> (result == 2),
        (x < 0 && y < 0) ==> (result == 3),
        (x >= 0 && y < 0) ==> (result == 4),
{
    if x >= 0 {
        if y >= 0 {
            1
        } else {
            4
        }
    } else {
        if y >= 0 {
            2
        } else {
            3
        }
    }
}

fn main() {
}

} // verus!
