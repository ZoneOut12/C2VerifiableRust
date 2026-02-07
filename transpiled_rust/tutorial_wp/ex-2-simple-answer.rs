#[derive(PartialEq)]
enum Kind {
    VOWEL,
    CONSONANT,
}

use Kind::*;

fn kind_of_letter(c: char) -> Kind {
    if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y' {
        VOWEL
    } else {
        CONSONANT
    }
}

fn quadrant(x: i32, y: i32) -> i32 {
    if x >= 0 {
        if y >= 0 { 1 } else { 4 }
    } else {
        if y >= 0 { 2 } else { 3 }
    }
}