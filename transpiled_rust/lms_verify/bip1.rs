fn d1(c: char) -> i32 {
    if c >= '0' && c <= '9' {
        (c as u8 - '0' as u8) as i32
    } else {
        -1
    }
}

fn e1(i: i32) -> char {
    if 0 <= i && i <= 9 {
        (i as u8 + '0' as u8) as char
    } else {
        ' '
    }
}

fn ed(c: char) -> char {
    e1(d1(c))
}

fn de(i: i32) -> i32 {
    d1(e1(i))
}

fn ded(c: char) -> i32 {
    d1(e1(d1(c)))
}

fn ede(i: i32) -> char {
    e1(d1(e1(i)))
}