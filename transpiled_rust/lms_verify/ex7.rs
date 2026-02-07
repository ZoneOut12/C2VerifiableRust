fn member(p: &[i32], n: i32, v: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if p[i as usize] == v {
            return i;
        }
        i += 1;
    }
    -1
}

fn member_noreturn(p: &[i32], n: i32, v: i32) -> i32 {
    let mut r: i32 = -1;
    let mut i: i32 = 0;
    while i < n {
        if r == -1 && p[i as usize] == v {
            r = i;
        }
        i += 1;
    }
    r
}