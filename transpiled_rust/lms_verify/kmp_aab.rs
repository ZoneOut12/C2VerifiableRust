fn r#match(s: &String) -> i32 {
    let mut j: i32 = 0;
    let mut k: i32 = 0;
    while k < s.len() as i32 && j < 3 {
        if j == 0 {
            if s.as_bytes()[k as usize] == 'a' as u8 {
                j += 1;
                k += 1;
            } else {
                j = 0;
                k += 1;
            }
        } else if j == 1 {
            if s.as_bytes()[k as usize] == 'a' as u8 {
                j += 1;
                k += 1;
            } else {
                j = 0;
            }
        } else if j == 2 {
            if s.as_bytes()[k as usize] == 'b' as u8 {
                j += 1;
                k += 1;
            } else {
                j = 1;
            }
        } else {
            return -1;
        }
    }
    if j == 3 {
        1
    } else {
        0
    }
}