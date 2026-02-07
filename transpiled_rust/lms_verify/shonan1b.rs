fn mv_mult_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32]) {
    let mut r: i32 = 0;
    while r < n {
        o[r as usize] = 0;
        let mut c: i32 = 0;
        while c < n {
            o[r as usize] = ((o[r as usize] != 0) || (m[(n * r + c) as usize] != 0 && v[c as usize] != 0)) as i32;
            c += 1;
        }
        r += 1;
    }
}

fn mv_mults_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32]) {
    let r: i32 = 0;
    o[r as usize] = 0;
    let mut c: i32 = 0;
    while c < n {
        o[r as usize] = ((o[r as usize] != 0) || (m[(n * r + c) as usize] != 0 && v[c as usize] != 0)) as i32;
        c += 1;
    }
    o[1] = 0;
}

fn mv_multu_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32]) {
    o[0] = 0;
    o[0] = ((o[0] != 0) || (v[0] != 0)) as i32;
    o[0] = ((o[0] != 0) || (v[1] != 0)) as i32;
    o[1] = 0;
}