fn mv_mult2_bool(m: &[i32], v: &[i32], o: &mut [i32]) {
    o[0] = ((m[0] != 0) && (v[0] != 0) || (m[1] != 0) && (v[1] != 0)) as i32;
    o[1] = ((m[2] != 0) && (v[0] != 0) || (m[3] != 0) && (v[1] != 0)) as i32;
}

fn mv_mult2(m: &[i32], v: &[i32], o: &mut [i32]) {
    o[0] = m[0] * v[0] + m[1] * v[1];
    o[1] = m[2] * v[0] + m[3] * v[1];
}

fn mv_mult2r_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32]) {
    let mut r: i32 = 0;
    while r < n {
        let mut t: bool = false;
        let mut c: i32 = 0;
        while c < n {
            t = t || ((m[(n * r + c) as usize] != 0) && (v[c as usize] != 0));
            c += 1;
        }
        o[r as usize] = t as i32;
        r += 1;
    }
}

fn mv_mult2s_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32]) {
    let mut r: i32 = 0;
    let mut t: bool = false;
    let mut c: i32 = 0;
    while c < n {
        t = t || ((m[(n * r + c) as usize] != 0) && (v[c as usize] != 0));
        c += 1;
    }
    o[r as usize] = t as i32;
    o[1] = 0;
}