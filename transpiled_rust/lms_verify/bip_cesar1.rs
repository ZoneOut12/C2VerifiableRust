fn cypher(s: i32) -> i32 {
    if s == 26 { 0 } else { s + 1 }
}

fn decypher(s: i32) -> i32 {
    if s == 0 { 26 } else { s - 1 }
}

fn encode(s1: &[i32], s2: &mut [i32], s3: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        s2[i as usize] = cypher(s1[i as usize]);
        i += 1;
    }
}

fn decode(s1: &[i32], s2: &mut [i32], s3: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        s2[i as usize] = decypher(s1[i as usize]);
        i += 1;
    }
}

fn autoencode(s1: &mut [i32], s2: &mut [i32], s3: &mut [i32], n: i32) {
    encode(s1, s2, s3, n);
    decode(s2, s3, s1, n);
    // verus_assert(1);
    // verus_assert(2);
    // verus_assert(3);
    // verus_assert(4);
    // verus_assert(5);
}