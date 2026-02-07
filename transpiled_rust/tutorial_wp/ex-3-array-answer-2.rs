fn copy(original: &[i32], copy: &mut [i32], length: i32) {
    let mut i: i32 = 0;
    while i < length {
        copy[i as usize] = original[i as usize];
        i += 1;
    }
}

fn foo(a: &mut [i32]) {
    let mut g: [i32; 10] = [0; 10];
    copy(a, &mut g, 10);

    let mut i: i32 = 0;
    while i < 10 {
        i += 1;
    }
}