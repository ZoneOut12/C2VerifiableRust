fn reset(array: &mut [i32], length: usize) {
    let mut i: usize = 0;
    while i < length {
        array[i] = 0;
        i += 1;
    }
}