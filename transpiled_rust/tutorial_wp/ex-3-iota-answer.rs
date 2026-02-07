fn iota(array: &mut [i32], len: usize, value: i32) {
    if len > 0 {
        array[0] = value;

        let mut i: usize = 1;
        while i < len {
            array[i] = array[i - 1] + 1;
            i += 1;
        }
    }
}