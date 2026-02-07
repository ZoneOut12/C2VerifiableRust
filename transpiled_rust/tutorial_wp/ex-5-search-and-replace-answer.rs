fn search_and_replace(array: &mut [i32], length: usize, old: i32, new: i32) {
    let mut i: usize = 0;
    while i < length {
        if array[i] == old {
            array[i] = new;
        }
        i += 1;
    }
}