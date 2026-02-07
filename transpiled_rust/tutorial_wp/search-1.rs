fn search(array: &mut [i32], length: usize, element: i32) -> Option<&mut i32> {
    let mut i: usize = 0;
    while i < length {
        if array[i] == element {
            return Some(&mut array[i]);
        }
        i += 1;
    }
    None
}