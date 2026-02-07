fn increment_array_by(arr: &mut [i32], n: i32, c: i32) {
    let mut i: i32 = 0;
    while i < n {
        arr[i as usize] = arr[i as usize] + c;
        i += 1;
    }
}