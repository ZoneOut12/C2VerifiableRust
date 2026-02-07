fn occurrences_of(value: i32, in_: &[i32], length: usize) -> usize {
    let mut result: usize = 0;
    let mut i: usize = length;
    while i > 0 {
        result += if in_[i - 1] == value { 1 } else { 0 };
        i -= 1;
    }
    result
}