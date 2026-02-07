fn bsearch(arr: &[i32], len: usize, value: i32) -> usize {
    if len == 0 {
        return 0;
    }
    let mut low: usize = 0;
    let mut up: usize = len;
    while low < up {
        let mid: usize = low + (up - low) / 2;
        if arr[mid] > value {
            up = mid;
        } else if arr[mid] < value {
            low = mid + 1;
        } else {
            return mid;
        }
    }
    len
}