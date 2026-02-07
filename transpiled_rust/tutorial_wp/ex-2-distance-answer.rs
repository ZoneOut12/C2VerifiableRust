fn distance(a: i32, b: i32) -> i32 {
    if a < b {
        return b - a;
    } else {
        return a - b;
    }
}