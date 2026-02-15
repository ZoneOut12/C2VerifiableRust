fn main() {
    let mut x: i32 = 1;
    let mut y: i32 = 0;

    while x <= 10
    {
        let old_measure = 10 - x;
        assert!(
            y <= 10 &&
            (x >= 1 && x <= 11) &&
            x <= 11 &&
            1 <= x &&
            0 <= y
        );
        y = 10 - x;
        x = x + 1;
        assert!(old_measure > 10 - x);
    }
    assert!(
        y <= 10 &&
        (x >= 1 && x <= 11) &&
        x <= 11 &&
        1 <= x &&
        0 <= y
    );
    assert!(y >= 0);
}

