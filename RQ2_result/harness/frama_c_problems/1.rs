fn main() {
    let mut i: i32 = 0;

    while i < 30
    {
        let old_measure = 30 - i;
        assert!(
            0 <= i && i <= 30
        );
        i += 1;
        assert!(old_measure > 30 - i);
    }
    assert!(
        0 <= i && i <= 30
    );
    assert!(i == 30);
}

