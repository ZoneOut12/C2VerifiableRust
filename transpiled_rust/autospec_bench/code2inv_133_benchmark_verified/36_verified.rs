fn unknown() -> i32 {
    unimplemented!();
}

fn main() {
    let mut c: i32 = 0;
    while unknown() != 0 {
        if unknown() != 0 {
            if c != 40 {
                c = c + 1;
            }
        } else {
            if c == 40 {
                c = 1;
            }
        }
    }
    if c != 40 {
        // verus_assert(1);
    }
}