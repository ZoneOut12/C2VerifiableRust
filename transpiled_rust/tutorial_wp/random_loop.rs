fn random_between(min: usize, max: usize) -> usize {
    unimplemented!();
}

fn random_loop(bound: usize) {
    let mut i: usize = bound;
    while i > 0 {
        i -= random_between(1, i);
    }
}