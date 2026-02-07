fn lemma_value_of_sum_of_n_integers_2(n: u32) {
    let mut i: u32 = 0;
    while i < n {
        i += 1;
    }
}

fn lemma_value_of_sum_of_range_of_integers(fst: i32, lst: i32) {
    let mut i: i32 = fst;
    while i < lst {
        i += 1;
    }
}

fn sum_n(n: u32) -> u32 {
    lemma_value_of_sum_of_n_integers_2(n);
    // verus_assert(1);
    (n * (n + 1)) / 2
}