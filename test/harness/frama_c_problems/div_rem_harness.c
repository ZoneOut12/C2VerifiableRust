// ========== Original Code (with ACSL) ==========
/*@\
    requires \valid(q) && \valid(r);
    requires \separated(q, r);
    requires y != 0;
    assigns *q, *r;
    ensures x == *q * y + *r;
    ensures *r < y;
*/
void div_rem(unsigned x, unsigned y, unsigned* q, unsigned* r) {
    *q = x / y;
    *r = x % y;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - x=10, y=3
void test_case_1() {
    unsigned x = 10;
    unsigned y = 3;
    unsigned q, r;
    div_rem(x, y, &q, &r);
    printf("test_case_1: q=%u, r=%u\n", q, r); // Expected: q=3, r=1
}

// Test case 2: Valid - x=5, y=5
void test_case_2() {
    unsigned x = 5;
    unsigned y = 5;
    unsigned q, r;
    div_rem(x, y, &q, &r);
    printf("test_case_2: q=%u, r=%u\n", q, r); // Expected: q=1, r=0
}

// Test case 3: Valid - x=0, y=5
void test_case_3() {
    unsigned x = 0;
    unsigned y = 5;
    unsigned q, r;
    div_rem(x, y, &q, &r);
    printf("test_case_3: q=%u, r=%u\n", q, r); // Expected: q=0, r=0
}

// Test case 4: Valid - x=1, y=1
void test_case_4() {
    unsigned x = 1;
    unsigned y = 1;
    unsigned q, r;
    div_rem(x, y, &q, &r);
    printf("test_case_4: q=%u, r=%u\n", q, r); // Expected: q=1, r=0
}

// Test case 5: Valid - x=7, y=2
void test_case_5() {
    unsigned x = 7;
    unsigned y = 2;
    unsigned q, r;
    div_rem(x, y, &q, &r);
    printf("test_case_5: q=%u, r=%u\n", q, r); // Expected: q=3, r=1
}

// Test case 6: Invalid - y=0
void test_case_6() {
    unsigned x = 5;
    unsigned y = 0;
    unsigned q, r;
    div_rem(x, y, &q, &r); // Frama-C should flag this
}

// Test case 7: Invalid
void test_case_7() {
    unsigned x = 22;
    unsigned y = 0;
    unsigned q, r;
    div_rem(x, y, &q, &r); // Frama-C should flag this
}

// Test case 8: Boundary - x=0, y=1
void test_case_8() {
    unsigned x = 0;
    unsigned y = 1;
    unsigned q, r;
    div_rem(x, y, &q, &r);
    printf("test_case_8: q=%u, r=%u\n", q, r); // Expected: q=0, r=0
}

// Test case 9: Boundary - x=3, y=4
void test_case_9() {
    unsigned x = 3;
    unsigned y = 4;
    unsigned q, r;
    div_rem(x, y, &q, &r);
    printf("test_case_9: q=%u, r=%u\n", q, r); // Expected: q=0, r=3
}

// Harness entry point (not main!)
void test_harness_div_rem() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - they're for precondition testing
}