// ========== Original Code (with ACSL) ==========
int main() {
    int x = 1;
    int y = 0;

    /*@
    loop invariant y <= 10;
    loop invariant x >= 1 && x <= 11;
    loop invariant x <= 11;
    loop invariant 1 <= x;
    loop invariant 0 <= y;
    loop assigns y;
    loop assigns x;
    loop variant 10 - x;
    */
    while (x <= 10) {
        y = 10 - x;
        x = x +1;
    }

    //@ assert y >= 0;
}

// ========== Testable Helper Function ==========
/*@ requires 1 <= x <= 10;
    requires y == 0;
    ensures \result >= 0;
*/
int test_loop(int x, int y) {
    while (x <= 10) {
        y = 10 - x;
        x = x + 1;
    }
    return y;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - initial x=1, y=0
void test_case_1() {
    int result = test_loop(1, 0);
    printf("test_case_1: %d\n", result);  // Expected: 0
}

// Test case 2: Valid - middle x=5, y=0
void test_case_2() {
    int result = test_loop(5, 0);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - x=9, y=0
void test_case_3() {
    int result = test_loop(9, 0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - x=2, y=0
void test_case_4() {
    int result = test_loop(2, 0);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - x=7, y=0
void test_case_5() {
    int result = test_loop(7, 0);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid - x=0 violates x >= 1
void test_case_6() {
    int result = test_loop(0, 0);  // Frama-C should flag this
}

// Test case 7: Invalid - x=11 violates x <= 10
void test_case_7() {
    int result = test_loop(11, 0);  // Frama-C should flag this
}

// Test case 8: Boundary - minimum x=1
void test_case_8() {
    int result = test_loop(1, 0);
    printf("test_case_8: %d\n", result);  // Expected: 0
}

// Test case 9: Boundary - maximum x=10
void test_case_9() {
    int result = test_loop(10, 0);
    printf("test_case_9: %d\n", result);  // Expected: 0
}

// Harness entry point (not main!)
void test_harness_test_loop() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
    test_case_8();
    test_case_9();
}
void test_case_1() {
    int result = test_loop(1, 0);
    ASSERT(result == 1);
}
void test_case_2() {
    int result = test_loop(2, 0);
    ASSERT(result == 2);
}
void test_case_3() {
    int result = test_loop(5, 0);
    ASSERT(result == 5);
}
void test_case_4() {
    int result = test_loop(8, 0);
    ASSERT(result == 8);
}
void test_case_5() {
    int result = test_loop(10, 0);
    ASSERT(result == 10);
}
void test_case_6() {
    int result = test_loop(0, 0);
    ASSERT(result == -1);
}
void test_case_7() {
    int result = test_loop(5, 1);
    ASSERT(result == -1);
}
void test_case_8() {
    int result = test_loop(1, 0);
    ASSERT(result == 1);
}
void test_case_9() {
    int result = test_loop(10, 0);
    ASSERT(result == 10);
}