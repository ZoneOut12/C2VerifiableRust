// ========== Original Code (with ACSL) ==========
#include <stdio.h>
/*@ requires c > 0;
    ensures \\result == c;
    assigns \\nothing;
*/
int func(int c) {
    int x = c;
    int y = 0;
    /*@
        loop invariant c == x + y && x >= 0;
        loop assigns x, y;
        loop variant x;
    */
    while(x > 0) {
        x = x - 1;
        y = y + 1;
    }
    return y;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - minimal allowed value
void test_case_1() {
    int result = func(1);
    printf("test_case_1: %d\\n", result);  // Expected: 1
}

// Test case 2: Valid - medium value
void test_case_2() {
    int result = func(5);
    printf("test_case_2: %d\\n", result);  // Expected: 5
}

// Test case 3: Valid - another typical value
void test_case_3() {
    int result = func(10);
    printf("test_case_3: %d\\n", result);  // Expected: 10
}

// Test case 4: Valid - larger value
void test_case_4() {
    int result = func(100);
    printf("test_case_4: %d\\n", result);  // Expected: 100
}

// Test case 5: Valid - large value
void test_case_5() {
    int result = func(1000);
    printf("test_case_5: %d\\n", result);  // Expected: 1000
}

// Test case 6: Boundary - minimal allowed value
void test_case_6() {
    int result = func(1);
    printf("test_case_6: %d\\n", result);  // Expected: 1
}

// Test case 7: Boundary - loop execution test
void test_case_7() {
    int result = func(2);
    printf("test_case_7: %d\\n", result);  // Expected: 2
}

// Test case 8: Invalid - zero input
void test_case_8() {
    int result = func(0);  // Frama-C should flag this
}

// Test case 9: Invalid - negative input
void test_case_9() {
    int result = func(-5);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_func() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}