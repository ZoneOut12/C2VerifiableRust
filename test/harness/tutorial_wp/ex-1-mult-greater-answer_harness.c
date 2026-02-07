// ========== Original Code (with ACSL) ==========
/*@ lemma mult_greater:
    \forall integer x, y, z ; x >= 0 ==> y <= z ==> x * y <= x * z ;
*/

/*@ requires x >= 0;
    requires y <= z;
    ensures \result == x * y;
*/
int mult(int x, int y, int z) {
    return x * y;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - x positive, y < z
void test_case_1() {
    int result = mult(2, 3, 5);
    printf("test_case_1: %d\n", result);  // Expected: 6
}

// Test case 2: Valid - x=0, y < z
void test_case_2() {
    int result = mult(0, -5, 10);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - y == z
void test_case_3() {
    int result = mult(5, 5, 5);
    printf("test_case_3: %d\n", result);  // Expected: 25
}

// Test case 4: Valid - x positive, y negative < z
void test_case_4() {
    int result = mult(1, -1, 0);
    printf("test_case_4: %d\n", result);  // Expected: -1
}

// Test case 5: Valid - y == z
void test_case_5() {
    int result = mult(10, 2, 2);
    printf("test_case_5: %d\n", result);  // Expected: 20
}

// Test case 6: Boundary - all zeros
void test_case_6() {
    int result = mult(0, 0, 0);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - max integers
void test_case_7() {
    int result = mult(1, 2147483647, 2147483647);
    printf("test_case_7: %d\n", result);  // Expected: 2147483647
}

// Test case 8: Invalid - x < 0
void test_case_8() {
    int result = mult(-1, 3, 5);  // Frama-C should flag this
}

// Test case 9: Invalid - y > z
void test_case_9() {
    int result = mult(4, 5, 3);  // Frama-C should flag this
}

// Harness entry point
void test_harness_mult() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and 9 not called - invalid cases
}
void test_case_8() {
  assert(mult(-1, 2, 3) == -6);
}
void test_case_9() {
  assert(mult(5, 4, 3) == 60);
}