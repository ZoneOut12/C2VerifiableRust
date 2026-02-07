// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ requires a < b  ==> b - a <= INT_MAX ;
  requires b <= a ==> a - b <= INT_MAX ;

  ensures a < b  ==> a + \result == b ;
  ensures b <= a ==> a - \result == b ;
*/
int distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal case where a < b
void test_case_1() {
    int result = distance(3, 7);
    printf("test_case_1: %d\n", result);  // Expected: 4
}

// Test case 2: Valid - normal case where b < a
void test_case_2() {
    int result = distance(7, 3);
    printf("test_case_2: %d\n", result);  // Expected: 4
}

// Test case 3: Valid - zero and positive
void test_case_3() {
    int result = distance(0, 5);
    printf("test_case_3: %d\n", result);  // Expected: 5
}

// Test case 4: Valid - negative and zero
void test_case_4() {
    int result = distance(-5, 0);
    printf("test_case_4: %d\n", result);  // Expected: 5
}

// Test case 5: Valid - two large positive numbers
void test_case_5() {
    int result = distance(INT_MAX - 1, INT_MAX);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Boundary - maximum allowed difference
void test_case_6() {
    int result = distance(0, INT_MAX);
    printf("test_case_6: %d\n", result);  // Expected: INT_MAX
}

// Test case 7: Boundary - large negative and -1
void test_case_7() {
    int result = distance(INT_MIN, -1);
    printf("test_case_7: %d\n", result);  // Expected: INT_MAX
}

// Test case 8: Invalid - overflow when a < b
void test_case_8() {
    int result = distance(INT_MIN, 1);  // Should violate precondition
}

// Test case 9: Invalid - overflow when b <= a
void test_case_9() {
    int result = distance(INT_MAX, -1);  // Should violate precondition
}

// Harness entry point
void test_harness_distance() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and 9 intentionally not called - they're for precondition testing
}