// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@
  requires a < b  ==> b - a <= INT_MAX ;
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

// Test case 1: Valid - normal case
void test_case_1() {
    int result = distance(5, 10);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - negative to positive
void test_case_2() {
    int result = distance(-3, 2);
    printf("test_case_2: %d\n", result);  // Expected: 5
}

// Test case 3: Valid - equal values
void test_case_3() {
    int result = distance(0, 0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - near INT_MAX
void test_case_4() {
    int result = distance(2147483645, 2147483647);
    printf("test_case_4: %d\n", result);  // Expected: 2
}

// Test case 5: Valid - near INT_MIN
void test_case_5() {
    int result = distance(-2147483647, 0);
    printf("test_case_5: %d\n", result);  // Expected: 2147483647
}

// Test case 6: Boundary - maximum allowed difference
void test_case_6() {
    int result = distance(0, 2147483647);
    printf("test_case_6: %d\n", result);  // Expected: 2147483647
}

// Test case 7: Boundary - equal INT_MIN values
void test_case_7() {
    int result = distance(-2147483648, -2147483648);
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - a < b with overflow
void test_case_8() {
    int result = distance(-2147483648, 0);
    // No output check needed for invalid case
}

// Test case 9: Invalid - b <= a with overflow
void test_case_9() {
    int result = distance(2147483647, -2147483647);
    // No output check needed for invalid case
}

// Harness entry point (not main!)
void test_harness_distance() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
void test_case_8() {
    volatile int a = INT_MIN;
    volatile int b = 0;
    volatile int result = distance(a, b);
}

void test_case_9() {
    volatile int a = INT_MAX;
    volatile int b = -1;
    volatile int result = distance(a, b);
}