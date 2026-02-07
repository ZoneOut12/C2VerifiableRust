// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ 
  requires a < b  ==> b - a <= INT_MAX ;
  requires b <= a ==> a - b <= INT_MAX ;

  assigns \nothing ;

  behavior inf:
    assumes a < b ;
    ensures a + \result == b ;

  behavior sup:
    assumes b <= a ;
    ensures a - \result == b ;

  complete behaviors ;
  disjoint behaviors ;
*/
int distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - a < b, normal difference
void test_case_1() {
    int result = distance(5, 10);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - a < b with negative a
void test_case_2() {
    int result = distance(-3, 4);
    printf("test_case_2: %d\n", result);  // Expected: 7
}

// Test case 3: Valid - a == b
void test_case_3() {
    int result = distance(0, 0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - a > b
void test_case_4() {
    int result = distance(10, 3);
    printf("test_case_4: %d\n", result);  // Expected: 7
}

// Test case 5: Valid - a just above INT_MIN
void test_case_5() {
    int result = distance(-2147483647, -2147483648);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Boundary - difference is INT_MAX (a=0, b=INT_MAX)
void test_case_6() {
    int result = distance(0, 2147483647);
    printf("test_case_6: %d\n", result);  // Expected: 2147483647
}

// Test case 7: Boundary - a < b with difference INT_MAX (a=INT_MIN, b=-1)
void test_case_7() {
    int result = distance(-2147483648, -1);
    printf("test_case_7: %d\n", result);  // Expected: 2147483647
}

// Test case 8: Invalid - a < b and b - a exceeds INT_MAX (a=INT_MIN, b=0)
void test_case_8() {
    int result = distance(-2147483648, 0);  // Frama-C should flag this
    // No output check
}

// Test case 9: Invalid - a >= b and a - b exceeds INT_MAX (a=INT_MAX, b=-1)
void test_case_9() {
    int result = distance(2147483647, -1);  // Frama-C should flag this
    // No output check
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
    // test_case_8 and test_case_9 not called - invalid preconditions
}
void test_case_8() { RUN_TEST_HELPER(distance, -2147483648, 1, 2147483649); }
void test_case_9() { RUN_TEST_HELPER(distance, 2147483647, -1, 2147483648); }