// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ requires \valid_read(a);
  requires *a <= INT_MAX - 5 ;

  assigns \nothing ;

  ensures \result == *a + 5 ;
*/
int plus_5(int* a){
  return *a + 5 ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input with value 0
void test_case_1() {
    int a_val = 0;
    int result = plus_5(&a_val);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid input with positive value
void test_case_2() {
    int a_val = 10;
    int result = plus_5(&a_val);
    printf("test_case_2: %d\n", result);  // Expected: 15
}

// Test case 3: Valid input with negative value
void test_case_3() {
    int a_val = -5;
    int result = plus_5(&a_val);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid input with larger value
void test_case_4() {
    int a_val = 100;
    int result = plus_5(&a_val);
    printf("test_case_4: %d\n", result);  // Expected: 105
}

// Test case 5: Valid input near upper bound
void test_case_5() {
    int a_val = INT_MAX - 10;
    int result = plus_5(&a_val);
    printf("test_case_5: %d\n", result);  // Expected: INT_MAX-5
}

// Test case 6: Invalid input - NULL pointer
void test_case_6() {
    int result = plus_5(NULL);  // Frama-C should flag this
}

// Test case 7: Invalid input - value exceeds upper bound
void test_case_7() {
    int a_val = INT_MAX - 4;
    int result = plus_5(&a_val);  // Frama-C should flag this
}

// Test case 8: Boundary input - maximum allowed value
void test_case_8() {
    int a_val = INT_MAX - 5;
    int result = plus_5(&a_val);
    printf("test_case_8: %d\n", result);  // Expected: INT_MAX
}

// Test case 9: Boundary input - minimum possible value
void test_case_9() {
    int a_val = INT_MIN;
    int result = plus_5(&a_val);
    printf("test_case_9: %d\n", result);  // Expected: INT_MIN+5
}

// Harness entry point (not main!)
void test_harness_plus_5() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid tests intentionally not called
}
void test_case_6() {
    int result = plus_5(NULL);
}

void test_case_7() {
    int val = INT_MAX - 4;
    int result = plus_5(&val);
}