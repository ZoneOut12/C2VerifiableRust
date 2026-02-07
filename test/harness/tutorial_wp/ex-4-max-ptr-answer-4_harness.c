// ========== Original Code (with ACSL) ==========
#include <stdlib.h>
#include <limits.h>

/*@
  requires a == NULL || \valid_read(a) ;
  requires b == NULL || \valid_read(b);
  
  assigns  \nothing ;

  ensures  \result == INT_MIN || \result == *a || \result == *b ;
  
  behavior both_null:
    assumes a == NULL && b == NULL ;
    ensures \result == INT_MIN ;

  behavior a_null:
    assumes a == NULL && b != NULL ;
    ensures \result == *b ;

  behavior b_null:
    assumes a != NULL && b == NULL ;
    ensures \result == *a ;

  behavior is_a:
    assumes a != NULL && b != NULL && *a >= *b ;
    ensures \result == *a ;

  behavior is_b:
    assumes a != NULL && b != NULL && *a <  *b ;
    ensures \result == *b ;

  complete behaviors ;
  disjoint behaviors ;
*/
int max_ptr(int* a, int* b){
  if(!a && !b) return INT_MIN ;
  if(!a) return *b ;
  if(!b) return *a ;  
  return (*a < *b) ? *b : *a ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - both NULL
void test_case_1() {
    int* a = NULL;
    int* b = NULL;
    int result = max_ptr(a, b);
    printf("test_case_1: %d\n", result);  // Expected: INT_MIN
}

// Test case 2: Valid - a NULL, b valid
void test_case_2() {
    int b_val = 30;
    int* a = NULL;
    int* b = &b_val;
    int result = max_ptr(a, b);
    printf("test_case_2: %d\n", result);  // Expected: 30
}

// Test case 3: Valid - b NULL, a valid
void test_case_3() {
    int a_val = 25;
    int* a = &a_val;
    int* b = NULL;
    int result = max_ptr(a, b);
    printf("test_case_3: %d\n", result);  // Expected: 25
}

// Test case 4: Valid - both valid, a >= b
void test_case_4() {
    int a_val = 50;
    int b_val = 30;
    int* a = &a_val;
    int* b = &b_val;
    int result = max_ptr(a, b);
    printf("test_case_4: %d\n", result);  // Expected: 50
}

// Test case 5: Valid - both valid, a < b
void test_case_5() {
    int a_val = 30;
    int b_val = 50;
    int* a = &a_val;
    int* b = &b_val;
    int result = max_ptr(a, b);
    printf("test_case_5: %d\n", result);  // Expected: 50
}

// Test case 6: Boundary - both valid and equal
void test_case_6() {
    int a_val = 50;
    int b_val = 50;
    int* a = &a_val;
    int* b = &b_val;
    int result = max_ptr(a, b);
    printf("test_case_6: %d\n", result);  // Expected: 50
}

// Test case 7: Boundary - extreme values
void test_case_7() {
    int a_val = INT_MIN;
    int b_val = INT_MAX;
    int* a = &a_val;
    int* b = &b_val;
    int result = max_ptr(a, b);
    printf("test_case_7: %d\n", result);  // Expected: INT_MAX
}

// Test case 8: Invalid - a is invalid pointer
void test_case_8() {
    int b_val = 100;
    int* a = (int*)0x1;  // Invalid pointer
    int* b = &b_val;
    int result = max_ptr(a, b);
    // No output check needed for invalid case
}

// Test case 9: Invalid - b is invalid pointer
void test_case_9() {
    int a_val = 100;
    int* a = &a_val;
    int* b = (int*)0x1;  // Invalid pointer
    int result = max_ptr(a, b);
    // No output check needed for invalid case
}

// Harness entry point
void test_harness_max_ptr() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called - for precondition testing
}
