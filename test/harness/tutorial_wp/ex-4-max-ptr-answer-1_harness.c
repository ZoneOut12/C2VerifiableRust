// ========== Original Code (with ACSL) ==========
/*@
  requires \valid_read(a) && \valid_read(b);
  assigns  \nothing ;
  ensures  *a <  *b ==> \result == *b ;
  ensures  *a >= *b ==> \result == *a ;
  ensures  \result == *a || \result == *b ;
*/
int max_ptr(int* a, int* b){
  return (*a < *b) ? *b : *a ;
}

extern int h ;

int main(){
  h = 42 ;

  int a = 24 ;
  int b = 42 ;

  int x = max_ptr(&a, &b) ;
  
  //@ assert x == 42 ;
  //@ assert h == 42 ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - original case
void test_case_1() {
    int a = 24;
    int b = 42;
    int result = max_ptr(&a, &b);
    printf("test_case_1: %d\n", result);  // Expected: 42
}

// Test case 2: Valid - a > b
void test_case_2() {
    int a = 50;
    int b = 30;
    int result = max_ptr(&a, &b);
    printf("test_case_2: %d\n", result);  // Expected: 50
}

// Test case 3: Valid - a negative, b positive
void test_case_3() {
    int a = -5;
    int b = 3;
    int result = max_ptr(&a, &b);
    printf("test_case_3: %d\n", result);  // Expected: 3
}

// Test case 4: Valid - both zero
void test_case_4() {
    int a = 0;
    int b = 0;
    int result = max_ptr(&a, &b);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - extreme values
void test_case_5() {
    int a = 2147483647; // INT_MAX
    int b = -2147483648; // INT_MIN
    int result = max_ptr(&a, &b);
    printf("test_case_5: %d\n", result);  // Expected: INT_MAX
}

// Test case 6: Boundary - equal values
void test_case_6() {
    int a = 42;
    int b = 42;
    int result = max_ptr(&a, &b);
    printf("test_case_6: %d\n", result);  // Expected: 42
}

// Test case 7: Boundary - same pointer
void test_case_7() {
    int val = 42;
    int result = max_ptr(&val, &val);
    printf("test_case_7: %d\n", result);  // Expected: 42
}

// Test case 8: Invalid - a is NULL
void test_case_8() {
    int b = 42;
    int result = max_ptr(NULL, &b); // Frama-C should flag this
}

// Test case 9: Invalid - b is NULL
void test_case_9() {
    int a = 24;
    int result = max_ptr(&a, NULL); // Frama-C should flag this
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
    // test_case_8 and test_case_9 intentionally not called
}