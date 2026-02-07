// ========== Original Code (with ACSL) ==========
/*@ requires \valid(a) && \valid(b) ;
  assigns *a, *b ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

/*@ requires \valid(a) && \valid(b) ;
  assigns *a, *b ;
*/
void min_ptr(int* a, int* b){
  max_ptr(b, a);
}

/*@ requires \valid(a) && \valid(b) && \valid(c) ;
  assigns *a, *b, *c ;
*/
void order_3_inc_min(int* a, int* b, int* c){
  min_ptr(a, b) ;
  min_ptr(a, c) ;
  min_ptr(b, c) ;
}

/*@ requires \valid(a) && \valid_read(b) ;
  requires INT_MIN <= *a + *b <= INT_MAX ;
  assigns  *a;
*/
void incr_a_by_b(int* a, int const* b){
  *a += *b;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - normal addition
void test_case_1() {
    int a = 5;
    int b = 10;
    incr_a_by_b(&a, &b);
    printf("test_case_1: %d\n", a);  // Expected: 15
}

// Test case 2: Valid - mixed sign
void test_case_2() {
    int a = -3;
    int b = 5;
    incr_a_by_b(&a, &b);
    printf("test_case_2: %d\n", a);  // Expected: 2
}

// Test case 3: Valid - INT_MAX + 0
void test_case_3() {
    int a = INT_MAX;
    int b = 0;
    incr_a_by_b(&a, &b);
    printf("test_case_3: %d\n", a);  // Expected: INT_MAX
}

// Test case 4: Boundary - INT_MIN + 0
void test_case_4() {
    int a = INT_MIN;
    int b = 0;
    incr_a_by_b(&a, &b);
    printf("test_case_4: %d\n", a);  // Expected: INT_MIN
}

// Test case 5: Valid - zero addition
void test_case_5() {
    int a = 0;
    int b = 0;
    incr_a_by_b(&a, &b);
    printf("test_case_5: %d\n", a);  // Expected: 0
}

// Test case 6: Invalid - NULL pointer for a
void test_case_6() {
    int b = 5;
    incr_a_by_b(NULL, &b);  // Frama-C should flag this
}

// Test case 7: Boundary - overflow case (INT_MAX + 1)
void test_case_7() {
    int a = INT_MAX;
    int b = 1;
    incr_a_by_b(&a, &b);  // Frama-C should flag overflow
}

// Test case 8: Valid - exact INT_MAX reach
void test_case_8() {
    int a = INT_MAX - 5;
    int b = 5;
    incr_a_by_b(&a, &b);
    printf("test_case_8: %d\n", a);  // Expected: INT_MAX
}

// Test case 9: Invalid - underflow case (INT_MIN - 1)
void test_case_9() {
    int a = INT_MIN;
    int b = -1;
    incr_a_by_b(&a, &b);  // Frama-C should flag underflow
}

// Harness entry point (not main!)
void test_harness_incr_a_by_b() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    // Invalid cases intentionally not called - for precondition testing
}
void test_case_6() {
    int b = 10;
    incr_a_by_b(NULL, &b);
}

void test_case_9() {
    int a_val = INT_MAX;
    int b_val = 1;
    incr_a_by_b(&a_val, &b_val);
}