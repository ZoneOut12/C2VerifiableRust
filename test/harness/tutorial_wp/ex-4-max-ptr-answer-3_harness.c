// ========== Original Code (with ACSL) ==========
#include <stdlib.h>
#include <limits.h>

/*@
  requires \valid_read(a) && \valid_read(b);
  
  assigns  \nothing ;

  ensures  \result == *a || \result == *b ;
  
  behavior is_b:
    assumes *a < *b ;
    ensures \result == *b ;

  behavior is_a:
    assumes *a > *b ;
    ensures \result == *a ;

  behavior is_both:
    assumes *a == *b ;
    ensures \result == *a == *b ;

  complete behaviors ;
  disjoint behaviors ;
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

// Test case 1: Valid - a < b
void test_case_1() {
    int a_val = 10;
    int b_val = 20;
    int result = max_ptr(&a_val, &b_val);
    printf("test_case_1: %d\\n", result);  // Expected: 20
}

// Test case 2: Valid - a > b
void test_case_2() {
    int a_val = 30;
    int b_val = 15;
    int result = max_ptr(&a_val, &b_val);
    printf("test_case_2: %d\\n", result);  // Expected: 30
}

// Test case 3: Valid - a == b
void test_case_3() {
    int a_val = 5;
    int b_val = 5;
    int result = max_ptr(&a_val, &b_val);
    printf("test_case_3: %d\\n", result);  // Expected: 5
}

// Test case 4: Valid - negative and positive
void test_case_4() {
    int a_val = -5;
    int b_val = 5;
    int result = max_ptr(&a_val, &b_val);
    printf("test_case_4: %d\\n", result);  // Expected: 5
}

// Test case 5: Valid - both zero
void test_case_5() {
    int a_val = 0;
    int b_val = 0;
    int result = max_ptr(&a_val, &b_val);
    printf("test_case_5: %d\\n", result);  // Expected: 0
}

// Test case 6: Invalid - a is NULL
void test_case_6() {
    int b_val = 42;
    int result = max_ptr(NULL, &b_val);  // Frama-C should flag this
}

// Test case 7: Invalid - b is NULL
void test_case_7() {
    int a_val = 24;
    int result = max_ptr(&a_val, NULL);  // Frama-C should flag this
}

// Test case 8: Boundary - INT_MIN and INT_MAX
void test_case_8() {
    int a_val = INT_MIN;
    int b_val = INT_MAX;
    int result = max_ptr(&a_val, &b_val);
    printf("test_case_8: %d\\n", result);  // Expected: INT_MAX
}

// Test case 9: Boundary - same pointer
void test_case_9() {
    int val = 5;
    int result = max_ptr(&val, &val);
    printf("test_case_9: %d\\n", result);  // Expected: 5
}

// Harness entry point (not main!)
void test_harness_max_ptr() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
}