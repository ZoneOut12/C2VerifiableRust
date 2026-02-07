// ========== Original Code (with ACSL) ==========
/*@ requires \valid(a) && \valid(b);
  assigns  *a, *b ;
  ensures  \old(*a) < \old(*b)  ==> *a == \old(*b) && *b == \old(*a) ;
  ensures  \old(*a) >= \old(*b) ==> *a == \old(*a) && *b == \old(*b) ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

extern int h ;

int main(){
  h = 42 ;

  int a = 24 ;
  int b = 42 ;

  max_ptr(&a, &b) ;

  //@ assert a == 42 && b == 24 ;
  //@ assert h == 42 ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - a < b
void test_case_1() {
    int a_val = 24;
    int b_val = 42;
    max_ptr(&a_val, &b_val);
    printf("test_case_1: a=%d, b=%d\n", a_val, b_val); // Expected: a=42, b=24
}

// Test case 2: Valid - a > b
void test_case_2() {
    int a_val = 50;
    int b_val = 30;
    max_ptr(&a_val, &b_val);
    printf("test_case_2: a=%d, b=%d\n", a_val, b_val); // Expected: a=50, b=30
}

// Test case 3: Valid - a == b
void test_case_3() {
    int a_val = 10;
    int b_val = 10;
    max_ptr(&a_val, &b_val);
    printf("test_case_3: a=%d, b=%d\n", a_val, b_val); // Expected: a=10, b=10
}

// Test case 4: Valid - a negative, b positive
void test_case_4() {
    int a_val = -5;
    int b_val = 3;
    max_ptr(&a_val, &b_val);
    printf("test_case_4: a=%d, b=%d\n", a_val, b_val); // Expected: a=3, b=-5
}

// Test case 5: Valid - a larger positive
void test_case_5() {
    int a_val = 100;
    int b_val = 50;
    max_ptr(&a_val, &b_val);
    printf("test_case_5: a=%d, b=%d\n", a_val, b_val); // Expected: a=100, b=50
}

// Test case 6: Invalid - a is NULL
void test_case_6() {
    int b_val = 42;
    max_ptr(NULL, &b_val); // Frama-C should flag this
}

// Test case 7: Invalid - b is NULL
void test_case_7() {
    int a_val = 24;
    max_ptr(&a_val, NULL); // Frama-C should flag this
}

// Test Case 8: Boundary - Negative and Zero ---
void test_case_8() {
    int a_val = -1;
    int b_val = 0;
    max_ptr(&a_val, &b_val);
    printf("test_case_8: a=%d, b=%d\n", a_val, b_val); // Expected: a=0, b=-1
}

// Test case 9: Boundary - INT_MIN and INT_MAX
void test_case_9() {
    int a_val = -2147483648;
    int b_val = 2147483647;
    max_ptr(&a_val, &b_val);
    printf("test_case_9: a=%d, b=%d\n", a_val, b_val); // Expected: a=2147483647, b=-2147483648
}

// Harness entry point
void test_harness_max_ptr() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called
}