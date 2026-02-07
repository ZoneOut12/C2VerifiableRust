// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ 
  requires INT_MIN <= *p + *q <= INT_MAX ;
  requires \valid_read(p) && \valid_read(q) && \valid(r) ;
  requires \separated(p, r);
  requires \separated(q, r);
  assigns *r ;
  ensures *r == *p + *q ;
*/
void add(int *p, int *q, int *r){
  *r = *p + *q ;
}

int main(){
  int a = 24 ;
  int b = 42 ;

  int x ;

  add(&a, &b, &x) ;
  //@ assert x == a + b ;
  //@ assert x == 66 ;

  add(&a, &a, &x) ;
  //@ assert x == a + a ;
  //@ assert x == 48 ;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid case with positive integers
void test_case_1() {
    int a = 10;
    int b = 20;
    int x;
    add(&a, &b, &x);
    printf("test_case_1: %d\n", x);  // Expected: 30
}

// Test case 2: Valid case with negative integers
void test_case_2() {
    int a = -5;
    int b = -10;
    int x;
    add(&a, &b, &x);
    printf("test_case_2: %d\n", x);  // Expected: -15
}

// Test case 3: Valid case with same input pointers
void test_case_3() {
    int a = 30;
    int x;
    add(&a, &a, &x);
    printf("test_case_3: %d\n", x);  // Expected: 60
}

// Test case 4: Valid case with zero sum
void test_case_4() {
    int a = -30;
    int b = 30;
    int x;
    add(&a, &b, &x);
    printf("test_case_4: %d\n", x);  // Expected: 0
}

// Test case 5: Valid case with zero inputs
void test_case_5() {
    int a = 0;
    int b = 0;
    int x;
    add(&a, &b, &x);
    printf("test_case_5: %d\n", x);  // Expected: 0
}

// Test case 6: Invalid case - overlapping p and r pointers
void test_case_6() {
    int a = 5;
    int b = 10;
    add(&a, &b, &a);  // r is same as p - violates separation
}

// Test case 7: Invalid case - sum exceeds INT_MAX
void test_case_7() {
    int a = INT_MAX;
    int b = 1;
    int x;
    add(&a, &b, &x);  // sum violates first precondition
}

// Test case 8: Boundary case - sum equals INT_MAX
void test_case_8() {
    int a = INT_MAX;
    int b = 0;
    int x;
    add(&a, &b, &x);
    printf("test_case_8: %d\n", x);  // Expected: INT_MAX
}

// Test case 9: Boundary case - sum equals INT_MIN
void test_case_9() {
    int a = INT_MIN;
    int b = 0;
    int x;
    add(&a, &b, &x);
    printf("test_case_9: %d\n", x);  // Expected: INT_MIN
}

// Harness entry point (not main!)
void test_harness_add() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6();  // Not called for functional testing
    // test_case_7();  // Not called for functional testing
    test_case_8();
    test_case_9();
}
void test_case_1() {
    int a = 0, b = 0, c;
    add(&a, &b, &c);
}
void test_case_2() {
    int a = 2147483647, b = -1, c;
    add(&a, &b, &c);
}
void test_case_3() {
    int a = -2147483647, b = 1, c;
    add(&a, &b, &c);
}
void test_case_4() {
    int a = 100, b = -50, c;
    add(&a, &b, &c);
}
void test_case_5() {
    int a = -10, b = -20, c;
    add(&a, &b, &c);
}
void test_case_6() {
    int a = 2147483647, b = 1, c;
    add(&a, &b, &c);
}
void test_case_7() {
    int a = 5, b = 10;
    add(&a, &b, &a);
}
void test_case_8() {
    int a = 2147483647, b = 0, c;
    add(&a, &b, &c);
}
void test_case_9() {
    int a = -2147483648, b = 0, c;
    add(&a, &b, &c);
}