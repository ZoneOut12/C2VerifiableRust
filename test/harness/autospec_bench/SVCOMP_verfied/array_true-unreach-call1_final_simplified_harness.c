// ========== Original Code (with ACSL) ==========
#include "assert.h"

void main() {
  int A[2048];
  int i;

  /*@
  loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
  loop invariant 0 <= i <= 1024;
  loop assigns i;
  loop assigns A[0..1023];
  loop variant 1024 - i; 
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }

  //@ assert A[1023] == 1023;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - array size 2048
void test_case_1() {
  int A[2048];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
  printf("test_case_1: %d\n", A[1023]);  // Expected: 1023
}

// Test case 2: Valid - array size exactly 1024
void test_case_2() {
  int A[1024];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
  printf("test_case_2: %d\n", A[1023]);  // Expected: 1023
}

// Test case 3: Valid - array size 1500
void test_case_3() {
  int A[1500];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
  printf("test_case_3: %d\n", A[1023]);  // Expected: 1023
}

// Test case 4: Valid - array size 3000
void test_case_4() {
  int A[3000];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
  printf("test_case_4: %d\n", A[1023]);  // Expected: 1023
}

// Test case 5: Valid - array size 1024 (duplicate check)
void test_case_5() {
  int A[1024];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
  printf("test_case_5: %d\n", A[1023]);  // Expected: 1023
}

// Test case 6: Invalid - array size 500 (violates size requirement)
void test_case_6() {
  int A[500];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;  // Frama-C should flag this
  }
}

// Test case 7: Invalid - i initialized to 1 (violates i initialization)
void test_case_7() {
  int A[2048];
  int i = 1;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 1; i < 1024; i++) {
    A[i] = i;  // Frama-C should flag this
  }
}

// Test case 8: Boundary - array size exactly 1024
void test_case_8() {
  int A[1024];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
  printf("test_case_8: %d\n", A[1023]);  // Expected: 1023
}

// Test case 9: Boundary - loop runs exactly 1024 times
void test_case_9() {
  int A[2048];
  int i = 0;
  /*@
    loop invariant \\forall integer j; 0 <= j < i ==> A[j] == j;
    loop invariant 0 <= i <= 1024;
    loop assigns i;
    loop assigns A[0..1023];
    loop variant 1024 - i;
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
  printf("test_case_9: %d\n", A[1023]);  // Expected: 1023
}

// Harness entry point
void test_harness_main() {
  test_case_1();
  test_case_2();
  test_case_3();
  test_case_4();
  test_case_5();
  // test_case_6() and test_case_7() intentionally not called - for precondition testing
  test_case_8();
  test_case_9();
}