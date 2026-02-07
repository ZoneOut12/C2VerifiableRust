// ========== Original Code (with ACSL) ==========
/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b ;

  behavior reorder:
    assumes *a < *b ;
    ensures *a == \old(*b) && *b == \old(*a) ;

  behavior do_not_change:
    assumes *a >= *b ;
    ensures *a == \old(*a) && *b == \old(*b) ;

  complete behaviors ;
  disjoint behaviors ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

/*@... (other functions omitted for brevity) ...*/

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - a < b
void test_case_1() {
    int a = 3, b = 5;
    max_ptr(&a, &b);
    printf("test_case_1: a=%d, b=%d\n", a, b);  // Expected: a=5, b=3
}

// Test case 2: Valid - a > b
void test_case_2() {
    int a = 5, b = 3;
    max_ptr(&a, &b);
    printf("test_case_2: a=%d, b=%d\n", a, b);  // Expected: no change
}

// Test case 3: Valid - a == b
void test_case_3() {
    int a = 4, b = 4;
    max_ptr(&a, &b);
    printf("test_case_3: a=%d, b=%d\n", a, b);  // Expected: no change
}

// Test case 4: Valid - negative values swapped
void test_case_4() {
    int a = -5, b = -3;
    max_ptr(&a, &b);
    printf("test_case_4: a=%d, b=%d\n", a, b);  // Expected: a=-3, b=-5
}

// Test case 5: Valid - INT_MIN and INT_MAX swapped
void test_case_5() {
    int a = -2147483648, b = 2147483647;
    max_ptr(&a, &b);
    printf("test_case_5: a=%d, b=%d\n", a, b);  // Expected: a=INT_MAX, b=INT_MIN
}

// Test case 6: Invalid - a is NULL
void test_case_6() {
    int b = 5;
    // a is NULL
    max_ptr(NULL, &b);  // Frama-C should flag invalid precondition
}

// Test case 7: Invalid - b is NULL
void test_case_7() {
    int a = 5;
    // b is NULL
    max_ptr(&a, NULL);  // Frama-C should flag invalid precondition
}

// Test case 8: Boundary - zero equality
void test_case_8() {
    int a = 0, b = 0;
    max_ptr(&a, &b);
    printf("test_case_8: a=%d, b=%d\n", a, b);  // Expected: no change
}

// Test case 9: Boundary - adjacent values
void test_case_9() {
    int a = 1, b = 2;
    max_ptr(&a, &b);
    printf("test_case_9: a=%d, b=%d\n", a, b);  // Expected: a=2, b=1
}

// Harness entry point
void test_harness_max_ptr() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6();  // Invalid cases not called for execution
    // test_case_7();
    test_case_8();
    test_case_9();
}
void test_case_6() {
  int a_val = 42;
  max_ptr(&a_val, NULL);
}

void test_case_7() {
  int b_val = 10;
  max_ptr(NULL, &b_val);
}