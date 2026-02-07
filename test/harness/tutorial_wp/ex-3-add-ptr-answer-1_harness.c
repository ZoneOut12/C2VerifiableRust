// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ 
  requires INT_MIN <= *p + *q <= INT_MAX ;
  requires \\valid_read(p) && \\valid_read(q);
  assigns \\nothing ;
  ensures \\result == *p + *q ;
*/
int add(int *p, int *q){
  return *p + *q ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal case
void test_case_1() {
    int a = 24;
    int b = 42;
    int result = add(&a, &b);
    printf("test_case_1: %d\n", result);  // Expected: 66
}

// Test case 2: Valid - same pointer
void test_case_2() {
    int a = 24;
    int result = add(&a, &a);
    printf("test_case_2: %d\n", result);  // Expected: 48
}

// Test case 3: Valid - two positive numbers
void test_case_3() {
    int a = 100;
    int b = 200;
    int result = add(&a, &b);
    printf("test_case_3: %d\n", result);  // Expected: 300
}

// Test case 4: Valid - positive and negative
void test_case_4() {
    int a = -5;
    int b = 10;
    int result = add(&a, &b);
    printf("test_case_4: %d\n", result);  // Expected: 5
}

// Test case 5: Valid - zeros
void test_case_5() {
    int a = 0;
    int b = 0;
    int result = add(&a, &b);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - sum is INT_MAX
void test_case_6() {
    int a = 2147483647; // INT_MAX
    int b = 0;
    int result = add(&a, &b);
    printf("test_case_6: %d\n", result);  // Expected: INT_MAX
}

// Test case 7: Boundary - sum is INT_MIN
void test_case_7() {
    int a = -2147483648; // INT_MIN
    int b = 0;
    int result = add(&a, &b);
    printf("test_case_7: %d\n", result);  // Expected: INT_MIN
}

// Test case 8: Invalid - p is NULL
void test_case_8() {
    int b = 5;
    int result = add(NULL, &b); // Invalid \\valid_read(p)
}

// Test case 9: Invalid - sum overflow
void test_case_9() {
    int a = 2147483647; // INT_MAX
    int b = 1;
    int result = add(&a, &b); // Sum violates first requires clause
}

// Harness entry point
void test_harness_add() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called - for precondition testing
}
void test_case_8() {
    int a = INT_MAX;
    int b = 1;
    int result = add(&a, &b);
}

void test_case_9() {
    int a = INT_MIN;
    int b = -1;
    int result = add(&a, &b);
}