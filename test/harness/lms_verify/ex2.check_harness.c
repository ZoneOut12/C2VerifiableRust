// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
requires (x0>0);
assigns \nothing;
ensures ((0<=\result) &&
(\result<x0));
*/
int pick_index(int  x0) {
  return 0;
}
/*@
requires ((x7>0) &&
\valid(x6+(0..x7-1)));
assigns \nothing;
*/
int pick_element(int  * x6, int  x7) {
  int x9 = pick_index(x7);
  int x10 = x6[x9];
  return x10;
}
/*@
requires \valid(x15);
assigns \nothing;
ensures (\result==x15[0]);
*/
int pick_first(int  * x15) {
  int x17 = x15[0];
  return x17;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array with 5 elements
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    int result = pick_element(arr, 5);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - array with 2 elements
void test_case_2() {
    int arr[] = {10, 20};
    int result = pick_element(arr, 2);
    printf("test_case_2: %d\n", result);  // Expected: 10
}

// Test case 3: Valid - single element array
void test_case_3() {
    int arr[] = {42};
    int result = pick_element(arr, 1);
    printf("test_case_3: %d\n", result);  // Expected: 42
}

// Test case 4: Valid - array with repeated values
void test_case_4() {
    int arr[] = {5, 5, 5};
    int result = pick_element(arr, 3);
    printf("test_case_4: %d\n", result);  // Expected: 5
}

// Test case 5: Valid - array with mixed values
void test_case_5() {
    int arr[] = {0, -1, 2, 3};
    int result = pick_element(arr, 4);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid - x7=0 violates x7>0 precondition
void test_case_6() {
    int arr[] = {1, 2};
    int result = pick_element(arr, 0);  // Frama-C should flag this
}

// Test case 7: Invalid - NULL array violates validity precondition
void test_case_7() {
    int result = pick_element(NULL, 2);  // Frama-C should flag this
}

// Test case 8: Boundary - minimal valid x7=1
void test_case_8() {
    int arr[] = {100};
    int result = pick_element(arr, 1);
    printf("test_case_8: %d\n", result);  // Expected: 100
}

// Test case 9: Boundary - array exactly size x7=2
void test_case_9() {
    int arr[] = {5, 6};
    int result = pick_element(arr, 2);
    printf("test_case_9: %d\n", result);  // Expected: 5
}

// Harness entry point (not main!)
void test_harness_pick_element() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
    test_case_8();
    test_case_9();
}

// Test case 1: single element
void test_case_1_pick_first() {
    int arr[] = {42};
    int result = pick_first(arr);
    printf("test_case_1: %d\n", result); // Expected: 42
}

// Test case 2: multiple elements
void test_case_2_pick_first() {
    int arr[] = {1, 2, 3};
    int result = pick_first(arr);
    printf("test_case_2: %d\n", result); // Expected: 1
}

// Test case 3: first element is zero
void test_case_3_pick_first() {
    int arr[] = {0, 10, 20};
    int result = pick_first(arr);
    printf("test_case_3: %d\n", result); // Expected: 0
}

// Test case 4: first element negative
void test_case_4_pick_first() {
    int arr[] = {-5, 3, 7};
    int result = pick_first(arr);
    printf("test_case_4: %d\n", result); // Expected: -5
}

// Test case 5: larger array
void test_case_5_pick_first() {
    int arr[] = {100, 200, 300, 400};
    int result = pick_first(arr);
    printf("test_case_5: %d\n", result); // Expected: 100
}

void test_case_6_pick_first() {
    int* p = NULL;
    pick_first(p);
}