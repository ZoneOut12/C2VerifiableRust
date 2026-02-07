// ========== Original Code (with ACSL) ==========
/*@ requires n > 0;
    ensures 0 <= \\result && \\result < n;
    assigns \\nothing;
*/
int pick_index(int n) { return 0; }

/*@ 
  requires n > 0;
  requires \\valid_read(p + (0..n-1));
  assigns \\nothing;
*/
int pick_element(int* p, int n) {
  int i = pick_index(n);
  //@ assert (0 <= i && i < n);
  //@ assert \\valid_read(p + (0..n-1));
  return p[i];
}

/*@
  requires \valid_read(p + (0..0));
  ensures \result == p[0];
  assigns \nothing;
*/
int pick_first(int* p) {
  return p[0];
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid with n=3 and array [1,2,3]
void test_case_1() {
    int arr[] = {1, 2, 3};
    int result = pick_element(arr, 3);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid single element array
void test_case_2() {
    int arr[] = {42};
    int result = pick_element(arr, 1);
    printf("test_case_2: %d\n", result);  // Expected: 42
}

// Test case 3: Valid array with zero and negative values
void test_case_3() {
    int arr[] = {0, -5};
    int result = pick_element(arr, 2);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid array with all negative values
void test_case_4() {
    int arr[] = {-1, -2, -3, -4};
    int result = pick_element(arr, 4);
    printf("test_case_4: %d\n", result);  // Expected: -1
}

// Test case 5: Valid larger array with n=5
void test_case_5() {
    int arr[] = {10, 20, 30, 40, 50};
    int result = pick_element(arr, 5);
    printf("test_case_5: %d\n", result);  // Expected: 10
}

// Test case 6: Boundary case with minimal allowed n=1
void test_case_6() {
    int arr[] = {5};
    int result = pick_element(arr, 1);
    printf("test_case_6: %d\n", result);  // Expected: 5
}

// Test case 7: Boundary case with exactly 2 elements
void test_case_7() {
    int arr[] = {100, 200};
    int result = pick_element(arr, 2);
    printf("test_case_7: %d\n", result);  // Expected: 100
}

// Test case 8: Invalid n=0
void test_case_8() {
    int arr[] = {1, 2};
    int result = pick_element(arr, 0);  // Frama-C should flag this
}

// Test case 9: Invalid NULL pointer
void test_case_9() {
    int* arr = NULL;
    int result = pick_element(arr, 2);  // Frama-C should flag this
}

// Harness entry point
void test_harness_pick_element() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not fully tested - for precondition analysis
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