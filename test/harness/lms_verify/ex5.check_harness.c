// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
requires \valid(x0+(0..1));
ensures ((x0[0]==\old(x0[1])) &&
(x0[1]==\old(x0[0])));
*/
void array_swap(int  * x0) {
  int x2 = x0[0];
  int x3 = x0[1];
  x0[0] = x3;
  x0[1] = x2;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - normal swap
void test_case_1() {
    int arr[] = {1, 2};
    array_swap(arr);
    printf("test_case_1: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);  // Expected: 2,1
}

// Test case 2: Valid - equal values
void test_case_2() {
    int arr[] = {5, 5};
    array_swap(arr);
    printf("test_case_2: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);  // Expected: 5,5
}

// Test case 3: Valid - negative numbers
void test_case_3() {
    int arr[] = {-3, -7};
    array_swap(arr);
    printf("test_case_3: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);  // Expected: -7,-3
}

// Test case 4: Valid - zero and positive
void test_case_4() {
    int arr[] = {0, 42};
    array_swap(arr);
    printf("test_case_4: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);  // Expected: 42,0
}

// Test case 5: Valid - zero and negative
void test_case_5() {
    int arr[] = {0, -1};
    array_swap(arr);
    printf("test_case_5: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);  // Expected: -1,0
}

// Test case 6: Boundary - max and min integers
void test_case_6() {
    int arr[] = {INT_MAX, INT_MIN};
    array_swap(arr);
    printf("test_case_6: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);  // Expected: INT_MIN,INT_MAX
}

// Test case 7: Boundary - adjacent values
void test_case_7() {
    int arr[] = {1, 0};
    array_swap(arr);
    printf("test_case_7: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);  // Expected: 0,1
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    array_swap(NULL);  // Frama-C should flag this
}

// Test case 9: Invalid - insufficient array size
void test_case_9() {
    int arr[1] = {5};
    array_swap(arr);  // Frama-C should flag this
}

// Harness entry point
void test_harness_array_swap() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called
}