// ========== Original Code (with ACSL) ==========
/*@ requires \valid(p+ (0..1));
    ensures p[0] == \old(p[1]);
    ensures p[1] == \old(p[0]);
    assigns p[0], p[1];
*/
void array_swap(int* p) {
  int tmp = p[0];
  p[0] = p[1];
  p[1] = tmp;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array [1,2]
void test_case_1() {
    int arr[] = {1, 2};
    array_swap(arr);
    printf("test_case_1: arr[0] = %d, arr[1] = %d\n", arr[0], arr[1]);  // Expected: 2, 1
}

// Test case 2: Valid - negative and zero values [-5,0]
void test_case_2() {
    int arr[] = {-5, 0};
    array_swap(arr);
    printf("test_case_2: arr[0] = %d, arr[1] = %d\n", arr[0], arr[1]);  // Expected: 0, -5
}

// Test case 3: Valid - identical elements [42,42]
void test_case_3() {
    int arr[] = {42, 42};
    array_swap(arr);
    printf("test_case_3: arr[0] = %d, arr[1] = %d\n", arr[0], arr[1]);  // Expected: 42, 42
}

// Test case 4: Valid - large values [1000,2000]
void test_case_4() {
    int arr[] = {1000, 2000};
    array_swap(arr);
    printf("test_case_4: arr[0] = %d, arr[1] = %d\n", arr[0], arr[1]);  // Expected: 2000, 1000
}

// Test case 5: Valid - zero and positive value [0,5]
void test_case_5() {
    int arr[] = {0, 5};
    array_swap(arr);
    printf("test_case_5: arr[0] = %d, arr[1] = %d\n", arr[0], arr[1]);  // Expected: 5, 0
}

// Test case 6: Invalid - NULL pointer
void test_case_6() {
    array_swap(NULL);  // Frama-C should flag this
}

// Test case 7: Invalid - single element array
void test_case_7() {
    int arr[] = {3};
    array_swap(arr);  // Frama-C should flag this
}

// Test case 8: Boundary - minimal valid array size [0,1]
void test_case_8() {
    int arr[] = {0, 1};
    array_swap(arr);
    printf("test_case_8: arr[0] = %d, arr[1] = %d\n", arr[0], arr[1]);  // Expected: 1, 0
}

// Test case 9: Boundary - array with extra elements [10,20,30]
void test_case_9() {
    int arr[] = {10, 20, 30};
    array_swap(arr);
    printf("test_case_9: arr[0] = %d, arr[1] = %d\n", arr[0], arr[1]);  // Expected: 20, 10
}

// Harness entry point (not main!)
void test_harness_array_swap() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - invalid preconditions
}