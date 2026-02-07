// ========== Original Code (with ACSL) ==========
/*@ requires n >= 0;
    requires 0 <= n1 < n && 0 <= n2 < n;
    requires \valid(arr + (0..n-1));
    ensures (arr[n2] == \old(arr[n1])) && (arr[n2] == \old(arr[n1]));
*/
void array_swap(int* arr, int n, int n1, int n2) {
    int temp = arr[n1];
    arr[n1] = arr[n2];
    arr[n2] = temp;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal swap
void test_case_1() {
    int arr[] = {1, 2, 3};
    array_swap(arr, 3, 0, 1);
    printf("test_case_1: [%d, %d, %d]\n", arr[0], arr[1], arr[2]);  // Expected: [2, 1, 3]
}

// Test case 2: Valid - same indices
void test_case_2() {
    int arr[] = {5, 6};
    array_swap(arr, 2, 1, 1);
    printf("test_case_2: [%d, %d]\n", arr[0], arr[1]);  // Expected: [5, 6]
}

// Test case 3: Valid - middle elements swap
void test_case_3() {
    int arr[] = {10, 20, 30, 40};
    array_swap(arr, 4, 2, 3);
    printf("test_case_3: [%d, %d, %d, %d]\n", arr[0], arr[1], arr[2], arr[3]);  // Expected: [10, 20, 40, 30]
}

// Test case 4: Valid - first and last swap
void test_case_4() {
    int arr[] = {0, 1, 2, 3};
    array_swap(arr, 4, 0, 3);
    printf("test_case_4: [%d, %d, %d, %d]\n", arr[0], arr[1], arr[2], arr[3]);  // Expected: [3, 1, 2, 0]
}

// Test case 5: Valid - non-adjacent swap
void test_case_5() {
    int arr[] = {5, 4, 3, 2, 1};
    array_swap(arr, 5, 2, 4);
    printf("test_case_5: [%d, %d, %d, %d, %d]\n", arr[0], arr[1], arr[2], arr[3], arr[4]);  // Expected: [5, 4, 1, 2, 3]
}

// Test case 6: Invalid - negative n
void test_case_6() {
    int arr[] = {1, 2, 3};
    array_swap(arr, -3, 0, 1);  // Frama-C should flag n >= 0 violation
}

// Test case 7: Invalid - array too small
void test_case_7() {
    int arr[] = {1, 2};
    array_swap(arr, 3, 2, 0);  // Frama-C should flag \valid(arr) violation
}

// Test case 8: Boundary - single element
void test_case_8() {
    int arr[] = {42};
    array_swap(arr, 1, 0, 0);
    printf("test_case_8: [%d]\n", arr[0]);  // Expected: [42]
}

// Test case 9: Boundary - 2-element swap
void test_case_9() {
    int arr[] = {1, 2};
    array_swap(arr, 2, 0, 1);
    printf("test_case_9: [%d, %d]\n", arr[0], arr[1]);  // Expected: [2, 1]
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
    // Invalid test cases intentionally not called
}
void test_case_6() {
    int arr[] = {1, 2, 3};
    int n = -1;
    int n1 = 0;
    int n2 = 1;
    array_swap(arr, n, n1, n2);
}

void test_case_7() {
    int *arr = NULL;
    int n = 2;
    int n1 = 0;
    int n2 = 1;
    array_swap(arr, n, n1, n2);
}