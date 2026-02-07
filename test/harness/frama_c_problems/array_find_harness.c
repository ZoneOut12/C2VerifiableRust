// ========== Original Code (with ACSL) ==========
/*@ 
    requires n >= 0;
    requires \valid_read(arr+(0..n-1));
    assigns \nothing;

    ensures -1 <= \result < n;

    ensures 0 <= \result < n ==> arr[\result] == x;
    ensures (\result == -1) ==> (\forall integer i; 0 <= i < n ==> arr[i] != x);
*/
int array_find(int* arr, int n, int x) {
    int i = 0;
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> arr[k] != x;
        loop assigns i;
        loop variant n-i;
    */
    for (i = 0; i < n; i++) {
        if (arr[i] == x) {
            return i;
        }
    }
    return -1;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - x found in the middle
void test_case_1() {
    int arr[] = {10, 20, 30, 40};
    int result = array_find(arr, 4, 30);
    printf("test_case_1: %d\n", result);  // Expected: 2
}

// Test case 2: Valid - x is the first element
void test_case_2() {
    int arr[] = {5, 15, 25};
    int result = array_find(arr, 3, 5);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - x is the last element
void test_case_3() {
    int arr[] = {1, 3, 5};
    int result = array_find(arr, 3, 5);
    printf("test_case_3: %d\n", result);  // Expected: 2
}

// Test case 4: Valid - x not found
void test_case_4() {
    int arr[] = {2, 4, 6, 8};
    int result = array_find(arr, 4, 5);
    printf("test_case_4: %d\n", result);  // Expected: -1
}

// Test case 5: Valid - single-element array with x found
void test_case_5() {
    int arr[] = {42};
    int result = array_find(arr, 1, 42);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - empty array (n=0)
void test_case_6() {
    int arr[] = {0};  // Dummy array
    int result = array_find(arr, 0, 99);
    printf("test_case_6: %d\n", result);  // Expected: -1
}

// Test case 7: Boundary - single-element array with x not found
void test_case_7() {
    int arr[] = {77};
    int result = array_find(arr, 1, 0);
    printf("test_case_7: %d\n", result);  // Expected: -1
}

// Test case 8: Invalid - negative n
void test_case_8() {
    int arr[] = {1, 2, 3};
    int result = array_find(arr, -3, 0);  // Frama-C should flag this
}

// Test case 9: Invalid - NULL array pointer
void test_case_9() {
    int *arr = NULL;
    int result = array_find(arr, 2, 5);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_array_find() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called - for precondition testing
}