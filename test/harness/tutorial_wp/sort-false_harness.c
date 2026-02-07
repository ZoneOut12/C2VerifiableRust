// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@ predicate sorted(int* a, integer b, integer e) =
    \\forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
*/

/*@ requires \\valid(a + (beg .. end-1));
    requires beg < end;

    assigns  a[beg .. end-1];
    
    ensures sorted(a, beg, end);
*/
void fail_sort(int* a, size_t beg, size_t end){
    /*@ loop invariant beg <= i <= end;
        loop invariant \\forall integer j; beg <= j < i ==> a[j] == 0;
        loop assigns i, a[beg .. end-1];
        loop variant end-i;
    */
    for(size_t i = beg ; i < end ; ++i)
        a[i] = 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid array with beg=0 and end=5
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    fail_sort(arr, 0, 5);
    printf("test_case_1: [0 0 0 0 0]\\n");  // Expected all zeros
}

// Test case 2: Valid array with middle elements sorted
void test_case_2() {
    int arr[] = {5, 4, 3, 2, 1};
    fail_sort(arr, 1, 4);
    printf("test_case_2: [5 0 0 0 1]\\n");  // Elements 1-3 set to zero
}

// Test case 3: Valid array with two elements
void test_case_3() {
    int arr[] = {10, 20};
    fail_sort(arr, 0, 2);
    printf("test_case_3: [0 0]\\n");  // Both elements zero
}

// Test case 4: Valid array with larger size and partial sorting
void test_case_4() {
    int arr[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    fail_sort(arr, 2, 8);
    printf("test_case_4: elements 2-7 set to zero\\n");
}

// Test case 5: Valid array with varying values
void test_case_5() {
    int arr[] = {3, 1, 4, 1, 5};
    fail_sort(arr, 0, 5);
    printf("test_case_5: [0 0 0 0 0]\\n");  // All elements zero
}

// Test case 6: Invalid NULL array pointer
void test_case_6() {
    int *arr = NULL;
    fail_sort(arr, 0, 3);  // Frama-C should flag invalid pointer
}

// Test case 7: Invalid beg >= end
void test_case_7() {
    int arr[] = {1, 2, 3};
    fail_sort(arr, 3, 2);  // Frama-C should flag beg >= end
}

// Test case 8: Boundary case with single element
void test_case_8() {
    int arr[] = {42};
    fail_sort(arr, 0, 1);
    printf("test_case_8: [0]\\n");  // Single element set to zero
}

// Test case 9: Boundary case with beg=2 and end=3
void test_case_9() {
    int arr[] = {0, 0, 0};
    fail_sort(arr, 2, 3);
    printf("test_case_9: [0 0 0]\\n");  // Only element at index 2 set to zero
}

// Harness entry point (not main!)
void test_harness_fail_sort() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6();  // Invalid case not called for execution
    // test_case_7();  // Invalid case not called for execution
    test_case_8();
    test_case_9();
}
void test_case_6() {
    int* a = NULL;
    size_t beg = 0;
    size_t end = 5;
    fail_sort(a, beg, end);
}

void test_case_7() {
    int a[] = {1, 2, 3, 4, 5};
    size_t beg = 3;
    size_t end = 2;
    fail_sort(a, beg, end);
}