// ========== Original Code (with ACSL) ==========
/*@\
    requires n > 0;\
    requires \valid_read(a+(0..(n-1)));\
    assigns \nothing;\
\
    behavior all_even:\
        assumes \forall integer k; 0 <= k < n ==> a[k]%2 == 0;\
        ensures \result == 1;\
\
    behavior all_not_even:\
        assumes \exists integer k; 0 <= k < n && a[k]%2 != 0;\
        ensures \result == 0;\
\
    disjoint behaviors;\
    complete behaviors;\
*/
int areElementsEven(int *a, int n) {
    int p = 0;
    /*@\
        loop invariant 0 <= p <= n;\
        loop invariant \forall integer k; 0 <= k < p ==> a[k]%2 == 0;\
        loop assigns p; \
        loop variant n - p;\
    */
    while (p < n) {
        if (a[p]%2 != 0) {
            return 0;
        }
        p = p + 1;
    }
    return 1;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - all even elements
void test_case_1() {
    int arr[] = {2, 4, 6, 8, 10};
    int result = areElementsEven(arr, 5);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - contains odd element
void test_case_2() {
    int arr[] = {2, 3, 4};
    int result = areElementsEven(arr, 3);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - single even element
void test_case_3() {
    int arr[] = {4};
    int result = areElementsEven(arr, 1);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - single odd element
void test_case_4() {
    int arr[] = {5};
    int result = areElementsEven(arr, 1);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - all zeros
void test_case_5() {
    int arr[10] = {0};
    int result = areElementsEven(arr, 10);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Invalid - n = 0
void test_case_6() {
    int arr[] = {0};
    int result = areElementsEven(arr, 0);  // Violates n > 0
}

// Test case 7: Invalid - NULL array pointer
void test_case_7() {
    int result = areElementsEven(NULL, 3);  // Violates \valid_read
}

// Test case 8: Boundary - minimum valid n with even
void test_case_8() {
    int arr[] = {2};
    int result = areElementsEven(arr, 1);
    printf("test_case_8: %d\n", result);  // Expected: 1
}

// Test case 9: Boundary - minimum valid n with odd
void test_case_9() {
    int arr[] = {3};
    int result = areElementsEven(arr, 1);
    printf("test_case_9: %d\n", result);  // Expected: 0
}

// Harness entry point
void test_harness_areElementsEven() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();  // Invalid case for precondition testing
    test_case_7();  // Invalid case for precondition testing
    test_case_8();
    test_case_9();
}