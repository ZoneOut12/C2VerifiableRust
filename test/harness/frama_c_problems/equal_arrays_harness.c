// ========== Original Code (with ACSL) ==========
/*@ 
    requires n > 0;
    requires \valid_read (a + (0..n-1));
    requires \valid_read (b + (0..n-1));
    assigns \nothing;

    behavior equal:
        assumes \forall integer k;  0 <= k < n ==> b[k] == a[k];
        ensures \result == 1;

    behavior not_equal:
        assumes \exists integer k;  0 <= k < n && b[k] != a[k];
        ensures \result == 0;
*/
int check(int *a, int *b, int n) {
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == b[k];
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return 0;
        }
    }
    return 1;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - equal arrays with n=5
void test_case_1() {
    int a[] = {1, 2, 3, 4, 5};
    int b[] = {1, 2, 3, 4, 5};
    int result = check(a, b, 5);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - arrays differ at index 1 with n=3
void test_case_2() {
    int a[] = {1, 2, 3};
    int b[] = {1, 9, 3};
    int result = check(a, b, 3);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - arrays differ at last element with n=3
void test_case_3() {
    int a[] = {10, 20, 30};
    int b[] = {10, 20, 40};
    int result = check(a, b, 3);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - equal arrays with n=1
void test_case_4() {
    int a[] = {42};
    int b[] = {42};
    int result = check(a, b, 1);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - arrays differ at index 2 with n=4
void test_case_5() {
    int a[] = {5, 5, 5, 5};
    int b[] = {5, 5, 6, 5};
    int result = check(a, b, 4);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - minimum valid n=1 with equal elements
void test_case_6() {
    int a[] = {100};
    int b[] = {100};
    int result = check(a, b, 1);
    printf("test_case_6: %d\n", result);  // Expected: 1
}

// Test case 7: Boundary - minimum valid n=1 with different elements
void test_case_7() {
    int a[] = {50};
    int b[] = {60};
    int result = check(a, b, 1);
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - n=0 violates n>0
void test_case_8() {
    int a[] = {0};
    int b[] = {0};
    int result = check(a, b, 0);  // Frama-C should flag this
}

// Test case 9: Invalid - a=NULL violates \valid_read
void test_case_9() {
    int b[] = {1, 2, 3};
    int *a = NULL;
    int result = check(a, b, 3);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_check() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}