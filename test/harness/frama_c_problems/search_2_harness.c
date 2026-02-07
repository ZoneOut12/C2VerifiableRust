// ========== Original Code (with ACSL) ==========
/*@\
    requires n > 0;
    requires \valid_read(a + (0..n-1));
    assigns \nothing;

    behavior present:
        assumes \exists integer k; 0 <= k < n && x == a[k];
        ensures \result == 1;

    behavior not_present:
        assumes  \forall integer k; 0 <= k < n ==> x != a[k];
        ensures \result == 0;
*/
int arraySearch(int *a, int x, int n) {
    int p = 0;
    /*@
        loop invariant  0 <= p <= n;
        loop invariant \forall integer k; 0 <= k < p ==> x != a[k];
        loop assigns p;
        loop variant n - p;
    */
    while (p < n) {
        if (a[p] == x) {
            return 1;
        }
        if (p == (n-1))
            break;
        p++;
    }
    return 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - x present in the middle
void test_case_1() {
    int a[] = {1, 2, 3, 4};
    int result = arraySearch(a, 3, 4);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - x not present
void test_case_2() {
    int a[] = {1, 2, 3, 4};
    int result = arraySearch(a, 5, 4);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - x is first element
void test_case_3() {
    int a[] = {5, 6, 7};
    int result = arraySearch(a, 5, 3);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - x is last element
void test_case_4() {
    int a[] = {10, 20, 30};
    int result = arraySearch(a, 30, 3);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - x present in larger array
void test_case_5() {
    int a[] = {1, 2, 3, 4, 5};
    int result = arraySearch(a, 4, 5);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Boundary - n=1 and x present
void test_case_6() {
    int a[] = {42};
    int result = arraySearch(a, 42, 1);
    printf("test_case_6: %d\n", result);  // Expected: 1
}

// Test case 7: Boundary - n=1 and x not present
void test_case_7() {
    int a[] = {42};
    int result = arraySearch(a, 5, 1);
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - n=0
void test_case_8() {
    int a[] = {1, 2, 3};
    int result = arraySearch(a, 2, 0);  // Frama-C should flag this
}

// Test case 9: Invalid - a is NULL
void test_case_9() {
    int *a = NULL;
    int result = arraySearch(a, 5, 3);  // Frama-C should flag this
}

// Harness entry point
void test_harness_arraySearch() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
void test_case_8() {
    int *a = NULL;
    int x = 42;
    int n = 5;
    int expected = -1;
    int result = arraySearch(a, x, n);
    assert(result == expected);
}

void test_case_9() {
    int a[] = {10, 20};
    int x = 20;
    int n = 3;
    int expected = -1;
    int result = arraySearch(a, x, n);
    assert(result == expected);
}