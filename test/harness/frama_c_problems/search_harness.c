// ========== Original Code (with ACSL) ==========
/*@ 
requires n > 0;
requires \valid_read(a + (0..n-1));
assigns \nothing;

behavior present:
    assumes \exists integer k;  0 <= k < n && x == a[k];
    ensures \result == 1;

behavior not_present:
    assumes \forall integer k;  0 <= k < n ==> x != a[k];
    ensures \result == 0;

disjoint behaviors;
complete behaviors;
*/
int arraysearch(int* a, int x, int n) { 
  /*@ 
     loop invariant 0 <= p <= n;
     loop invariant \forall integer k;  0 <= k < p ==> x != a[k];
     loop assigns p;
     loop variant n - p;
 */
  for (int p = 0; p < n; p++) {
    if (x == a[p]) 
       return 1;
  }
  return 0;
} 

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - x present at first position
void test_case_1() {
    int a[] = {5, 6, 7};
    int result = arraysearch(a, 5, 3);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - x present in middle
void test_case_2() {
    int a[] = {1, 2, 3, 4};
    int result = arraysearch(a, 3, 4);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - x present at last position
void test_case_3() {
    int a[] = {10, 20};
    int result = arraysearch(a, 20, 2);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - x not present
void test_case_4() {
    int a[] = {1, 2, 3};
    int result = arraysearch(a, 5, 3);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - single element, x present
void test_case_5() {
    int a[] = {7};
    int result = arraysearch(a, 7, 1);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Invalid - n equals 0
void test_case_6() {
    int a[] = {0};  // Dummy array
    int result = arraysearch(a, 5, 0);  // Frama-C should flag this
    // No output check needed for invalid case
}

// Test case 7: Invalid - array pointer is NULL
void test_case_7() {
    int* a = NULL;
    int result = arraysearch(a, 3, 2);  // Frama-C should flag this
    // No output check needed for invalid case
}

// Test case 8: Boundary - single element, x not present
void test_case_8() {
    int a[] = {5};
    int result = arraysearch(a, 6, 1);
    printf("test_case_8: %d\n", result);  // Expected: 0
}

// Test case 9: Boundary - two elements, x at last position
void test_case_9() {
    int a[] = {1, 2};
    int result = arraysearch(a, 2, 2);
    printf("test_case_9: %d\n", result);  // Expected: 1
}

// Harness entry point (not main!)
void test_harness_arraysearch() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
}
void test_case_6() {
    int a[] = {1,2,3};
    int result = arraysearch(a, 2, 0);
}

void test_case_7() {
    int* a = NULL;
    int result = arraysearch(a, 5, 5);
}