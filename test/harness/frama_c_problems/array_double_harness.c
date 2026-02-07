// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
    requires n > 0;
    requires \valid(a+(0..n-1));
    requires \forall integer k; 0 <= k < n ==> a[k] == k && 2*k <= INT_MAX;
    ensures \forall integer k; 0 <= k < n ==> a[k] == 2*k;
*/
void arrayDouble(int *a, int n) {
    int p = 0;
    /*@
        loop invariant 0 <= p <= n;
        loop invariant \forall integer k; p <= k < n ==> a[k] == k;
        loop invariant \forall integer k; 0 <= k < p ==> a[k] == 2*k;
        loop assigns p, a[0..n-1];
        loop variant n - p;
    */
    while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    } 
}

int main() {
    int arr[] = {0,1,2,3,4,5};
    arrayDouble(arr, 6);
}


// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array
void test_case_1() {
    int arr[] = {0,1,2,3,4};
    arrayDouble(arr, 5);
    printf("test_case_1: arr[0]=%d, arr[1]=%d, arr[2]=%d, arr[3]=%d, arr[4]=%d\n", arr[0], arr[1], arr[2], arr[3], arr[4]);
}

// Test case 2: Valid - minimum n=1
void test_case_2() {
    int arr[] = {0};
    arrayDouble(arr, 1);
    printf("test_case_2: arr[0]=%d\n", arr[0]);
}

// Test case 3: Valid - n=2
void test_case_3() {
    int arr[] = {0,1};
    arrayDouble(arr, 2);
    printf("test_case_3: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);
}

// Test case 4: Valid - n=3
void test_case_4() {
    int arr[] = {0,1,2};
    arrayDouble(arr, 3);
    printf("test_case_4: arr[0]=%d, arr[1]=%d, arr[2]=%d\n", arr[0], arr[1], arr[2]);
}

// Test case 5: Valid - original example
void test_case_5() {
    int arr[] = {0,1,2,3,4,5};
    arrayDouble(arr, 6);
    printf("test_case_5: arr[0]=%d, arr[1]=%d, arr[2]=%d, arr[3]=%d, arr[4]=%d, arr[5]=%d\n", arr[0], arr[1], arr[2], arr[3], arr[4], arr[5]);
}

// Test case 6: Invalid - n=0 (violates n > 0)
void test_case_6() {
    int arr[] = {0};
    arrayDouble(arr, 0);
}

// Test case 7: Invalid - a[1] = 2 != 1
void test_case_7() {
    int arr[] = {0,2};
    arrayDouble(arr, 2);
}

// Test case 8: Boundary - minimum n=1
void test_case_8() {
    int arr[] = {0};
    arrayDouble(arr, 1);
    printf("test_case_8: arr[0]=%d\n", arr[0]);
}

// Test case 9: Boundary - n=2
void test_case_9() {
    int arr[] = {0,1};
    arrayDouble(arr, 2);
    printf("test_case_9: arr[0]=%d, arr[1]=%d\n", arr[0], arr[1]);
}

// Harness entry point (not main!)
void test_harness_arrayDouble() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - invalid preconditions
}
#define BOUNDARY_N (INT_MAX / 2 + 1)

void test_case_8() {
  int n = BOUNDARY_N;
  int a[n];
  for (int i = 0; i < n; i++) {
    a[i] = i;
  }
  arrayDouble(a, n);
  for (int i = 0; i < n; i++) {
    assert(a[i] == 2 * i);
  }
}

void test_case_6() {
  int a[] = {1, 2};
  arrayDouble(a, 2);
}

void test_case_7() {
  int *a = NULL;
  arrayDouble(a, 0);
}