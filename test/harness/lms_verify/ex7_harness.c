// ========== Original Code (with ACSL) ==========
/*@ requires n>0 && \valid(p+(0..n-1));
    ensures \result==-1 ==> !(\exists int i; 0<=i<n && p[i]==v);
    ensures \result!=-1 ==> 0 <= \result < n && p[\result]==v;
    assigns \nothing;
*/
int member(int* p, int n, int v) {
  /*@
    loop invariant (0 <= i <= n);
    loop invariant !(\exists int j; 0 <= j < i && p[j]==v);
    loop assigns i;
    loop variant n-i;
  */
  for (int i=0; i<n; i++) {
    if (p[i]==v) return i;
  }
  return -1;
}

/*@ requires n>0 && \valid(p+(0..n-1));
    ensures \result==-1 ==> !(\exists int i; 0<=i<n && p[i]==v);
    ensures \result!=-1 ==> 0 <= \result < n && p[\result]==v;
    assigns \nothing;
*/
int member_noreturn(int* p, int n, int v) {
  int r = -1;
  /*@
    loop invariant (0 <= i <= n);
    loop invariant r==-1 ==> !(\exists int j; 0 <= j < i && p[j]==v);
    loop invariant r!=-1 ==> 0 <= r < n && p[r]==v;
    loop assigns i, r;
    loop variant n-i;
  */
  for (int i=0; i<n; i++) {
    if (r==-1 && p[i]==v) {
      r = i;
    }
  }
  return r;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - element at first position
void test_case_1() {
    int arr[] = {5, 2, 3};
    int res1 = member(arr, 3, 5);
    printf("test_case_1 (member): %d\n", res1);           // Expected: 0
    int res2 = member_noreturn(arr, 3, 5);
    printf("test_case_1 (member_noreturn): %d\n", res2);  // Expected: 0
}

// Test case 2: Valid - element in middle
void test_case_2() {
    int arr[] = {1, 3, 5, 7, 9};
    int res1 = member(arr, 5, 5);
    printf("test_case_2 (member): %d\n", res1);           // Expected: 2
    int res2 = member_noreturn(arr, 5, 5);
    printf("test_case_2 (member_noreturn): %d\n", res2);  // Expected: 2
}

// Test case 3: Valid - element not found
void test_case_3() {
    int arr[] = {10, 20, 30, 40};
    int res1 = member(arr, 4, 15);
    printf("test_case_3 (member): %d\n", res1);           // Expected: -1
    int res2 = member_noreturn(arr, 4, 15);
    printf("test_case_3 (member_noreturn): %d\n", res2);  // Expected: -1
}

// Test case 4: Valid - element at last position
void test_case_4() {
    int arr[] = {10, 20, 30, 40};
    int res1 = member(arr, 4, 40);
    printf("test_case_4 (member): %d\n", res1);           // Expected: 3
    int res2 = member_noreturn(arr, 4, 40);
    printf("test_case_4 (member_noreturn): %d\n", res2);  // Expected: 3
}

// Test case 5: Valid - multiple occurrences
void test_case_5() {
    int arr[] = {2, 2, 2, 2, 2};
    int res1 = member(arr, 5, 2);
    printf("test_case_5 (member): %d\n", res1);           // Expected: 0
    int res2 = member_noreturn(arr, 5, 2);
    printf("test_case_5 (member_noreturn): %d\n", res2);  // Expected: 0
}

// Test case 6: Invalid - n=0 (violates n>0)
void test_case_6() {
    int arr[] = {1, 2, 3};
    member(arr, 0, 5);
    member_noreturn(arr, 0, 5);
}

// Test case 7: Invalid - NULL array (violates \valid)
void test_case_7() {
    member(NULL, 3, 5);
    member_noreturn(NULL, 3, 5);
}

// Test case 8: Boundary - n=1 with element present
void test_case_8() {
    int arr[] = {42};
    int res1 = member(arr, 1, 42);
    printf("test_case_8 (member): %d\n", res1);           // Expected: 0
    int res2 = member_noreturn(arr, 1, 42);
    printf("test_case_8 (member_noreturn): %d\n", res2);  // Expected: 0
}

// Test case 9: Boundary - n=1 with element not present
void test_case_9() {
    int arr[] = {42};
    int res1 = member(arr, 1, 0);
    printf("test_case_9 (member): %d\n", res1);           // Expected: -1
    int res2 = member_noreturn(arr, 1, 0);
    printf("test_case_9 (member_noreturn): %d\n", res2);  // Expected: -1
}

// Harness entry point
void test_harness_member() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
}