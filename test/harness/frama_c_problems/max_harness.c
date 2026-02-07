// ========== Original Code (with ACSL) ==========
/*@ 
    requires \valid_read(a + (0..n-1));
    requires n > 0;

    ensures \forall integer k;  0 <= k < n ==> \result >=  a[k];
    ensures \exists integer k;  0 <= k < n && \result == a[k];

    assigns \nothing;
*/
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];

  /*@ 
    loop invariant \exists integer k; 0 <= k < i && max == a[k];
    loop invariant \forall integer k; 0 <= k < i ==> max >= a[k];
    loop invariant 0 <= i <= n;
    loop assigns i,max;
    loop variant n - i;
 */
  while (i < n) {
    // Beginning of loop
    if (max < a[i]){
      max = a[i];
      //@ assert \exists integer k; 0 <= k < i+1 && max == a[k];
    }
    i = i + 1;
    // End of loop: Loop invariant comes here
  }
  return max;
}  

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal increasing array
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    int result = arraymax(arr, 5);
    printf("test_case_1: %d\\n", result);  // Expected: 5
}

// Test case 2: Valid - normal decreasing array
void test_case_2() {
    int arr[] = {5, 4, 3, 2, 1};
    int result = arraymax(arr, 5);
    printf("test_case_2: %d\\n", result);  // Expected: 5
}

// Test case 3: Valid - mixed array with max in middle
void test_case_3() {
    int arr[] = {3, 1, 4, 2};
    int result = arraymax(arr, 4);
    printf("test_case_3: %d\\n", result);  // Expected: 4
}

// Test case 4: Valid - all elements same
void test_case_4() {
    int arr[] = {2, 2, 2};
    int result = arraymax(arr, 3);
    printf("test_case_4: %d\\n", result);  // Expected: 2
}

// Test case 5: Valid - single element array
void test_case_5() {
    int arr[] = {42};
    int result = arraymax(arr, 1);
    printf("test_case_5: %d\\n", result);  // Expected: 42
}

// Test case 6: Boundary - all elements same (n=2)
void test_case_6() {
    int arr[] = {9, 9};
    int result = arraymax(arr, 2);
    printf("test_case_6: %d\\n", result);  // Expected: 9
}

// Test case 7: Boundary - two elements with max first
void test_case_7() {
    int arr[] = {7, 3};
    int result = arraymax(arr, 2);
    printf("test_case_7: %d\\n", result);  // Expected: 7
}

// Test case 8: Invalid - n=0 violates n > 0
void test_case_8() {
    int arr[] = {1, 2, 3};
    int result = arraymax(arr, 0);  // Frama-C should flag this
}

// Test case 9: Invalid - NULL array pointer
void test_case_9() {
    int* arr = NULL;
    int result = arraymax(arr, 3);  // Frama-C should flag this
}

// Harness entry point
void test_harness_arraymax() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
