// ========== Original Code (with ACSL) ==========
#include <stddef.h>
#include <limits.h>

/*@
  axiomatic Sum_array{
    logic integer sum(int* array, integer begin, integer end);

    axiom empty:
      \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
    axiom range:
      \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1)+a[e-1];
  }
*/

/*@
  requires \valid(a+(0..len-1));
  requires \forall integer i, j; INT_MIN <= sum(a,i,j) <= INT_MAX;
  assigns \nothing;
  ensures \forall integer l, h;  0 <= l <= h <= len ==> sum(a,l,h) <= \result;
  ensures \exists integer l, h;  0 <= l <= h <= len &&  sum(a,l,h) == \result;
*/
int max_subarray(int *a, size_t len) {
  int max = 0;
  int cur = 0;
  /*@ ghost size_t cur_low = 0; */
  /*@ ghost size_t low = 0; */
  /*@ ghost size_t high = 0; */

  /*@
    loop invariant BOUNDS: low <= high <= i <= len && cur_low <= i;
    loop invariant REL :   cur == sum(a,cur_low,i) <= max == sum(a,low,high);
    loop invariant POST:   \forall integer l;    0 <= l <= i      ==> sum(a,l,i) <= cur;
    loop invariant POST:   \forall integer l, h; 0 <= l <= h <= i ==> sum(a,l,h) <= max;
    loop assigns i, cur, max, cur_low, low, high;
    loop variant len - i;
  */
  for(size_t i = 0; i < len; i++) {
    /*@ assert(cur+a[i] == sum(a, cur_low, i + 1)); */
    cur += a[i];
    if (cur < 0) {
      cur = 0;
      /*@ ghost cur_low = i+1; */
    }
    if (cur > max) {
      max = cur;
      /*@ ghost low = cur_low; */
      /*@ ghost high = i+1; */
    }
  }
  return max;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array
void test_case_1() {
    int arr[] = {1, 2, 3};
    int result = max_subarray(arr, 3);
    printf("test_case_1: %d\n", result);  // Expected: 6
}

// Test case 2: Valid - mixed values
void test_case_2() {
    int arr[] = {2, -1, 3, -2};
    int result = max_subarray(arr, 4);
    printf("test_case_2: %d\n", result);  // Expected: 4
}

// Test case 3: Valid - all negatives
void test_case_3() {
    int arr[] = {-5, -3, -2};
    int result = max_subarray(arr, 3);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - single positive
void test_case_4() {
    int arr[] = {42};
    int result = max_subarray(arr, 1);
    printf("test_case_4: %d\n", result);  // Expected: 42
}

// Test case 5: Valid - single zero
void test_case_5() {
    int arr[] = {0};
    int result = max_subarray(arr, 1);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid - NULL pointer
void test_case_6() {
    int result = max_subarray(NULL, 3);  // Frama-C should flag this
}

// Test case 7: Invalid - sum exceeds INT_MAX
void test_case_7() {
    int arr[] = {1073741824, 1073741824};  // 2^30 + 2^30 = 2^31 > INT_MAX
    int result = max_subarray(arr, 2);  // Frama-C should flag this
}

// Test case 8: Boundary - empty array
void test_case_8() {
    int arr[] = {0};  // Dummy array (won't be accessed)
    int result = max_subarray(arr, 0);
    printf("test_case_8: %d\n", result);  // Expected: 0
}

// Test case 9: Boundary - single element at INT_MAX
void test_case_9() {
    int arr[] = {2147483647};
    int result = max_subarray(arr, 1);
    printf("test_case_9: %d\n", result);  // Expected: 2147483647
}

// Harness entry point (not main!)
void test_harness_max_subarray() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    test_case_8();
    test_case_9();
}
void test_case_6() {
    int a[] = {1073741824, 1073741824};
    size_t len = 2;
    int result = max_subarray(a, len);
}

void test_case_7() {
    int *a = NULL;
    size_t len = 5;
    int result = max_subarray(a, len);
}