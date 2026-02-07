// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@ predicate inv_vec_Int(int* x0, integer  x1) = ((x1==0) || ((x1>0) &&
\valid(x0+(0..x1-1))));*/
/*@
requires inv_vec_Int(x15,x16);
assigns \nothing;
ensures inv_vec_Int(x15,x16);
*/
int count_pos(int* x15, int  x16) {
  int x18 = 0;
  /*@
  loop invariant 0<=x20<=x16;
  loop invariant ((0<=x18) &&
  (x18<=x20));
  loop assigns x20, x18;
  loop variant x16-x20;
  */
  for(int x20=0; x20 < x16; x20++) {
    int x22 = x18;
    int x21 = x15[x20];
    int x26 = x21 > 0;
    int x27;
    if (x26) {
      x27 = 1;
    } else {
      x27 = 0;
    }
    int x28 = x22 + x27;
    x18 = x28;
  }
  int x32 = x18;
  return x32;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal case with mixed values
void test_case_1() {
    int arr[] = {1, -2, 3, 0, 5};
    int result = count_pos(arr, 5);
    printf("test_case_1: %d\n", result);  // Expected: 3
}

// Test case 2: Valid - all zeros
void test_case_2() {
    int arr[] = {0, 0, 0};
    int result = count_pos(arr, 3);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - all positive
void test_case_3() {
    int arr[] = {2, 3, 4, 5};
    int result = count_pos(arr, 4);
    printf("test_case_3: %d\n", result);  // Expected: 4
}

// Test case 4: Valid - mix of zero, positive, negative
void test_case_4() {
    int arr[] = {0, 1, -1, 2};
    int result = count_pos(arr, 4);
    printf("test_case_4: %d\n", result);  // Expected: 2
}

// Test case 5: Valid - empty array (x16=0)
void test_case_5() {
    int arr[] = {0};  // Dummy array, not accessed
    int result = count_pos(arr, 0);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - single zero element
void test_case_6() {
    int arr[] = {0};
    int result = count_pos(arr, 1);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - single positive element
void test_case_7() {
    int arr[] = {5};
    int result = count_pos(arr, 1);
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Test case 8: Invalid - negative array size
void test_case_8() {
    int arr[] = {1, 2, 3};
    int result = count_pos(arr, -3);  // Frama-C should flag this
}

// Test case 9: Invalid - NULL array pointer
void test_case_9() {
    int* arr = NULL;
    int result = count_pos(arr, 3);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_count_pos() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}