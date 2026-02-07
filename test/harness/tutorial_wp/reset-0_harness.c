// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@
  inductive zeroed(int* a, integer b, integer e){
  case zeroed_empty:
    \forall int* a, integer b, e; b >= e ==> zeroed(a,b,e);
  case zeroed_range:
    \forall int* a, integer b, e; b < e ==>
      zeroed(a,b,e-1) && a[e-1] == 0 ==> zeroed(a,b,e);
  }
*/


/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  zeroed(array,0,length);
*/
void reset(int* array, size_t length){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant zeroed(array,0,i);
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i){
    array[i] = 0;
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    reset(arr, 5);
    printf("test_case_1: success\n");
}

// Test case 2: Valid - single element
void test_case_2() {
    int arr[] = {7};
    reset(arr, 1);
    printf("test_case_2: success\n");
}

// Test case 3: Valid - longer array
void test_case_3() {
    int arr[10];
    for (int i = 0; i < 10; i++) arr[i] = 5;
    reset(arr, 10);
    printf("test_case_3: success\n");
}

// Test case 4: Valid - already zeros
void test_case_4() {
    int arr[] = {0, 0, 0};
    reset(arr, 3);
    printf("test_case_4: success\n");
}

// Test case 5: Valid - mixed values
void test_case_5() {
    int arr[] = {1, -1, 2};
    reset(arr, 3);
    printf("test_case_5: success\n");
}

// Test case 6: Boundary - zero-length array
void test_case_6() {
    int dummy[1];
    reset(dummy, 0);
    printf("test_case_6: success\n");
}

// Test case 7: Boundary - smallest non-zero length
void test_case_7() {
    int arr[] = {42};
    reset(arr, 1);
    printf("test_case_7: success\n");
}

// Test case 8: Invalid - NULL pointer with non-zero length
void test_case_8() {
    int *arr = NULL;
    reset(arr, 3);
}

// Test case 9: Invalid - array too small
void test_case_9() {
    int arr[] = {1, 2};
    reset(arr, 3);
}

// Harness entry point
void test_harness_reset() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called
}