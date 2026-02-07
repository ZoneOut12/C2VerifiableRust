// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  \forall size_t j; 0 <= j < length ==> array[j] == 0;
*/
void reset(int* array, size_t length){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; 0 <= j < i ==> array[j] == 0;
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i)
    array[i] = 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    reset(arr, 5);
    for(size_t i = 0; i < 5; i++) {
        printf("arr[%zu] = %d\n", i, arr[i]);  // Expected: 0
    }
}

// Test case 2: Valid - single element
void test_case_2() {
    int arr[] = {42};
    reset(arr, 1);
    printf("arr[0] = %d\n", arr[0]);  // Expected: 0
}

// Test case 3: Valid - 2 elements
void test_case_3() {
    int arr[] = {10, 20};
    reset(arr, 2);
    for(size_t i = 0; i < 2; i++) {
        printf("arr[%zu] = %d\n", i, arr[i]);  // Expected: 0
    }
}

// Test case 4: Valid - 6 elements
void test_case_4() {
    int arr[] = {5, 4, 3, 2, 1, 0};
    reset(arr, 6);
    for(size_t i = 0; i < 6; i++) {
        printf("arr[%zu] = %d\n", i, arr[i]);  // Expected: 0
    }
}

// Test case 5: Valid - negative values
void test_case_5() {
    int arr[] = {-1, -2, -3};
    reset(arr, 3);
    for(size_t i = 0; i < 3; i++) {
        printf("arr[%zu] = %d\n", i, arr[i]);  // Expected: 0
    }
}

// Test case 6: Boundary - zero-length array
void test_case_6() {
    int arr[1];  // Dummy array (won't be accessed)
    reset(arr, 0);
    // No output check needed for zero-length
}

// Test case 7: Boundary - minimum non-zero length
void test_case_7() {
    int arr[] = {99};
    reset(arr, 1);
    printf("arr[0] = %d\n", arr[0]);  // Expected: 0
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    reset(NULL, 3);  // Frama-C should flag this
}

// Test case 9: Invalid - array too small
void test_case_9() {
    int arr[] = {1, 2};
    reset(arr, 3);  // Frama-C should flag this
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
    // test_case_8();  // Intentionally not called
    // test_case_9();  // Intentionally not called
}
void test_case_8() {
    int *arr = NULL;
    size_t length = 5;
    reset(arr, length);
}

void test_case_9() {
    int arr[2] = {0, 0};
    size_t length = 3;
    reset(arr, length);
}