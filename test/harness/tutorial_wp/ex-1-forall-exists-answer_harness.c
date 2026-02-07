// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@ assigns \nothing ; ensures \result <==> (0 <= value <= 42) ; */
int pred(int value){ return 0 <= value && value <= 42; }

/*@ requires \valid_read(array + (0 .. len-1)); assigns \nothing ; ensures \result <==> (\forall integer i ; 0 <= i < len ==> 0 <= array[i] <= 42) ; */
int forall_pred(const int* array, size_t len){
  /*@ loop invariant 0 <= i <= len ; loop invariant \forall integer j ; 0 <= j < i ==> 0 <= array[j] <= 42 ; loop assigns i ; loop variant len-i ; */
  for(size_t i = 0 ; i < len ; ++i){ if(! pred(array[i])) return 0; } return 1;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - all elements within range
void test_case_1() {
    int arr[] = {0, 21, 42};
    int result = forall_pred(arr, 3);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - single element at upper bound
void test_case_2() {
    int arr[] = {42};
    int result = forall_pred(arr, 1);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - single element outside range
void test_case_3() {
    int arr[] = {43};
    int result = forall_pred(arr, 1);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - all elements below range
void test_case_4() {
    int arr[] = {-1, -2, -3};
    int result = forall_pred(arr, 3);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - empty array
void test_case_5() {
    int arr[] = {0};  // Dummy array (not accessed)
    int result = forall_pred(arr, 0);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Invalid - NULL array with len > 0
void test_case_6() {
    int* arr = NULL;
    int result = forall_pred(arr, 2);  // Frama-C should flag this
}

// Test case 7: Invalid - array shorter than len
void test_case_7() {
    int arr[] = {1, 2};
    int result = forall_pred(arr, 3);  // Frama-C should flag this
}

// Test case 8: Boundary - single element at lower bound
void test_case_8() {
    int arr[] = {0};
    int result = forall_pred(arr, 1);
    printf("test_case_8: %d\n", result);  // Expected: 1
}

// Test case 9: Boundary - elements at both bounds
void test_case_9() {
    int arr[] = {0, 42};
    int result = forall_pred(arr, 2);
    printf("test_case_9: %d\n", result);  // Expected: 1
}

// Harness entry point (not main!)
void test_harness_forall_pred() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid cases intentionally not called - for precondition testing
}
void test_case_6() {
    int *array = NULL;
    size_t len = 3;
    int result = forall_pred(array, len);
}

void test_case_7() {
    int array[] = {1, 2};
    size_t len = 3;
    int result = forall_pred(array, len);
}