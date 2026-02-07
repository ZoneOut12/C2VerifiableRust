#include <stddef.h>
#include <limits.h>

/*@
  requires \valid_read(array + (0 .. length-1)) ;
  assigns \nothing ;
  ensures \result == NULL ||
          (\exists integer i ; 0 <= i < length && array+i == \result) ;
*/
int* search(int* array, size_t length, int element){
  /*@
    loop invariant 0 <= i <= length ;
    loop assigns i ;
    loop variant length - i ;
  */
  for(size_t i = 0; i < length; i++)
    if(array[i] == element) return &array[i];
  return NULL;
}

/*@
  requires \forall integer i ; 0 <= i < length ==> array[i] < INT_MAX ;
  requires \valid(array + (0 .. length-1)) ;
*/
void foo(int *array, size_t length){
  int *p = search(array,length,0);
  if (p){
    *p += 1 ;
  }
}


// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - element in middle
void test_case_1() {
    int arr[] = {1,2,3,4};
    size_t length = 4;
    int element = 3;
    int* result = search(arr, length, element);
    if (result != NULL) {
        printf("test_case_1: %d\n", *result);
    } else {
        printf("test_case_1: NULL\n");
    }
}

// Test case 2: Valid - element at start
void test_case_2() {
    int arr[] = {5,6,7};
    size_t length = 3;
    int element = 5;
    int* result = search(arr, length, element);
    if (result != NULL) {
        printf("test_case_2: %d\n", *result);
    } else {
        printf("test_case_2: NULL\n");
    }
}

// Test case 3: Valid - element at end
void test_case_3() {
    int arr[] = {10,20};
    size_t length = 2;
    int element = 20;
    int* result = search(arr, length, element);
    if (result != NULL) {
        printf("test_case_3: %d\n", *result);
    } else {
        printf("test_case_3: NULL\n");
    }
}

// Test case 4: Valid - single element not found
void test_case_4() {
    int arr[] = {42};
    size_t length = 1;
    int element = 99;
    int* result = search(arr, length, element);
    if (result != NULL) {
        printf("test_case_4: %d\n", *result);
    } else {
        printf("test_case_4: NULL\n");
    }
}

// Test case 5: Valid - multiple elements not found
void test_case_5() {
    int arr[] = {1,3,5};
    size_t length = 3;
    int element = 2;
    int* result = search(arr, length, element);
    if (result != NULL) {
        printf("test_case_5: %d\n", *result);
    } else {
        printf("test_case_5: NULL\n");
    }
}

// Test case 6: Boundary - empty array
void test_case_6() {
    int dummy[1];
    int* result = search(dummy, 0, 5);
    printf("test_case_6: %s\n", result == NULL ? "NULL" : "Not NULL");
}

// Test case 7: Boundary - element at last position
void test_case_7() {
    int arr[] = {7,8,9};
    size_t length = 3;
    int element = 9;
    int* result = search(arr, length, element);
    if (result != NULL) {
        printf("test_case_7: %d\n", *result);
    } else {
        printf("test_case_7: NULL\n");
    }
}

// Test case 8: Invalid - NULL array pointer
void test_case_8() {
    int* result = search(NULL, 5, 3);
}

// Test case 9: Invalid - length exceeds array size
void test_case_9() {
    int arr[] = {1,2};
    int* result = search(arr, 3, 0);
}

// Harness entry point
void test_harness_search() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}

/* Case 1: Standard case with a single zero in the middle */
void test_case_1() {
    int arr[] = {1, 0, 3};
    foo(arr, 3);
    /* Expected: index 1 is updated to 1 -> {1, 1, 3} */
}

/* Case 2: Multiple zeros - verify only the first occurrence is modified */
void test_case_2() {
    int arr[] = {0, 2, 0};
    foo(arr, 3);
    /* Expected: first 0 becomes 1, second 0 remains -> {1, 2, 0} */
}

/* Case 3: No zero found - search returns NULL, foo should do nothing */
void test_case_3() {
    int arr[] = {5, 10, 15};
    foo(arr, 3);
    /* Expected: No changes -> {5, 10, 15} */
}

/* Case 4: Boundary - Zero is at the final position of the array */
void test_case_4() {
    int arr[] = {10, 20, 0};
    foo(arr, 3);
    /* Expected: last element updated -> {10, 20, 1} */
}

/* Case 5: Boundary - Empty array (length = 0) */
void test_case_5() {
    int arr[1] = {99}; 
    foo(arr, 0);
    /* Expected: Loop does not run, no modification -> {99} */
}

/* Case 6: Boundary - Elements at the maximum allowed value (INT_MAX - 1) */
void test_case_6() {
    int arr[] = {INT_MAX - 1, 0};
    foo(arr, 2);
    /* Expected: {INT_MAX - 1, 1} */
}

/* Case 7: Boundary - Single element array that is zero */
void test_case_7() {
    int arr[] = {0};
    foo(arr, 1);
    /* Expected: {1} */
}

/* Case 8: Violation - Array contains INT_MAX */
/* Violates: requires \forall integer i ; array[i] < INT_MAX */
void test_case_8() {
    int arr[] = {INT_MAX, 0};
    /* This input is illegal according to the function contract */
    foo(arr, 2);
}

/* Case 9: Violation - NULL pointer with non-zero length */
/* Violates: requires \valid(array + (0 .. length-1)) */
void test_case_9() {
    int *arr = NULL;
    /* Attempting to process 5 elements from a NULL address */
    foo(arr, 5);
}