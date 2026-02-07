// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@
  requires \valid_read(array + (0 .. length-1));

  assigns  \nothing;

  behavior notin:
    assumes \forall size_t off ; 0 <= off < length ==> array[off] != element;
    ensures \result == NULL;

  behavior in:
    assumes \exists size_t off ; 0 <= off < length && array[off] == element;
    ensures array <= \result < array+length && *\result == element;

  disjoint behaviors;
  complete behaviors;
*/
int* search(int* array, size_t length, int element){
  /*@ loop invariant 0 <= i <= length;
      loop invariant \forall size_t j; 0 <= j < i ==> array[j] != element;
      loop assigns i;
      loop variant length - i; */
  for(size_t i = 0; i < length; i++)
    if(array[i] == element) return &array[i];
  return NULL;
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