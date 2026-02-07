// ========== Original Code (with ACSL) ==========
/* run.config
   STDOPT:#"-warn-unsigned-overflow -warn-unsigned-downcast"
*/

#include <stddef.h>

/*@
  requires beg < end ;
  requires \valid_read(a+(beg .. end-1)) ;
  assigns \nothing ;
  ensures beg <= \result < end ;
*/
size_t min_idx_in(int* a, size_t beg, size_t end){
  size_t min_i = beg;
  /*@
    loop invariant beg+1 <= i <= end ;
    loop invariant beg <= min_i < end ;
    loop assigns i, min_i ;
    loop variant end-i ;
  */
  for(size_t i = beg+1; i < end; ++i){
    if(a[i] < a[min_i]) min_i = i;
  }
  return min_i;
}

/*@
  requires \valid(p) && \valid(q);
  assigns *p, *q;
*/
void swap(int* p, int* q){
  int tmp = *p; *p = *q; *q = tmp;
}

/*@
  requires beg <= end ;
  requires \valid(a+(beg .. end-1)) ;
  assigns a[beg .. end-1] ;
*/
void sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end ;
    loop assigns i, a[beg .. end-1] ;
    loop variant end-i ;
  */
  for(size_t i = beg ; i < end ; ++i){
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array
void test_case_1() {
    int a[] = {5, 3, 2, 4};
    sort(a, 0, 4);
    printf("test_case_1: [%d, %d, %d, %d]\n", a[0], a[1], a[2], a[3]);  // Expected: [2, 3, 4, 5]
}

// Test case 2: Valid - single element
void test_case_2() {
    int a[] = {42};
    sort(a, 0, 1);
    printf("test_case_2: [%d]\n", a[0]);  // Expected: [42]
}

// Test case 3: Valid - already sorted
void test_case_3() {
    int a[] = {1, 2, 3, 4};
    sort(a, 0, 4);
    printf("test_case_3: [%d, %d, %d, %d]\n", a[0], a[1], a[2], a[3]);  // Expected: [1, 2, 3, 4]
}

// Test case 4: Valid - descending order
void test_case_4() {
    int a[] = {4, 3, 2, 1};
    sort(a, 0, 4);
    printf("test_case_4: [%d, %d, %d, %d]\n", a[0], a[1], a[2], a[3]);  // Expected: [1, 2, 3, 4]
}

// Test case 5: Valid - duplicates
void test_case_5() {
    int a[] = {3, 2, 3, 2};
    sort(a, 0, 4);
    printf("test_case_5: [%d, %d, %d, %d]\n", a[0], a[1], a[2], a[3]);  // Expected: [2, 2, 3, 3]
}

// Test case 6: Invalid - beg > end
void test_case_6() {
    int a[] = {1, 2, 3};
    sort(a, 3, 2);  // Frama-C should flag this
}

// Test case 7: Invalid - array too small
void test_case_7() {
    int a[] = {1, 2};
    sort(a, 0, 3);  // Frama-C should flag this
}

// Test case 8: Boundary - empty range
void test_case_8() {
    int a[] = {1, 2, 3, 4};
    sort(a, 2, 2);
    printf("test_case_8: [%d, %d, %d, %d]\n", a[0], a[1], a[2], a[3]);  // Expected: [1, 2, 3, 4]
}

// Test case 9: Boundary - single element range
void test_case_9() {
    int a[] = {42};
    sort(a, 0, 1);
    printf("test_case_9: [%d]\n", a[0]);  // Expected: [42]
}

// Harness entry point (not main!)
void test_harness_sort() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
}

void test_harness_valid_min_idx_in() {
    int arr[] = {10, 2, 33, 2, 55, -5, 100};
    size_t res;

    // --- Test Case 1: Standard range, min at the beginning of sub-range ---
    // Range: arr[1..2] is {2, 33}, min is 2 at index 1
    res = min_idx_in(arr, 1, 3);
    printf("Valid 1: Expected 1, Got %zu\n", res);

    // --- Test Case 2: Standard range, min at the end of sub-range ---
    // Range: arr[0..1] is {10, 2}, min is 2 at index 1
    res = min_idx_in(arr, 0, 2);
    printf("Valid 2: Expected 1, Got %zu\n", res);

    // --- Test Case 3: Single element range (beg + 1 == end) ---
    // Range: arr[4..4] is {55}, min index must be 4
    res = min_idx_in(arr, 4, 5);
    printf("Valid 3: Expected 4, Got %zu\n", res);

    // --- Test Case 4: Range contains negative values ---
    // Full array, min is -5 at index 5
    res = min_idx_in(arr, 0, 7);
    printf("Valid 4: Expected 5, Got %zu\n", res);

    // --- Test Case 5: Duplicate minimum values ---
    // Range: {2, 33, 2, 55}. Stability check: should return the first index (1)
    res = min_idx_in(arr, 1, 5);
    printf("Valid 5: Expected 1, Got %zu\n", res);

    // --- Test Case 6: Boundary - end of the physical array ---
    res = min_idx_in(arr, 5, 7);
    printf("Valid 6: Expected 5, Got %zu\n", res);

    // --- Test Case 7: Sub-range with INT_MIN ---
    int arr_ext[] = {0, INT_MAX, INT_MIN, 10};
    res = min_idx_in(arr_ext, 0, 4);
    printf("Valid 7: Expected 2, Got %zu\n", res);
}

void test_harness_invalid_min_idx_in() {
    int arr[] = {1, 2, 3};

    // --- Test Case 8: Invalid - Violates 'requires beg < end' ---
    // beg (5) is greater than end (2). Logic will likely return 5 or hang.
    // size_t res8 = min_idx_in(arr, 5, 2); 

    // --- Test Case 9: Invalid - Violates '\valid_read' (Buffer Overflow) ---
    // end (10) exceeds the allocated size of arr (3).
    // size_t res9 = min_idx_in(arr, 0, 10); 
}

void test_harness_swap() {
    int a, b;

    // Valid 1: Distinct variables
    a = 10; b = 20; swap(&a, &b);
    
    // Valid 2: 
    a = -100; b = -214400; swap(&a, &b);

    // Valid 3: Identical values
    a = 42; b = 42; swap(&a, &b);

    // Valid 4: Negative values
    a = -1; b = 5; swap(&a, &b);

    // Valid 5: Extreme values
    a = 2147483647; b = -2147483648; swap(&a, &b);

    // Valid 6: Heap memory
    int *p = malloc(sizeof(int)); *p = 100;
    int *q = malloc(sizeof(int)); *q = 200;
    swap(p, q); free(p); free(q);

    // Valid 7:
    int *p7 = malloc(sizeof(int)); *p = -5;
    int *q7 = malloc(sizeof(int)); *q = 20;
    swap(p7, q7); free(p7); free(q7);

    // Invalid 8: p is NULL
    // swap(NULL, &a);

    // Invalid 9: q is invalid address
    // swap(&a, (int*)0x1);
}