// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
requires (\valid(x0+x1) &&
\valid(x0+x2));
ensures ((x0[x1]==\old(x0[x2])) &&
(x0[x2]==\old(x0[x1])));
assigns x0[x1], x0[x2];
*/
void inswap(int* x0, int  x1, int  x2) {
  int x4 = x0[x1];
  int x5 = x0[x2];
  x0[x1] = x5;
  x0[x2] = x4;
}
/*@
requires ((x23>0) &&
\valid(x22+(0..x23-1)));
ensures (\forall int  x174; (((0<=x174) &&
(x174<(x23-1))) ==> (x22[x174]<=x22[(x174+1)])));
assigns x22[(0..x23-1)];
*/
void insort(int  * x22, int  x23) {
  int x26 = x23;
  /*@
  loop invariant ((((0<=x26) &&
  (x26<=x23)) &&
  (\forall int  x130; (((x26<=x130) &&
  (x130<(x23-1))) ==> (x22[x130]<=x22[(x130+1)])))) &&
  (\forall int  x143; ((((0<=x143) &&
  (x143<x26)) &&
  (x26<=(x23-1))) ==> (x22[x143]<=x22[x26]))));
  loop assigns x26, x22[(0..x23-1)];
  loop variant x26;
  */
  for (;;) {
    int x27 = x26;
    int x28 = x27 > 1;
    if (!x28) break;
    int x30 = 0;
    int x31 = x26;
    /*@
    loop invariant ((((((((0<=x26) &&
    (x26<=x23)) &&
    (0<=x33)) &&
    (x33<=x26)) &&
    (0<=x30)) &&
    (x30<=(x26-1))) &&
    ((x26-1)<x23)) &&
    (\forall int  x62; (((0<=x62) &&
    (x62<x33)) ==> (x22[x62]<=x22[x30]))));
    loop assigns x33, x30;
    loop variant (x26-x33);
    */
    for(int x33=0; x33 < x31; x33++) {
      int x34 = x22[x33];
      int x35 = x30;
      int x36 = x22[x35];
      int x37 = x34 >= x36;
      if (x37) {
        x30 = x33;
      } else {
      }
    }
    int x82 = x30;
    int x81 = x31 - 1;
    inswap(x22,x81,x82);
    /*@assert (\forall int  x84; ((((x26-1)<x84) &&
    (x84<(x23-1))) ==> (x22[x84]<=x22[(x84+1)])));
    */
    /*@assert ((x26<=(x23-1)) ==> (x22[(x26-1)]<=x22[x26]));
    */
    /*@assert (\forall int  x108; (((0<=x108) &&
    (x108<x26)) ==> (x22[x108]<=x22[(x26-1)])));
    */
    x26 = x81;
  }
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

// Test case 1: Valid - normal unsorted array
void test_case_1() {
    int arr[] = {3, 1, 4, 1, 5};
    insort(arr, 5);
    printf("test_case_1: %d %d %d %d %d\n", arr[0], arr[1], arr[2], arr[3], arr[4]);  // Expected: 1 1 3 4 5
}

// Test case 2: Valid - already sorted array
void test_case_2() {
    int arr[] = {1, 2, 3, 4, 5};
    insort(arr, 5);
    printf("test_case_2: %d %d %d %d %d\n", arr[0], arr[1], arr[2], arr[3], arr[4]);  // Expected: 1 2 3 4 5
}

// Test case 3: Valid - all elements equal
void test_case_3() {
    int arr[] = {5, 5, 5, 5};
    insort(arr, 4);
    printf("test_case_3: %d %d %d %d\n", arr[0], arr[1], arr[2], arr[3]);  // Expected: 5 5 5 5
}

// Test case 4: Valid - reverse-sorted 2-element array
void test_case_4() {
    int arr[] = {2, 1};
    insort(arr, 2);
    printf("test_case_4: %d %d\n", arr[0], arr[1]);  // Expected: 1 2
}

// Test case 5: Valid - reverse-sorted 3-element array
void test_case_5() {
    int arr[] = {5, 3, 1};
    insort(arr, 3);
    printf("test_case_5: %d %d %d\n", arr[0], arr[1], arr[2]);  // Expected: 1 3 5
}

// Test case 6: Invalid - size zero
void test_case_6() {
    int arr[] = {1, 2, 3};
    insort(arr, 0);  // Frama-C should flag this
}

// Test case 7: Invalid - NULL pointer
void test_case_7() {
    insort(NULL, 3);  // Frama-C should flag this
}

// Test case 8: Boundary - size 1
void test_case_8() {
    int arr[] = {42};
    insort(arr, 1);
    printf("test_case_8: %d\n", arr[0]);  // Expected: 42
}

// Test case 9: Boundary - two equal elements
void test_case_9() {
    int arr[] = {2, 2};
    insort(arr, 2);
    printf("test_case_9: %d %d\n", arr[0], arr[1]);  // Expected: 2 2
}

// Harness entry point
void test_harness_insort() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6();  // Intentionally not called for precondition testing
    // test_case_7();  // Intentionally not called for precondition testing
    test_case_8();
    test_case_9();
}


// Function prototype matching the ACSL contract
void inswap(int* x0, int x1, int x2);

// --- Test Case 1: Standard swap of different indices ---
void test_case_1() {
    int arr[] = {10, 20, 30};
    inswap(arr, 0, 2);
    printf("test_case_1: [%d, %d, %d]\n", arr[0], arr[1], arr[2]); 
    // Expected: [30, 20, 10]
}

// --- Test Case 2: Swapping adjacent elements ---
void test_case_2() {
    int arr[] = {1, 2, 3};
    inswap(arr, 0, 1);
    printf("test_case_2: [%d, %d, %d]\n", arr[0], arr[1], arr[2]); 
    // Expected: [2, 1, 3]
}

// --- Test Case 3: Identity swap (x1 == x2) ---
void test_case_3() {
    int arr[] = {100, 200};
    inswap(arr, 1, 1);
    printf("test_case_3: [%d, %d]\n", arr[0], arr[1]); 
    // Expected: [100, 200]
}

// --- Test Case 4: Negative values in array ---
void test_case_4() {
    int arr[] = {-5, 0, 5};
    inswap(arr, 0, 2);
    printf("test_case_4: [%d, %d, %d]\n", arr[0], arr[1], arr[2]); 
    // Expected: [5, 0, -5]
}

// --- Test Case 5: Large array (Heap allocated) ---
void test_case_5() {
    int* arr = (int*)malloc(100 * sizeof(int));
    if (arr) {
        arr[0] = 1; arr[99] = 99;
        inswap(arr, 0, 99);
        printf("test_case_5: arr[0]=%d, arr[99]=%d\n", arr[0], arr[99]); 
        // Expected: arr[0]=99, arr[99]=1
        free(arr);
    }
}

// --- Test Case 6: Boundary - last elements ---
void test_case_6() {
    int arr[] = {10, 20, 30, 40};
    inswap(arr, 2, 3);
    printf("test_case_6: [%d, %d, %d, %d]\n", arr[0], arr[1], arr[2], arr[3]); 
    // Expected: [10, 20, 40, 30]
}

// --- Test Case 7: Extreme values (INT_MIN/MAX) ---
void test_case_7() {
    int arr[] = {INT_MIN, INT_MAX};
    inswap(arr, 0, 1);
    printf("test_case_7: [%d, %d]\n", arr[0], arr[1]); 
    // Expected: [2147483647, -2147483648]
}

// --- Test Case 8: Invalid - Offset x1 out of bounds ---
void test_case_8() {
    int arr[] = {1, 2, 3};
    // Violates: \valid(x0 + 10)
    // inswap(arr, 10, 0); 
}

// --- Test Case 9: Invalid - Base pointer is NULL ---
void test_case_9() {
    // Violates: \valid(NULL + 0)
    // inswap(NULL, 0, 1); 
}

// --- Harness Entry Point ---
void test_harness_inswap() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
}