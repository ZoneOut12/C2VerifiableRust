// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@ requires \valid(a) && \valid(b);
  assigns *a, *b;
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

/*@
  requires \valid(array + (0 .. len-1)) ;
  assigns array[0 .. len-1];
*/
void reverse(int* array, size_t len){
  /*@
    loop invariant 0 <= i <= len/2 ;
    loop assigns i, array[0 .. len-1] ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len/2 ; ++i){
    swap(array+i, array+len-i-1) ;
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// --- Valid Test Cases ---
void test_swap_valid() {
    int x = 1, y = 2;
    // L1: Standard
    swap(&x, &y); 
    
    // L2: Same values
    int a2 = 5, b2 = 5;
    swap(&a2, &b2);
    
    // L3: Zero
    int a3 = 0, b3 = 10;
    swap(&a3, &b3);
    
    // L4: Negatives
    int a4 = -1, b4 = -10;
    swap(&a4, &b4);
    
    // L5: Big Values
    int a5 = 100, b5 = 300;
    swap(&a5, &b5);
    
    // L6: Limits
    int a6 = 2147483647, b6 = -2147483648;
    swap(&a6, &b6);
    
    // L7: Dynamic memory
    int *a7 = malloc(sizeof(int));
    int *b7 = malloc(sizeof(int));
    *a7 = 1; *b7 = 2;
    swap(a7, b7);
    free(a7); free(b7);
}

// --- Invalid Test Cases ---
void test_swap_invalid() {
    int x = 10;
    // L8: NULL pointer
    swap(NULL, &x);
    
    // L9: Uninitialized/Invalid address
    int *p; // random garbage
    swap(&x, p);
}


// Test case 1: Valid even-length array
void test_case_1() {
    int arr[] = {1, 2, 3, 4};
    size_t len = 4;
    reverse(arr, len);
    printf("test_case_1: [");
    for(int i=0; i < 4; i++) {
        printf("%d%s", arr[i], i < 3 ? ", " : "]\n");
    }
}

// Test case 2: Valid odd-length array
void test_case_2() {
    int arr[] = {5, 6, 7};
    size_t len = 3;
    reverse(arr, len);
    printf("test_case_2: [");
    for(int i=0; i < 3; i++) {
        printf("%d%s", arr[i], i < 2 ? ", " : "]\n");
    }
}

// Test case 3: Valid array with negative numbers
void test_case_3() {
    int arr[] = {-1, -2, -3};
    size_t len = 3;
    reverse(arr, len);
    printf("test_case_3: [");
    for(int i=0; i < 3; i++) {
        printf("%d%s", arr[i], i < 2 ? ", " : "]\n");
    }
}

// Test case 4: Valid array of zeros
void test_case_4() {
    int arr[] = {0, 0, 0};
    size_t len = 3;
    reverse(arr, len);
    printf("test_case_4: [");
    for(int i=0; i < 3; i++) {
        printf("%d%s", arr[i], i < 2 ? ", " : "]\n");
    }
}

// Test case 5: Valid array with mixed values
void test_case_5() {
    int arr[] = {1, -2, 3, -4};
    size_t len = 4;
    reverse(arr, len);
    printf("test_case_5: [");
    for(int i=0; i < 4; i++) {
        printf("%d%s", arr[i], i < 3 ? ", " : "]\n");
    }
}

// Test case 6: Boundary empty array (len=0)
void test_case_6() {
    int arr[1] = {0};
    size_t len = 0;
    reverse(arr, len);
    printf("test_case_6: [len=0] (unchanged)\n");
}

// Test case 7: Boundary single-element array (len=1)
void test_case_7() {
    int arr[] = {42};
    size_t len = 1;
    reverse(arr, len);
    printf("test_case_7: [");
    printf("%d] (unchanged)\n", arr[0]);
}

// Test case 8: Invalid null array pointer
void test_case_8() {
    reverse(NULL, 2); // Frama-C should flag this
}

// Test case 9: Invalid array length (buffer overflow)
void test_case_9() {
    int arr[1] = {5};
    reverse(arr, 2); // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_reverse() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called
}