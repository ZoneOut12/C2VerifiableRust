// ========== Original Code (with ACSL) ==========
/*@ requires 0 <= length;
    requires \valid_read(original+(0 .. length-1));
    requires \valid(copy+(0 .. length-1));
    requires \separated(original+(0 .. length-1), copy+(0 .. length-1));
    assigns copy[0 .. length-1];
    ensures \forall integer j ; 0 <= j < length ==> original[j] == copy[j] ;
*/
void copy(int *original, int* copy, int length){
  /*@ loop invariant 0 <= i <= length ;
      loop invariant \forall integer j ; 0 <= j < i ==> original[j] == copy[j] ;
      loop assigns i, copy[0 .. length-1];
      loop variant length - i ; */
  for(int i = 0 ; i < length ; ++i){
    copy[i] = original[i];
  }
}

/*@ requires \valid(a + (0 .. 9)) ;
  assigns  a[0 .. 9] ;
  ensures  \forall integer j ; 0 <= j < 10 ==> a[j] == \old(a[j]) ;
*/
void foo(int a[10]){
  int g[10] ;
	copy(a, g, 10);

  /*@ loop invariant 0 <= i <= 10 ;
    loop invariant \forall integer j ; 0 <= j < 10 ==> a[j] == g[j] ;
    loop assigns i, a[0 .. 9] ;
    loop variant 10 - i ;
  */
  for(int i = 0; i < 10; i++);
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// ========== Test Cases for copy() ==========

// Test case 1: Standard copy with positive integers
void test_case_1() {
    int original[] = {1, 2, 3, 4, 5};
    int destination[5] = {0};
    int length = 5;
    
    copy(original, destination, length);
    
    printf("test_case_1: ");
    for(int i = 0; i < length; i++) {
        printf("%d%s", destination[i], i < length - 1 ? ", " : "\n");
    }
}

// Test case 2: Valid copy with mixed positive and negative numbers
void test_case_2() {
    int original[] = {-10, 0, 10, INT_MAX, INT_MIN + 1};
    int destination[5] = {0};
    int length = 5;
    
    copy(original, destination, length);
    
    printf("test_case_2: ");
    for(int i = 0; i < length; i++) {
        printf("%d%s", destination[i], i < length - 1 ? ", " : "\n");
    }
}

// Test case 3: Boundary - Single element (length = 1)
void test_case_3() {
    int original[] = {42};
    int destination[1] = {0};
    int length = 1;
    
    copy(original, destination, length);
    
    printf("test_case_3: %d\n", destination[0]); // Expected: 42
}

// Test case 4: Boundary - Empty copy (length = 0)
// This is valid according to '0 <= length' and the loops will simply not execute.
void test_case_4() {
    int original[1] = {99};
    int destination[1] = {0};
    int length = 0;
    
    copy(original, destination, length);
    
    printf("test_case_4: [length 0] (Destination unchanged: %d)\n", destination[0]);
}

// Test case 5: Valid copy with large destination buffer
// Requires only that length elements are valid and separated.
void test_case_5() {
    int original[] = {1, 2};
    int destination[10] = {0}; // Buffer much larger than length
    int length = 2;
    
    copy(original, destination, length);
    
    printf("test_case_5: %d, %d\n", destination[0], destination[1]);
}

// Test case 6: Valid copy where original and destination are far apart in memory
// Specifically testing the \separated requirement.
void test_case_6() {
    int buffer[20];
    int *src = &buffer[0];
    int *dst = &buffer[10]; // Explicitly separated by 10 elements
    int length = 5;
    
    for(int i = 0; i < length; i++) src[i] = i + 100;
    
    copy(src, dst, length);
    
    printf("test_case_6: %d (src[0]), %d (dst[0])\n", src[0], dst[0]);
}

// Test case 7: Valid copy of an array filled with zeros
void test_case_7() {
    int original[3] = {0, 0, 0};
    int destination[3] = {1, 1, 1}; // Pre-filled with 1s
    int length = 3;
    
    copy(original, destination, length);
    
    printf("test_case_7: %d, %d, %d\n", destination[0], destination[1], destination[2]);
}

// Harness entry point
void test_harness_copy() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
}

// ========== Invalid Test Cases for copy() ==========

// Test case 8: Invalid - Buffer Overflow (Violates \valid)
// The length parameter (5) exceeds the allocated size of the destination buffer (3).
void test_case_8() {
    int original[] = {1, 2, 3, 4, 5};
    int destination[3]; // Too small for length 5
    int length = 5;

    // Frama-C should flag this: \valid(copy + (0 .. length-1)) is false
    copy(original, destination, length); 
}

// Test case 9: Invalid - Memory Overlap (Violates \separated)
// The source and destination buffers overlap in memory.
// According to ACSL: \separated(original+(0..length-1), copy+(0..length-1))
void test_case_9() {
    int buffer[] = {1, 2, 3, 4, 5, 6};
    int *src = &buffer[0];
    int *dst = &buffer[2]; // Overlaps with src because length is 4
    int length = 4;

    /* Memory Layout:
       src points to: [1, 2, 3, 4]
       dst points to:       [3, 4, 5, 6]
       The regions {1,2,3,4} and {3,4,5,6} overlap at indices {3,4}.
    */
    
    // Frama-C should flag this: \separated precondition violated
    copy(src, dst, length);
}

// Test case 1: Valid - sequential numbers
void test_case_1() {
    int a[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    foo(a);
    printf("test_case_1: [");
    for (int i = 0; i < 10; i++) {
        printf("%d ", a[i]);
    }
    printf("]\n");
}

// Test case 2: Valid - all elements same
void test_case_2() {
    int a[10] = {5, 5, 5, 5, 5, 5, 5, 5, 5, 5};
    foo(a);
    printf("test_case_2: [");
    for (int i = 0; i < 10; i++) {
        printf("%d ", a[i]);
    }
    printf("]\n");
}

// Test case 3: Valid - mixed positive/negative
void test_case_3() {
    int a[10] = {-1, 2, -3, 4, -5, 6, -7, 8, -9, 10};
    foo(a);
    printf("test_case_3: [");
    for (int i = 0; i < 10; i++) {
        printf("%d ", a[i]);
    }
    printf("]\n");
}

// Test case 4: Valid - descending order
void test_case_4() {
    int a[10] = {10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
    foo(a);
    printf("test_case_4: [");
    for (int i = 0; i < 10; i++) {
        printf("%d ", a[i]);
    }
    printf("]\n");
}

// Test case 5: Valid - first element non-zero
void test_case_5() {
    int a[10] = {42, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    foo(a);
    printf("test_case_5: [");
    for (int i = 0; i < 10; i++) {
        printf("%d ", a[i]);
    }
    printf("]\n");
}

// Test case 6: Boundary - all zeros
void test_case_6() {
    int a[10] = {0};
    foo(a);
    printf("test_case_6: [");
    for (int i = 0; i < 10; i++) {
        printf("%d ", a[i]);
    }
    printf("]\n");
}

// Test case 7: Boundary - array size exactly 10
void test_case_7() {
    int a[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    foo(a);
    printf("test_case_7: [");
    for (int i = 0; i < 10; i++) {
        printf("%d ", a[i]);
    }
    printf("]\n");
}

// Test case 8: Invalid - NULL array
void test_case_8() {
    int *a = NULL;
    foo(a);
}

// Test case 9: Invalid - array size 9
void test_case_9() {
    int a[9] = {1, 2, 3, 4, 5, 6, 7, 8, 9};
    foo((int*)a);
}

// Harness entry point
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called for precondition testing
}