// ========== Original Code (with ACSL) ==========
/*@ 
  logic integer min3(integer x, integer y, integer z) = 
    (x <= y && x <= z) ? x : (y <= z ? y : z);

  logic integer max3(integer x, integer y, integer z) = 
    (x >= y && x >= z) ? x : (y >= z ? y : z);

  logic integer mid3(integer x, integer y, integer z) = 
    x + y + z - min3(x, y, z) - max3(x, y, z);
*/

/*@
    requires \valid(a) && \valid(b) && \valid(c);
    requires \separated(a, b, c);
    assigns *a, *b, *c;
    ensures *a <= *b <= *c;
    ensures \old(*a == *b == *c) ==> (*a == *b == *c);
    ensures *a == min3(\old(*a), \old(*b), \old(*c));
    ensures *b == mid3(\old(*a), \old(*b), \old(*c));
    ensures *c == max3(\old(*a), \old(*b), \old(*c));
*/
void order_3(int *a, int *b, int *c) {
    if (*a > *b) {
        int temp = *a;
        *a = *b;
        *b = temp;
    }
    if (*a > *c) {    
        int temp = *a;
        *a = *c;
        *c = temp;
    }
    if (*b > *c) {
        int temp = *b;
        *b = *c;
        *c = temp;
    }
}

// ========== Test Cases ==========
#include <stdio.h>

// Valid Test Case 1: Distinct values
void test_case_1() {
    int a = 5, b = 3, c = 4;
    order_3(&a, &b, &c);
    printf("test_case_1: a=%d, b=%d, c=%d\n", a, b, c);
}

// Valid Test Case 2: All equal
void test_case_2() {
    int a = 2, b = 2, c = 2;
    order_3(&a, &b, &c);
    printf("test_case_2: a=%d, b=%d, c=%d\n", a, b, c);
}

// Valid Test Case 3: Duplicates in a and c
void test_case_3() {
    int a = 4, b = 3, c = 4;
    order_3(&a, &b, &c);
    printf("test_case_3: a=%d, b=%d, c=%d\n", a, b, c);
}

// Valid Test Case 4: Already sorted
void test_case_4() {
    int a = 1, b = 2, c = 3;
    order_3(&a, &b, &c);
    printf("test_case_4: a=%d, b=%d, c=%d\n", a, b, c);
}

// Valid Test Case 5: Single swap needed
void test_case_5() {
    int a = 3, b = 5, c = 4;
    order_3(&a, &b, &c);
    printf("test_case_5: a=%d, b=%d, c=%d\n", a, b, c);
}

// Invalid Test Case 6: NULL pointer for a
void test_case_6() {
    int b = 3, c = 4;
    order_3(NULL, &b, &c);
}

// Invalid Test Case 7: Overlapping a and b
void test_case_7() {
    int x = 5, c = 4;
    order_3(&x, &x, &c);
}

// Boundary Test Case 8: Duplicate min values
void test_case_8() {
    int a = 3, b = 3, c = 4;
    order_3(&a, &b, &c);
    printf("test_case_8: a=%d, b=%d, c=%d\n", a, b, c);
}

// Boundary Test Case 9: Duplicate max values
void test_case_9() {
    int a = 2, b = 3, c = 3;
    order_3(&a, &b, &c);
    printf("test_case_9: a=%d, b=%d, c=%d\n", a, b, c);
}

// Harness entry point
void test_harness_order_3() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid test cases intentionally not called
}