// ========== Original Code (with ACSL) ==========
#include <stdlib.h>
/*@
    requires n >= 0 && n <= 100;
    ensures \result >= 0;
    ensures \result == (n+1)*(n)/2;
    assigns \nothing;
*/
int sum(char n) {
    int s = 0;
    char k = 0;
    /*@
        loop invariant 0 <= k <= n+1;
        loop invariant s == (k-1)*(k)/2;
        loop assigns k, s;
        loop variant n - k;
    */
    while(k <= n) {    
        s = s + (int)k;
        k = k + 1;
    }
    return (int)s;
}

int main() {
    int s = sum(5);
    //@ assert s == 15;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input n=1
void test_case_1() {
    char n = 1;
    int result = sum(n);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid input n=5
void test_case_2() {
    char n = 5;
    int result = sum(n);
    printf("test_case_2: %d\n", result);  // Expected: 15
}

// Test case 3: Valid input n=10
void test_case_3() {
    char n = 10;
    int result = sum(n);
    printf("test_case_3: %d\n", result);  // Expected: 55
}

// Test case 4: Valid input n=50
void test_case_4() {
    char n = 50;
    int result = sum(n);
    printf("test_case_4: %d\n", result);  // Expected: 1275
}

// Test case 5: Valid input n=99
void test_case_5() {
    char n = 99;
    int result = sum(n);
    printf("test_case_5: %d\n", result);  // Expected: 4950
}

// Test case 6: Boundary input n=0
void test_case_6() {
    char n = 0;
    int result = sum(n);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary input n=100
void test_case_7() {
    char n = 100;
    int result = sum(n);
    printf("test_case_7: %d\n", result);  // Expected: 5050
}

// Test case 8: Invalid input n=-1
void test_case_8() {
    char n = -1;
    int result = sum(n);  // Frama-C should flag this
}

// Test case 9: Invalid input n=101
void test_case_9() {
    char n = 101;
    int result = sum(n);  // Frama-C should flag this
}

// Harness entry point
void test_harness_sum() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}