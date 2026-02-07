/*@ requires -10 <= x <= 0 ;
    requires 0 <= y <= 5 ;
    ensures -10 <= \result <= 10 ;
*/
int function(int x, int y) {
    int res ;
    y += 10 ;
    x -= 5 ;
    res = x + y ;
    //@ assert -5 <= res <= 10;
    return res ;
}

#include <stdio.h>

// Test case 1: Valid - mid-range inputs
void test_case_1() {
    int result = function(-5, 2);
    printf("test_case_1: %d\n", result); // Expected: 2
}

// Test case 2: Valid - x at minimum with mid y
void test_case_2() {
    int result = function(-10, 3);
    printf("test_case_2: %d\n", result); // Expected: -2
}

// Test case 3: Valid - x mid with y minimum
void test_case_3() {
    int result = function(-2, 0);
    printf("test_case_3: %d\n", result); // Expected: 3
}

// Test case 4: Valid - x mid with y maximum
void test_case_4() {
    int result = function(-7, 5);
    printf("test_case_4: %d\n", result); // Expected: 3
}

// Test case 5: Valid - x maximum with mid y
void test_case_5() {
    int result = function(0, 2);
    printf("test_case_5: %d\n", result); // Expected: 7
}

// Test case 6: Boundary - x min and y max
void test_case_6() {
    int result = function(-10, 5);
    printf("test_case_6: %d\n", result); // Expected: 0
}

// Test case 7: Boundary - x max and y min
void test_case_7() {
    int result = function(0, 0);
    printf("test_case_7: %d\n", result); // Expected: 5
}

// Test case 8: Invalid - x below minimum
void test_case_8() {
    int result = function(-11, 2); // Frama-C should flag this
}

// Test case 9: Invalid - y above maximum
void test_case_9() {
    int result = function(-5, 6); // Frama-C should flag this
}

// Harness entry point
void test_harness_function() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
void test_case_8() {
    int result = function(1, 3);
    assert(result == -1);
}
void test_case_9() {
    int result = function(-5, 6);
    assert(result == -1);
}