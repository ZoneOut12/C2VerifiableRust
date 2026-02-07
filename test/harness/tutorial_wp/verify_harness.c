// ========== Original Code (with ACSL) ==========
/*@\n  requires \valid(a) && \valid(b);\n  assigns *a, *b;\n  ensures *a == \old(*b);\n  ensures *b == \old(*a);\n*/\nvoid swap(int* a, int* b){\n  int tmp = *a;\n  *a = *b;\n  *b = tmp;\n}\n\n// ========== Test Cases ==========\n#include <stdio.h>\n\n// Test case 1: Valid - normal case\nvoid test_case_1() {\n    int a = 42;\n    int b = 37;\n    swap(&a, &b);\n    printf("test_case_1: a=%d, b=%d\n", a, b); // Expected: a=37, b=42\n}\n\n// Test case 2: Valid - two positive integers\nvoid test_case_2() {\n    int a = 10;\n    int b = 20;\n    swap(&a, &b);\n    printf("test_case_2: a=%d, b=%d\n", a, b); // Expected: a=20, b=10\n}\n\n// Test case 3: Valid - positive and negative\nvoid test_case_3() {\n    int a = 5;\n    int b = -3;\n    swap(&a, &b);\n    printf("test_case_3: a=%d, b=%d\n", a, b); // Expected: a=-3, b=5\n}\n\n// Test case 4: Valid - two negatives\nvoid test_case_4() {\n    int a = -4;\n    int b = -7;\n    swap(&a, &b);\n    printf("test_case_4: a=%d, b=%d\n", a, b); // Expected: a=-7, b=-4\n}\n\n// Test case 5: Valid - same values\nvoid test_case_5() {\n    int a = 15;\n    int b = 15;\n    swap(&a, &b);\n    printf("test_case_5: a=%d, b=%d\n", a, b); // Expected: a=15, b=15\n}\n\n// Test case 6: Boundary - same variable\nvoid test_case_6() {\n    int x = 5;\n    swap(&x, &x);\n    printf("test_case_6: x=%d\n", x); // Expected: 5\n}\n\n// Test case 7: Boundary - zero values\nvoid test_case_7() {\n    int a = 0;\n    int b = 0;\n    swap(&a, &b);\n    printf("test_case_7: a=%d, b=%d\n", a, b); // Expected: a=0, b=0\n}\n\n// Test case 8: Invalid - NULL pointer for a\nvoid test_case_8() {\n    int b = 10;\n    swap(NULL, &b); // Frama-C should flag this\n}\n\n// Test case 9: Invalid - NULL pointer for b\nvoid test_case_9() {\n    int a = 10;\n    swap(&a, NULL); // Frama-C should flag this\n}\n\n// Harness entry point\nvoid test_harness_swap() {\n    test_case_1();\n    test_case_2();\n    test_case_3();\n    test_case_4();\n    test_case_5();\n    test_case_6();\n    test_case_7();\n    // test_case_8() and test_case_9() intentionally not called\n}
void test_case_1() {
    int a = 5, b = 10;
    swap(&a, &b);
    assert(a == 10 && b == 5);
}

void test_case_2() {
    int a = 0, b = 0;
    swap(&a, &b);
    assert(a == 0 && b == 0);
}

void test_case_3() {
    int a = -3, b = -7;
    swap(&a, &b);
    assert(a == -7 && b == -3);
}

void test_case_4() {
    int a = 100, b = 1;
    swap(&a, &b);
    assert(a == 1 && b == 100);
}

void test_case_5() {
    int a = 0, b = 42;
    swap(&a, &b);
    assert(a == 42 && b == 0);
}

void test_case_6() {
    int x = 5;
    swap(&x, &x);
    assert(x == 5);
}

void test_case_7() {
    int a = INT_MAX, b = INT_MIN;
    swap(&a, &b);
    assert(a == INT_MIN && b == INT_MAX);
}

void test_case_8() {
    int b = 5;
    swap(NULL, &b);
}

void test_case_9() {
    swap(NULL, NULL);
}