/*@\n  requires \valid(a) && \valid_read(b) ;\n  requires \separated(a, b) ;\n\n  assigns *a ;\n\n  ensures \old(*b) ==> *a == 0 ;\n  ensures ! \old(*b) ==> *a == \old(*a) ;\n  ensures *b == \old(*b);\n*/\nvoid reset_1st_if_2nd_is_true(int* a, int const* b){\n  if(*b) *a = 0 ;\n}\n\n// ========== Test Cases ==========\n#include <stdio.h>\n\n// Test case 1: Valid - a=5, b=0\nvoid test_case_1() {\n    int a = 5;\n    int b = 0;\n    reset_1st_if_2nd_is_true(&a, &b);\n    printf("test_case_1: a = %d, b = %d\n", a, b); // Expected: a=5, b=0\n}\n\n// Test case 2: Valid - a=3, b=1\nvoid test_case_2() {\n    int a = 3;\n    int b = 1;\n    reset_1st_if_2nd_is_true(&a, &b);\n    printf("test_case_2: a = %d, b = %d\n", a, b); // Expected: a=0, b=1\n}\n\n// Test case 3: Valid - a=0, b=0\nvoid test_case_3() {\n    int a = 0;\n    int b = 0;\n    reset_1st_if_2nd_is_true(&a, &b);\n    printf("test_case_3: a = %d, b = %d\n", a, b); // Expected: a=0, b=0\n}\n\n// Test case 4: Valid - a=-5, b=1\nvoid test_case_4() {\n    int a = -5;\n    int b = 1;\n    reset_1st_if_2nd_is_true(&a, &b);\n    printf("test_case_4: a = %d, b = %d\n", a, b); // Expected: a=0, b=1\n}\n\n// Test case 5: Valid - a=10, b=2\nvoid test_case_5() {\n    int a = 10;\n    int b = 2;\n    reset_1st_if_2nd_is_true(&a, &b);\n    printf("test_case_5: a = %d, b = %d\n", a, b); // Expected: a=0, b=2\n}\n\n// Test case 6: Invalid - a is NULL\nvoid test_case_6() {\n    int b = 1;\n    reset_1st_if_2nd_is_true(NULL, &b); // Frama-C should flag invalid pointer\n}\n\n// Test case 7: Invalid - a and b point to same address\nvoid test_case_7() {\n    int a = 1;\n    reset_1st_if_2nd_is_true(&a, &a); // Frama-C should flag non-separated pointers\n}\n\n// Test case 8: Boundary - a=0, b=1\nvoid test_case_8() {\n    int a = 0;\n    int b = 1;\n    reset_1st_if_2nd_is_true(&a, &b);\n    printf("test_case_8: a = %d, b = %d\n", a, b); // Expected: a=0, b=1\n}\n\n// Test case 9: Boundary - a=7, b=0\nvoid test_case_9() {\n    int a = 7;\n    int b = 0;\n    reset_1st_if_2nd_is_true(&a, &b);\n    printf("test_case_9: a = %d, b = %d\n", a, b); // Expected: a=7, b=0\n}\n\n// Harness entry point\nvoid test_harness_reset_1st_if_2nd_is_true() {\n    test_case_1();\n    test_case_2();\n    test_case_3();\n    test_case_4();\n    test_case_5();\n    test_case_8();\n    test_case_9();\n    // Invalid test cases intentionally not called for execution\n}
void test_case_1() {
    int a = 5;
    int b = 1;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 0);
}

void test_case_2() {
    int a = 3;
    int b = 0;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 3);
}

void test_case_3() {
    int a = -2;
    int b = 1;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 0);
}

void test_case_4() {
    int a = 0;
    int b = 1;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 0);
}

void test_case_5() {
    int a = 42;
    int b = 42;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 0);
}

void test_case_6() {
    int b = 5;
    reset_1st_if_2nd_is_true(NULL, &b);
}

void test_case_7() {
    int x = 10;
    reset_1st_if_2nd_is_true(&x, &x);
}

void test_case_8() {
    int a = 1;
    int b = 2;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 0);
}

void test_case_9() {
    int a = -1;
    int b = -1;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 0);
}