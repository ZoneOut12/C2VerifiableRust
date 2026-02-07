// ========== Original Code (with ACSL) ==========
/*@\n  requires \valid(a + (0 .. 9)) ;\n  assigns  a[0 .. 9] ;\n  ensures  \forall integer j ; 0 <= j < 10 ==> a[j] == \old(a[j]) ;\n*/\nvoid foo(int a[10]){\n  int g[10] ;\n  /*@\n    loop invariant 0 <= i <= 10 ;\n    loop invariant \forall integer j ; 0 <= j < i ==> a[j] == g[j] ;\n    loop assigns i, g[0 .. 9];\n    loop variant 10 - i ;\n  */\n  for(int i = 0 ; i < 10 ; ++i){\n    g[i] = a[i];\n  }\n  /*@\n    loop invariant 0 <= i <= 10 ;\n    loop invariant \forall integer j ; 0 <= j < 10 ==> a[j] == g[j] ;\n    loop assigns i, a[0 .. 9] ;\n    loop variant 10 - i ;\n  */\n  for(int i = 0; i < 10; i++);\n}\n\n// ========== Test Cases ==========\n#include <stdio.h>\n\n// Test case 1: Valid - array with elements 0-9\nvoid test_case_1() {\n    int a[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};\n    printf("test_case_1 before: a[0]=%d, a[9]=%d\n", a[0], a[9]);\n    foo(a);\n    printf("test_case_1 after: a[0]=%d, a[9]=%d\n", a[0], a[9]);  // Expected same values\n}\n\n// Test case 2: Valid - all zeros\nvoid test_case_2() {\n    int a[10] = {0};\n    printf("test_case_2 before: a[0]=%d\n", a[0]);\n    foo(a);\n    printf("test_case_2 after: a[0]=%d\n", a[0]);  // Expected 0\n}\n\n// Test case 3: Valid - all ones\nvoid test_case_3() {\n    int a[10] = {1};\n    printf("test_case_3 before: a[0]=%d\n", a[0]);\n    foo(a);\n    printf("test_case_3 after: a[0]=%d\n", a[0]);  // Expected 1\n}\n\n// Test case 4: Valid - mix of values\nvoid test_case_4() {\n    int a[10] = {-5, -3, 0, 2, 4, 7, 8, 9, 10, 15};\n    printf("test_case_4 before: a[0]=%d, a[9]=%d\n", a[0], a[9]);\n    foo(a);\n    printf("test_case_4 after: a[0]=%d, a[9]=%d\n", a[0], a[9]);  // Expected same values\n}\n\n// Test case 5: Valid - all same value\nvoid test_case_5() {\n    int a[10] = {42};\n    printf("test_case_5 before: a[0]=%d\n", a[0]);\n    foo(a);\n    printf("test_case_5 after: a[0]=%d\n", a[0]);  // Expected 42\n}\n\n// Test case 6: Invalid - NULL pointer\nvoid test_case_6() {\n    foo(0);  // Frama-C should flag this\n}\n\n// Test case 7: Invalid - array with 9 elements\nvoid test_case_7() {\n    int a[9] = {0};\n    foo(a);  // Frama-C should flag this\n}\n\n// Test case 8: Boundary - exactly 10 zeros\nvoid test_case_8() {\n    int a[10] = {0};\n    printf("test_case_8 before: a[0]=%d\n", a[0]);\n    foo(a);\n    printf("test_case_8 after: a[0]=%d\n", a[0]);  // Expected 0\n}\n\n// Test case 9: Boundary - exactly 10 elements\nvoid test_case_9() {\n    int a[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};\n    printf("test_case_9 before: a[0]=%d, a[9]=%d\n", a[0], a[9]);\n    foo(a);\n    printf("test_case_9 after: a[0]=%d, a[9]=%d\n", a[0], a[9]);  // Expected same values\n}\n\n// Harness entry point\nvoid test_harness_foo() {\n    test_case_1();\n    test_case_2();\n    test_case_3();\n    test_case_4();\n    test_case_5();\n    test_case_8();\n    test_case_9();\n    // Invalid test cases intentionally not called for execution\n}
void test_case_1() {
  int a[10] = {0,1,2,3,4,5,6,7,8,9};
  foo(a);
}

void test_case_2() {
  int a[10] = {5,5,5,5,5,5,5,5,5,5};
  foo(a);
}

void test_case_3() {
  int a[10] = {10,9,8,7,6,5,4,3,2,1};
  foo(a);
}

void test_case_4() {
  int a[10] = {-5,-4,-3,-2,-1,0,1,2,3,4};
  foo(a);
}

void test_case_5() {
  int a[10] = {0};
  foo(a);
}

void test_case_6() {
  int *a = NULL;
  foo(a);
}

void test_case_7() {
  int a[9] = {1,2,3,4,5,6,7,8,9};
  foo(a);
}

void test_case_8() {
  int a[10] = {0,1,0,1,0,1,0,1,0,1};
  foo(a);
}

void test_case_9() {
  int *a;
  foo(a); // Uninitialized pointer
}