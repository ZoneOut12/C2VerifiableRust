// ========== Original Code (with ACSL) ==========
/*@\n  requires 1 <= m <= 12 ;\n  ensures m == 2 ==> \result == 28 ;\n  ensures (m == 1 || m == 3 || m == 5 || m == 7 || m == 8 || m == 10 || m == 12) ==> \result == 31 ;\n  ensures (m == 4 || m == 6 || m == 9 || m == 11) ==> \result == 30 ;\n*/\nint day_of(int m){\n  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;\n  return days[m-1] ;\n}\n\n// ========== Test Cases ==========\n#include <stdio.h>\n\n// Test case 1: Valid - February\nvoid test_case_1() {\n    int result = day_of(2);\n    printf("test_case_1: %d\n", result);  // Expected: 28\n}\n\n// Test case 2: Valid - January\nvoid test_case_2() {\n    int result = day_of(1);\n    printf("test_case_2: %d\n", result);  // Expected: 31\n}\n\n// Test case 3: Valid - April\nvoid test_case_3() {\n    int result = day_of(4);\n    printf("test_case_3: %d\n", result);  // Expected: 30\n}\n\n// Test case 4: Valid - July\nvoid test_case_4() {\n    int result = day_of(7);\n    printf("test_case_4: %d\n", result);  // Expected: 31\n}\n\n// Test case 5: Valid - September\nvoid test_case_5() {\n    int result = day_of(9);\n    printf("test_case_5: %d\n", result);  // Expected: 30\n}\n\n// Test case 6: Invalid - Month 0\nvoid test_case_6() {\n    int result = day_of(0);\n    // Frama-C should flag this\n}\n\n// Test case 7: Invalid - Month 13\nvoid test_case_7() {\n    int result = day_of(13);\n    // Frama-C should flag this\n}\n\n// Test case 8: Boundary - Minimum month\nvoid test_case_8() {\n    int result = day_of(1);\n    printf("test_case_8: %d\n", result);  // Expected: 31\n}\n\n// Test case 9: Boundary - Maximum month\nvoid test_case_9() {\n    int result = day_of(12);\n    printf("test_case_9: %d\n", result);  // Expected: 31\n}\n\n// Harness entry point\nvoid test_harness_day_of() {\n    test_case_1();\n    test_case_2();\n    test_case_3();\n    test_case_4();\n    test_case_5();\n    test_case_8();\n    test_case_9();\n    // test_case_6 and test_case_7 intentionally not called\n}
void test_case_1() {
    CU_ASSERT(day_of(1) == 31);
}
void test_case_2() {
    CU_ASSERT(day_of(2) == 28);
}
void test_case_3() {
    CU_ASSERT(day_of(3) == 31);
}
void test_case_4() {
    CU_ASSERT(day_of(6) == 30);
}
void test_case_5() {
    CU_ASSERT(day_of(12) == 31);
}
void test_case_6() {
    CU_ASSERT(day_of(0) == -1);
}
void test_case_7() {
    CU_ASSERT(day_of(13) == -1);
}
void test_case_8() {
    CU_ASSERT(day_of(1) == 31);
}
void test_case_9() {
    CU_ASSERT(day_of(12) == 31);
}