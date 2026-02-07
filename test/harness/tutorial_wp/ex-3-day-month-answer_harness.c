/*@ requires 1 <= m <= 12 ;\n  assigns \nothing ;\n\n  behavior february:\n    assumes m \in { 2 } ;\n    ensures \result == 28 ;\n\n  behavior thirty:\n    assumes m \in { 4, 6, 9, 11 } ;\n    ensures \result == 30 ;\n\n  behavior thirty_one:\n    assumes m \in { 1, 3, 5, 7, 8, 10, 12 } ;\n    ensures \result == 31 ;\n\n  complete behaviors;\n  disjoint behaviors;\n*/\nint day_of(int m){\n  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;\n  return days[m-1] ;\n}\n\n#include <stdio.h>\n\n// Test case 1: Valid - February\nvoid test_case_1() {\n    int result = day_of(2);\n    printf("test_case_1: %d\n", result);  // Expected: 28\n}\n\n// Test case 2: Valid - April (30 days)\nvoid test_case_2() {\n    int result = day_of(4);\n    printf("test_case_2: %d\n", result);  // Expected: 30\n}\n\n// Test case 3: Valid - June (30 days)\nvoid test_case_3() {\n    int result = day_of(6);\n    printf("test_case_3: %d\n", result);  // Expected: 30\n}\n\n// Test case 4: Valid - March (31 days)\nvoid test_case_4() {\n    int result = day_of(3);\n    printf("test_case_4: %d\n", result);  // Expected: 31\n}\n\n// Test case 5: Valid - October (31 days)\nvoid test_case_5() {\n    int result = day_of(10);\n    printf("test_case_5: %d\n", result);  // Expected: 31\n}\n\n// Test case 6: Boundary - January\nvoid test_case_6() {\n    int result = day_of(1);\n    printf("test_case_6: %d\n", result);  // Expected: 31\n}\n\n// Test case 7: Boundary - December\nvoid test_case_7() {\n    int result = day_of(12);\n    printf("test_case_7: %d\n", result);  // Expected: 31\n}\n\n// Test case 8: Invalid - m=0\nvoid test_case_8() {\n    int result = day_of(0);  // Frama-C should flag this\n}\n\n// Test case 9: Invalid - m=13\nvoid test_case_9() {\n    int result = day_of(13);  // Frama-C should flag this\n}\n\nvoid test_harness_day_of() {\n    test_case_1();\n    test_case_2();\n    test_case_3();\n    test_case_4();\n    test_case_5();\n    test_case_6();\n    test_case_7();\n    // test_case_8 and test_case_9 intentionally not called\n}
void test_case_1() {
    assert(day_of(1) == 31);
}
void test_case_2() {
    assert(day_of(2) == 28);
}
void test_case_3() {
    assert(day_of(3) == 31);
}
void test_case_4() {
    assert(day_of(4) == 30);
}
void test_case_5() {
    assert(day_of(5) == 31);
}
void test_case_6() {
    assert(day_of(1) == 31);
}
void test_case_7() {
    assert(day_of(12) == 31);
}
void test_case_8() {
    assert(day_of(0) == 0);
}
void test_case_9() {
    assert(day_of(13) == 0);
}