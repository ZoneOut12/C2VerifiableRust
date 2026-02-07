/*@
    requires \valid(a) && \valid_read(b);
    requires \separated(a, b);
    assigns *a;
    ensures \old(*b) ==> *a == 0;
    ensures ! \old(*b) ==> *a == \old(*a);
    ensures *b == \old(*b);
*/
void reset_1st_if_2nd_is_true(int* a, int const* b){
    if(*b) *a = 0 ;
}

int main(){
    int a = 5 ;
    int x = 0 ;
    reset_1st_if_2nd_is_true(&a, &x);
    //@ assert a == 5 ;
    //@ assert x == 0 ;

    int const b = 1 ;
    reset_1st_if_2nd_is_true(&a, &b);
    //@ assert a == 0 ;
    //@ assert b == 1 ;
}

// ========== Test Cases ==========
// Case 1: Standard True - a is reset
void test_case_1() {
    int a = 5, b = 1;
    int old_a = a, old_b = b;
    CheckPre_reset(&a, &b);
    reset_1st_if_2nd_is_true(&a, &b);
    CheckPost_reset(old_a, old_b, a, b);
    printf("test_case_1 passed: a reset to %d\n", a);
}

// Case 2: Standard False - a remains unchanged
void test_case_2() {
    int a = 5, b = 0;
    int old_a = a, old_b = b;
    CheckPre_reset(&a, &b);
    reset_1st_if_2nd_is_true(&a, &b);
    CheckPost_reset(old_a, old_b, a, b);
    printf("test_case_2 passed: a remains %d\n", a);
}

// Case 3: Negative True - In C, -1 is true
void test_case_3() {
    int a = 10, b = -1;
    int old_a = a, old_b = b;
    CheckPre_reset(&a, &b);
    reset_1st_if_2nd_is_true(&a, &b);
    CheckPost_reset(old_a, old_b, a, b);
    printf("test_case_3 passed: a reset by negative b\n");
}

// Case 4: Large True - b is INT_MAX
void test_case_4() {
    int a = 100, b = INT_MAX;
    int old_a = a, old_b = b;
    CheckPre_reset(&a, &b);
    reset_1st_if_2nd_is_true(&a, &b);
    CheckPost_reset(old_a, old_b, a, b);
    printf("test_case_4 passed: a reset by INT_MAX\n");
}

// Case 5: Already Zero - b is true
void test_case_5() {
    int a = 0, b = 42;
    int old_a = a, old_b = b;
    CheckPre_reset(&a, &b);
    reset_1st_if_2nd_is_true(&a, &b);
    CheckPost_reset(old_a, old_b, a, b);
    printf("test_case_5 passed: a was already 0\n");
}

// Case 6: Multiple calls - persistence
void test_case_6() {
    int a = 9, b = 1;
    reset_1st_if_2nd_is_true(&a, &b);
    assert(a == 0);
    int b2 = 0;
    reset_1st_if_2nd_is_true(&a, &b2);
    assert(a == 0);
    printf("test_case_6 passed: multiple calls stable\n");
}

// Case 7: Boundary - b is INT_MIN (True)
void test_case_7() {
    int a = 123, b = INT_MIN;
    int old_a = a, old_b = b;
    CheckPre_reset(&a, &b);
    reset_1st_if_2nd_is_true(&a, &b);
    CheckPost_reset(old_a, old_b, a, b);
    printf("test_case_7 passed: a reset by INT_MIN\n");
}

// ========== (Invalid Cases) ==========

// Case 8: NULL pointer (Violation: \valid)
void test_case_8_invalid() {
    printf("Running test_case_8 (Expect assert fail)...\n");
    int b = 1;
    CheckPre_reset(NULL, &b);
}

// Case 9: Non-separated pointers (Violation: \separated)
void test_case_9_invalid() {
    printf("Running test_case_9 (Expect assert fail)...\n");
    int x = 10;
    CheckPre_reset(&x, &x);
}