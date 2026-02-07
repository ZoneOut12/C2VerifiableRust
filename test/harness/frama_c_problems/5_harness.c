/*@
    requires x >= y && x > 0 && y > 0;
    requires \valid(r);
    ensures *r < y;
    ensures x == \result*y + *r;
    
*/
int fun(int x, int y , int *r) {
    *r = x;
    int d = 0;
    /*@
        loop invariant  *r == x - y*d;
        loop assigns *r, d;
        loop variant *r;
    */
    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }
    return d;
}

// ========== Test Cases ==========
void test_case_1() {
    int r;
    int result = fun(6, 4, &r);
}

void test_case_2() {
    int r;
    int result = fun(10, 5, &r);
}

void test_case_3() {
    int r;
    int result = fun(3, 3, &r);
}

void test_case_4() {
    int r;
    int result = fun(2, 1, &r);
}

void test_case_5() {
    int r;
    int result = fun(1, 1, &r);
}

void test_case_6() {
    int r;
    int result = fun(3, 5, &r);
}

void test_case_7() {
    int result = fun(5, 3, NULL);
}

void test_case_8() {
    int r;
    int result = fun(1, 1, &r);
}

void test_case_9() {
    int r;
    int result = fun(2, 1, &r);
}