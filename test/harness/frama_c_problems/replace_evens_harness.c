/*@
    requires n > 0;
    requires \valid(a + (0..n-1));
    ensures  \forall integer k; (0<=k<n) && (k%2==0) ==> (a[k] == 0);
*/
void func(int *a, int n) {
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer k;  (0 <= k < i) && (k%2==0) ==> a[k] == 0;
        loop invariant \forall integer k;  (0 <= k < i) && (k%2==1) ==> a[k] == a[k];
        loop assigns i, a[0..(n-1)];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (i%2==0) 
            a[i] = 0;
    }
}

void test_case_1() {
    int a[] = {1, 2, 3};
    int n = 3;
    func(a, n);
}

void test_case_2() {
    int a[] = {5};
    int n = 1;
    func(a, n);
}

void test_case_3() {
    int a[] = {0, -1};
    int n = 2;
    func(a, n);
}

void test_case_4() {
    int a[] = {4, 3, 2, 1};
    int n = 4;
    func(a, n);
}

void test_case_5() {
    int a[] = {1, 1, 1, 1, 1};
    int n = 5;
    func(a, n);
}

void test_case_6() {
    int *a = NULL;
    int n = 2;
    func(a, n);
}

void test_case_7() {
    int a[] = {7};
    int n = 2;
    func(a, n);
}

void test_case_8() {
    int a[] = {10};
    int n = 1;
    func(a, n);
}

void test_case_9() {
    int a[] = {2, 3};
    int n = 2;
    func(a, n);
}