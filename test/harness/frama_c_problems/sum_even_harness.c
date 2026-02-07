#include <limits.h>
/*@
    requires n>=0;
    requires n/2*(n/2+1) <= INT_MAX;
    ensures \result == n/2*(n/2+1);
    assigns \nothing;
*/
int func(int n) {
    int sum = 0;
    int i = 0;
    /*@
        loop invariant i <= n/2 + 1;
        loop invariant (sum == i*(i-1));
        loop assigns sum, i;
        loop variant n/2 - i;
    */
    while(i <= n/2) {
        sum = sum + 2*(i);
        i++;
    }
    //@ assert i == n/2 + 1;
    return sum;
}

// --- Valid Test Cases ---

// 1. Minimum valid input
void test_case_1() {
    int n = 0;
    int result = func(n); // Expected: 0 * (0 + 1) = 0
}

// 2. Small even number
void test_case_2() {
    int n = 4;
    int result = func(n); // Expected: 2 * (2 + 1) = 6 (0 + 2 + 4)
}

// 3. Small odd number
void test_case_3() {
    int n = 5;
    int result = func(n); // Expected: 2 * (2 + 1) = 6 (0 + 2 + 4)
}

// 4. Mid-range value
void test_case_4() {
    int n = 10;
    int result = func(n); // Expected: 5 * 6 = 30
}

// 5. Larger even number
void test_case_5() {
    int n = 100;
    int result = func(n); // Expected: 50 * 51 = 2550
}

// 6. Near boundary of INT_MAX
// Note: n/2 * (n/2 + 1) must be <= INT_MAX. 
// If n = 92680, result is 46340 * 46341 = 2,147,431,940 (Close to 2^31 - 1)
void test_case_6() {
    int n = 92680;
    int result = func(n); 
}

// 7. Another valid odd number
void test_case_7() {
    int n = 11;
    int result = func(n); // Expected: 5 * 6 = 30
}

// --- Invalid Test Cases ---

// 8. Violation: n < 0
void test_case_8() {
    int n = -1;
    int result = func(n); // Violates requires n >= 0
}

// 9. Violation: Result exceeds INT_MAX
// If n = 100,000, n/2 = 50,000. 50,000 * 50,001 = 2,500,050,000 > 2,147,483,647
void test_case_9() {
    int n = 100000;
    int result = func(n); // Violates requires n/2 * (n/2 + 1) <= INT_MAX
}