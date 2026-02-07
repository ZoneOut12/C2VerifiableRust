// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
requires (x0>0);
assigns \nothing;
ensures ((0<=\result) &&
(\result<x0));
*/
int picker_first(int  x0) {
  return 0;
}
/*@
requires ((x7>0) &&
\valid(x6+(0..x7-1)));
assigns \nothing;
*/
int pick_first_element(int  * x6, int  x7) {
  int x9 = picker_first(x7);
  int x10 = x6[x9];
  return x10;
}
/*@
requires ((x16>0) &&
\valid(x15+(0..x16-1)));
assigns \nothing;
*/
int pick_first_directly(int  * x15, int  x16) {
  int x18 = x15[0];
  return x18;
}
/*@
requires (x23>0);
assigns \nothing;
ensures ((0<=\result) &&
(\result<x23));
*/
int picker_last(int  x23) {
  int x25 = x23 - 1;
  return x25;
}
/*@
requires ((x31>0) &&
\valid(x30+(0..x31-1)));
assigns \nothing;
*/
int pick_last_element(int  * x30, int  x31) {
  int x33 = picker_last(x31);
  int x34 = x30[x33];
  return x34;
}
/*@
requires ((x40>0) &&
\valid(x39+(0..x40-1)));
assigns \nothing;
*/
int pick_last_directly(int  * x39, int  x40) {
  int x42 = x40 - 1;
  int x43 = x39[x42];
  return x43;
}

// ========== Test Cases ==========
#include <stdio.h>

void test_case_1() {
    int arr[] = {10};

    int r1 = picker_first(1);
    //@ assert r1 == 0;

    int r2 = pick_first_element(arr, 1);
    //@ assert r2 == 10;

    int r3 = pick_first_directly(arr, 1);
    //@ assert r3 == 10;

    int r4 = picker_last(1);
    //@ assert r4 == 0;

    int r5 = pick_last_element(arr, 1);
    //@ assert r5 == 10;

    int r6 = pick_last_directly(arr, 1);
    //@ assert r6 == 10;
}

void test_case_2() {
    int arr[] = {1, 2, 3};

    int r1 = picker_first(3);
    //@ assert r1 == 0;

    int r2 = pick_first_element(arr, 3);
    //@ assert r2 == 1;

    int r3 = pick_first_directly(arr, 3);
    //@ assert r3 == 1;

    int r4 = picker_last(3);
    //@ assert r4 == 2;

    int r5 = pick_last_element(arr, 3);
    //@ assert r5 == 3;

    int r6 = pick_last_directly(arr, 3);
    //@ assert r6 == 3;
}

void test_case_3() {
    int arr[] = {-1, -2, -3};

    int r1 = picker_first(3);
    //@ assert r1 == 0;

    int r2 = pick_first_element(arr, 3);
    //@ assert r2 == -1;

    int r3 = pick_first_directly(arr, 3);
    //@ assert r3 == -1;

    int r4 = picker_last(3);
    //@ assert r4 == 2;

    int r5 = pick_last_element(arr, 3);
    //@ assert r5 == -3;

    int r6 = pick_last_directly(arr, 3);
    //@ assert r6 == -3;
}

void test_case_4() {
    int arr[] = {10, 20, 30, 40, 50};

    int r1 = picker_first(5);
    //@ assert r1 == 0;

    int r2 = pick_first_element(arr, 5);
    //@ assert r2 == 10;

    int r3 = pick_first_directly(arr, 5);
    //@ assert r3 == 10;

    int r4 = picker_last(5);
    //@ assert r4 == 4;

    int r5 = pick_last_element(arr, 5);
    //@ assert r5 == 50;

    int r6 = pick_last_directly(arr, 5);
    //@ assert r6 == 50;
}

void test_case_5() {
    int arr[] = {7, 7, 7, 7};

    int r1 = picker_first(4);
    //@ assert r1 == 0;

    int r2 = pick_first_element(arr, 4);
    //@ assert r2 == 7;

    int r3 = pick_first_directly(arr, 4);
    //@ assert r3 == 7;

    int r4 = picker_last(4);
    //@ assert r4 == 3;

    int r5 = pick_last_element(arr, 4);
    //@ assert r5 == 7;

    int r6 = pick_last_directly(arr, 4);
    //@ assert r6 == 7;
}

void test_case_6() {
    int arr[] = {0, -1, 2, -3};

    int r1 = picker_first(4);
    //@ assert r1 == 0;

    int r2 = pick_first_element(arr, 4);
    //@ assert r2 == 0;

    int r3 = pick_first_directly(arr, 4);
    //@ assert r3 == 0;

    int r4 = picker_last(4);
    //@ assert r4 == 3;

    int r5 = pick_last_element(arr, 4);
    //@ assert r5 == -3;

    int r6 = pick_last_directly(arr, 4);
    //@ assert r6 == -3;
}

void test_case_7() {
    int arr[] = {100, 200};

    int r1 = picker_first(2);
    //@ assert r1 == 0;

    int r2 = pick_first_element(arr, 2);
    //@ assert r2 == 100;

    int r3 = pick_first_directly(arr, 2);
    //@ assert r3 == 100;

    int r4 = picker_last(2);
    //@ assert r4 == 1;

    int r5 = pick_last_element(arr, 2);
    //@ assert r5 == 200;

    int r6 = pick_last_directly(arr, 2);
    //@ assert r6 == 200;
}

void invalid_test_case_8() {
    int arr[] = {1, 2};

    picker_first(0);
    pick_first_element(arr, 0);
    pick_first_directly(arr, 0);
    picker_last(0);
    pick_last_element(arr, 0);
    pick_last_directly(arr, 0);
}

void invalid_test_case_9() {
    int* p = NULL;

    picker_first(-1);
    pick_first_element(p, 1);
    pick_first_directly(p, 1);
    picker_last(-1);
    pick_last_element(p, 1);
    pick_last_directly(p, 1);
}