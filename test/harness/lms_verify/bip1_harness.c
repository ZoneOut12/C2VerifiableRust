// ========== Original Code (with ACSL) ==========
#include <string.h>

/*@ logic integer d(integer c) = (0 <= c - '0' <= 9) ? c - '0' : -1;
   logic integer e(integer i) = (0 <= i <= 9) ? i + '0' : ' ';
*/

/*@ assigns \nothing;
  ensures -1<=\result<=9;
  ensures d(c)==\result;
*/
int d1(char c) {
  return ('0' <= c && c <= '9') ? c - '0' : -1;
}

/*@ assigns \nothing;
  ensures '0'<=\result<='9' || \result==' ';
  ensures e(i)==\result;
*/
char e1(int i) {
  return (0 <= i && i <= 9) ? i + '0' : ' ';
}

/*@ assigns \nothing;
  ensures '0'<=c<='9' ==> \result==c;
  ensures c!=\result ==> \result==' ';
  ensures e(d(c))==\result;
*/
char ed(char c) {
  return e1(d1(c));
}

/*@ assigns \nothing;
  ensures 0<=i<=9 ==> \result==i;
  ensures i!=\result ==> \result==-1;
  ensures d(e(i))==\result;
*/
int de(int i) {
  return d1(e1(i));
}

/*@ assigns \nothing;
  ensures d(e(d(c)))==d(c);
*/
int ded(char c) {
  return d1(e1(d1(c)));
}

/*@ assigns \nothing;
  ensures e(d(e(i)))==e(i);
*/
char ede(int i) {
  return e1(d1(e1(i)));
}

// ========== Test Cases ==========
#include <stdio.h>

void test_case_1() {
    char c = '0';
    int  i = 0;

    int  r_d1  = d1(c);
    char r_e1  = e1(i);
    char r_ed  = ed(c);
    int  r_de  = de(i);
    int  r_ded = ded(c);
    char r_ede = ede(i);

    printf("test_case_1:\n");
    printf("  d1('%c')  = %d\n", c, r_d1);
    printf("  e1(%d)    = '%c'\n", i, r_e1);
    printf("  ed('%c')  = '%c'\n", c, r_ed);
    printf("  de(%d)    = %d\n", i, r_de);
    printf("  ded('%c') = %d\n", c, r_ded);
    printf("  ede(%d)   = '%c'\n", i, r_ede);
}

void test_case_2() {
    char c = '5';
    int  i = 5;

    int  r_d1  = d1(c);
    char r_e1  = e1(i);
    char r_ed  = ed(c);
    int  r_de  = de(i);
    int  r_ded = ded(c);
    char r_ede = ede(i);

    printf("test_case_2:\n");
    printf("  d1('%c')  = %d\n", c, r_d1);
    printf("  e1(%d)    = '%c'\n", i, r_e1);
    printf("  ed('%c')  = '%c'\n", c, r_ed);
    printf("  de(%d)    = %d\n", i, r_de);
    printf("  ded('%c') = %d\n", c, r_ded);
    printf("  ede(%d)   = '%c'\n", i, r_ede);
}

void test_case_3() {
    char c = '9';
    int  i = 9;

    int  r_d1  = d1(c);
    char r_e1  = e1(i);
    char r_ed  = ed(c);
    int  r_de  = de(i);
    int  r_ded = ded(c);
    char r_ede = ede(i);

    printf("test_case_3:\n");
    printf("  d1('%c')  = %d\n", c, r_d1);
    printf("  e1(%d)    = '%c'\n", i, r_e1);
    printf("  ed('%c')  = '%c'\n", c, r_ed);
    printf("  de(%d)    = %d\n", i, r_de);
    printf("  ded('%c') = %d\n", c, r_ded);
    printf("  ede(%d)   = '%c'\n", i, r_ede);
}

void test_case_4() {
    char c = 'A';
    int  i = 10;

    int  r_d1  = d1(c);
    char r_e1  = e1(i);
    char r_ed  = ed(c);
    int  r_de  = de(i);
    int  r_ded = ded(c);
    char r_ede = ede(i);

    printf("test_case_4:\n");
    printf("  d1('%c')  = %d\n", c, r_d1);
    printf("  e1(%d)    = '%c'\n", i, r_e1);
    printf("  ed('%c')  = '%c'\n", c, r_ed);
    printf("  de(%d)    = %d\n", i, r_de);
    printf("  ded('%c') = %d\n", c, r_ded);
    printf("  ede(%d)   = '%c'\n", i, r_ede);
}

void test_case_5() {
    char c = ' ';
    int  i = -1;

    int  r_d1  = d1(c);
    char r_e1  = e1(i);
    char r_ed  = ed(c);
    int  r_de  = de(i);
    int  r_ded = ded(c);
    char r_ede = ede(i);

    printf("test_case_5:\n");
    printf("  d1('%c')  = %d\n", c, r_d1);
    printf("  e1(%d)    = '%c'\n", i, r_e1);
    printf("  ed('%c')  = '%c'\n", c, r_ed);
    printf("  de(%d)    = %d\n", i, r_de);
    printf("  ded('%c') = %d\n", c, r_ded);
    printf("  ede(%d)   = '%c'\n", i, r_ede);
}

void test_case_6() {
    char c = '/';
    int  i = -2;

    int  r_d1  = d1(c);
    char r_e1  = e1(i);
    char r_ed  = ed(c);
    int  r_de  = de(i);
    int  r_ded = ded(c);
    char r_ede = ede(i);

    printf("test_case_6:\n");
    printf("  d1('%c')  = %d\n", c, r_d1);
    printf("  e1(%d)    = '%c'\n", i, r_e1);
    printf("  ed('%c')  = '%c'\n", c, r_ed);
    printf("  de(%d)    = %d\n", i, r_de);
    printf("  ded('%c') = %d\n", c, r_ded);
    printf("  ede(%d)   = '%c'\n", i, r_ede);
}

void test_case_7() {
    char c = ':';
    int  i = 42;

    int  r_d1  = d1(c);
    char r_e1  = e1(i);
    char r_ed  = ed(c);
    int  r_de  = de(i);
    int  r_ded = ded(c);
    char r_ede = ede(i);

    printf("test_case_7:\n");
    printf("  d1('%c')  = %d\n", c, r_d1);
    printf("  e1(%d)    = '%c'\n", i, r_e1);
    printf("  ed('%c')  = '%c'\n", c, r_ed);
    printf("  de(%d)    = %d\n", i, r_de);
    printf("  ded('%c') = %d\n", c, r_ded);
    printf("  ede(%d)   = '%c'\n", i, r_ede);
}

// Harness entry point
void test_harness() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
}