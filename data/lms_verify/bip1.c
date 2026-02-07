#include <string.h>

/*@
logic integer d(integer c) = (0 <= c - '0' <= 9) ? c - '0' : -1;
logic integer e(integer i) = (0 <= i <= 9) ? i + '0' : ' ';
*/

/*@
assigns \nothing;
ensures -1<=\result<=9;
ensures d(c)==\result;
*/
int d1(char c) {
  return ('0' <= c && c <= '9') ? c - '0' : -1;
}

/*@
assigns \nothing;
ensures '0'<=\result<='9' || \result==' ';
ensures e(i)==\result;
*/
char e1(int i) {
  return (0 <= i && i <= 9) ? i + '0' : ' ';
}

/*@
assigns \nothing;
ensures '0'<=c<='9' ==> \result==c;
ensures c!=\result ==> \result==' ';
ensures e(d(c))==\result;
*/
char ed(char c) {
  return e1(d1(c));
}

/*@
assigns \nothing;
ensures 0<=i<=9 ==> \result==i;
ensures i!=\result ==> \result==-1;
ensures d(e(i))==\result;
*/
int de(int i) {
  return d1(e1(i));
}

/*@
assigns \nothing;
ensures d(e(d(c)))==d(c);
*/
int ded(char c) {
  return d1(e1(d1(c)));
}

/*@
assigns \nothing;
ensures e(d(e(i)))==e(i);
*/
char ede(int i) {
  return e1(d1(e1(i)));
}
