/*@ axiomatic gcd {
       logic integer gcd(integer a, integer b);

       axiom nil:
          \forall integer n; gcd(n,0) == n;
       axiom next:
          \forall integer a,b; gcd(b, a % b) == gcd(a,b);
    }
 */
/*@
  decreases b;
  ensures \result == gcd(a, b);
*/
unsigned gcd(unsigned a, unsigned b) {

    if (b == 0)
      return a;

    return gcd(b, a % b);
}

