// ========== Original Code (with ACSL) ==========
int unknown();

int main() {
  int c = 0;

  /*@
  loop invariant c <= 40;
  loop invariant c != 40 ==> c <= 40;
  loop invariant \exists integer k; 0 <= k <= c && k != 40;
  loop invariant 0 <= c;
  loop invariant (c != 40) ==> (c < 40);
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c != 40) {
        c  = c + 1;
      }
    } else {
      if (c == 40) {
        c  = 1;
      }
    }
  }
  if(c != 40) {
    //@ assert c <= 40;
  }
}

// ========== Test Cases ==========
// None