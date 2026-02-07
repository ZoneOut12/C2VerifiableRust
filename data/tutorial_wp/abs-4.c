#include <limits.h>
#include <stdlib.h>

/*@
  requires x > INT_MIN;
  assigns \nothing;
  ensures \result >= 0;
*/
int my_abs(int x) {
    return abs(x);
}