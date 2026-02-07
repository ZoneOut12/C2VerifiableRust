
int main() {
    int x = 1;
    int y = 0;

    /*@
    loop invariant y <= 10;
    loop invariant x >= 1 && x <= 11;
    loop invariant x <= 11;
    loop invariant 1 <= x;
    loop invariant 0 <= y;
    loop assigns y;
    loop assigns x;
    loop variant 10 - x;
    */
    while (x <= 10) {
        y = 10 - x;
        x = x +1;
    }

    //@ assert y >= 0;
}
