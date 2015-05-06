void main() {
    int a ;

    while (a >= 1) {

        int x = nondet();
        if (a == 2*x) {
            a = x;
        } else {
            a = 3*a+1;
        }
   }
}
