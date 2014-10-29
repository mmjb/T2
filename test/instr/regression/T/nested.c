#include "slayer.h"

void main() {
    int x;
    int y;

    x = nondet();
    y = nondet();

    while (x>0) {
        y = nondet();
        assume(y>=1);
        while (y>0) {
            x--;
            y--;
        }
    }
}

