#include "slayer.h"

void f(void) {}

void main() {
    int x,y,z;
    while (x<0) {x++;}
    while(1) { x--; f(); TerminationIgnore(); }

}
