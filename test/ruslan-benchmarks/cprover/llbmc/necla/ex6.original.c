#include "necla.h"

int x,y;

int foo(int * ptr){
    if (ptr == &x)
        *ptr = 0;
    if (ptr == &y)
        *ptr = 1;

    return 1;
}


int main(){

    foo (&x);
    foo( &y);

    ASSERT(x <= y);
    return 1;
}
