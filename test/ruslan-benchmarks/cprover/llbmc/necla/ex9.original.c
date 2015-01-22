#include "necla.h"
#include <stdlib.h>

int *a;
int n;

int test() {
    int i;

    for (i = 0; i < n; ++i){

        if (a[i])
            n--;
      
        a[i] = 0;
    }

    return 0;
}


int main() {

    n = __NONDET__();
   
    if (n <= 0 || n >= 6) {
        n=5;
        a = (int *) malloc(n * sizeof(int));
    } else {
        a = (int *) malloc( n * sizeof(int));
    }

    ASSUME(a != NULL);

    test();

    return 1;
}
