#include "necla.h"

int __llbmc_main( int n){
    int i, sum=0;
    ASSUME( n >= 0);
    ASSUME(n <= 1000);

    for (i=0; i < n; ++i)
        sum = sum +i;

    ASSERT(sum >= 0);

    return 0;
}
