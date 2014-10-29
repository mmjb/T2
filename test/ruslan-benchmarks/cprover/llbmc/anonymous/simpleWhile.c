#include "llbmc.h"

/* void simpleWhile(int N) */
void main(int N)
{
    __llbmc_assume(N >= 0);
    __llbmc_assume(N <= 1000);
    int x = 0, i = 0;
    while (i < N) {
        if (i % 2 == 0) {
            x += 2;
        }
        i++;
    }
    __llbmc_assert(x == N || x == N + 1);
}
