#include <llbmc.h>

int intSqRoot(int N)
{
    __llbmc_assume(N >= 1);
    __llbmc_assume(N <= 200);
    int r = 1, q = N;
    while (r + 1 < q) {
        int p = (r + q) / 2;
        if (N < p * p) {
            q = p;
        } else {
            r = p;
        }
    }
    __llbmc_assert(r * r <= N);
    __llbmc_assert((r + 1) * (r + 1) > N);
    return r;
}
