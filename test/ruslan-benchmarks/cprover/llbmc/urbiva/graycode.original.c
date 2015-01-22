#include <llbmc.h>
#include <stdlib.h>

int main()
{
    int nDim = 12;

    int bDomain = 1;
    int bAllDiff = 1;
    int bGray = 1;

    int ni, nj;

    int *na = malloc(nDim * sizeof(int));

    for (ni = 0; ni < nDim; ni++) {
        na[ni] = __llbmc_nondef_int();
    }

    for (ni = 0; ni < nDim; ni++) {
        bDomain = bDomain && (0 <= na[ni]) && (na[ni] < nDim);
    }

    for (ni = 0; ni < nDim - 1; ni++) {
        for (nj = ni + 1; nj < nDim; nj++) {
            bAllDiff = bAllDiff && (na[ni] != na[nj]);
        }
    }

    for (ni = 0; ni < nDim - 1; ni++) {
        int nDiff = na[ni] ^ na[ni + 1];
        bGray = bGray && !(nDiff & (nDiff - 1)) && (nDiff != 0);
    }

    __llbmc_assert(!(bDomain && bAllDiff && bGray));
    free(na);

    return 0;
}
