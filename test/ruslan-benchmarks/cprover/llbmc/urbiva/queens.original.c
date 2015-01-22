#include <llbmc.h>
#include <stdlib.h>

int main()
{
    int nDim = 9;

    int bDomain = 1;
    int bNoCapture = 1;

    int ni, nj;

    int *n = malloc(nDim * sizeof(int));
    for (ni=0; ni<nDim; ni++) {
        n[ni] = __llbmc_nondef_int();
    }

    for(ni=0; ni<nDim; ni++) {
        bDomain = bDomain && (n[ni] >= 0) && (n[ni] < nDim);
        for(nj=0; nj<nDim; nj++)
            if(ni!=nj) {
                bNoCapture = bNoCapture && (n[ni] != n[nj]);
                bNoCapture = bNoCapture && ni+n[nj] != nj+n[ni]
                                        && ni+n[ni] != nj+n[nj];
            }
    }

    __llbmc_assert(!(bDomain && bNoCapture));
    free(n);

    return 0;
}
