#include <llbmc.h>
#include <stdlib.h>

int main()
{
    int bDomain = 1;
    int bSorted = 1;
    int nDim = 10;

    int *nA, *nB;
    int ni, nj;

    nA = malloc(nDim * sizeof(int));
    nA[0] = 5;
    nA[1] = 9;
    nA[2] = 4;
    nA[3] = 1;
    nA[4] = 3;
    nA[5] = 2;
    nA[6] = 6;
    nA[7] = 8;
    nA[8] = 0;
    nA[9] = 7;

    nB = malloc(nDim * sizeof(int));
    for (ni=0; ni<nDim; ni++) {
        nB[ni] = __llbmc_nondef_int();
    }

    for (ni = 0; ni < nDim; ni++) {
        int bExists = 0;
        for (nj = 0; nj < nDim; nj++) {
            bExists = bExists || nA[ni] == nB[nj];
        }
        bDomain = bDomain && bExists;
    }

    for (ni = 0; ni < nDim - 1; ni++)
        bSorted = bSorted && (nB[ni] < nB[ni+1]);

    __llbmc_assert(!(bDomain && bSorted));
    free(nA);
    free(nB);

    return 0;
}
