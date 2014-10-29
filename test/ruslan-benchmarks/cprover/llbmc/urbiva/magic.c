#include "llbmc.h"
/* #include <stdlib.h> */

int main()
{
    int nDim = 4;
    int nN = nDim*nDim;
    int nSum = nDim*(nDim*nDim+1)/2;

    int bDomain = 1;
    int bDistinct = 1;
    int bSum = 1;
    int bSymmetry = 0;

    int nSumDiag1 = 0;
    int nSumDiag2 = 0;
    int nSumRow = 0;
    int nSumCol = 0;

    int ni, nj;

    int *nT = malloc(nN * sizeof(int));
    for (ni = 0; ni < nN; ni++) {
        nT[ni] = __llbmc_nondef_int();
    }

    for (ni = 0; ni < nN; ni++)
        bDomain = bDomain && (1 <= nT[ni]) && (nT[ni] <= nN);

    for (ni = 0; ni < nN; ni++)
        for (nj = ni+1; nj < nN; nj++)
            bDistinct = bDistinct && (nT[ni] != nT[nj]);

    for (ni = 0; ni < nDim; ni++)
        nSumDiag1 += nT[ni+nDim*ni];

    bSum = bSum && (nSumDiag1 == nSum);

    for (ni = 0; ni < nDim; ni++)
        nSumDiag2 += nT[(ni+1)*(nDim-1)];

    bSum = bSum && (nSumDiag2 == nSum);

    for (ni = 0; ni < nDim; ni++) {
        nSumRow = 0;
        for (nj = 0; nj < nDim; nj++)
            nSumRow += nT[ni*nDim+nj];

        bSum = bSum && (nSumRow == nSum);
    }

    for (nj = 0; nj < nDim; nj++) {
        nSumCol = 0;
        for (ni = 0; ni < nDim; ni++)
            nSumCol += nT[ni*nDim+nj];

        bSum = bSum && (nSumCol == nSum);
    }

    bSymmetry = (nT[0] < nT[nDim - 1]) && (nT[0] < nT[nDim*(nDim - 1)]) && (nT[0] < nT[nDim*nDim - 1]) && (nT[nDim - 1] < nT[nDim*(nDim - 1)]);

    __llbmc_assert(!(bDomain && bDistinct && bSum && bSymmetry));
    free(nT);

    return 0;
}
