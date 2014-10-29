#include <llbmc.h>

void __llbmc_main(unsigned int nS, unsigned int nE, unsigned int nN, unsigned int nD, unsigned int nM, unsigned int nO, unsigned int nR, unsigned int nY)
{
    int bAllDifferent;
    int bDomain;
    int bNoLeadingZeros;
    int bSum;

    bAllDifferent =                  (nS != nE) && (nS != nN) && (nS != nD) && (nS != nM) && (nS != nO) && (nS != nR) && (nS!=nY);
    bAllDifferent = bAllDifferent && (nE != nN) && (nE != nD) && (nE != nM) && (nE != nO) && (nE != nR) && (nE != nY);
    bAllDifferent = bAllDifferent && (nN != nD) && (nN != nM) && (nN != nO) && (nN != nR) && (nN != nY);
    bAllDifferent = bAllDifferent && (nD != nM) && (nD != nO) && (nD != nR) && (nD!=nY);
    bAllDifferent = bAllDifferent && (nM != nO) && (nM != nR) && (nM != nY);
    bAllDifferent = bAllDifferent && (nO != nR) && (nO != nY);
    bAllDifferent = bAllDifferent && (nR != nY);
    bDomain = (nS < 10) && (nE < 10) && (nN < 10) && (nD < 10) && (nM < 10) && (nO < 10) && (nR < 10) && (nY < 10);
    bNoLeadingZeros = (nM != 0) && (nS != 0);
    bSum =            nS*1000 + nE*100 + nN*10 + nD +
                      nM*1000 + nO*100 + nR*10 + nE   ==
           nM*10000 + nO*1000 + nN*100 + nE*10 + nY;

    __llbmc_assert(!(bAllDifferent && bDomain && bNoLeadingZeros && bSum));
}
