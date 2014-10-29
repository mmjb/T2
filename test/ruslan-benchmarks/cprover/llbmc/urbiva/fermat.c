#include "llbmc.h"
#include <stdint.h>

inline uint32_t nPow(uint32_t nx, int np) {
    uint32_t nPow = 1;
    int ni;
    for (ni = 0; ni < np; ni++) {
        nPow *= nx;
    }
    return nPow;
}

/* void __llbmc_main(uint32_t na, uint32_t nb, uint32_t nc) { */
void main(uint32_t na, uint32_t nb, uint32_t nc) {
    int nN = 3;
    __llbmc_assume(na > 0);
    __llbmc_assume(nb > 0);
    __llbmc_assume(nc > 0);
    __llbmc_assert(nPow(na, nN) + nPow(nb, nN) != nPow(nc, nN));
}
