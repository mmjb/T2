#include "necla.h"
#include <stdlib.h>

typedef struct dist_{
   
    int x;
    int y;
    int z;

} DIST;


int __llbmc_main(int h, int w){

    DIST **lut; // lookup table, 2D array of structures
    int x, y;
  
    ASSUME(h > 0);
    ASSUME(w > 0);
    ASSUME(h <= 10);
    ASSUME(w <= 10);

    lut = (DIST**)malloc(sizeof(DIST*)*h);
    lut[0] = (DIST*)malloc(sizeof(DIST)*h*w);
    for (y=0; y<h; y++)
        lut[y] = lut[0] + w*y;

    ASSERT(lut[0][h*w-1].x == lut[h-1][w-1].x);
    
    free(lut[0]);
    free(lut);

    return 1;
}
