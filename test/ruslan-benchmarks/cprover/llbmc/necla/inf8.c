#include "necla.h"

/* int __llbmc_main(int a, int b, int c, int d) { */
int main(int a, int b, int c, int d) {
    int id, utriag, ltriag, triag, unknown;
    id = utriag = ltriag = triag = unknown = 0; 
    if(c == 0 || b == 0) {
        triag = 1;
    }

    if(triag > 0) {
        if(c == 0 && b == 0) {
            if(a == 1 && d == 1) {
                id = 1;
            }
            ltriag = 1;
            utriag = 1;
        }
        else if(b == 0) {
            ltriag = 1;
        }
        else {
            utriag = 1;
            ASSERT(c == 0);
        }
    }
    else {
        unknown = 1;
    }

    if(triag) {
        ASSERT(id || ltriag || utriag);
    }

    if(triag && utriag == ltriag)
        ASSERT(c == 0 && b == 0);

    ASSERT(unknown > 0 || triag > 0);
    return 1;
}
