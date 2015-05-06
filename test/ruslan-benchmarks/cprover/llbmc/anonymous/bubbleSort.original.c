#include <llbmc.h>
#include <stdlib.h>

void bubbleSort(int *a, int N)
{
    int j, i;
    for (j = 0; j < N - 1; j++) {
        for (i = 0; i < N - j - 1; i++) {
            if (a[i] > a[i + 1]) {
                int t = a[i];
                a[i] = a[i + 1];
                a[i + 1] = t;
            }
        }
    }
    for (j = 0; j < N - 1; j++) {
        __llbmc_assert(a[j] <= a[j + 1]);
    }
}

void __llbmc_main(int N)
{
    int i;
    __llbmc_assume(N > 0);
    __llbmc_assume(N <= 5);
    int *a = malloc(N * sizeof(int));
    for (i = 0; i < N; i++) {
        a[i] = __llbmc_nondef_int();
    }
    bubbleSort(a, N);
    free(a);
}
