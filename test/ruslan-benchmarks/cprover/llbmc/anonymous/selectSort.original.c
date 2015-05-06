#include <llbmc.h>
#include <stdlib.h>

void selectSort(int *a, int N)
{
    int j, i;
    for (j = 0; j < N - 1; j++) {
        int min = j;
        for (i = j + 1; i < N; i++) {
            if (a[min] > a[i]) {
                min = i;
            }
        }
        int t = a[j];
        a[j] = a[min];
        a[min] = t;
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
    selectSort(a, N);
    free(a);
}
