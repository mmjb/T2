/* #include <stdlib.h> */

int main()
{
    int *x = (int*)malloc(sizeof(int));
    free(x);
    free(x);
    x = (int*)malloc(sizeof(int));
    return 0;
}
