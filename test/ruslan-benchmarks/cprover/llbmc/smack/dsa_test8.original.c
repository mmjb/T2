#include <stdlib.h>

void set(int ***a) {
  *a = (int**)malloc(sizeof(int*));
  **a = (int*)malloc(sizeof(int));
  ***a = 2;
}

int main() {
  int **a;
  set(&a);
  return **a;
}

