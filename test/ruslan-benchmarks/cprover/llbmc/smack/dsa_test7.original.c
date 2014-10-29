#include <stdlib.h>

int **a;

void set(int *x) {
  *x = 1;
}

int main() {
  int y;
  int *x;
  a = &x;
  *a = &y;
  **a = 2;
  set(&y);
  return 0;
}

