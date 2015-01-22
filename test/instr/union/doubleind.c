#include "slayer.h"

int main() {
  int *x;
  int **y;

  x = malloc(sizeof(int));
  y = &x;
  
  while (**y > 0) {
    **y--;
  }

  free(x);
  return 0;
}
