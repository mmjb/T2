#include "slayer.h"

int main() {
  int *x;
  int *y;

  x = malloc(sizeof(int));
  y = x;

  while (*x > 0) {
    (*y)--;
  }

  free(x);
}
