#include "slayer.h"

int main() {
  int val;
  int **x;

  x = malloc(sizeof(int **));
  *x = &val;

  while (**x > 0) {
    val--;
  }

  free(x);

  return 0;
}
