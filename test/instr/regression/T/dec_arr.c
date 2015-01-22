#include "slayer.h"

int main() {
  int *x;
  int n;
  int m;
  assume(0 < n);
  assume(0 < m && m < n);
  x = malloc(sizeof(int) * n);

  while (x[m] > 0) {
    x[m]--;
  }

  free(x);
}
