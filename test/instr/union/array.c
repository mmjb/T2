#include "slayer.h"

int test(int *x, int n) {
  int pred;
  int i;
  pred = 1;
  for (i=0; i<n; i++) {
    pred &= (x[i] > 0);
  }
  return pred;
}

int main() {
  int *x;
  int n;
  int m;
  assume(0 < n);
  assume(0 < m && m < n);
  x = malloc(sizeof(int) * n);

  while (test(x,n)) {
    x[m]--;
  }

  free(x);
}
