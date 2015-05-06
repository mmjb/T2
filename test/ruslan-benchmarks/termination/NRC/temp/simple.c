#include "nrutil.h"

int **mx;
int m;
int n;

/* int simple(int **mx, int m, int n) { */
int simple() {

  int c, i, j, *v, **mmx;

  c = 0;
  v = ivector(1, m);
  mmx = imatrix(1, m, 1, n);
  
  for (; i<m; i++) {
    v[i] = i;
    for(; j<n; j++) {
      c++;
      mmx[i][j] = c;
      mx[i][j] = c;
    }
  }
  
  return 0;
}
