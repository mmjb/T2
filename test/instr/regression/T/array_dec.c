#include "slayer.h"

int main() {
  int i;
  int *x;
  x = malloc(sizeof(int) * 8);
  for (i=0; i<8; i++) {
    while (x[i] > 0) {
      x[i]--;
    }
  }
  free(x);
}
