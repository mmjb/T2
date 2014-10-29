#include "slayer.h"

int main() {
  void *x;
  void *y;
  void *z;
  void **w;

  x = &y;
  y = &x;
  z = &y;

  w = &z;
  while (*w != NULL) {
    w = *w;
  }

  return 0;
}
