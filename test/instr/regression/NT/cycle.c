#include "slayer.h"

int main() {
  void *x;
  void *y;
  void **z;

  x = &y;
  y = &x;

  z = &x;
  while (*z != NULL) {
    z = *z;
  }

  return 0;
}
