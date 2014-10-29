#include "slayer.h"

int main() {
  int *x = malloc(sizeof(int));
  *x = 42;
  free(x);
  return 0;
}
