#include "slayer.h"

struct { int x; } r;
int main() {
  while (r.x > 0) {
    r.x--;
  }
}
