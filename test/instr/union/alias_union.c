#include "slayer.h"

union { int x; int y; } r;
int main() {
  while (r.x > 0) {
    r.y--;
  }
}
