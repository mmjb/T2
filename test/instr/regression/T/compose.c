#include "slayer.h"

int g(int x) {
  return x;
}


int f(int x) {
  return x;
}

int main() {
  int x;
  f(g(x));
  return 0;
}
