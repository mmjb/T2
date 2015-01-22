#include "smack.h"

int main() {
  int x = 0;
  char* p = (char*)&x;
  p[2] = 1;

  __SMACK_assert(x != 0);

  return 0;
}

