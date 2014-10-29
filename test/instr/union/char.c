#include "slayer.h"

int main() {
  char *p;
  char *x = "hello world\n";
  p = x;
  while (*p != '\0') {
    p++;
  }
  return 0;
}
