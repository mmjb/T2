/* #include <stdlib.h> */

int *a;

inline void set(int *x) {
  *x = 1;
}

int main() {
  int y;
  a = &y;
  *a = 2;
  set(&y);
  return 0;
}

