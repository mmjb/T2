int main(void) {
/*   int NONDET; */
/*   int x = NONDET; */
/*   int y = NONDET; */
  int x;
  int y;

  // comment
  if (y >= 1) { // 3
    while (x > 0) { // 126, 146
      x = x - y; // 158
      y = y + 1; // 166
    }
  }
}
