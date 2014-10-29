#include "slayer.h"

int x, y;

void f() {
  if (x>0) {
    x--;

    f();
  }
}

void g() {
  if (y>0) {
    y++;

    g();
    TerminationIgnore ();
  }
}



main() {
  int i,j;

  f();

  g();


  while (i >= 0) {
    TerminationIgnore();
    i++;
  }

  while (j >= 0) {
    j--;
  }

}
