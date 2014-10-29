struct { int x; } r1;
struct { int x; } r2;
struct { int x; } r3;
int main() {

//int sel = 1;
//while ((r2.x = (sel ? r1.x : r3.x)) > 0) {
//  sel = 0;
//  r3.x = r2.x - 1;
//}

  int sel = 1;
  do {
    r2.x = sel ? r1.x : r3.x;
    sel = 0;
    r3.x = r2.x - 1;
  } while (r3.x > 0);
}
