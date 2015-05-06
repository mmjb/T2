typedef unsigned long ULONG;

int main(void)
{
  ULONG CurSpaceX;
  ULONG Scaling;
  ULONG mask;
  ULONG scale;

  for (mask = 0x80; mask && CurSpaceX; mask >>= 1) {
    for (scale = 0; scale < Scaling && CurSpaceX; scale++) {
          ;
          CurSpaceX--;
      }
  }

  return 0;
}
