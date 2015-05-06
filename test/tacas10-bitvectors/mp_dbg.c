
#define DUMP_BytesPerLine 16

typedef unsigned long ULONG;
typedef int INT;

int main(void)
{
  ULONG cb;
  INT cbLine;

  while (cb)
  {

      cbLine = (cb < DUMP_BytesPerLine) ? cb : DUMP_BytesPerLine;
      ;
      cb -= cbLine;
      ;
  }

  return 0;
}
