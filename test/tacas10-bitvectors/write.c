
#define PAGE_SIZE 0x2000

typedef unsigned long ULONG;

int main(void)
{
  ULONG Len;

  while (Len != 0) {

      ;

      ;
      if (Len <= PAGE_SIZE) {
          break;
      }
      Len -= PAGE_SIZE;
  }

  return 0;
}
