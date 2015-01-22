
typedef unsigned long ULONG;
typedef unsigned char UCHAR;

int main(void)
{
  ULONG i;
  ULONG maxlenpersmb;
  ULONG maxlenperarraysize=7;
  UCHAR NativeFs_i;

  for (i=1;;i++){
      if (i==maxlenpersmb) {
          break;
      }
      if (i==maxlenperarraysize) {
          break;
      }
      if (NativeFs_i==0) {
          break;
      }
  }

  return 0;
}
