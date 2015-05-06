
typedef unsigned char UCHAR;
typedef unsigned short USHORT;
typedef unsigned int UINT;
typedef unsigned long ULONG;


int main(void)
{
  UCHAR id_bNumEndpoints;
  ULONG i;
  UINT  j, n;
  UCHAR ed_bLength, id_bLength;
  UCHAR cd_wTotalLength;

  // we abstrac buf/pch to a ulong array counter
  //char buf[256];
  //char *pch=buf;
  ULONG buf; // some "position in space"
  ULONG pch=buf; // some other position, initially the same

  do {
      ;

      pch += id_bLength;
      for (j=0; j<id_bNumEndpoints; j++) {

          pch += ed_bLength;
      }
      i = (ULONG)(pch - buf);

  } while (i<cd_wTotalLength);

  return 0;
}
