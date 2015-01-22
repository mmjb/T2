#define CCMP_BSIZE 16

typedef unsigned short USHORT;

int main(void)
{
  USHORT aad_len, i;

  for (i = 0; i < (int)(aad_len & (~(CCMP_BSIZE - 1))); i += CCMP_BSIZE) {
      ;
  }

  return 0;
}
