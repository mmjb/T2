
typedef unsigned char       BYTE;
typedef unsigned long       DWORD;

int main(void)
{
  DWORD dwPitch;
  BYTE    bBlock;

  for (bBlock = 1; dwPitch >= 0x400; dwPitch >>= 1, bBlock++)
          ;

  return 0;
}
