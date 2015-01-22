
typedef unsigned long ULONG;

int G_ReadLen = 512;          // #bytes to read

int main(void)
{

  G_ReadLen=nondet();

  while( G_ReadLen % sizeof( ULONG ) ) {
      G_ReadLen++;
  }

  return 0;
}
