typedef unsigned long ULONG;

int main(void)
{
  ULONG Value;

  while ( (Value & 0xfffffffe) != 0 ) {

      ;
      Value >>= 1;
  }

  return 0;
}
