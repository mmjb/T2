
typedef unsigned long ULONG;
typedef unsigned short USHORT;

int main(void)
{
  USHORT Name_Length;
  ULONG Index;

  for ( Index = 0; Index < (ULONG)Name_Length; Index += 1 ) {

      ;

      if ( nondet() ) {

          Index += 1;

          continue;
      }

      if ( nondet() ) {

//          return FALSE;
        break;
      }
  }

  return 0;
}
