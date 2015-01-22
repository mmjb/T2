
typedef unsigned long ULONG;

int nondet();

int main(void)
{
  ULONG i;

  for ( ; i > 0; i-- ) {

      if (nondet()) {

          if ((i > 0) && nondet()) {

              i++;
          }

          ;
          break;
      }
  }

  return 0;
}
