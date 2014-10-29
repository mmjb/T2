
typedef unsigned long ULONG;

int nondet();

int main(void)
{
  ULONG Index;
  ULONG NumberOfPages; // nondet

  for (Index = 0; Index < NumberOfPages; Index++) {

      if (nondet()) {

          ;

          while ((Index < NumberOfPages) && nondet()) {
              ;
              ++Index;
          }

          // return;
          break;
      }
  }

  return 0;
}
