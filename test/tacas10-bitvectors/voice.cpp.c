
typedef unsigned long       DWORD;

int nondet();

int main(void)
{
  DWORD dwLength;
  DWORD dwSoFar;

  assume(dwLength!=0);

  for (;;)
  {
      ;

      dwSoFar=nondet();

      // nondet-break removed
      
      if (dwSoFar >= dwLength) break;

      ;
      dwLength -= dwSoFar;
  }

  return 0;
}
