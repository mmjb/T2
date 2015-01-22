
typedef unsigned long ULONG;
typedef unsigned long  ULONG_PTR;
typedef ULONG_PTR SIZE_T, *PSIZE_T;

int main(void)
{
  ULONG currentOffset=0;
  SIZE_T streamLength;
  ULONG subStreamLength;

  assume(subStreamLength <= streamLength);

  while (currentOffset+subStreamLength <= streamLength)
   {
      ;
      currentOffset += subStreamLength;
   }

  return 0;
}
