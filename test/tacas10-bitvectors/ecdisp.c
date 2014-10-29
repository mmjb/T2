
typedef unsigned long ULONG;
typedef unsigned short USHORT;
typedef int INT;

int main(void)
{
  USHORT BitSize;
  ULONG nUlongs;
  ULONG UlongIndex;
  USHORT BitsToAdd;
  USHORT nBits;
  INT iByteOffset;

  for (UlongIndex = 0; UlongIndex < nUlongs; UlongIndex++)
  {
      BitsToAdd = BitSize;

      while (BitsToAdd > 0)
      {
          nBits = min (8 - iByteOffset, BitsToAdd);

          ;

          iByteOffset = (iByteOffset + nBits) % 8;

          BitsToAdd -= nBits;

          ;
      }
  }

  return 0;
}
