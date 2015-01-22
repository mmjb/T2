
typedef unsigned short USHORT;

int main(void)
{
  USHORT MaximumNumberOfMids;
  USHORT MaximumMidsRoundedToPowerOf2 = 0x100;

  while (MaximumNumberOfMids > MaximumMidsRoundedToPowerOf2) {
      MaximumMidsRoundedToPowerOf2 = MaximumMidsRoundedToPowerOf2 << 1;
      ;
  }

  return 0;
}
