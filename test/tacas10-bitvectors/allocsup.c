
typedef unsigned long ULONG;
typedef __int64             LONGLONG;

LONGLONG nondet();

int main(void)
{
  ULONG CurrentMcbOffset=0;
  ULONG Fcb_Mcb_CurrentEntryCount;
  LONGLONG FileOffset;
  LONGLONG CurrentMcbEntry_ByteCount;
  LONGLONG CurrentMcbEntry_FileOffset;

  while (CurrentMcbOffset < Fcb_Mcb_CurrentEntryCount) {

      //
      //  Check if the offset lies within the current Mcb position.
      //

      if (FileOffset < CurrentMcbEntry_FileOffset + CurrentMcbEntry_ByteCount) {

          break;
      }

      //
      //  Move to the next entry.
      //

      CurrentMcbOffset += 1;

      CurrentMcbEntry_FileOffset=nondet();
      CurrentMcbEntry_ByteCount=nondet();
  }

  return 0;
}
