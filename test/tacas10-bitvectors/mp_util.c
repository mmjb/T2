
typedef long LONG;
typedef unsigned long ULONG;
typedef ULONG *PULONG;
typedef LONG *PLONG;

// this is usually an atomic operation;
// for this testcase a stub is enough.
LONG InterlockedCompareExchange (PULONG dst, ULONG exc, ULONG cmp)
{
  LONG res=*dst;

  if (*dst==cmp)
  {
    *dst=exc;
  }

  return res;
}

int main(void)
{
  ULONG FlagsObj; // we need something to point to
  PULONG Flags=&FlagsObj;
  ULONG NewFlags, OldFlags;
  ULONG sFlag, cFlag;

  OldFlags = * (volatile ULONG *) Flags;
  NewFlags = (OldFlags | sFlag) & ~cFlag;

  while (NewFlags != OldFlags) {
      // Call to InterlockedCompareExchange inlined/dereferenced
      //NewFlags = InterlockedCompareExchange (Flags, NewFlags, OldFlags);

      LONG tmp=FlagsObj;
      if(FlagsObj==OldFlags)
      {
        FlagsObj=NewFlags;
      }
      NewFlags=FlagsObj;

      if (NewFlags == OldFlags) {
          break;
      }

      OldFlags = NewFlags;
      NewFlags = (NewFlags | sFlag) & ~cFlag;
  }

  return 0;
}
