typedef unsigned long ULONG;
typedef unsigned short WCHAR;
typedef WCHAR *PWCHAR, *LPWCH, *PWCH;


int main(void)
{
  ULONG NameLength = 0;
  PWCHAR CurrentCharacter;
  ULONG CdName_FileName_Length;

  // heap abstraction 
  WCHAR string[255]; // some length
  ULONG i=0;
  WCHAR c=string[i]; // the character
  CurrentCharacter=&string[0];
   

  while ((NameLength < CdName_FileName_Length) &&
         (c != L';')) {

      i++;
      c = string[i];
      NameLength += 2;
  }

  return 0;
}
