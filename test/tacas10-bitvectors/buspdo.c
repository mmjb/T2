typedef unsigned short WCHAR, *PWCHAR;

int main(void)
{
  unsigned short obj[256]; // some size
  PWCHAR buffer=obj;
  unsigned char x; // nondet
  unsigned i=0;
  // abstracting the current character
  char c=buffer[0];

  assume(x<=255 && obj[x]==0); // string is terminated,
                               // but we don't know where

  while (c) {
    i++;
    c=buffer[i]; // rewritten from *(buffer++) to buffer[i]
      while (c) {
        i++;
        c=buffer[i];
          ;
      }
  }

  return 0;
}
