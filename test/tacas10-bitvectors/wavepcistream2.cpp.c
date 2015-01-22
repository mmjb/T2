
const int BDL_MASK = 31;

typedef unsigned char UCHAR;

int main(void)
{
  UCHAR nCurrentIndex;
  int stBDList_nHead;

  if (nCurrentIndex != ((stBDList_nHead -1) & BDL_MASK))
  {
      int i = stBDList_nHead;
      while (i != nCurrentIndex)
      {
          ;
          i = (i + 1) & BDL_MASK;
      }
  }

  return 0;
}
