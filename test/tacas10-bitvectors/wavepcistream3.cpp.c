
const int BDL_MASK = 31;

int nondet();

int main(void)
{
  int stBDList_nHead, stBDList_nTail;
  int nSearchIndex;

  assume(stBDList_nHead <= stBDList_nTail);

  nSearchIndex = stBDList_nHead;
  do
  {
      if (nondet())
          break;
      nSearchIndex = (nSearchIndex + 1) & BDL_MASK;
  } while (nSearchIndex != stBDList_nTail);

  return 0;
}
