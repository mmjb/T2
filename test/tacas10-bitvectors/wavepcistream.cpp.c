
const int BDL_MASK = 31;
const int MAX_BDL_ENTRIES = 32;

int main(void)
{
  int nFirst, nLast, nNewPos;
  int nBlockCounter = 0;

  do
  {
      nBlockCounter++;
      //
      // We must copy the block when the index wraps around (ring buffer)
      // or we are at the last entry.
      //
      if (((nNewPos + nBlockCounter) == MAX_BDL_ENTRIES) ||   // wrap around
          ((nFirst + nBlockCounter) == MAX_BDL_ENTRIES) ||    // wrap around
          ((nFirst + nBlockCounter) == (nLast + 1)))          // last entry
      {
          //
          // copy one block (multiple entries).
          //
          ;
          // adjust the index
          nNewPos = (nNewPos + nBlockCounter) & BDL_MASK;
          nFirst = (nFirst + nBlockCounter) & BDL_MASK;
          nBlockCounter = 0;
      }
  // nBlockCounter should be zero when the end condition hits.
  } while (((nFirst + nBlockCounter - 1) & BDL_MASK) != nLast);

  return 0;
}
