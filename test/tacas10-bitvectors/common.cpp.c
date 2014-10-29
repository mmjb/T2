
typedef unsigned char UCHAR;
typedef unsigned long ULONG;
typedef unsigned char *PUCHAR;

const UCHAR CAS_CAS         = 0x01;
const ULONG CAS             = 0x34;

UCHAR
READ_PORT_UCHAR(
    PUCHAR  Port
    );


int main(void)
{
  PUCHAR m_pBusMasterBase; // nondet
  ULONG ulCount=0;

  while (READ_PORT_UCHAR (m_pBusMasterBase + CAS) & CAS_CAS)
  {
      if (ulCount++ > 100)
      {
          return 1;
      }

      ;
  }

  return 0;
}
