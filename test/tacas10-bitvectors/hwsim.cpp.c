typedef unsigned long ULONG;

ULONG nondet();

int main(void)
{
  ULONG m_ScatterGatherMappingsQueued;
  ULONG m_ScatterGatherBytesQueued;
  ULONG BufferRemaining;

  while (BufferRemaining &&
      m_ScatterGatherMappingsQueued > 0 &&
      m_ScatterGatherBytesQueued >= BufferRemaining) {

      ULONG BytesToCopy = nondet();

      m_ScatterGatherMappingsQueued--;

        ;

      assume(BytesToCopy <= BufferRemaining);

      BufferRemaining -= BytesToCopy;

      m_ScatterGatherBytesQueued -= nondet();

      ;
  }

  return 0;
}
