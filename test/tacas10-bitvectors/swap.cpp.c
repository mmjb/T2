
typedef unsigned int        UINT32;

int main(void)
{
  UINT32   u32ValidFrameCount;
  UINT32   u32SampleIndex;
  UINT32   u32SamplesPerFrame;

  while (u32ValidFrameCount--)
  {
      for (u32SampleIndex=0; u32SampleIndex+1<u32SamplesPerFrame; u32SampleIndex += 2)
      {
          ;
      }
  }

  return 0;
}
