
typedef unsigned long ULONG, *PULONG;
typedef unsigned long ULONG_PTR;
typedef unsigned char UCHAR;
typedef void *HANDLE;

typedef struct _CYCLE_TIME {
    ULONG               CL_CycleOffset:12;
    ULONG               CL_CycleCount:13;
    ULONG               CL_SecondCount:7;
} CYCLE_TIME, *PCYCLE_TIME;

typedef struct _RING3_ISOCH_DESCRIPTOR {
    ULONG           fulFlags;
     ULONG           ulLength;
    ULONG           nMaxBytesPerFrame;
    ULONG           ulSynch;
    ULONG           ulTag;
    CYCLE_TIME      CycleTime;
    ULONG           bUseCallback;
    ULONG           bAutoDetach;
    UCHAR           Data[1];
} RING3_ISOCH_DESCRIPTOR, *PRING3_ISOCH_DESCRIPTOR;

typedef struct _ISOCH_ATTACH_BUFFERS {
    HANDLE                  hResource;
     ULONG                   nNumberOfDescriptors;
    ULONG                   ulBufferSize;
    PULONG                  pIsochDescriptor;
    RING3_ISOCH_DESCRIPTOR  R3_IsochDescriptor[1];
} ISOCH_ATTACH_BUFFERS, *PISOCH_ATTACH_BUFFERS;


int main(void)
{
  ULONG IsochAttachBuffers_nNumberOfDescriptors; // nondet;
  PRING3_ISOCH_DESCRIPTOR pTempR3Desc;
  ULONG pTempR3Desc_ulLength; // nondet;
  ULONG ulBuffSize = sizeof (ISOCH_ATTACH_BUFFERS) - sizeof (RING3_ISOCH_DESCRIPTOR);
  ULONG i=0;

  ULONG inputBufferLength;

  for (i = 0; i < IsochAttachBuffers_nNumberOfDescriptors; i++)
  {

      if ((ULONG_PTR)pTempR3Desc & 0x3)
      {
          ;
          ;
          break;
      }

      if ((ulBuffSize + sizeof (RING3_ISOCH_DESCRIPTOR)) < ulBuffSize)
      {

          ;
          ;
          break;
      }
      ulBuffSize += sizeof (RING3_ISOCH_DESCRIPTOR);
      if (inputBufferLength < ulBuffSize)
      {
        ;
        ;
        break;
      }

                    if ((ulBuffSize + pTempR3Desc_ulLength) < ulBuffSize)
                    {

                        ;
                        break;
                    }
    ulBuffSize += pTempR3Desc_ulLength;
    if (inputBufferLength < ulBuffSize)
    {
      ;
      ;
      break;
    }

    ;
  }

}
