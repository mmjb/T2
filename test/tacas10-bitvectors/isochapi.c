
typedef unsigned long ULONG;

int nondet();

int main(void)
{
  ULONG nNumberOfDescriptors; // nondet
  ULONG i,j;

  if(nNumberOfDescriptors>0)
  {

  for (i=0;i < nNumberOfDescriptors; i++) {

    if (nondet()) {

      ;

      if (nondet())
      {

        for (j = 0; j < i; j++)
        {
          ;
        }

        goto Exit_IsochAttachBuffers;
      }

      }
      else {

          ;
      }

      ;

      if (nondet()) {

          if (i != nNumberOfDescriptors-1) {

              ;
          }
          else {

              if (nondet())
              {
        for (j = 0; j < i; j++)
        {
          if (nondet())
          {
            ;
          }
        }
                  goto Exit_IsochAttachBuffers;
              }

              ;

          }
      }
      else {

          ;
      }

      ;
  }

  Exit_IsochAttachBuffers: ;

  }

  return 0;
}
