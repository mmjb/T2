void KeAcquireSpinLock(int *x) { }
void KeReleaseSpinLock(int *y) { }

typedef struct irp {
  int Status;
  int Information;
} *PIRP;

typedef struct req {
  int status;
  PIRP irp;
  struct req *Next;
} *PREQ;

typedef struct devext {
  PREQ WriteListHeadVa;
  int  writeListLock;
} *PDEVEXT;

PDEVEXT devExt;
PREQ request;
int nPacketsOld;
int nPackets;
PIRP irp;
int i;
int loop_max;
int loop_count;

main () {


  while(1) {
    //get the write lock

    KeAcquireSpinLock(&devExt->writeListLock);

    nPacketsOld = nPackets; 
    request = devExt->WriteListHeadVa;

    if (!(loop_count<loop_max)) {
        break;
    }
    
    if(request && request->status){
      devExt->WriteListHeadVa = request->Next;
      KeReleaseSpinLock(&devExt->writeListLock);
      irp = request->irp;
      if(request->status > 0){
	irp->Status = 1;
	irp->Information = request->status;
      }
      else{
	irp->Status = 0;
	irp->Information = request->status;
      }
      if (nondet()) nPackets++;
    loop_count++;
    }
    if (nPackets == nPacketsOld) {
        break;
    }
  } 
  
  KeReleaseSpinLock(&devExt->writeListLock);
}
