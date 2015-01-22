// #include "ctl.h"

// Property: G(keA => F keR)

#define NTSTATUS int
#define PIRP int
#define PDEVICE_OBJECT int
#define KIRQL int
#include<stdio.h>
#define STATUS_UNSUCCESSFUL 1
#define STATUS_SUCCESS 2
#define IOCTL_SERIAL_GET_WAIT_MASK 3
#define STATUS_BUFFER_TOO_SMALL 4
#define IOCTL_SERIAL_SET_WAIT_MASK 5
#define ULONG int
#define IOCTL_SERIAL_WAIT_ON_MASK 6
#define STATUS_PENDING 7
#define IOCTL_SERIAL_PURGE 8
#define PULONG int
#define IOCTL_SERIAL_GET_MODEMSTATUS 9
#define SERIAL_PURGE_RXABORT 10
#define STATUS_CANCELLED 11
#define IOCTL_SERIAL_SET_TIMEOUTS 12
#define PSERIAL_TIMEOUTS int
#define PSERIAL_STATUS int
#define PSERIAL_BAUD_RATE int
#define SERIAL_TIMEOUTS 14
#define STATUS_INVALID_PARAMETER 15
#define IOCTL_SERIAL_GET_TIMEOUTS 16
#define IOCTL_SERIAL_SET_DTR 17
#define IOCTL_SERIAL_CLR_DTR 18
#define IOCTL_SERIAL_GET_COMMSTATUS 19
#define IOCTL_SERIAL_GET_BAUD_RATE 20
#define IOCTL_SERIAL_SET_BAUD_RATE 21
#define IOCTL_SERIAL_SET_QUEUE_SIZE 22
#define SERIAL_BAUD_RATE int
#define IOCTL_SERIAL_SET_LINE_CONTROL 23
#define UCHAR int
#define SERIAL_LINE_CONTROL int
#define PSERIAL_LINE_CONTROL int
#define SERIAL_6_DATA 24
#define SERIAL_7_DATA 25
#define SERIAL_8_DATA 26
#define SERIAL_5_DATA 27
#define NO_PARITY 28
#define SERIAL_NONE_PARITY 29
#define EVEN_PARITY 30
#define SERIAL_EVEN_PARITY 31
#define ODD_PARITY 32
#define SERIAL_ODD_PARITY 33
#define SPACE_PARITY 34
#define SERIAL_SPACE_PARITY 35
#define MARK_PARITY 36
#define SERIAL_MARK_PARITY 37
#define STOP_BIT_1 28
#define STOP_BITS_2 29
#define STOP_BIT_3 30
#define STOP_BIT_4 31
#define SERIAL_1_STOP 32
#define SERIAL_2_STOP 33
#define SERIAL_3_STOP 34
#define SERIAL_4_STOP 35
#define STOP_BITS_1_5 36
#define SERIAL_1_5_STOP 37
#define SERIAL_LCR_BREAK 38
#define IOCTL_SERIAL_GET_LINE_CONTROL 39
#define IOCTL_SERIAL_SET_RTS 40
#define STATUS_NOT_SUPPORTED 41
#define PDEVICE_EXTENSION int
#define PCROM_DATA int
#define PASYNC_ADDRESS_DATA int
#define PISOCH_DETACH_DATA int
#define PISOCH_RESOURCE_DATA int
#define TRUE 1
#define FALSE 0
#define PIRB int
#define IRB int
#define CCHAR int
#define PBUS_RESET_IRP int
#define PDRIVER_CANCEL int
#define NonPagedPool 1
#define IO_NO_INCREMENT 2


int CancelIrql;
int irql;
//int csl;
//PDEVICE_OBJECT   DeviceObject;
PIRP             Irp;
NTSTATUS            ntStatus;
//PDEVICE_EXTENSION   deviceExtension;
KIRQL               Irql;
int k1;
int k2;
int k3;
int k4;
int k5;
PCROM_DATA      CromData;
PASYNC_ADDRESS_DATA     AsyncAddressData;
PISOCH_RESOURCE_DATA    IsochResourceData;
PISOCH_DETACH_DATA      IsochDetachData;
ULONG                   i;
PIRB                pIrb;
PIRP                ResourceIrp;
//CCHAR               StackSize;
//PBUS_RESET_IRP  BusResetIrp;
//PDRIVER_CANCEL  prevCancel;



int keA; int keR; int ioA; int ioR;
unsigned int pc;
 inline int __phi() { return CEF(CAND(CAP(keA==1),CAG(CAP(keR!=1)))); }
int __rho_1_;
int __rho_56_;
int __rho_99_;
int __rho_2_;
int __rho_3_;
int __rho_4_;
int __rho_5_;
int __rho_6_;
int __rho_7_;
int __rho_8_;
int __rho_9_;
int __rho_10_;
int __rho_11_;
int __rho_12_;
int __rho_13_;

 inline void init() {
  keA = 0;
  keR = 0;
}

 inline void KeAcquireSpinLock(int * lp, int * ip) { keA = 1; keA = 0;
   /* (*lp) = 1; */
   /* (*ip) = irql; */
}

 inline void KeReleaseSpinLock(int * lp, int i) { keR = 1; keR = 0;
   /* (*lp) = 0; */
   /* irql = i; */
}

 inline void IoAcquireCancelSpinLock(int * ip) { ioA = 1; ioA = 0;
   /* csl = 1; */
   /* (*ip) = irql; */
}

 inline void IoReleaseCancelSpinLock(int ip) { ioR = 1; ioR = 0;
   /* csl = 0; */
   /* irql = ip; */
}

 inline int t1394_IsochCleanup(int a) { }
 inline int ExAllocatePool(int a, int b) { }
 inline int t1394Diag_PnpStopDevice(int a,int b) { }
 inline int t1394_SubmitIrpSynch(int a, int b) { }
 inline int IoFreeIrp(int a) { }
 inline int IoSetDeviceInterfaceState() { }
 inline int RtlZeroMemory(int a, int b) { }
 inline int KeCancelTimer() { }
 inline int IoAllocateIrp(int a, int b) { 
  __rho_99_ = nondet();
  return __rho_99_;
}
 inline int IoFreeMdl() { }
 inline int IoSetCancelRoutine(int a) { }
 inline int ExFreePool0() { }
 inline int ExFreePool1(int a) { }
 inline int ExFreePool2(int a, int b) { }
 inline int IoCompleteRequest(int a) { }

inline int body() {
  __rho_1_ = nondet();
   if (__rho_1_>0) {

       // haven't stopped yet, lets do so
       ntStatus = t1394Diag_PnpStopDevice(1, Irp);
   }

   ntStatus = IoSetDeviceInterfaceState();


   // lets free up any crom data structs we've allocated...
   keA = 1; keA = 0; KeAcquireSpinLock(1, Irql);

   __rho_2_ = nondet();
   k1 = __rho_2_;
   while (1) { 
     if (!(k1>0)) break;

     __rho_3_ = nondet();
       CromData = __rho_3_;

       // get struct off list
       k1--;

       // need to free up everything associated with this allocate...
       if (CromData>0)
       {
	   __rho_4_ = nondet();
           if (__rho_4_>0)
               ExFreePool0();

	   __rho_5_ = nondet();
           if (__rho_5_>0)
               IoFreeMdl();

           // we already checked CromData
           ExFreePool1(CromData);
       }
   }

   keR = 1; keR = 0; KeReleaseSpinLock(1, Irql);

   keA = 1; keA = 0; KeAcquireSpinLock(1, Irql);

   __rho_6_ = nondet();
   k2 = __rho_6_;
   while (1) {
     if (!(k2>0)) break;

     AsyncAddressData = nondet();

       // get struct off list
       AsyncAddressData = nondet();
       k2--;

       // need to free up everything associated with this allocate...

       __rho_7_ = nondet();
       if (__rho_7_>0)
           IoFreeMdl();

       __rho_8_ = nondet();
       if (__rho_8_>0)
           ExFreePool0();

       __rho_9_ = nondet();
       if (__rho_9_>0)
           ExFreePool0();

       if (AsyncAddressData>0)
           ExFreePool0();
   }

   keR = 1; keR = 0; KeReleaseSpinLock(1, Irql);

   // free up any attached isoch buffers
   while (TRUE) {

       keA = 1; keA = 0; KeAcquireSpinLock(1, Irql);

       __rho_10_ = nondet();
       k3 = __rho_10_;
       if (k3>0) {

	 IsochDetachData = nondet();
	 i = nondet();

           IsochDetachData = nondet();
           k3--;


           KeCancelTimer();
           keR = 1; keR = 0; KeReleaseSpinLock(1, Irql);


           t1394_IsochCleanup(IsochDetachData);
       }
       else {

           keR = 1; keR = 0; KeReleaseSpinLock(1, Irql);
           break;
       }
   }

   // remove any isoch resource data

   __rho_11_ = nondet();
   k4 = __rho_11_;
   while (TRUE) {

       keA = 1; keA = 0; KeAcquireSpinLock(1, Irql);
       if (k4>0) {

	 __rho_12_ = nondet();
           IsochResourceData = __rho_12_;
           k4--;

           keR = 1; keR = 0; KeReleaseSpinLock(1, Irql);


           if (IsochResourceData>0) {

	       pIrb = nondet();
               ResourceIrp = nondet();
               //StackSize = nondet();
               ResourceIrp = IoAllocateIrp(1, FALSE);

               if (ResourceIrp == 0) {

               }
               else {

                   pIrb = ExAllocatePool(NonPagedPool, 0);

                   if (pIrb<=0) {

                       IoFreeIrp(ResourceIrp);
                   }
                   else {

                       RtlZeroMemory (pIrb, 0);

                       ntStatus = t1394_SubmitIrpSynch(ResourceIrp, pIrb);


                       ExFreePool1(pIrb);
                       IoFreeIrp(ResourceIrp);
                   }
               }
           }
       }
       else {

           keR = 1; keR = 0; KeReleaseSpinLock(1, Irql);
           break;
       }
   }

   // get rid of any pending bus reset notify requests
   keA = 1; keA = 0; KeAcquireSpinLock(1, Irql);

   __rho_13_ = nondet();
   k5 = __rho_13_;
   while (1) {
     if (!(k5>0)) break;

     //prevCancel = NULL;

       // get the irp off of the list
       //BusResetIrp = nondet();
       __rho_56_ = nondet();
       if(__rho_56_>0)
	 k5--;


       // make this irp non-cancelable...
       //prevCancel = IoSetCancelRoutine(NULL);


       // and complete it...
       IoCompleteRequest(IO_NO_INCREMENT);

       ExFreePool1(1);
   }

   keR = 1; keR = 0; KeReleaseSpinLock(1, Irql);

   // free up the symbolic link

  while(1) { dummy=dummy; } L_return: return 0;
} // t1394Diag_PnpRemoveDevice

 int main() { init(); body(); }
