// #include "ctl.h"

// Property: G(a => F r)

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

int lock;
int CancelIrql;
int irql;
int csl;
PIRP    CurrentWaitIrp=NULL;
ULONG NewMask;
PIRP CancelIrp;
ULONG Mask;
int length;
PSERIAL_TIMEOUTS NewTimeouts;
PSERIAL_STATUS SerialStatus;
PSERIAL_BAUD_RATE pBaudRate;
PSERIAL_LINE_CONTROL pLineControl;
UCHAR LData;
UCHAR LStop;
UCHAR LParity;
UCHAR Mask;

int keA; 
int keR;

unsigned int pc;
int __phi() { return CAG(CIMP(CAP(keA==1),CAF(CAP(keR==1)))); }

int __rho_1_;
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
int __rho_14_;
int __rho_15_;
int __rho_16_;
int __rho_17_;
int __rho_18_;
int __rho_19_;
int __rho_20_;
int __rho_21_;
int __rho_22_;
int __rho_23_;
int __rho_24_;
int __rho_25_;
int __rho_26_;
int __rho_27_;
int __rho_28_;
int __rho_29_;
int __rho_30_;
int __rho_31_;
int __rho_32_;
int __rho_33_;
int __rho_34_;
int __rho_91_;



void KeAcquireSpinLock(int * lp, int * ip) {
   /* (*lp) = 1; */
   /* (*ip) = irql; */
}

void KeReleaseSpinLock(int * lp, int i) {
   /* (*lp) = 0; */
   /* irql = i; */
}

void IoAcquireCancelSpinLock(int * ip) {
   /* csl = 1; */
   /* (*ip) = irql; */
}

void IoReleaseCancelSpinLock(int ip) {
   /* csl = 0; */
   /* irql = ip; */
}

void IoMarkIrpPending(int x) {}

// This could be modelled in more detail
void RemoveReferenceAndCompleteRequest(int x,int y) {}

// This could be modelled in more detail
void RemoveReferenceForDispatch(int x) {}

// This could be modelled in more detail
void ProcessConnectionStateChange(int x) {}

int DeviceObject;
int Irp;
NTSTATUS          status;
KIRQL             OldIrql;

void init() {
  keA = keR = 0;

 lock = nondet();
 CancelIrql = nondet();
 irql = nondet();
 csl = nondet();
 DeviceObject = nondet();
 Irp = nondet();
 status=STATUS_UNSUCCESSFUL;
 OldIrql;
 status = nondet();
 keA = 0;
 keR = 0;
length = nondet();
NewTimeouts = nondet();
SerialStatus=nondet();
pBaudRate = nondet();
pLineControl = nondet();
 LData = 0;
LStop = 0;
 LParity = 0;
 Mask = 0xff;
}

NTSTATUS body()

{


   if (STATUS_SUCCESS != status)
   {
     while(1) { int ddd2; ddd2 = ddd2; }

   }


   if(1>0) {
     __rho_1_ = nondet();
     __rho_3_ = nondet();
     __rho_5_ = nondet();
     __rho_8_ = nondet();
     __rho_12_ = nondet();
     __rho_13_ = nondet();
     __rho_14_ = nondet();
     __rho_15_ = nondet();
     __rho_16_ = nondet();
     __rho_17_ = nondet();
     __rho_18_ = nondet();
     __rho_19_ = nondet();
     __rho_20_ = nondet();
     __rho_21_ = nondet();
     __rho_22_ = nondet();
      if(__rho_1_>0) {

	__rho_2_ = nondet();
           if (__rho_2_>0) {
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;
           }

           /*break*/;
       }

       else if(__rho_3_>0) /* case IOCTL_SERIAL_SET_WAIT_MASK:*/ {

           CurrentWaitIrp=NULL;
           NewMask = nondet();

	   __rho_4_ = nondet();
           if (__rho_4_>0) {

               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           } else {

               keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

               NewMask = nondet();




               keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

               if (CurrentWaitIrp != NULL) {






                   RemoveReferenceAndCompleteRequest(CurrentWaitIrp,
STATUS_SUCCESS);
               }


           }

           /*break*/;
       }

       else if(__rho_5_>0) /* case IOCTL_SERIAL_WAIT_ON_MASK:*/ {

           CurrentWaitIrp=NULL;

	   __rho_6_ = nondet();
           if (__rho_6_>0) {
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           }


           keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);




           CurrentWaitIrp=nondet();



	   __rho_7_ = nondet();
           if (__rho_7_>0) {



               status=STATUS_UNSUCCESSFUL;

           } else {




               IoMarkIrpPending(Irp);
               status=STATUS_PENDING;
           }

           keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

           if (CurrentWaitIrp != NULL) {






               RemoveReferenceAndCompleteRequest(
                   CurrentWaitIrp, STATUS_SUCCESS);
           }


           /*break*/;
       }

       else if(__rho_8_>0) /* case IOCTL_SERIAL_PURGE:*/ {

	 CancelIrp = nondet();
	 Mask= nondet();

	 __rho_9_ = nondet();
           if (__rho_9_ > 0) {
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           }

	   __rho_91_ = nondet();
           if (__rho_91_ >0) { //Mask & SERIAL_PURGE_RXABORT) {

               keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

               length = nondet();
               while (1) {
		 if (!(length>0)) break;

                   length--;
                   CancelIrp=nondet();

                   IoAcquireCancelSpinLock(CancelIrql);

		   __rho_10_ = nondet();
                   if (__rho_10_>0) {
                       IoReleaseCancelSpinLock(CancelIrql);
                       continue;
                   }

                   //IoSetCancelRoutine(CancelIrp, NULL);

                   IoReleaseCancelSpinLock(CancelIrql);

                   keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);


                   RemoveReferenceAndCompleteRequest(
                        CancelIrp, STATUS_CANCELLED);

                   keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);
               }

               CancelIrp=NULL;

	       __rho_11_ = nondet();
               if (__rho_11_>0)
               {
                   CancelIrp=nondet();

               }

               keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

               if (CancelIrp != NULL) {

                   RemoveReferenceAndCompleteRequest(
                       CancelIrp, STATUS_CANCELLED);

               }

           }


           /*break*/;
       }


       else if(__rho_12_>0) /* case IOCTL_SERIAL_GET_MODEMSTATUS:*/ {


	 __rho_13_ = nondet();
	 if (__rho_13_>0) {

               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           }



           /*break*/;
       }

       else if(__rho_13_>0) /* case IOCTL_SERIAL_SET_TIMEOUTS:*/ {

           NewTimeouts = nondet();

	   __rho_23_ = nondet();
           if (__rho_23_>0) { 
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           }

	   __rho_24_ = nondet();
           if (__rho_24_>0) {
               status = STATUS_INVALID_PARAMETER;
               /*break*/;
           }

           keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

           keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

           /*break*/;
       }

       else if(__rho_14_>0) /* case IOCTL_SERIAL_GET_TIMEOUTS:*/ {

	 __rho_25_ = nondet();
	 if (__rho_25_>0){

               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           }

           keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

           keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

           /*break*/;
       }

       else if(__rho_15_>0) /* case IOCTL_SERIAL_GET_COMMSTATUS:*/ {

           SerialStatus=nondet();

	   __rho_26_ = nondet();
           if (__rho_26_>0) {
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           }

           keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

           keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

           /*break*/;
       }

      //else if(nondet())  case IOCTL_SERIAL_SET_DTR:  {}
       else if(__rho_16_>0) /* case IOCTL_SERIAL_CLR_DTR:*/ {


           keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);



           keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

           ProcessConnectionStateChange(DeviceObject);


           /*break*/;
       }


       else if(__rho_17_>0) /* case IOCTL_SERIAL_SET_QUEUE_SIZE:*/ {

	 __rho_27_ = nondet();
           if (__rho_27_>0) {
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;
           }

           /*break*/;
       }


       else if(__rho_18_>0) /* case IOCTL_SERIAL_SET_BAUD_RATE:*/ {

	 __rho_28_ = nondet();
           if (__rho_28_>0) {
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           } else {

               keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

               keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);
           }


           /*break*/;
       }

       else if(__rho_19_>0) /* case IOCTL_SERIAL_GET_BAUD_RATE:*/ {

           pBaudRate = nondet();

	 __rho_29_ = nondet();
           if (__rho_29_>0) {

               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;

           } else {

               keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

               keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);


           }

           /*break*/;
       }

       else if(__rho_20_>0) /* case IOCTL_SERIAL_SET_LINE_CONTROL:*/ {

           pLineControl = nondet();
           LData = 0;
           LStop = 0;
           LParity = 0;
           Mask = 0xff;

	 __rho_30_ = nondet();
           if (__rho_30_>0) {
               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;
           }

           if(1) { // switch(nondet())

	     __rho_31_ = nondet();
               if(__rho_31_==5) /* case 5:*/ {

                   LData = SERIAL_5_DATA;
                   Mask = 0x1f;
                   /*break*/;

               }
               else if(__rho_31_==6) /* case 6:*/ {

                   LData = SERIAL_6_DATA;
                   Mask = 0x3f;
                   /*break*/;

               }
               else if(__rho_31_==7) /* case 7:*/ {

                   LData = SERIAL_7_DATA;
                   Mask = 0x7f;
                   /*break*/;

               }
               else if(__rho_31_==8) /* case 8:*/ {

                   LData = SERIAL_8_DATA;
                   /*break*/;

               }
	       else /*default:*/ {

                   status = STATUS_INVALID_PARAMETER;

               }
           }

           if (status != STATUS_SUCCESS)
           {
               /*break*/;
           }

           if(1) { // switch (nondet()) {

	     __rho_32_ = nondet();

               if(__rho_32_==NO_PARITY) /* case NO_PARITY:*/ {
                   LParity = SERIAL_NONE_PARITY;
                   /*break*/;

               }
               else if(__rho_32_==EVEN_PARITY) /* case EVEN_PARITY:*/ {
                   LParity = SERIAL_EVEN_PARITY;
                   /*break*/;

               }
               else if(__rho_32_==ODD_PARITY) /* case ODD_PARITY:*/ {
                   LParity = SERIAL_ODD_PARITY;
                   /*break*/;

               }
               else if(__rho_32_==SPACE_PARITY) /* case SPACE_PARITY:*/ {
                   LParity = SERIAL_SPACE_PARITY;
                   /*break*/;

               }
               else if(__rho_32_==MARK_PARITY) /* case MARK_PARITY:*/ {
                   LParity = SERIAL_MARK_PARITY;
                   /*break*/;

               }
               else /*default:*/ {

                   status = STATUS_INVALID_PARAMETER;
                   /*break*/;
               }

           }

           if (status != STATUS_SUCCESS)
           {
               /*break*/;
           }

           if (1) { /* switch */

	     __rho_33_ = nondet();
               if(__rho_33_==STOP_BIT_1) /* case STOP_BIT_1:*/ {

                   LStop = SERIAL_1_STOP;
                   /*break*/;
               }

               else if(__rho_33_==STOP_BITS_1_5) /* case STOP_BITS_1_5:*/ {

                   if (LData != SERIAL_5_DATA) {

                       status = STATUS_INVALID_PARAMETER;
                       /*break*/;
                   }
                   LStop = SERIAL_1_5_STOP;
                   /*break*/;

               }
               else if(__rho_33_==STOP_BITS_2) /* case STOP_BITS_2:*/ {

                   if (LData == SERIAL_5_DATA) {

                       status = STATUS_INVALID_PARAMETER;
                       /*break*/;
                   }

                   LStop = SERIAL_2_STOP;
                   /*break*/;
               }

               else /*default:*/ {

                   status = STATUS_INVALID_PARAMETER;
               }

           }

           if (status != STATUS_SUCCESS)
           {
               /*break*/;
           }


           keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);

           keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

           /*break*/;
       }

       else if(__rho_21_>0) /* case IOCTL_SERIAL_GET_LINE_CONTROL:*/ {

	 __rho_34_ = nondet();
           if (__rho_34_>0)  {

               status = STATUS_BUFFER_TOO_SMALL;
               /*break*/;
           }

           keA = 1; keA = 0; KeAcquireSpinLock(lock, OldIrql);


           keR = 1; keR = 0; KeReleaseSpinLock(lock, OldIrql);

           /*break*/;
       }

       else if(__rho_22_>0) /* case IOCTL_SERIAL_SET_RTS:*/ {

           /*break*/;

       }

       else /*default: */

           status=STATUS_NOT_SUPPORTED;
   }

   if (status != STATUS_PENDING) {




       if (Irp != NULL)
       {
           RemoveReferenceAndCompleteRequest(Irp, status);
       }
   }


   RemoveReferenceForDispatch(DeviceObject);


  while(1) { dummy=dummy; } L_return: return 0;


}

int main() {}
