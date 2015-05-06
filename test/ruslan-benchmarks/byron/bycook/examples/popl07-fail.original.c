// #include "ctl.h"

// Property: G(a => F r)

#define STATUS_SUCCESS 1
#define STATUS_OBJECT_NAME_COLLISION 2
#define PC_IO 1
#define PC_NIO 0
int pc;
int i; int Pdolen; int num; int DName;
int lptNamei; //[5];
int dcIdi; // [5];
int Pdoi; //[5];
int PdoType; int status;

int set; int unset;
int __phi() { return CAG(CIMP(CAP(set==1),CAF(CAP(unset==1)))); }

void init() { set = unset = 0; }

// The Program
int PPMakeDeviceName(int a, int b, int c, int d) { return nondet(); }
int IoCreateDevice(int a) { return nondet(); }
void ExFreePool(int a) {}
void PPBlockInits() {}
void PPUnblockInits() {}
void RtlInitUnicodeString(int a) {}


void body() {
  set = 1; set = 0;
  PPBlockInits(); 
  while (1) {
    if (!(i < Pdolen)) break;
    DName = PPMakeDeviceName(lptNamei, PdoType, dcIdi, num); 
    if (DName>0) { break; } 
    RtlInitUnicodeString(DName); 
    status = IoCreateDevice(Pdoi); pc = PC_IO; pc = PC_NIO;
    if (STATUS_SUCCESS != status) { 
      Pdoi = 0; 
      if (STATUS_OBJECT_NAME_COLLISION == status) { 
	ExFreePool(DName); 
	num++; 
	//goto loc_continue; 
      } 
      break; 
    } else { 
      i++; 
    } 
  } 
  num = 0; 
  dummy = nondet();
  if(dummy > 0) {
    unset = 1; unset = 0;
  }
  PPUnblockInits();
 loc_continue:0;
  while(1) { dummy=dummy; } L_return: return 0;
}

int main() { }
