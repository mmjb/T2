#ifndef _SLAYER_H_
#define _SLAYER_H_

// "SLAyer" is defined when frontend_slam calls slam.

#include "slayer_specifications.h"
#include "SLAyer_malloc.h"

#ifdef SLAyer
int nondet() { int x; return x; }
void TerminationIgnore(void) {}
#endif


/* Trick slam into keeping the assume expr simple.  */
#ifdef SLAyer
#define assume(c) { if (!(c)) { assume(0); } }
#endif


/* FAIL forces a SLAyer backend error by writing to an unallocted pointer. */
/* (slamcl unsoundly translates stores to most pointer constants to nop, */
/* but it seems that function pointers are treated soundly.) */
#ifdef SLAyer
#define FAIL					\
    {						\
      *(int *) &nondet = 0;			\
    }

#define FAIL_IF(p) if (p) FAIL
#endif

/* Replacement CONTAINING_RECORD. This has the same semantics as */
/* the original wdf.h one, but uses +P-(P->f) to get around the fact that */
/* the frontend seems to immediately translate 0->f as sizeof(f).  */
/* P is an arbitrary pointer.  */
#ifdef SLAyer
void SLAyer_P() { }
#define AddrOfSLAyer_P (&SLAyer_P)
/* The fe seems to drop the outer (type*) cast, but leaves the SL_ULONG ones. */
typedef unsigned long SL_ULONG;
#define SLAyer_CONTAINING_RECORD(address, type, field)			\
  ((type *)(								\
	    ((SL_ULONG)(address)) +					\
	    ((SL_ULONG)AddrOfSLAyer_P) -				\
	    (SL_ULONG)(&((type *)(AddrOfSLAyer_P))->field)))


#define CONTAINING_RECORD SLAyer_CONTAINING_RECORD
#else
#define CONTAINING_RECORD(address, type, field) ((type *)( \
                                                  (PCHAR)(address) - \
                                                  (ULONG_PTR)(&((type *)0)->field)))
#endif

/* printf stub avoids slam generating one with the wrong type. */
#ifdef SLAyer
int printf (const char *fmt,...) { return 0; }
#endif

#endif // #ifndef _SLAYER_H_
