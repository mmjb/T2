/*** field2n.h ***/

#define WORDSIZE	((int)(sizeof(int)*8))
#define NUMBITS		113
#define TYPE2
/*#undef TYPE2 */

#ifdef TYPE2
#define field_prime	((NUMBITS<<1)+1)
#else
#define field_prime (NUMBITS+1)
#endif

#define	NUMWORD		(NUMBITS/WORDSIZE)
#define UPRSHIFT	(NUMBITS%WORDSIZE)
#define MAXLONG		(NUMWORD+1)

#define MAXBITS		(MAXLONG*WORDSIZE)
#define MAXSHIFT	(WORDSIZE-1)
#define MSB			(1L<<MAXSHIFT)

#define UPRBIT		(1L<<(UPRSHIFT-1))
#define UPRMASK		(~(-1L<<UPRSHIFT))
#define SUMLOOP(i)	for(i=0; i<MAXLONG; i++)

#define LONGWORD	(field_prime/WORDSIZE)
#define LONGSHIFT	((field_prime-1)%WORDSIZE)
#define LONGBIT		(1L<<(LONGSHIFT-1))
#define LONGMASK         (~(-1L<<LONGSHIFT))

typedef	short int INDEX;

typedef unsigned long ELEMENT;

typedef struct {
	ELEMENT 	e[MAXLONG];
}  FIELD2N;

typedef struct {
	ELEMENT e[LONGWORD+1];
} CUSTFIELD;

/* prototypes  */

void rot_left();
void rot_right();
void null();
void copy();
void null_cust();
void copy_cust ();
void genlambda();
void genlambda2();
void opt_mul();
void opt_inv();
INDEX log_2();
void one();
void cus_times_u_to_n();
void init_opt_math();
