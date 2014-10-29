#define __INITPATTERN int z; int pos; z = NONDET; assume (z >= 0); pos = 0;

#define __INITPATTERNP int z; int pos; int next; z = NONDET; assume (z >= 0); pos = 0; next = 1;


#define __BEGINP if (z <= 0) {
#define __BEGINPP if (z <= 0) { 

#define __FIRSTP(LETTER, VAR) if (pos <= 0) { assume (VAR == LETTER); pos++; }
#define __FIRSTP0(VAR) if (pos <= 0) { assume (VAR <= 0); pos++; }
#define __FIRSTP1(VAR) if (pos <= 0) { assume (VAR >= 1); pos++; }

#define __P(POS, LETTER, VAR) else if (pos <= POS) { assume (VAR == LETTER); pos++;}
#define __P0(POS, VAR) else if (pos <= POS) { assume (VAR <= 0); pos++;}
#define __P1(POS,  VAR) else if (pos <= POS) { assume (VAR >= 1); pos++;}

#define __WEND else {i--; pos = 0;}

#define __ENDP else { z = NONDET; assume (z >= 0); pos = 0; } } else {z--;}
#define __ENDPP else { next++; z = NONDET; assume (z >= 0); pos = 0; } } else {z--;}
