/*

  SLAyer_malloc.h -- #def {malloc,free} as SLAyer_{malloc,free}.

  The slayer frontends translate SLAyer_{malloc,free} to the internal
  {Alloc,Free}. We avoid the usual {malloc,free} because slam treats
  malloc unsoundly. See PS#181.

*/

#ifndef _SLAyer_malloc_H_
#define _SLAyer_malloc_H_

#ifndef _SIZE_T_DEFINED
typedef unsigned int size_t;
#endif

#ifndef NULL
#define NULL 0
#endif


#ifdef SLAyer
void* SLAyer_malloc(size_t);
void  SLAyer_free(void*);

#define malloc SLAyer_malloc
#define free   SLAyer_free
#endif

#endif /* _SLAyer_malloc_H_ */
