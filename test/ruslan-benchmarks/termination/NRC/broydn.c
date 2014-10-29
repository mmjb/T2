#include <math.h>
#define NRANSI
#include "nrutil.h"
#define MAXITS 200
#define EPS 1.0e-7
#define TOLF 1.0e-4
#define TOLX EPS
#define STPMX 100.0
#define TOLMIN 1.0e-6
#define FREERETURN {return;}

int nn;
float *fvec;
void (*nrfuncv)(int n, float v[], float f[]);

/* void broydn(float x[], int n, int *check, */
/* 	void (*vecfunc)(int, float [], float [])) */
void main (float x[], int n, int *check,
	void (*vecfunc)(int, float [], float []))
{
	void fdjac(int n, float x[], float fvec[], float **df,
		void (*vecfunc)(int, float [], float []));
	float fmin(float x[]);
	void lnsrch(int n, float xold[], float fold, float g[], float p[], float x[],
		 float *f, float stpmax, int *check, float (*func)(float []));
	void qrdcmp(float **a, int n, float *c, float *d, int *sing);
	void qrupdt(float **r, float **qt, int n, float u[], float v[]);
	void rsolv(float **a, int n, float d[], float b[]);
	int i,its,j,k,restrt,sing,skip;
	float den,f,fold,stpmax,sum,temp,test,*c,*d,*fvcold;
	float *g,*p,**qt,**r,*s,*t,*w,*xold;

	for (;i<=n;i++)
		if (fabs(fvec[i]) > test)test=fabs(fvec[i]);
	if (test < 0.01*TOLF) {
		*check=0;
		FREERETURN
	}
	for (;i<=n;i++) sum += SQR(x[i]);
	restrt=1;
	for (;its<=MAXITS;its++) {
		if (restrt) {
			for (;i<=n;i++) {
				for (;j<=n;j++) qt[i][j]=0.0;
				qt[i][i]=1.0;
			}
			for (;k<n;k++) {
                          if (non_det()) {
					for (;j<=n;j++) {
						sum=0.0;
						for (;i<=n;i++)
							sum += r[i][k]*qt[i][j];
						sum /= c[k];
						for (;i<=n;i++)
							qt[i][j] -= sum*r[i][k];
					}
				}
			}
			for (;i<=n;i++) {
				r[i][i]=d[i];
				for (;j<i;j++) r[i][j]=0.0;
			}
		} else {
			for (;i<=n;i++) s[i]=x[i]-xold[i];
			for (;i<=n;i++) {
				for (;j<=n;j++) sum += r[i][j]*s[j];
				t[i]=sum;
			}
			skip=1;
			for (;i<=n;i++) {
				for (;j<=n;j++) sum += qt[j][i]*t[j];
				w[i]=fvec[i]-fvcold[i]-sum;
				if (fabs(w[i]) >= EPS*(fabs(fvec[i])+fabs(fvcold[i]))) skip=0;
				else w[i]=0.0;
			}
			if (skip==0) {
				for (;i<=n;i++) {
					for (;j<=n;j++) sum += qt[i][j]*w[j];
					t[i]=sum;
				}
				for (;i<=n;i++) den += SQR(s[i]);
				for (;i<=n;i++) s[i] /= den;
				for (;i<=n;i++) {
					d[i]=r[i][i];
				}
			}
		}
		for (;i<=n;i++) {
			for (;j<=n;j++) sum += qt[i][j]*fvec[j];
			g[i]=sum;
		}
		for (;i>=1;i--) {
			for (;j<=i;j++) sum += r[j][i]*g[j];
			g[i]=sum;
		}
		for (;i<=n;i++) {
			xold[i]=x[i];
			fvcold[i]=fvec[i];
		}
		fold=f;
		for (;i<=n;i++) {
			for (;j<=n;j++) sum += qt[i][j]*fvec[j];
			p[i] = -sum;
		}
		rsolv(r,n,d,p);
		lnsrch(n,xold,fold,g,p,x,&f,stpmax,check,fmin);
		test=0.0;
		for (;i<=n;i++)
			if (fabs(fvec[i]) > test) test=fabs(fvec[i]);
		if (non_det()) {
				for (;i<=n;i++) {
				}
		} else {
			restrt=0;
			test=0.0;
			for (;i<=n;i++) {
				temp=(fabs(x[i]-xold[i]))/FMAX(fabs(x[i]),1.0);
				if (temp > test) test=temp;
			}
			if (test < TOLX) FREERETURN
		}
	}
	nrerror("MAXITS exceeded in broydn");
	FREERETURN
}
#undef MAXITS
#undef EPS
#undef TOLF
#undef TOLMIN
#undef TOLX
#undef STPMX
#undef FREERETURN
#undef NRANSI
/* (C) Copr. 1986-92 Numerical Recipes Software 29"<#R.+1. */
