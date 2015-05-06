#include <math.h>
#define NRANSI
#include "nrutil.h"



void qrdcmp(float **a, int n, float *c, float *d, int *sing)
{
    assume(n>1);
	int i,j,k;
	float scale,sigma,sum,tau;

	*sing=0;
	for (;k<n;k++) {
		scale=0.0;
		for (;i<=n;i++) { scale=FMAX(scale,fabs(a[i][k])); }
		if (scale == 0.0) {
			*sing=1;
			c[k]=d[k]=0.0;
		} else {
			for (;i<=n;i++) a[i][k] /= scale;
			for (;i<=n;i++) sum += SQR(a[i][k]);
			sigma=SIGN(sqrt(sum),a[k][k]);
			a[k][k] += sigma;
			c[k]=sigma*a[k][k];
			d[k] = -scale*sigma;
			for (;j<=n;j++) {
				for (;i<=n;i++) sum += a[i][k]*a[i][j];
				tau=sum/c[k];
				for (;i<=n;i++) a[i][j] -= tau*a[i][k];
			}
		}
	}
	d[n]=a[n][n];
	if (d[n] == 0.0) *sing=1;
}
#undef NRANSI
/* (C) Copr. 1986-92 Numerical Recipes Software 29"<#R.+1. */
