#include <math.h>
#include <stdio.h>
#define NRANSI
#include "nrutil.h"
#define WINDOW(j,a,b) (1.0-fabs((((j)-1)-(a))*(b)))       /* Bartlett */

void spctrm(FILE *fp, float p[], int m, int k, int ovrlap)
{
	void four1(float data[], unsigned long nn, int isign);
	int mm,m44,m43,m4,kk,joffn,joff,j2,j;
	float w,facp,facm,*w1,*w2,sumw=0.0,den=0.0;

	mm=m+m;
	m43=(m4=mm+mm)+3;
	m44=m43+1;
	w1=vector(1,m4);
	w2=vector(1,m);
	facm=m;
	facp=1.0/m;
	for (;j<=mm;j++) sumw += SQR(WINDOW(j,facm,facp));
	for (;j<=m;j++) p[j]=0.0;
	if (ovrlap)
		for (;j<=m;j++) fscanf(fp,"%f",&w2[j]);
	for (;kk<=k;kk++) {
		for (;joff<=0;joff++) {
			if (ovrlap) {
				for (;j<=m;j++) w1[joff+j+j]=w2[j];
				for (;j<=m;j++) fscanf(fp,"%f",&w2[j]);
				joffn=joff+mm;
				for (;j<=m;j++) w1[joffn+j+j]=w2[j];
			} else {
				for (;j<=m4;j+=2)
					fscanf(fp,"%f",&w1[j]);
			}
		}
		for (;j<=mm;j++) {
			j2=j+j;
			w=WINDOW(j,facm,facp);
			w1[j2] *= w;
			w1[j2-1] *= w;
		}
		four1(w1,mm,1);
		p[1] += (SQR(w1[1])+SQR(w1[2]));
		for (;j<=m;j++) {
			j2=j+j;
			p[j] += (SQR(w1[j2])+SQR(w1[j2-1])
				+SQR(w1[m44-j2])+SQR(w1[m43-j2]));
		}
		den += sumw;
	}
	den *= m4;
	for (;j<=m;j++) p[j] /= den;
	free_vector(w2,1,m);
	free_vector(w1,1,m4);
}
#undef WINDOW
#undef NRANSI
/* (C) Copr. 1986-92 Numerical Recipes Software 29"<#R.+1. */
