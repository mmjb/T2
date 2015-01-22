
//
// Skin1D model.
//

// Initialization macros
#define GRANULARITY 3

#define INIT_VAR(V)				\
  if (V > GRANULARITY) { V = GRANULARITY; }	\
  else if (V < 0) { V = 0; }



int main() {

  // Variables.
  int wntext0, wntext0_new;
  int frizzled0, frizzled0_new;
  int dsh0, dsh0_new;
  int axin0, axin0_new;
  int bcat0, bcat0_new;
  int gt1_0, gt1_0_new;
  int gt2_0, gt2_0_new;
  int delta0, delta0_new;
  int deltaext0, deltaext0_new;
  int notchic0, notchic0_new;
  int p21_0, p21_0_new;
  int wnt0, wnt0_new;

  int wntext1, wntext1_new;
  int frizzled1, frizzled1_new;
  int dsh1, dsh1_new;
  int axin1, axin1_new;
  int bcat1, bcat1_new;
  int gt1_1, gt1_1_new;
  int gt2_1, gt2_1_new;
  int delta1, delta1_new;
  int deltaext1, deltaext1_new;
  int notchic1, notchic1_new;
  int p21_1, p21_1_new;
  int wnt1, wnt1_new;

  int wntext2, wntext2_new;
  int frizzled2, frizzled2_new;
  int dsh2, dsh2_new;
  int axin2, axin2_new;
  int bcat2, bcat2_new;
  int gt1_2, gt1_2_new;
  int gt2_2, gt2_2_new;
  int delta2, delta2_new;
  int deltaext2, deltaext2_new;
  int notchic2, notchic2_new;
  int p21_2, p21_2_new;
  int wnt2, wnt2_new;

  int wntext3, wntext3_new;
  int frizzled3, frizzled3_new;
  int dsh3, dsh3_new;
  int axin3, axin3_new;
  int bcat3, bcat3_new;
  int gt1_3, gt1_3_new;
  int gt2_3, gt2_3_new;
  int delta3, delta3_new;
  int deltaext3, deltaext3_new;
  int notchic3, notchic3_new;
  int p21_3, p21_3_new;
  int wnt3, wnt3_new;

  int wntext4, wntext4_new;
  int frizzled4, frizzled4_new;
  int dsh4, dsh4_new;
  int axin4, axin4_new;
  int bcat4, bcat4_new;
  int gt1_4, gt1_4_new;
  int gt2_4, gt2_4_new;
  int delta4, delta4_new;
  int deltaext4, deltaext4_new;
  int notchic4, notchic4_new;
  int p21_4, p21_4_new;
  int wnt4, wnt4_new;

/*   int copied = 0; */
/*   int nondet() { int x; return x; } */
/*   int slic_error() { SLIC_ERROR:0; } */

  // Initialization
  INIT_WNTEXT(wntext0) ;
  INIT_VAR(wntext0) ;
  INIT_VAR(frizzled0) ;
  INIT_VAR(dsh0) ;
  INIT_VAR(axin0) ;
  INIT_VAR(bcat0) ;
  INIT_VAR(gt1_0) ;
  INIT_VAR(gt2_0) ;
  INIT_VAR(delta0) ;
  INIT_VAR(deltaext0) ;
  INIT_VAR(notchic0) ;
  INIT_VAR(p21_0) ;
  INIT_VAR(wnt0) ;
  INIT_VAR(wntext1) ;
  INIT_VAR(frizzled1) ;
  INIT_VAR(dsh1) ;
  INIT_VAR(axin1) ;
  INIT_VAR(bcat1) ;
  INIT_VAR(gt1_1) ;
  INIT_VAR(gt2_1) ;
  INIT_VAR(delta1) ;
  INIT_VAR(deltaext1) ;
  INIT_VAR(notchic1) ;
  INIT_VAR(p21_1) ;
  INIT_VAR(wnt1) ;
  INIT_VAR(wntext2) ;
  INIT_VAR(frizzled2) ;
  INIT_VAR(dsh2) ;
  INIT_VAR(axin2) ;
  INIT_VAR(bcat2) ;
  INIT_VAR(gt1_2) ;
  INIT_VAR(gt2_2) ;
  INIT_VAR(delta2) ;
  INIT_VAR(deltaext2) ;
  INIT_VAR(notchic2) ;
  INIT_VAR(p21_2) ;
  INIT_VAR(wnt2) ;
  INIT_VAR(wntext3) ;
  INIT_VAR(frizzled3) ;
  INIT_VAR(dsh3) ;
  INIT_VAR(axin3) ;
  INIT_VAR(bcat3) ;
  INIT_VAR(gt1_3) ;
  INIT_VAR(gt2_3) ;
  INIT_VAR(delta3) ;
  INIT_VAR(deltaext3) ;
  INIT_VAR(notchic3) ;
  INIT_VAR(p21_3) ;
  INIT_VAR(wnt3) ;
  INIT_VAR(wntext4) ;
  INIT_VAR(frizzled4) ;
  INIT_VAR(dsh4) ;
  INIT_VAR(axin4) ;
  INIT_VAR(bcat4) ;
  INIT_VAR(gt1_4) ;
  INIT_VAR(gt2_4) ;
  INIT_VAR(delta4) ;
  INIT_VAR(deltaext4) ;
  INIT_VAR(notchic4) ;
  INIT_VAR(p21_4) ;
  INIT_VAR(wnt4) ;


  // Iteration
  while (1) {

    // Calculate new
    if ((3 + wnt1 > 1 + (2 * wntext0)))
      wntext0_new = wntext0 + 1;
    else if ((3 + wnt1 < (2 * wntext0)))
      wntext0_new = wntext0 - 1;
    else
      wntext0_new = wntext0;
    if ((wntext0 > frizzled0))
      frizzled0_new = frizzled0 + 1;
    else if ((wntext0 < frizzled0))
      frizzled0_new = frizzled0 - 1;
    else
      frizzled0_new = frizzled0;
    if ((frizzled0 > dsh0))
      dsh0_new = dsh0 + 1;
    else if ((frizzled0 < dsh0))
      dsh0_new = dsh0 - 1;
    else
      dsh0_new = dsh0;
    if (((3 - dsh0) > axin0))
      axin0_new = axin0 + 1;
    else if ((((3 - dsh0) < axin0) && (axin0 > 0)))
      axin0_new = axin0 - 1;
    else
      axin0_new = axin0;
    if (((3 - axin0) > bcat0))
      bcat0_new = bcat0 + 1;
    else if ((((3 - axin0) < bcat0) && (bcat0 > 0)))
      bcat0_new = bcat0 - 1;
    else
      bcat0_new = bcat0;
    if ((bcat0 > gt1_0))
      gt1_0_new = gt1_0 + 1;
    else if ((bcat0 < gt1_0))
      gt1_0_new = gt1_0 - 1;
    else
      gt1_0_new = gt1_0;
    if ((notchic0 > gt2_0))
      gt2_0_new = gt2_0 + 1;
    else if ((notchic0 < gt2_0))
      gt2_0_new = gt2_0 - 1;
    else
      gt2_0_new = gt2_0;
    if ((gt1_0 + gt2_0 > (2 * delta0)))
      delta0_new = delta0 + 1;
    else if ((gt1_0 + gt2_0 < ((2 * delta0) - 1)))
      delta0_new = delta0 - 1;
    else
      delta0_new = delta0;
    if ((2 + delta1 > (2 * deltaext0)))
      deltaext0_new = deltaext0 + 1;
    else if ((2 + delta1 < ((2 * deltaext0) - 1)))
      deltaext0_new = deltaext0 - 1;
    else
      deltaext0_new = deltaext0;
    if (((1 > notchic0) && (deltaext0 > notchic0)))
      notchic0_new = notchic0 + 1;
    else if ((1 < notchic0) || (deltaext0 < notchic0))
      notchic0_new = notchic0 - 1;
    else
      notchic0_new = notchic0;
    if ((notchic0 > p21_0))
      p21_0_new = p21_0 + 1;
    else if ((notchic0 < p21_0))
      p21_0_new = p21_0 - 1;
    else
      p21_0_new = p21_0;
    if (((3 - p21_0) > wnt0))
      wnt0_new = wnt0 + 1;
    else if (((3 - p21_0) < wnt0))
      wnt0_new = wnt0 - 1;
    else
      wnt0_new = wnt0;
    if ((wnt0 + wnt2 > 1 + (2 * wntext1)))
      wntext1_new = wntext1 + 1;
    else if ((wnt0 + wnt2 < (2 * wntext1)))
      wntext1_new = wntext1 - 1;
    else
      wntext1_new = wntext1;
    if ((wntext1 > frizzled1))
      frizzled1_new = frizzled1 + 1;
    else if ((wntext1 < frizzled1))
      frizzled1_new = frizzled1 - 1;
    else
      frizzled1_new = frizzled1;
    if ((frizzled1 > dsh1))
      dsh1_new = dsh1 + 1;
    else if ((frizzled1 < dsh1))
      dsh1_new = dsh1 - 1;
    else
      dsh1_new = dsh1;
    if (((3 - dsh1) > axin1))
      axin1_new = axin1 + 1;
    else if ((((3 - dsh1) < axin1) && (axin1 > 0)))
      axin1_new = axin1 - 1;
    else
      axin1_new = axin1;
    if (((3 - axin1) > bcat1))
      bcat1_new = bcat1 + 1;
    else if ((((3 - axin1) < bcat1) && (bcat1 > 0)))
      bcat1_new = bcat1 - 1;
    else
      bcat1_new = bcat1;
    if ((bcat1 > gt1_1))
      gt1_1_new = gt1_1 + 1;
    else if ((bcat1 < gt1_1))
      gt1_1_new = gt1_1 - 1;
    else
      gt1_1_new = gt1_1;
    if ((notchic1 > gt2_1))
      gt2_1_new = gt2_1 + 1;
    else if ((notchic1 < gt2_1))
      gt2_1_new = gt2_1 - 1;
    else
      gt2_1_new = gt2_1;
    if ((gt1_1 + gt2_1 > (2 * delta1)))
      delta1_new = delta1 + 1;
    else if ((gt1_1 + gt2_1 < ((2 * delta1) - 1)))
      delta1_new = delta1 - 1;
    else
      delta1_new = delta1;
    if ((delta0 + delta2 > (2 * deltaext1)))
      deltaext1_new = deltaext1 + 1;
    else if ((delta0 + delta2 < ((2 * deltaext1) - 1)))
      deltaext1_new = deltaext1 - 1;
    else
      deltaext1_new = deltaext1;
    if (((2 > notchic1) && (deltaext1 > notchic1)))
      notchic1_new = notchic1 + 1;
    else if ((2 < notchic1) || (deltaext1 < notchic1))
      notchic1_new = notchic1 - 1;
    else
      notchic1_new = notchic1;
    if ((notchic1 > p21_1))
      p21_1_new = p21_1 + 1;
    else if ((notchic1 < p21_1))
      p21_1_new = p21_1 - 1;
    else
      p21_1_new = p21_1;
    if (((3 - p21_1) > wnt1))
      wnt1_new = wnt1 + 1;
    else if (((3 - p21_1) < wnt1))
      wnt1_new = wnt1 - 1;
    else
      wnt1_new = wnt1;
    if ((wnt1 + wnt3 > 1 + (2 * wntext2)))
      wntext2_new = wntext2 + 1;
    else if ((wnt1 + wnt3 < (2 * wntext2)))
      wntext2_new = wntext2 - 1;
    else
      wntext2_new = wntext2;
    if ((wntext2 > frizzled2))
      frizzled2_new = frizzled2 + 1;
    else if ((wntext2 < frizzled2))
      frizzled2_new = frizzled2 - 1;
    else
      frizzled2_new = frizzled2;
    if ((frizzled2 > dsh2))
      dsh2_new = dsh2 + 1;
    else if ((frizzled2 < dsh2))
      dsh2_new = dsh2 - 1;
    else
      dsh2_new = dsh2;
    if (((3 - dsh2) > axin2))
      axin2_new = axin2 + 1;
    else if ((((3 - dsh2) < axin2) && (axin2 > 0)))
      axin2_new = axin2 - 1;
    else
      axin2_new = axin2;
    if (((3 - axin2) > bcat2))
      bcat2_new = bcat2 + 1;
    else if ((((3 - axin2) < bcat2) && (bcat2 > 0)))
      bcat2_new = bcat2 - 1;
    else
      bcat2_new = bcat2;
    if ((bcat2 > gt1_2))
      gt1_2_new = gt1_2 + 1;
    else if ((bcat2 < gt1_2))
      gt1_2_new = gt1_2 - 1;
    else
      gt1_2_new = gt1_2;
    if ((notchic2 > gt2_2))
      gt2_2_new = gt2_2 + 1;
    else if ((notchic2 < gt2_2))
      gt2_2_new = gt2_2 - 1;
    else
      gt2_2_new = gt2_2;
    if ((gt1_2 + gt2_2 > (2 * delta2)))
      delta2_new = delta2 + 1;
    else if ((gt1_2 + gt2_2 < ((2 * delta2) - 1)))
      delta2_new = delta2 - 1;
    else
      delta2_new = delta2;
    if ((delta1 + delta3 > (2 * deltaext2)))
      deltaext2_new = deltaext2 + 1;
    else if ((delta1 + delta3 < ((2 * deltaext2) - 1)))
      deltaext2_new = deltaext2 - 1;
    else
      deltaext2_new = deltaext2;
    if (((3 > notchic2) && (deltaext2 > notchic2)))
      notchic2_new = notchic2 + 1;
    else if ((3 < notchic2) || (deltaext2 < notchic2))
      notchic2_new = notchic2 - 1;
    else
      notchic2_new = notchic2;
    if ((notchic2 > p21_2))
      p21_2_new = p21_2 + 1;
    else if ((notchic2 < p21_2))
      p21_2_new = p21_2 - 1;
    else
      p21_2_new = p21_2;
    if (((3 - p21_2) > wnt2))
      wnt2_new = wnt2 + 1;
    else if (((3 - p21_2) < wnt2))
      wnt2_new = wnt2 - 1;
    else
      wnt2_new = wnt2;
    if ((wnt2 + wnt4 > 1 + (2 * wntext3)))
      wntext3_new = wntext3 + 1;
    else if ((wnt2 + wnt4 < (2 * wntext3)))
      wntext3_new = wntext3 - 1;
    else
      wntext3_new = wntext3;
    if ((wntext3 > frizzled3))
      frizzled3_new = frizzled3 + 1;
    else if ((wntext3 < frizzled3))
      frizzled3_new = frizzled3 - 1;
    else
      frizzled3_new = frizzled3;
    if ((frizzled3 > dsh3))
      dsh3_new = dsh3 + 1;
    else if ((frizzled3 < dsh3))
      dsh3_new = dsh3 - 1;
    else
      dsh3_new = dsh3;
    if (((3 - dsh3) > axin3))
      axin3_new = axin3 + 1;
    else if ((((3 - dsh3) < axin3) && (axin3 > 0)))
      axin3_new = axin3 - 1;
    else
      axin3_new = axin3;
    if (((3 - axin3) > bcat3))
      bcat3_new = bcat3 + 1;
    else if ((((3 - axin3) < bcat3) && (bcat3 > 0)))
      bcat3_new = bcat3 - 1;
    else
      bcat3_new = bcat3;
    if ((bcat3 > gt1_3))
      gt1_3_new = gt1_3 + 1;
    else if ((bcat3 < gt1_3))
      gt1_3_new = gt1_3 - 1;
    else
      gt1_3_new = gt1_3;
    if ((notchic3 > gt2_3))
      gt2_3_new = gt2_3 + 1;
    else if ((notchic3 < gt2_3))
      gt2_3_new = gt2_3 - 1;
    else
      gt2_3_new = gt2_3;
    if ((gt1_3 + gt2_3 > (2 * delta3)))
      delta3_new = delta3 + 1;
    else if ((gt1_3 + gt2_3 < ((2 * delta3) - 1)))
      delta3_new = delta3 - 1;
    else
      delta3_new = delta3;
    if ((delta2 + delta4 > (2 * deltaext3)))
      deltaext3_new = deltaext3 + 1;
    else if ((delta2 + delta4 < ((2 * deltaext3) - 1)))
      deltaext3_new = deltaext3 - 1;
    else
      deltaext3_new = deltaext3;
    if (((3 > notchic3) && (deltaext3 > notchic3)))
      notchic3_new = notchic3 + 1;
    else if ((3 < notchic3) || (deltaext3 < notchic3))
      notchic3_new = notchic3 - 1;
    else
      notchic3_new = notchic3;
    if ((notchic3 > p21_3))
      p21_3_new = p21_3 + 1;
    else if ((notchic3 < p21_3))
      p21_3_new = p21_3 - 1;
    else
      p21_3_new = p21_3;
    if (((3 - p21_3) > wnt3))
      wnt3_new = wnt3 + 1;
    else if (((3 - p21_3) < wnt3))
      wnt3_new = wnt3 - 1;
    else
      wnt3_new = wnt3;
    if ((wnt3 + 0 > 1 + (2 * wntext4)))
      wntext4_new = wntext4 + 1;
    else if ((wnt3 + 0 < (2 * wntext4)))
      wntext4_new = wntext4 - 1;
    else
      wntext4_new = wntext4;
    if ((wntext4 > frizzled4))
      frizzled4_new = frizzled4 + 1;
    else if ((wntext4 < frizzled4))
      frizzled4_new = frizzled4 - 1;
    else
      frizzled4_new = frizzled4;
    if ((frizzled4 > dsh4))
      dsh4_new = dsh4 + 1;
    else if ((frizzled4 < dsh4))
      dsh4_new = dsh4 - 1;
    else
      dsh4_new = dsh4;
    if (((3 - dsh4) > axin4))
      axin4_new = axin4 + 1;
    else if ((((3 - dsh4) < axin4) && (axin4 > 0)))
      axin4_new = axin4 - 1;
    else
      axin4_new = axin4;
    if (((3 - axin4) > bcat4))
      bcat4_new = bcat4 + 1;
    else if ((((3 - axin4) < bcat4) && (bcat4 > 0)))
      bcat4_new = bcat4 - 1;
    else
      bcat4_new = bcat4;
    if ((bcat4 > gt1_4))
      gt1_4_new = gt1_4 + 1;
    else if ((bcat4 < gt1_4))
      gt1_4_new = gt1_4 - 1;
    else
      gt1_4_new = gt1_4;
    if ((notchic4 > gt2_4))
      gt2_4_new = gt2_4 + 1;
    else if ((notchic4 < gt2_4))
      gt2_4_new = gt2_4 - 1;
    else
      gt2_4_new = gt2_4;
    if ((gt1_4 + gt2_4 > (2 * delta4)))
      delta4_new = delta4 + 1;
    else if ((gt1_4 + gt2_4 < ((2 * delta4) - 1)))
      delta4_new = delta4 - 1;
    else
      delta4_new = delta4;
    if ((delta3 + 2 > (2 * deltaext4)))
      deltaext4_new = deltaext4 + 1;
    else if ((delta3 + 2 < ((2 * deltaext4) - 1)))
      deltaext4_new = deltaext4 - 1;
    else
      deltaext4_new = deltaext4;
    if (((3 > notchic4) && (deltaext4 > notchic4)))
      notchic4_new = notchic4 + 1;
    else if ((3 < notchic4) || (deltaext4 < notchic4))
      notchic4_new = notchic4 - 1;
    else
      notchic4_new = notchic4;
    if ((notchic4 > p21_4))
      p21_4_new = p21_4 + 1;
    else if ((notchic4 < p21_4))
      p21_4_new = p21_4 - 1;
    else
      p21_4_new = p21_4;
    if (((3 - p21_4) > wnt4))
      wnt4_new = wnt4 + 1;
    else if (((3 - p21_4) < wnt4))
      wnt4_new = wnt4 - 1;
    else
      wnt4_new = wnt4;

    // Terminates?
    if (
	wntext0 == wntext0_new
	&& frizzled0 == frizzled0_new
	&& dsh0 == dsh0_new
	&& axin0 == axin0_new
	&& bcat0 == bcat0_new
	&& gt1_0 == gt1_0_new
	&& gt2_0 == gt2_0_new
	&& delta0 == delta0_new
	&& deltaext0 == deltaext0_new
	&& notchic0 == notchic0_new
	&& p21_0 == p21_0_new
	&& wnt0 == wnt0_new
	&& wntext1 == wntext1_new
	&& frizzled1 == frizzled1_new
	&& dsh1 == dsh1_new
	&& axin1 == axin1_new
	&& bcat1 == bcat1_new
	&& gt1_1 == gt1_1_new
	&& gt2_1 == gt2_1_new
	&& delta1 == delta1_new
	&& deltaext1 == deltaext1_new
	&& notchic1 == notchic1_new
	&& p21_1 == p21_1_new
	&& wnt1 == wnt1_new
	&& wntext2 == wntext2_new
	&& frizzled2 == frizzled2_new
	&& dsh2 == dsh2_new
	&& axin2 == axin2_new
	&& bcat2 == bcat2_new
	&& gt1_2 == gt1_2_new
	&& gt2_2 == gt2_2_new
	&& delta2 == delta2_new
	&& deltaext2 == deltaext2_new
	&& notchic2 == notchic2_new
	&& p21_2 == p21_2_new
	&& wnt2 == wnt2_new
	&& wntext3 == wntext3_new
	&& frizzled3 == frizzled3_new
	&& dsh3 == dsh3_new
	&& axin3 == axin3_new
	&& bcat3 == bcat3_new
	&& gt1_3 == gt1_3_new
	&& gt2_3 == gt2_3_new
	&& delta3 == delta3_new
	&& deltaext3 == deltaext3_new
	&& notchic3 == notchic3_new
	&& p21_3 == p21_3_new
	&& wnt3 == wnt3_new
	&& wntext4 == wntext4_new
	&& frizzled4 == frizzled4_new
	&& dsh4 == dsh4_new
	&& axin4 == axin4_new
	&& bcat4 == bcat4_new
	&& gt1_4 == gt1_4_new
	&& gt2_4 == gt2_4_new
	&& delta4 == delta4_new
	&& deltaext4 == deltaext4_new
	&& notchic4 == notchic4_new
	&& p21_4 == p21_4_new
	&& wnt4 == wnt4_new

	) break;

/*     if (copied) { */
/*       if (!( */
/* 	    0 */
/* 	    )) slic_error(); */
/*     } else if (nondet()) { */
/*       copied=1; */
/*     } */

    // Update: new = old.
    wntext0 = wntext0_new;
    frizzled0 = frizzled0_new;
    dsh0 = dsh0_new;
    axin0 = axin0_new;
    bcat0 = bcat0_new;
    gt1_0 = gt1_0_new;
    gt2_0 = gt2_0_new;
    delta0 = delta0_new;
    deltaext0 = deltaext0_new;
    notchic0 = notchic0_new;
    p21_0 = p21_0_new;
    wnt0 = wnt0_new;
    wntext1 = wntext1_new;
    frizzled1 = frizzled1_new;
    dsh1 = dsh1_new;
    axin1 = axin1_new;
    bcat1 = bcat1_new;
    gt1_1 = gt1_1_new;
    gt2_1 = gt2_1_new;
    delta1 = delta1_new;
    deltaext1 = deltaext1_new;
    notchic1 = notchic1_new;
    p21_1 = p21_1_new;
    wnt1 = wnt1_new;
    wntext2 = wntext2_new;
    frizzled2 = frizzled2_new;
    dsh2 = dsh2_new;
    axin2 = axin2_new;
    bcat2 = bcat2_new;
    gt1_2 = gt1_2_new;
    gt2_2 = gt2_2_new;
    delta2 = delta2_new;
    deltaext2 = deltaext2_new;
    notchic2 = notchic2_new;
    p21_2 = p21_2_new;
    wnt2 = wnt2_new;
    wntext3 = wntext3_new;
    frizzled3 = frizzled3_new;
    dsh3 = dsh3_new;
    axin3 = axin3_new;
    bcat3 = bcat3_new;
    gt1_3 = gt1_3_new;
    gt2_3 = gt2_3_new;
    delta3 = delta3_new;
    deltaext3 = deltaext3_new;
    notchic3 = notchic3_new;
    p21_3 = p21_3_new;
    wnt3 = wnt3_new;
    wntext4 = wntext4_new;
    frizzled4 = frizzled4_new;
    dsh4 = dsh4_new;
    axin4 = axin4_new;
    bcat4 = bcat4_new;
    gt1_4 = gt1_4_new;
    gt2_4 = gt2_4_new;
    delta4 = delta4_new;
    deltaext4 = deltaext4_new;
    notchic4 = notchic4_new;
    p21_4 = p21_4_new;
    wnt4 = wnt4_new;
  } // while


  return 0;
}
