/*
  This file is for syndrome computation
*/

#include "../imp/synd.h"

#include "../imp/params.h"
#include "../imp/root.h"

#include <stdio.h>

/* input: Goppa polynomial f, support L, received word r */
/* output: out, the syndrome of length 2t */
void synd(gf *out, gf *f, gf *L, unsigned char *r)
{
	int i, j;
	gf e, e_inv, c;

	for (j = 0; j < 2*SYS_T; j++)
		out[j] = 0;

	for (i = 0; i < SYS_N; i++)
	{
		c = (r[i/8] >> (i%8)) & 1;

		e = eval(f, L[i]);
		e_inv = gf_inv(gf_mul(e,e));

		for (j = 0; j < 2*SYS_T; j++)
		{
			out[j] = gf_add(out[j], gf_mul(e_inv, c));
			e_inv = gf_mul(e_inv, L[i]);
		}
	}
}

void synd_loop(gf *out, gf *f, gf li, gf c)
{
  int j;
	gf e, e_inv;
  e = eval(f, li);
  e_inv = gf_inv(gf_mul(e,e));

  for (j = 0; j < 2*SYS_T; j++)
  {
    out[j] = gf_add(out[j], gf_mul(e_inv, c));
    e_inv = gf_mul(e_inv, li);
  }
}

void synd_loop_2(gf *out, gf *f, gf li, gf c)
{
  int j;
	gf e, e_inv;
  e = eval(f, li);
  e_inv = gf_mul(gf_inv(gf_mul(e,e)), c);

  for (j = 0; j < 2*SYS_T; j++)
  {
    out[j] = gf_add(out[j], e_inv);
    e_inv = gf_mul(e_inv, li);
  }
}

void synd_outer(gf *out, gf *f, gf *L, unsigned char *r)
{
	int i;
	gf c, li;

	for (i = 0; i < 2*SYS_T; i++)
		out[i] = 0;

	for (i = 0; i < SYS_N; i++)
	{
		c = (r[i/8] >> (i%8)) & 1;
    li = L[i];
    synd_loop(out, f, li, c);
	}
}