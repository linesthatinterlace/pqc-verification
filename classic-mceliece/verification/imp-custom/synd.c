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

/*
synd_2 : [SYS_T_t + 1]gf_t -> [SYS_N_t]gf_t -> [SYS_N_t/8][8] -> [2*SYS_T_t]gf_t
synd_2 f L r = last zss
  where zss = [zero] # [ if c then synd_loop_2 e li zs else zs | zs <- zss | i <- [0 .. SYS_N_t - 1] | e <- root f L | li <- L | c <- reverse <~ loadbytes r]

synd_loop_2 : gf_t -> gf_t -> [2*SYS_T_t]gf_t -> [2*SYS_T_t]gf_t
synd_loop_2 e li in = [ gf_add z e_inv | z <- in | e_inv <- e_invs ]
  where e_invs = [gf_inv (gf_mul e e)] # [ gf_mul e_inv li | e_inv <- e_invs ]

synd_loop : {ix} (Integral ix, Literal 8 ix) => [SYS_T_t + 1]gf_t -> [SYS_N_t]gf_t -> [SYS_N_t/8][8] -> ix -> [2*SYS_T_t]gf_t -> [2*SYS_T_t]gf_t
synd_loop f L r i in = [ gf_add z (gf_mul e_inv c) | z <- in | e_inv <- e_invs ]
  where c = zext (((r@(i/8)) >> (i%8)) && 1)
        li = L@i
        e = eval f li
        e_inv_pre = gf_inv (gf_mul e e)
        e_invs = [e_inv_pre] # [ gf_mul e_inv li | e_inv <- e_invs ]

A draft version of it that isn't constant time but might run a bit quicker as a result (need to test), plus a development version that has the internals exposed (can probably scrap).
synd' : [SYS_T_t + 1]gf_t -> [SYS_N_t]gf_t -> [SYS_N_t/8][8] -> [2*SYS_T_t]gf_t
synd' f L r = last zs
  where zs = [zero] # [ update_i z i | z <- zs | i <- [0 .. SYS_N_t - 1]]
        r' = loadbytes r
        update_i z i = if r' ! i then [ gf_add x ei | x <- z | ei <- e_invs ] else z
          where li = L@i
                e = eval f li
                e_inv_pre = gf_inv (gf_mul e e)
                e_invs = iterate (\x -> gf_mul x li) e_inv_pre

synd'' : [SYS_T_t + 1]gf_t -> [SYS_N_t]gf_t -> [SYS_N_t/8][8] -> [2*SYS_T_t]gf_t
synd'' f L r = synd_outer_loop f L r zero

synd_outer_loop : [SYS_T_t + 1]gf_t -> [SYS_N_t]gf_t -> [SYS_N_t/8][8] -> [2*SYS_T_t]gf_t -> [2*SYS_T_t]gf_t
synd_outer_loop f L r state = foldr (synd_outer_loop_body f L r) state [0 .. SYS_N_t - 1]

synd_outer_loop_body : {ix} (Integral ix, Literal 8 ix) => [SYS_T_t + 1]gf_t -> [SYS_N_t]gf_t -> [SYS_N_t/8][8] -> ix -> [2*SYS_T_t]gf_t -> [2*SYS_T_t]gf_t
synd_outer_loop_body f L r i state = (synd_inner_loop c li {e_inv = e_inv_pre, o = state}).o
  where c = zext (((r@(i/8)) >> (i%8)) && 1)
        li = (L@i)
        e = eval f li
        e_inv_pre = gf_inv (gf_mul e e)
      
synd_inner_loop : gf_t -> gf_t -> {e_inv : gf_t, o : [2*SYS_T_t]gf_t} -> {e_inv : gf_t, o : [2*SYS_T_t]gf_t}
synd_inner_loop c li state = foldr (synd_inner_loop_body c li) state [0 .. 2*SYS_T_t - 1]

synd_inner_loop_body : {ix} (Integral ix, Literal 64 ix) => gf_t -> gf_t -> ix -> {e_inv : gf_t, o : [2*SYS_T_t]gf_t} -> {e_inv : gf_t, o : [2*SYS_T_t]gf_t}
synd_inner_loop_body c li j state = {e_inv = e_inv_post, o = o_post}
  where o_post = if c == 0x0001 then updateEnd state.o j (gf_add ((state.o)!j) state.e_inv) else state.o
        e_inv_post = gf_mul state.e_inv li

property c_f_p b i = c_f_1 b i == c_f_2 b i

c_f_1 : [SYS_N_t/8][8] -> [width SYS_N_t] -> gf_t
c_f_1 r i = if (i < SYS_N) then zext (((r@(i/8)) >> (i%8)) && 1) else zero

c_f_2 : [SYS_N_t/8][8] -> [width SYS_N_t] -> gf_t
c_f_2 r i = if (i < SYS_N) then zext [(loadbytes r) ! i] else zero

void synd_loop_2(gf *out, gf e, gf li)
{
  int j;
	gf e_inv;

  e_inv = gf_inv(gf_mul(e,e));
  for (j = 0; j < 2*SYS_T; j++)
  {
    out[j] = gf_add(out[j], e_inv);
    e_inv = gf_mul(e_inv, li);
  }
}

void synd_outer_2(gf *out, gf *f, gf *L, unsigned char *r)
{
	int i;

  gf rootL[SYS_N];

  root(rootL, f, L);

	for (i = 0; i < 2*SYS_T; i++)
		out[i] = 0;

	for (i = 0; i < SYS_N; i++)
	  if ((r[i/8] >> (i%8)) & 1) { synd_loop_2(out, rootL[i], L[i]); }
}

void synd_loop(gf *out, gf *f, gf *L, unsigned char *r, size_t i)
{
  int j;
	gf c, li, e, e_inv;

  c = (r[i/8] >> (i%8)) & 1;
  li = L[i];
  e = eval(f, li);
  e_inv = gf_inv(gf_mul(e,e));

  for (j = 0; j < 2*SYS_T; j++)
  {
    out[j] = gf_add(out[j], gf_mul(e_inv, c));
    e_inv = gf_mul(e_inv, li);
  }
}

void synd_outer(gf *out, gf *f, gf *L, unsigned char *r)
{
	int i;

	for (i = 0; i < 2*SYS_T; i++)
		out[i] = 0;

	for (i = 0; i < SYS_N; i++)
    synd_loop(out, f, L, r, i);
}

let synd_loop_2_spec = do {
  // Initialise variable(s).
  (in_v, pin) <- ptr_to_fresh "in" (llvm_array (eval_int {{2*SYS_T : [width 2*SYS_T_t]}}) gf_type);
  li <- llvm_fresh_var "li" gf_type;
  e <- llvm_fresh_var "e" gf_type;

  // Run function.
  llvm_execute_func [pin, llvm_term li, llvm_term e];

  // Result is equivalent to Cryptol function.
  llvm_points_to pin (llvm_term {{ synd_loop_2 li e in_v }});
};

let synd_2_spec = do {
  // Initialise variable(s).
  pout <- llvm_alloc (llvm_array (eval_int {{2*SYS_T : [width 2*SYS_T_t]}}) gf_type);
  (f, pf) <- ptr_to_fresh_readonly "f" (llvm_array (eval_int {{SYS_T + 1 : [width (SYS_T_t + 1)]}}) gf_type);
  (L, pL) <- ptr_to_fresh_readonly "L" (llvm_array SYS_N gf_type);
  (r, pr) <- ptr_to_fresh_readonly "r" (llvm_array (eval_int {{SYS_N/8 : [width SYS_N_t]}}) (llvm_int 8));

  // Run function.
  llvm_execute_func [pout, pf, pL, pr];

  // Result is equivalent to Cryptol function.
  llvm_points_to pout (llvm_term {{ synd_2 f L r }});
};
*/