#include <stdint.h>

#define SIZE 64

void test_plus(uint16_t *out, uint16_t *in0, uint16_t *in1)
{
  for (int i = 0; i < SIZE; i++)
    out[i] = in0[i] + in1[i];
}

void test_mult(uint16_t *out, uint16_t *in0, uint16_t *in1)
{
  for (int i = 0; i < SIZE; i++)
    out[i] = in0[i] * in1[i];
}

void test_dual(uint16_t *out, uint16_t *in0, uint16_t *in1)
{

    int i, j;

	uint16_t prod[SIZE*2-1];

  for (i = 0; i < 2*SIZE - 1; i++)
	  prod[i] = 0;

  
  for (i = 0; i < SIZE; i++)
    for (j = 0; j < SIZE; j++)
      prod[i+j] ^= in0[i]*in1[j]; 

  for (i = 0; i < SIZE*2-1; i++)
		out[i] = prod[i];

}