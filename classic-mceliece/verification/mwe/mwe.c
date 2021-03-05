#include <stdint.h>

uint16_t weird_add (uint16_t *a, uint16_t in0)
{
  in0 += a[0];
  return in0;
}

void pair_weird_add(uint16_t *out, uint16_t *a, uint16_t *L)
{
  out[0] = weird_add(a, L[0]);
  out[1] = weird_add(a, L[1]);
}