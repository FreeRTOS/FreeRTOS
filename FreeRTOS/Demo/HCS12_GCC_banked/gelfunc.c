/* gelfunc.c -- functions from GEL 1.6
   Author Jefferson Smith, Robotronics Inc.

*/

#include "asm-m68hcs12/ports_def.h"
void cop_reset (void);
void cop_optional_reset (void);

/* Reset the COP.  */
void
cop_reset (void)
{
  ARMCOP = 0x55;
  ARMCOP = 0xAA;
}

void
cop_optional_reset (void)
{
#if defined(M6811_USE_COP) && M6811_USE_COP == 1
  cop_reset ();
#endif
}

