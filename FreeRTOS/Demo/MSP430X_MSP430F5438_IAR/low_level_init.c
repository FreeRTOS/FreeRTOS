/**************************************************
 *
 * This is a template for early application low-level initialization.
 *
 * Copyright 1996-2010 IAR Systems AB.
 *
 * $Revision: 5993 $
 *
 **************************************************/

/*
 * The function __low_level_init it called by the start-up code before
 * "main" is called, and before data segment initialization is
 * performed.
 *
 * This is a template file, modify to perform any initialization that
 * should take place early.
 *
 * The return value of this function controls if data segment
 * initialization should take place. If 0 is returned, it is bypassed.
 *
 * For the MSP430 microcontroller family, please consider disabling
 * the watchdog timer here, as it could time-out during the data
 * segment initialization.
 */

/*
 * To disable the watchdog timer, include a suitable device header
 * file (or "msp430.h") and add the following line to the function
 * below:
 *
 *     WDTCTL = WDTPW+WDTHOLD;
 *
 */


#include <intrinsics.h>
#include "msp430.h"

int __low_level_init(void)
{
  /* Insert your low-level initializations here */
  _DINT();
  WDTCTL = WDTPW+WDTHOLD;


  /*
   * Return value:
   *
   *  1 - Perform data segment initialization.
   *  0 - Skip data segment initialization.
   */

  return 1;
}
