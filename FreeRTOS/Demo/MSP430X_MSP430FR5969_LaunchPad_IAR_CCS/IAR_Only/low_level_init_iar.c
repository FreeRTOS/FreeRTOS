/*******************************************************************************
 *

 * This is a template for early application low-level initialization.
 *
 * The following license agreement applies to linker command files,
 * example projects (unless another license is explicitly stated), the
 * cstartup code, low_level_init.c, and some other low-level runtime
 * library files.
 *
 *
 * Copyright 2013, IAR Systems AB.
 *
 * This source code is the property of IAR Systems. The source code may only
 * be used together with the IAR Embedded Workbench. Redistribution and use
 * in source and binary forms, with or without modification, is permitted
 * provided that the following conditions are met:
 *
 * - Redistributions of source code, in whole or in part, must retain the
 * above copyright notice, this list of conditions and the disclaimer below.
 *
 * - IAR Systems name may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 ******************************************************************************/

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

#include <intrinsics.h>
#include "msp430.h"

int __low_level_init(void)
{
  /* Insert your low-level initializations here */
  WDTCTL = WDTPW | WDTHOLD;
  
  /*
   * Return value:
   *
   *  1 - Perform data segment initialization.
   *  0 - Skip data segment initialization.
   */

  return 1;
}
