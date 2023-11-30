/** @file sys_esm.c
*   @brief Phantom Interrupt Source File
*   @date 15.July.2009
*   @version 1.00.000
*
*   This file contains:
*   - Phantom Interrupt Handler
*/

#include "gio.h"
#include "het.h"


/* ESM (Non-Maskable) Interrupt Handler */

#pragma INTERRUPT(esmHighLevelInterrupt, FIQ)

void esmHighLevelInterrupt(void)
{
	/* too indicate we are in the ESM interrupt light up the BLUE leds */

	/* Initalise the IO ports that drive the LEDs */
	gioSetDirection(hetPORT, 0xFFFFFFFF);
	/* switch all leds off */
	gioSetPort(hetPORT, 0x08110034);
	/* switch on blue leds */
	gioSetBit(hetPORT,  5, 0);
	gioSetBit(hetPORT, 27, 0);

	for(;;);
}
