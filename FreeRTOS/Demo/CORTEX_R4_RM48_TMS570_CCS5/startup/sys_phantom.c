/** @file sys_phantom.c 
*   @brief Phantom Interrupt Source File
*   @date 15.July.2009
*   @version 1.00.000
*
*   This file contains:
*   - Phantom Interrupt Handler
*/

#include "gio.h"
#include "het.h"


/* Phantom Interrupt Handler */

#pragma INTERRUPT(phantomInterrupt, IRQ)

void phantomInterrupt(void)
{
	/* too indicate we are in the phantom interrupt light up the BLUE leds */

	/* Initalise the IO ports that drive the LEDs */
	gioSetDirection(hetPORT, 0xFFFFFFFF);
	/* switch all leds off */
	gioSetPort(hetPORT, 0x08110034);
	/* switch on blue leds */
	gioSetBit(hetPORT,  5, 0);
	gioSetBit(hetPORT, 27, 0);

	for(;;);
}
