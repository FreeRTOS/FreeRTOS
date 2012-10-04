/** @file sys_phantom.c 
*   @brief Phantom Interrupt Source File
*   @date 15.July.2009
*   @version 1.00.000
*
*   This file contains:
*   - Phantom Interrupt Handler
*/

/* (c) Texas Instruments 2009, All rights reserved. */

/* Phantom Interrupt Handler */

#pragma INTERRUPT(phantomInterrupt, IRQ)

void phantomInterrupt(void)
{
	for(;;);
}
