/*
    FreeRTOS V8.0.0 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#include "FreeRTOS.h"
#include "Task.h"
#include "gio.h"
#include "het.h"

/*
 * Task that flashes the LEDS on the USB stick.
 *
 * This task is also run in Thumb mode to test the ARM/THUMB context switch
 */

#pragma TASK(vLedTask)
#pragma CODE_STATE(vLedTask, 16)

void vLedTask(void *pvParameters)
{
	unsigned led    = 0;
	unsigned count  = 0;
	unsigned colour = 0;

	/* Initalise the IO ports that drive the LEDs */
	gioSetDirection(hetPORT, 0xFFFFFFFF);
	/* switch all leds off */
	gioSetPort(hetPORT, 0x08110034);

	for(;;)
	{
		/* toggle on/off */
		led ^= 1;
		/* switch TOP row */
		gioSetBit(hetPORT, 25, led);
		gioSetBit(hetPORT, 18, led);
		gioSetBit(hetPORT, 29, led);
		/* switch BOTTOM row */
		gioSetBit(hetPORT, 17, led ^ 1);
		gioSetBit(hetPORT, 31, led ^ 1);
		gioSetBit(hetPORT,  0, led ^ 1);
		vTaskDelay(500);

		if (++count > 5)
		{
			count = 0;
			/* both leds to off */
			gioSetBit(hetPORT, 2, 1);  gioSetBit(hetPORT,  5, 1);  gioSetBit(hetPORT, 20, 1);
			gioSetBit(hetPORT, 4, 1);  gioSetBit(hetPORT, 27, 1);  gioSetBit(hetPORT, 16, 1);
			switch(colour)
			{
			case 0:
				gioSetBit(hetPORT, 2, 0);  /* red */
				gioSetBit(hetPORT, 4, 0);
				colour++;
				continue;
			case 1:
				gioSetBit(hetPORT,  5, 0);  /* blue */
				gioSetBit(hetPORT, 27, 0);
				colour++;
				continue;
			case 2:
				gioSetBit(hetPORT, 20, 0);  /* green */
				gioSetBit(hetPORT, 16, 0);
				colour++;
				continue;
			}
			colour = 0;
		}
	}
}

