/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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

