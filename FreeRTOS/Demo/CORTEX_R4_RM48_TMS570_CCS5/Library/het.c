/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#include "FreeRTOS.h"
#include "task.h"
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

