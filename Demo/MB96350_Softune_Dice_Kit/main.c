/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "Task.h"

/* Demo includes. */
#include "DiceTask.h"
#include "ParTest.h"
#include "Flash.h"

static void prvSetupHardware( void );

#define mainDISPLAY_1		0
#define mainDISPLAY_2		1

#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
/*-----------------------------------------------------------*/

void main( void )
{
	prvSetupHardware();

	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );

	xTaskCreate( vDiceTask, ( signed char * ) "Dice1", configMINIMAL_STACK_SIZE, ( void * ) mainDISPLAY_1, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vDiceTask, ( signed char * ) "Dice2", configMINIMAL_STACK_SIZE, ( void * ) mainDISPLAY_2, tskIDLE_PRIORITY, NULL );

	vTaskStartScheduler();

	while( 1 );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Setup interrupt hardware - interrupts are kept disabled for now to
	prevent any interrupts attempting to cause a context switch before the
	scheduler has been started. */
	InitIrqLevels();
	portDISABLE_INTERRUPTS();
	__set_il( 7 );	

	/* Enable P00_0/INT8 and P00_1/INT9 as input. */
	PIER00 = 0x03;
	PDR00  = 0x00;
	DDR00  = 0xfc;

	/* Set Port3 as output (7Segment Display). */
	DDR03  = 0xff;

	/* Enable P04_2/RX as input. */
	PIER04 = 0x04;

	/* CAN TX = 1. */
	PDR04  = 0x08;

	/* CAN RX = input. */
	DDR04  = 0xfb;

	/* All inputs are disabled on this port. */
	PIER05 = 0x00;

	/* Use Port 5 as I/O-Port. */
	ADER1  = 0;
	PDR05  = 0x7f;

	/* Set Port5 as output (7Segment Display). */
	DDR05  = 0xff;

	/* Disable inputs on the following ports. */
	PIER02 = 0x00;
	PDR02  = 0x00;
	DDR02  = 0xff;
	PIER03 = 0x00;
	PDR03  = 0xff;
	PIER06 = 0x00;
	PDR06  = 0x00;
	DDR06  = 0xff;
}

