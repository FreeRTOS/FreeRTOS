/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
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

/******************************************************************************
 * NOTE 1:  This project provides three demo applications.  A simple blinky
 * style project, a more comprehensive test and demo application, and an
 * lwIP example.  The mainSELECTED_APPLICATION setting in main.c is used to
 * select between the three.  See the notes on using mainSELECTED_APPLICATION
 * in main.c.  This file implements the simply blinky style version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * basic demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware are defined in main.c.
 ******************************************************************************
 *
 * The lwIP example can be configured to use either a static or dynamic IP
 * address:
 *    + To use a dynamically allocated IP address set LWIP_DHCP to 1 in
 *      lwipopts.h and connect the target to a network that includes a DHCP
 *      server.  The obtained IP address is printed to the UART console.
 *    + To use a static IP address set LWIP_DHCP to 0 in lwipopts.h and set
 *      the static IP address using the configIP_ADDR0 to configIP_ADDR3
 *      constants at the bottom of FreeRTOSConfig.h.  Constants used to define
 *      a netmask are also located at the bottom of FreeRTOSConfig.h.
 *
 * When connected correctly the demo uses the lwIP sockets API to create
 * a FreeRTOS+CLI command console, and the lwIP raw API to create a basic HTTP
 * web server with server side includes that generate dynamic run time web
 * pages.  See http://www.freertos.org/RTOS-Xilinx-Zynq.html for more
 * information.
 *
 * To connect to FreeRTOS+CLI, open a command prompt and enter "telnet <ipaddr>"
 * where <ipaddr> is the IP address of the target.  Once connected type "help"
 * to see a list of registered commands.  Note this example does not implement
 * a real telnet server, it just uses the telnet port number to allow easy
 * connection using telnet tools.
 *
 * To connect to the http server simply type the IP address of the target into
 * the address bar of a web browser.
 *
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Standard demo includes. */
#include "partest.h"

/* lwIP includes. */
#include "lwip/tcpip.h"

/* The rate at which data is sent to the queue.  The 200ms value is converted
to ticks using the portTICK_PERIOD_MS constant. */
#define mainTIMER_PERIOD_MS			( pdMS_TO_TICKS( 200 ) )

/* The LED toggled by the Rx task. */
#define mainTIMER_LED				( 0 )

/* A block time of zero just means "don't block". */
#define mainDONT_BLOCK				( 0 )

/*-----------------------------------------------------------*/

/*
 * The callback for the timer that just toggles an LED to show the system is
 * running.
 */
static void prvLEDToggleTimer( TimerHandle_t pxTimer );

/*
 * Defined in lwIPApps.c.
 */
extern void lwIPAppsInit( void *pvArguments );

/*-----------------------------------------------------------*/

void main_lwIP( void )
{
TimerHandle_t xTimer;

	/* Init lwIP and start lwIP tasks. */
	tcpip_init( lwIPAppsInit, NULL );

	/* A timer is used to toggle an LED just to show the application is
	executing. */
	xTimer = xTimerCreate( 	"LED", 					/* Text name to make debugging easier. */
							mainTIMER_PERIOD_MS, 	/* The timer's period. */
							pdTRUE,					/* This is an auto reload timer. */
							NULL,					/* ID is not used. */
							prvLEDToggleTimer );	/* The callback function. */

	/* Start the timer. */
	configASSERT( xTimer );
	xTimerStart( xTimer, mainDONT_BLOCK );

	/* Start the tasks and timer running. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the Idle and/or
	timer tasks to be created.  See the memory management section on the
	FreeRTOS web site for more details on the FreeRTOS heap
	http://www.freertos.org/a00111.html. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvLEDToggleTimer( TimerHandle_t pxTimer )
{
	/* Prevent compiler warnings. */
	( void ) pxTimer;

	/* Just toggle an LED to show the application is running. */
	vParTestToggleLED( mainTIMER_LED );
}

/*-----------------------------------------------------------*/

char *pcMainGetTaskStatusMessage( void )
{
	return "Running lwIP demo";
}
/*-----------------------------------------------------------*/
