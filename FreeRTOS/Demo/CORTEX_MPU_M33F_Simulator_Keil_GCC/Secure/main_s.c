/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Use CMSE intrinsics */
#include <arm_cmse.h>
#include "RTE_Components.h"
#include CMSIS_device_header

/* FreeRTOS includes. */
#include "secure_port_macros.h"

/* Start address of non-secure application. */
#define mainNONSECURE_APP_START_ADDRESS		( 0x200000U )

/* typedef for non-secure Reset Handler. */
typedef void ( *NonSecureResetHandler_t )	( void ) __attribute__( ( cmse_nonsecure_call ) );
/*-----------------------------------------------------------*/

/* Boot into the non-secure code. */
void BootNonSecure( uint32_t ulNonSecureStartAddress );
/*-----------------------------------------------------------*/

/*
 *	Instructions to Build and Run:
 *	 - The Keil multi-project workspace FreeRTOSDemo.uvmpw contains projects for
 *	   both the secure project, and non secure project.
 *	 - Set the FreeRTOSDemo_s project as Active - Right click on
 *	   "Project: FreeRTOSDemo_s" and select "Set as Active Project".
 *	 - Build the FreeRTOSDemo_s project using "Project --> Build" or by pressing
 *	   "F7".
 *	 - Set the FreeRTOSDemo_ns project as Active - Right click on
 *	   "Project: FreeRTOSDemo_ns" and select "Set as Active Project".
 *	 - Build the FreeRTOSDemo_ns project using "Project --> Build" or by
 *	   pressing "F7".
 *	 - Start Debug Session using "Debug -> Start/Stop Debug Session" or by
 *	   pressing "Ctrl+F5".
 */

/* Secure main() */
int main( void )
{
	/* Boot the non-secure code. */
	BootNonSecure( mainNONSECURE_APP_START_ADDRESS );

	/* Non-secure software does not return, this code is not executed. */
	for( ; ; )
	{
		/* Should not reach here. */
	}
}
/*-----------------------------------------------------------*/

void BootNonSecure( uint32_t ulNonSecureStartAddress )
{
	NonSecureResetHandler_t pxNonSecureResetHandler;

	/* Main Stack Pointer value for the non-secure side is the first entry in
	 * the non-secure vector table. Read the first entry and assign the same to
	 * the non-secure main stack pointer(MSP_NS). */
	secureportSET_MSP_NS( *( ( uint32_t * )( ulNonSecureStartAddress ) ) );

	/* Non secure Reset Handler is the second entry in the non-secure vector
	 * table. Read the non-secure reset handler.
	 */
	pxNonSecureResetHandler = ( NonSecureResetHandler_t )( * ( ( uint32_t * ) ( ( ulNonSecureStartAddress ) + 4U ) ) );

	/* Start non-secure software application by jumping to the non-secure Reset
	 * Handler. */
	pxNonSecureResetHandler();
}
/*-----------------------------------------------------------*/

