/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware includes. */
#include <microblaze_exceptions_i.h>
#include <microblaze_exceptions_g.h>

#define portexR3_STACK_OFFSET	4
#define portexR4_STACK_OFFSET	5
#define portexR5_STACK_OFFSET	6
#define portexR6_STACK_OFFSET	7
#define portexR7_STACK_OFFSET	8
#define portexR8_STACK_OFFSET	9
#define portexR9_STACK_OFFSET	10
#define portexR10_STACK_OFFSET	11
#define portexR11_STACK_OFFSET	12
#define portexR12_STACK_OFFSET	13
#define portexR15_STACK_OFFSET	16
#define portexR18_STACK_OFFSET  18
#define portexMSR_STACK_OFFSET	19
#define portexR19_STACK_OFFSET  -1

#define portexESR_DS_MASK		0x00001000UL

#define portexASM_HANDLER_STACK_FRAME_SIZE 84UL

/* Exclude the entire file if the MicroBlaze is not configured to handle
exceptions, or the application defined configuration item 
configINSTALL_EXCEPTION_HANDLERS is not set to 1. */
#if ( MICROBLAZE_EXCEPTIONS_ENABLED == 1 ) && ( configINSTALL_EXCEPTION_HANDLERS == 1 )

/* These are global volatiles to allow their inspection by a debugger. */
unsigned long *pulStackPointerOnFunctionEntry = NULL, ulBTROnFunctionEntry = 0UL;

static xPortRegisterDump xRegisterDump;

void vPortExceptionHandler( void *pvExceptionID );
extern void vPortExceptionHandlerEntry( void *pvExceptionID );

/*-----------------------------------------------------------*/
extern void vApplicationExceptionRegisterDump( xPortRegisterDump *xRegisterDump ) __attribute__((weak));
void vApplicationExceptionRegisterDump( xPortRegisterDump *xRegisterDump )
{
	for( ;; )
	{
		portNOP();
	}
}
/*-----------------------------------------------------------*/

void vPortExceptionHandler( void *pvExceptionID )
{
extern void *pxCurrentTCB;

	xRegisterDump.xCurrentTaskHandle = pxCurrentTCB;
	xRegisterDump.pcCurrentTaskName = pcTaskGetTaskName( NULL );

	configASSERT( pulStackPointerOnFunctionEntry );

	/* Obtain the values of registers that were stacked prior to this function
	being called, and may have changed since they were stacked. */
	xRegisterDump.ulR3 = pulStackPointerOnFunctionEntry[ portexR3_STACK_OFFSET ];
	xRegisterDump.ulR4 = pulStackPointerOnFunctionEntry[ portexR4_STACK_OFFSET ];
	xRegisterDump.ulR5 = pulStackPointerOnFunctionEntry[ portexR5_STACK_OFFSET ];
	xRegisterDump.ulR6 = pulStackPointerOnFunctionEntry[ portexR6_STACK_OFFSET ];
	xRegisterDump.ulR7 = pulStackPointerOnFunctionEntry[ portexR7_STACK_OFFSET ];
	xRegisterDump.ulR8 = pulStackPointerOnFunctionEntry[ portexR8_STACK_OFFSET ];
	xRegisterDump.ulR9 = pulStackPointerOnFunctionEntry[ portexR9_STACK_OFFSET ];
	xRegisterDump.ulR10 = pulStackPointerOnFunctionEntry[ portexR10_STACK_OFFSET ];
	xRegisterDump.ulR11 = pulStackPointerOnFunctionEntry[ portexR11_STACK_OFFSET ];
	xRegisterDump.ulR12 = pulStackPointerOnFunctionEntry[ portexR12_STACK_OFFSET ];
	xRegisterDump.ulR15_return_address_from_subroutine = pulStackPointerOnFunctionEntry[ portexR15_STACK_OFFSET ];
	xRegisterDump.ulR18 = pulStackPointerOnFunctionEntry[ portexR18_STACK_OFFSET ];
	xRegisterDump.ulR19 = pulStackPointerOnFunctionEntry[ portexR19_STACK_OFFSET ];

	/* Obtain the value of all other registers. */
	xRegisterDump.ulR2_small_data_area = mfgpr( R2 );
	xRegisterDump.ulR13_read_write_small_data_area = mfgpr( R13 );
	xRegisterDump.ulR14_return_address_from_interrupt = mfgpr( R14 );
	xRegisterDump.ulR16_return_address_from_trap = mfgpr( R16 );
	xRegisterDump.ulR17_return_address_from_some_exceptions = mfgpr( R17 );
	xRegisterDump.ulR18 = mfgpr( R18 );
	xRegisterDump.ulR20 = mfgpr( R20 );
	xRegisterDump.ulR21 = mfgpr( R21 );
	xRegisterDump.ulR22 = mfgpr( R22 );
	xRegisterDump.ulR23 = mfgpr( R23 );
	xRegisterDump.ulR24 = mfgpr( R24 );
	xRegisterDump.ulR25 = mfgpr( R25 );
	xRegisterDump.ulR26 = mfgpr( R26 );
	xRegisterDump.ulR27 = mfgpr( R27 );
	xRegisterDump.ulR28 = mfgpr( R28 );
	xRegisterDump.ulR29 = mfgpr( R29 );
	xRegisterDump.ulR30 = mfgpr( R30 );
	xRegisterDump.ulR31 = mfgpr( R31 );
	xRegisterDump.ulR1_SP = ( ( unsigned long ) pulStackPointerOnFunctionEntry ) + portexASM_HANDLER_STACK_FRAME_SIZE;
	xRegisterDump.ulBTR = ulBTROnFunctionEntry;
	xRegisterDump.ulMSR = pulStackPointerOnFunctionEntry[ portexMSR_STACK_OFFSET ];
	xRegisterDump.ulEAR = mfear();
	xRegisterDump.ulESR = mfesr();
	xRegisterDump.ulEDR = mfedr();


#ifdef THIS_IS_PROBABLY_INCORRECT
	if( ( xRegisterDump.ulESR * portexESR_DS_MASK ) != 0UL )
	{
		xRegisterDump.ulPC = mfbtr();
	}
	else
	{
		xRegisterDump.ulPC = xRegisterDump.ulR17_return_address_from_some_exceptions - 4;
	}
#else
	xRegisterDump.ulPC = xRegisterDump.ulR17_return_address_from_some_exceptions - 4;
#endif


	#if XPAR_MICROBLAZE_0_USE_FPU == 1
	{
		xRegisterDump.ulFSR = mffsr();
	}
	#else
	{
		xRegisterDump.ulFSR = 0UL;
	}
	#endif

	switch( ( unsigned long ) pvExceptionID )
	{
		case XEXC_ID_FSL :
				xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_FSL";
				break;

		case XEXC_ID_UNALIGNED_ACCESS :
				xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_UNALIGNED_ACCESS";
				break;

		case XEXC_ID_ILLEGAL_OPCODE :
				xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_ILLEGAL_OPCODE";
				break;

		case XEXC_ID_M_AXI_I_EXCEPTION :
				xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_M_AXI_I_EXCEPTION or XEXC_ID_IPLB_EXCEPTION";
				break;

		case XEXC_ID_M_AXI_D_EXCEPTION :
				xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_M_AXI_D_EXCEPTION or XEXC_ID_DPLB_EXCEPTION";
				break;

		case XEXC_ID_DIV_BY_ZERO :
				xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_DIV_BY_ZERO";
				break;

		case XEXC_ID_STACK_VIOLATION :
				xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_STACK_VIOLATION or XEXC_ID_MMU";
				break;

		#if XPAR_MICROBLAZE_0_USE_FPU == 1

			case XEXC_ID_FPU :
						/*_RB_ More decoding required here and in other exceptions. */
						xRegisterDump.pcExceptionCause = ( signed char * const ) "XEXC_ID_FPU see ulFSR value";
						break;

		#endif /* XPAR_MICROBLAZE_0_USE_FPU */
	}

	vApplicationExceptionRegisterDump( &xRegisterDump );

	/* Must not attempt to leave this function! */
	for( ;; )
	{
		portNOP();
	}
}
/*-----------------------------------------------------------*/

void vPortExceptionsInstallHandlers( void )
{
static unsigned long ulHandlersAlreadyInstalled = pdFALSE;

	if( ulHandlersAlreadyInstalled == pdFALSE )
	{
		ulHandlersAlreadyInstalled = pdTRUE;

		#if XPAR_MICROBLAZE_0_UNALIGNED_EXCEPTIONS == 1
			microblaze_register_exception_handler( XEXC_ID_UNALIGNED_ACCESS, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_UNALIGNED_ACCESS );
		#endif /* XPAR_MICROBLAZE_0_UNALIGNED_EXCEPTIONS*/

		#if XPAR_MICROBLAZE_0_ILL_OPCODE_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_ILLEGAL_OPCODE, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_ILLEGAL_OPCODE );
		#endif /* XPAR_MICROBLAZE_0_ILL_OPCODE_EXCEPTION*/

		#if XPAR_MICROBLAZE_0_M_AXI_I_BUS_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_M_AXI_I_EXCEPTION, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_M_AXI_I_EXCEPTION );
		#endif /* XPAR_MICROBLAZE_0_M_AXI_I_BUS_EXCEPTION*/

		#if XPAR_MICROBLAZE_0_M_AXI_D_BUS_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_M_AXI_D_EXCEPTION, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_M_AXI_D_EXCEPTION );
		#endif /* XPAR_MICROBLAZE_0_M_AXI_D_BUS_EXCEPTION*/

		#if XPAR_MICROBLAZE_0_IPLB_BUS_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_IPLB_EXCEPTION, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_IPLB_EXCEPTION );
		#endif /* XPAR_MICROBLAZE_0_IPLB_BUS_EXCEPTION*/

		#if XPAR_MICROBLAZE_0_DPLB_BUS_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_DPLB_EXCEPTION, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_DPLB_EXCEPTION );
		#endif /* XPAR_MICROBLAZE_0_DPLB_BUS_EXCEPTION*/

		#if XPAR_MICROBLAZE_0_DIV_ZERO_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_DIV_BY_ZERO, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_DIV_BY_ZERO );
		#endif /* XPAR_MICROBLAZE_0_DIV_ZERO_EXCEPTION*/

		#if XPAR_MICROBLAZE_0_FPU_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_FPU, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_FPU );
		#endif /* XPAR_MICROBLAZE_0_FPU_EXCEPTION*/

		#if XPAR_MICROBLAZE_0_FSL_EXCEPTION == 1
			microblaze_register_exception_handler( XEXC_ID_FSL, vPortExceptionHandlerEntry, ( void * ) XEXC_ID_FSL );
		#endif /* XPAR_MICROBLAZE_0_FSL_EXCEPTION*/
	}
}

/* Exclude the entire file if the MicroBlaze is not configured to handle
exceptions, or the application defined configuration item 
configINSTALL_EXCEPTION_HANDLERS is not set to 1. */
#endif /* ( MICROBLAZE_EXCEPTIONS_ENABLED == 1 ) && ( configINSTALL_EXCEPTION_HANDLERS == 1 ) */



