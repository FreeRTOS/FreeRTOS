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

#ifndef PORTMACRO_H
#define PORTMACRO_H

#ifdef __cplusplus
extern "C" {
#endif

/* BSP includes. */
#include <mb_interface.h>
#include <xparameters.h>

/*-----------------------------------------------------------
 * Port specific definitions.  
 *
 * The settings in this file configure FreeRTOS correctly for the
 * given hardware and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

/* Type definitions. */
#define portCHAR		char
#define portFLOAT		float
#define portDOUBLE		double
#define portLONG		long
#define portSHORT		short
#define portSTACK_TYPE	unsigned long
#define portBASE_TYPE	long

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned portLONG portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/	

/* Interrupt control macros and functions. */
void microblaze_disable_interrupts( void );
void microblaze_enable_interrupts( void );
#define portDISABLE_INTERRUPTS()	microblaze_disable_interrupts()
#define portENABLE_INTERRUPTS()		microblaze_enable_interrupts()

/*-----------------------------------------------------------*/

/* Critical section macros. */
void vPortEnterCritical( void );
void vPortExitCritical( void );
#define portENTER_CRITICAL()		{																\
										extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
										microblaze_disable_interrupts();							\
										uxCriticalNesting++;										\
									}

#define portEXIT_CRITICAL()			{																\
										extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
										/* Interrupts are disabled, so we can */					\
										/* access the variable directly. */							\
										uxCriticalNesting--;										\
										if( uxCriticalNesting == 0 )								\
										{															\
											/* The nesting has unwound and we 						\
											can enable interrupts again. */							\
											portENABLE_INTERRUPTS();								\
										}															\
									}

/*-----------------------------------------------------------*/

/* The yield macro maps directly to the vPortYield() function. */
void vPortYield( void );
#define portYIELD() vPortYield()

/* portYIELD_FROM_ISR() does not directly call vTaskSwitchContext(), but instead
sets a flag to say that a yield has been requested.  The interrupt exit code
then checks this flag, and calls vTaskSwitchContext() before restoring a task
context, if the flag is not false.  This is done to prevent multiple calls to
vTaskSwitchContext() being made from a single interrupt, as a single interrupt
can result in multiple peripherals being serviced. */
extern volatile unsigned long ulTaskSwitchRequested;
#define portYIELD_FROM_ISR( x ) if( x != pdFALSE ) ulTaskSwitchRequested = 1
/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portBYTE_ALIGNMENT			4
#define portSTACK_GROWTH			( -1 )
#define portTICK_RATE_MS			( ( portTickType ) 1000 / configTICK_RATE_HZ )
#define portNOP()					asm volatile ( "NOP" )
/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*-----------------------------------------------------------*/

/* The following structure is used by the FreeRTOS exception handler.  It is
filled with the MicroBlaze context as it was at the time the exception occurred.
This is done as an aid to debugging exception occurrences. */
typedef struct PORT_REGISTER_DUMP
{
	/* The following structure members hold the values of the MicroBlaze
	registers at the time the exception was raised. */
	unsigned long ulR1_SP;
	unsigned long ulR2_small_data_area;
	unsigned long ulR3;
	unsigned long ulR4;
	unsigned long ulR5;
	unsigned long ulR6;
	unsigned long ulR7;
	unsigned long ulR8;
	unsigned long ulR9;
	unsigned long ulR10;
	unsigned long ulR11;
	unsigned long ulR12;
	unsigned long ulR13_read_write_small_data_area;
	unsigned long ulR14_return_address_from_interrupt;
	unsigned long ulR15_return_address_from_subroutine;
	unsigned long ulR16_return_address_from_trap;
	unsigned long ulR17_return_address_from_exceptions; /* The exception entry code will copy the BTR into R17 if the exception occurred in the delay slot of a branch instruction. */
	unsigned long ulR18;
	unsigned long ulR19;
	unsigned long ulR20;
	unsigned long ulR21;
	unsigned long ulR22;
	unsigned long ulR23;
	unsigned long ulR24;
	unsigned long ulR25;
	unsigned long ulR26;
	unsigned long ulR27;
	unsigned long ulR28;
	unsigned long ulR29;
	unsigned long ulR30;
	unsigned long ulR31;
	unsigned long ulPC;
	unsigned long ulESR;
	unsigned long ulMSR;
	unsigned long ulEAR;
	unsigned long ulFSR;
	unsigned long ulEDR;

	/* A human readable description of the exception cause.  The strings used
	are the same as the #define constant names found in the
	microblaze_exceptions_i.h header file */
	signed char *pcExceptionCause;

	/* The human readable name of the task that was running at the time the
	exception occurred.  This is the name that was given to the task when the
	task was created using the FreeRTOS xTaskCreate() API function. */
	signed char *pcCurrentTaskName;

	/* The handle of the task that was running a the time the exception
	occurred. */
	void * xCurrentTaskHandle;

} xPortRegisterDump;


/*
 * Installs pxHandler as the interrupt handler for the peripheral specified by 
 * the ucInterruptID parameter.
 *
 * ucInterruptID:
 * 
 * The ID of the peripheral that will have pxHandler assigned as its interrupt
 * handler.  Peripheral IDs are defined in the xparameters.h header file, which 
 * is itself part of the BSP project.  For example, in the official demo 
 * application for this port, xparameters.h defines the following IDs for the 
 * four possible interrupt sources:
 *
 * XPAR_INTC_0_UARTLITE_1_VEC_ID  -  for the UARTlite peripheral.
 * XPAR_INTC_0_TMRCTR_0_VEC_ID    -  for the AXI Timer 0 peripheral.
 * XPAR_INTC_0_EMACLITE_0_VEC_ID  -  for the Ethernet lite peripheral.
 * XPAR_INTC_0_GPIO_1_VEC_ID      -  for the button inputs.
 *
 *
 * pxHandler:
 * 
 * A pointer to the interrupt handler function itself.  This must be a void
 * function that takes a (void *) parameter.
 *
 *
 * pvCallBackRef:
 *
 * The parameter passed into the handler function.  In many cases this will not
 * be used and can be NULL.  Some times it is used to pass in a reference to
 * the peripheral instance variable, so it can be accessed from inside the
 * handler function.
 *
 * 
 * pdPASS is returned if the function executes successfully.  Any other value
 * being returned indicates that the function did not execute correctly.
 */
portBASE_TYPE xPortInstallInterruptHandler( unsigned char ucInterruptID, XInterruptHandler pxHandler, void *pvCallBackRef );


/*
 * Enables the interrupt, within the interrupt controller, for the peripheral 
 * specified by the ucInterruptID parameter.
 *
 * ucInterruptID:
 * 
 * The ID of the peripheral that will have its interrupt enabled in the
 * interrupt controller.  Peripheral IDs are defined in the xparameters.h header 
 * file, which is itself part of the BSP project.  For example, in the official 
 * demo application for this port, xparameters.h defines the following IDs for 
 * the four possible interrupt sources:
 *
 * XPAR_INTC_0_UARTLITE_1_VEC_ID  -  for the UARTlite peripheral.
 * XPAR_INTC_0_TMRCTR_0_VEC_ID    -  for the AXI Timer 0 peripheral.
 * XPAR_INTC_0_EMACLITE_0_VEC_ID  -  for the Ethernet lite peripheral.
 * XPAR_INTC_0_GPIO_1_VEC_ID      -  for the button inputs.
 *
 */
void vPortEnableInterrupt( unsigned char ucInterruptID );

/*
 * Disables the interrupt, within the interrupt controller, for the peripheral 
 * specified by the ucInterruptID parameter.
 *
 * ucInterruptID:
 * 
 * The ID of the peripheral that will have its interrupt disabled in the
 * interrupt controller.  Peripheral IDs are defined in the xparameters.h header 
 * file, which is itself part of the BSP project.  For example, in the official 
 * demo application for this port, xparameters.h defines the following IDs for 
 * the four possible interrupt sources:
 *
 * XPAR_INTC_0_UARTLITE_1_VEC_ID  -  for the UARTlite peripheral.
 * XPAR_INTC_0_TMRCTR_0_VEC_ID    -  for the AXI Timer 0 peripheral.
 * XPAR_INTC_0_EMACLITE_0_VEC_ID  -  for the Ethernet lite peripheral.
 * XPAR_INTC_0_GPIO_1_VEC_ID      -  for the button inputs.
 *
 */
void vPortDisableInterrupt( unsigned char ucInterruptID );

/*
 * This is an application defined callback function used to install the tick
 * interrupt handler.  It is provided as an application callback because the 
 * kernel will run on lots of different MicroBlaze and FPGA configurations - not 
 * all of which will have the same timer peripherals defined or available.  This 
 * example uses the AXI Timer 0.  If that is available on your hardware platform 
 * then this example callback implementation should not require modification.  
 * The name of the interrupt handler that should be installed is vPortTickISR(), 
 * which the function below declares as an extern.
 */ 
void vApplicationSetupTimerInterrupt( void );

/* 
 * This is an application defined callback function used to clear whichever
 * interrupt was installed by the the vApplicationSetupTimerInterrupt() callback
 * function - in this case the interrupt generated by the AXI timer.  It is 
 * provided as an application callback because the kernel will run on lots of 
 * different MicroBlaze and FPGA configurations - not all of which will have the 
 * same timer peripherals defined or available.  This example uses the AXI Timer 0.  
 * If that is available on your hardware platform then this example callback 
 * implementation should not require modification provided the example definition
 * of vApplicationSetupTimerInterrupt() is also not modified. 
 */
void vApplicationClearTimerInterrupt( void );

/*
 * vPortExceptionsInstallHandlers() is only available when the MicroBlaze
 * is configured to include exception functionality, and 
 * configINSTALL_EXCEPTION_HANDLERS is set to 1 in FreeRTOSConfig.h.
 *
 * vPortExceptionsInstallHandlers() installs the FreeRTOS exception handler
 * for every possible exception cause.  
 *
 * vPortExceptionsInstallHandlers() can be called explicitly from application
 * code.  After that is done, the default FreeRTOS exception handler that will
 * have been installed can be replaced for any specific exception cause by using 
 * the standard Xilinx library function microblaze_register_exception_handler().
 *
 * If vPortExceptionsInstallHandlers() is not called explicitly by the 
 * application, it will be called automatically by the kernel the first time
 * xPortInstallInterruptHandler() is called.  At that time, any exception 
 * handlers that may have already been installed will be replaced.
 *
 * See the description of vApplicationExceptionRegisterDump() for information
 * on the processing performed by the FreeRTOS exception handler.
 */
void vPortExceptionsInstallHandlers( void );

/*
 * The FreeRTOS exception handler fills an xPortRegisterDump structure (defined 
 * in portmacro.h) with the MicroBlaze context, as it was at the time the 
 * exception occurred.  The exception handler then calls
 * vApplicationExceptionRegisterDump(), passing in the completed
 * xPortRegisterDump structure as its parameter.
 *
 * The FreeRTOS kernel provides its own implementation of
 * vApplicationExceptionRegisterDump(), but the kernel provided implementation 
 * is declared as being 'weak'.  The weak definition allows the application 
 * writer to provide their own implementation, should they wish to use the 
 * register dump information.  For example, an implementation could be provided
 * that wrote the register dump data to a display, or a UART port.
 */
void vApplicationExceptionRegisterDump( xPortRegisterDump *xRegisterDump );


#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

