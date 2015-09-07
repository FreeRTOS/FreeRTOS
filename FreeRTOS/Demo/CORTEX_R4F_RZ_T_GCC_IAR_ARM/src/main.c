#if 1
/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup, standard FreeRTOS hook functions, and the ISR hander called
 * by the RTOS after interrupt entry (including nesting) has been taken care of.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* Standard includes. */
#include "string.h"

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Renesas includes. */
#include "r_cg_macrodriver.h"
#include "r_cg_icu.h"
#include "r_cg_scifa.h"
#include "r_cg_rspi.h"
#include "r_system.h"
#include "r_reset.h"
#include "siochar.h"
#include "r_cg_userdefine.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	1

/*-----------------------------------------------------------*/

static void prvClearBSS( void );

/*
 * Configure the hardware as necessary to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/* Prototype for the IRQ handler called by the generic Cortex-A5 RTOS port
layer. */
void vApplicationIRQHandler( void );

/* Library initialisation. */
extern void R_Systeminit( void );

/*-----------------------------------------------------------*/

volatile uint32_t ultest = 0, ultest2 = 9999;

int main( void )
{
	prvClearBSS();

	configASSERT( ultest == 0 );
	configASSERT( ultest2 == 9999 );

	/* Configure the hardware ready to run the demo. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	R_Systeminit();

	/* Enable RSPI1 (serial peripheral interface). */
	R_RSPI1_Start();

	/* Configure the UART channel for communication with a host PC via on-board
	RL78/G1C device. */
	io_init_scifa2();

	/* Enable SCIFA2 (serial communications interface with FIFO). */
	R_SCIFA2_Start();

	/* SW3 interrupts. */
	R_ICU_IRQ12_Start();
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
//	xFreeHeapSpace = xPortGetFreeHeapSize();

	/* Remove compiler warning about xFreeHeapSpace being set but never used. */
	( void ) xFreeHeapSpace;
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0
	{
		extern void vFullDemoTickHook( void );

		vFullDemoTickHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

/* The function called by the RTOS port layer after it has managed interrupt
entry. */
void vApplicationIRQHandler( void )
{
#if 1
extern void FreeRTOS_Tick_Handler( void );

	/* Clear the interrupt source CMI5. */
	VIC.PIC9.LONG = 0x00001000UL;

	FreeRTOS_Tick_Handler();

	/* Dummy write */
	portDISABLE_INTERRUPTS();
	// Done in the epilogue code VIC.HVA0.LONG = 0x00000000UL;

#else
typedef void (*ISRFunction_t)( void );
ISRFunction_t pxISRFunction;
volatile uint32_t * pulAIC_IVR = ( uint32_t * ) configINTERRUPT_VECTOR_ADDRESS;

	/* Obtain the address of the interrupt handler from the AIR. */
	pxISRFunction = ( ISRFunction_t ) *pulAIC_IVR;

	/* Write back to the SAMA5's interrupt controller's IVR register in case the
	CPU is in protect mode.  If the interrupt controller is not in protect mode
	then this write is not necessary. */
	*pulAIC_IVR = ( uint32_t ) pxISRFunction;

	/* Ensure the write takes before re-enabling interrupts. */
	__DSB();
	__ISB();
    __enable_irq();

	/* Call the installed ISR. */
	pxISRFunction();
#endif
}
/*-----------------------------------------------------------*/

static void prvClearBSS( void )
{
extern uint32_t __bss_start__[];
extern uint32_t __bss_end__[];
size_t xSize;

	/* Zero out bss. */
	xSize = ( ( size_t ) __bss_end__ ) - ( ( size_t ) __bss_start__ );
	memset( ( void * ) __bss_start__, 0x00, xSize );
}






























#else













#include "FreeRTOS.h"
#include "task.h"

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_cgc.h"
#include "r_cg_icu.h"
#include "r_cg_port.h"
#include "r_cg_tpu.h"
#include "r_cg_cmt.h"
#include "r_cg_scifa.h"
#include "r_cg_rspi.h"
#include "r_cg_s12ad.h"
/* Start user code for include. Do not edit comment generated here */
#include "r_cg_mpc.h"
#include "r_system.h"
#include "r_reset.h"
#include "lcd_pmod.h"
#include "logo_data.h"
#include "stdio.h"
#include "siochar.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/* Start user code for global. Do not edit comment generated here */

#define LZ_ENABLE   (1)
#define LZ_DISABLE  (0)

/* Welcome banner - displayed on serial port at startup*/
static uint8_t welcome_banner[] = "\n\n\rRSK+RZT1 \n\n\r- Tutorial - Press 'c' or SW3 for ADC Conversion\r\n\0";

/* Used as a Data Transmit counter    */
static uint8_t uart_buffer[] = " ADC count: x.     Value: xxxxx\r\n";

/* Used as a Data Transmit counter    */
static uint8_t lcd_buffer[] = " ADC = xxxx ";

/* Function prototype for displaying the 2 bit binary counter using LEDs */
static void led_display_count (const uint8_t count);

extern void R_Systeminit(void);
void R_MAIN_UserInit(void);

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );


/* Prototype for the IRQ handler called by the generic Cortex-A5 RTOS port
layer. */
void vApplicationIRQHandler( void );

void main(void)
{
uint32_t adc_count = 0;

    R_Systeminit();

    R_MAIN_UserInit();

    /* SW3 interrupts */
    R_ICU_IRQ12_Start();

    /* Clear flags */
    g_switch_press_flg = 0;
    g_terminal_request = 0;

    /* Display the welcome banner on the serial terminal */
    R_SCIFA2_Serial_Send((uint8_t *)&welcome_banner, sizeof(welcome_banner));
        
    /* Data transmission and reception done in the infinite loop */
    while (1U)
    {         
        /* Check for a valid request from the switch or serial terminal */
        if ((g_terminal_request) || (g_switch_press_flg & SW3_PRESS_FLG))
        {          
            /* Update the binary count using LED2 and LED3 */
            led_display_count(adc_count);

            while(0u == SCIFA2.FSR.BIT.TDFE)
            {
                /* Wait for previous transmission to complete */
            }

            /* Write send data */
            R_SCIFA2_Serial_Send((uint8_t *)&uart_buffer, sizeof(uart_buffer));

            /* Clear TDFE */
            SCIFA2.FSR.BIT.TDFE = 0U;
            
            if (g_terminal_request)
            {
                /* Clear the request */
                g_terminal_request = 0U;
            }
                        
            if (g_switch_press_flg & SW3_PRESS_FLG)
            {
                /* Clear the request */
                g_switch_press_flg &= ((uint8_t)~SW3_PRESS_FLG);
            }

            adc_count++;
        }
    }
}
/***********************************************************************************************************************
* Function Name: R_MAIN_UserInit
* Description  : This function adds user code before implementing main function.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_MAIN_UserInit(void)
{
    /* Enable RSPI1 operations */
    R_RSPI1_Start();
	
    /* Configure UART channel for communication with host PC via RL78/G1C device */
    io_init_scifa2();
    
    /* Enable SCIFA2 operations */
    R_SCIFA2_Start();
}

static void led_display_count (const uint8_t count)
{
    /* Set LEDs according to lower nibble of count parameter */
    LED2 = (uint8_t) ((count & 0x01) ? LED_ON : LED_OFF);
    LED3 = (uint8_t) ((count & 0x02) ? LED_ON : LED_OFF);
}

/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	/* Remove compiler warning about xFreeHeapSpace being set but never used. */
	( void ) xFreeHeapSpace;
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
}
/*-----------------------------------------------------------*/

void vApplicationIRQHandler( void )
{
}


#endif

