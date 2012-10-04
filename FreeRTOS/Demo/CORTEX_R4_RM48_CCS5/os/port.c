/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
	

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
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*----------------------------------------------------------------------------*/
/* Include Files                                                              */

#include "FreeRTOS.h"
#include "task.h"

/*----------------------------------------------------------------------------*/
/* Global Variables                                                         */

unsigned portLONG ulCriticalNesting = 9999;

/*----------------------------------------------------------------------------*/
/* Macros                                                                     */

#define portINITIAL_SPSR                ((portSTACK_TYPE) 0x1F)
#define portINITIAL_FPSCR               ((portSTACK_TYPE) 0x00)
#define portINSTRUCTION_SIZE            ((portSTACK_TYPE) 0x04)
#define portTHUMB_MODE_BIT				((portSTACK_TYPE) 0x20)

/*----------------------------------------------------------------------------*/
/* pxPortInitialiseStack                                                      */

portSTACK_TYPE * pxPortInitialiseStack(portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters)
{
    portSTACK_TYPE *pxOriginalTOS = pxTopOfStack;
    
    *pxTopOfStack-- = (portSTACK_TYPE) pxCode + portINSTRUCTION_SIZE;		
    *pxTopOfStack-- = (portSTACK_TYPE) 0xaaaaaaaa;
    *pxTopOfStack-- = (portSTACK_TYPE) pxOriginalTOS;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x12121212;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x11111111;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x10101010;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x09090909;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x08080808;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x07070707;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x06060606;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x05050505;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x04040404;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x03030303;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x02020202;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x01010101;
    *pxTopOfStack-- = (portSTACK_TYPE) pvParameters;

#if __TI_VFPV3D16_SUPPORT__
    *pxTopOfStack-- = (portSTACK_TYPE) 0x3F3F3F3F;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x3E3E3E3E;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x3D3D3D3D;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x3C3C3C3C;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x3B3B3B3B;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x3A3A3A3A;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x39393939;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x38383838;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x37373737;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x36363636;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x35353535;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x34343434;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x33333333;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x32323232;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x31313131;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x30303030;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x2F2F2F2F;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x2E2E2E2E;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x2D2D2D2D;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x2C2C2C2C;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x2B2B2B2B;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x2A2A2A2A;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x29292929;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x28282828;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x27272727;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x26262626;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x25252525;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x24242424;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x23232323;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x22222222;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x21212121;
    *pxTopOfStack-- = (portSTACK_TYPE) 0x20202020;
    *pxTopOfStack-- = (portSTACK_TYPE) portINITIAL_FPSCR;
#endif


    *pxTopOfStack = (portSTACK_TYPE) ((_get_CPSR() & ~0xFF) | portINITIAL_SPSR);

    if (((unsigned long) pxCode & 0x01UL) != 0x00)
    {
        *pxTopOfStack |= portTHUMB_MODE_BIT;
    }

    return pxTopOfStack;
}


/*----------------------------------------------------------------------------*/
/* prvSetupTimerInterrupt                                                     */

static void prvSetupTimerInterrupt(void)
{
#if (configGENERATE_RUN_TIME_STATS == 1)
    RTI->GCTRL        &= ~0x00000001U;
#else
    RTI->GCTRL         =  0x00000000U;
#endif
    RTI->TBCTRL        =  0x00000000U;
    RTI->COMPCTRL      =  0x00000000U;
    RTI->CNT[0U].UCx   =  0x00000000U;
    RTI->CNT[0U].FRCx  =  0x00000000U;
    RTI->CNT[0U].CPUCx =  0x00000001U;
    RTI->CMP[0U].COMPx =  configCPU_CLOCK_HZ / 2 / configTICK_RATE_HZ;
    RTI->CMP[0U].UDCPx =  configCPU_CLOCK_HZ / 2 / configTICK_RATE_HZ;
    RTI->INTFLAG       =  0x0007000FU;
    RTI->CLEARINT      =  0x00070F0FU;
    RTI->SETINT        =  0x00000001U;
    RTI->GCTRL        |=  0x00000001U;
}


/*----------------------------------------------------------------------------*/
/* vPortStartFirstTask                                                        */

/* vPortStartFirstSTask() is defined in portASM.asm */
extern void vPortStartFirstTask(void);


/*----------------------------------------------------------------------------*/
/* xPortStartScheduler                                                        */

portBASE_TYPE xPortStartScheduler(void)
{
	/* Start the timer that generates the tick ISR. */
    prvSetupTimerInterrupt();
    /* Enable critical sections */
    ulCriticalNesting = 0;
	/* Start the first task.  This is done from portASM.asm as ARM mode must be
	used. */
    vPortStartFirstTask();	
	/* Should not get here! */
    return 0;
}


/*----------------------------------------------------------------------------*/
/* vPortEndScheduler                                                          */

void vPortEndScheduler(void)
{
	/* It is unlikely that the ARM port will require this function as there
	is nothing to return to.  If this is required - stop the tick ISR then
	return back to main. */
}


/*----------------------------------------------------------------------------*/
/* vNonPreemptiveTick / vPreemptiveTick                                       */

#if configUSE_PREEMPTION == 0

	/* The cooperative scheduler requires a normal IRQ service routine to 
	 * simply increment the system tick. */
	__interrupt void vNonPreemptiveTick( void ) 
	{
        /* clear clock interrupt flag */
        RTI->INTFLAG = 0x00000001;

		/* Increment the tick count - this may make a delaying task ready
		to run - but a context switch is not performed. */		
		vTaskIncrementTick();
	}

 #else

	/*
	 **************************************************************************
	 * The preemptive scheduler ISR is written in assembler and can be found   
	 * in the portASM.asm file. This will only get used if portUSE_PREEMPTION
	 * is set to 1 in portmacro.h
	 ************************************************************************** 
	 */
    void vPreemptiveTick(void);

#endif



/*----------------------------------------------------------------------------*/
/* vPortEnterCritical                                                         */

void vPortEnterCritical(void)
{
	/* Disable interrupts as per portDISABLE_INTERRUPTS(); */
    portDISABLE_INTERRUPTS();
	/* Now interrupts are disabled ulCriticalNesting can be accessed 
	directly.  Increment ulCriticalNesting to keep a count of how many times
	portENTER_CRITICAL() has been called. */
    ulCriticalNesting++;
}


/*----------------------------------------------------------------------------*/
/* vPortExitCritical                                                          */

void vPortExitCritical(void)
{
    if(ulCriticalNesting > 0)
    {
		/* Decrement the nesting count as we are leaving a critical section. */
        ulCriticalNesting--;

		/* If the nesting level has reached zero then interrupts should be 
        re-enabled. */
        if(ulCriticalNesting == 0)
        {
			/* Enable interrupts as per portENABLE_INTERRUPTS(). */
            portENABLE_INTERRUPTS();
        }
    }
}

/*----------------------------------------------------------------------------*/
