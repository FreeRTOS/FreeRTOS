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

#ifndef __OS_PORTMACRO_H__
#define __OS_PORTMACRO_H__


/*----------------------------------------------------------------------------*/
/* RTI Register Frame Definition                                              */

struct rti
{
    unsigned GCTRL;
    unsigned TBCTRL;
    unsigned CAPCTRL;
    unsigned COMPCTRL;
    struct
    {
        unsigned FRCx;
        unsigned UCx;
        unsigned CPUCx;
        unsigned : 32;
        unsigned CAFRCx;
        unsigned CAUCx;
        unsigned : 32;
        unsigned : 32;
    } CNT[2U];
    struct
    {
        unsigned COMPx;
        unsigned UDCPx;
    } CMP[4U];
    unsigned TBLCOMP;
    unsigned TBHCOMP;
    unsigned : 32;
    unsigned : 32;
    unsigned SETINT;
    unsigned CLEARINT;
    unsigned INTFLAG;
    unsigned : 32;
    unsigned DWDCTRL;
    unsigned DWDPRLD;
    unsigned WDSTATUS;
    unsigned WDKEY;
    unsigned WDCNTR;
};

#define RTI ((volatile struct rti *)0xFFFFFC00U)

/*----------------------------------------------------------------------------*/
/* Type Definitions                                                           */

#define portCHAR        char
#define portFLOAT       float
#define portDOUBLE      double
#define portLONG        long
#define portSHORT       short
#define portSTACK_TYPE  unsigned long
#define portBASE_TYPE   long

#if (configUSE_16_BIT_TICKS == 1)
    typedef unsigned portSHORT portTickType;
    #define portMAX_DELAY (portTickType) 0xFFFF
#else
    typedef unsigned portLONG portTickType;
    #define portMAX_DELAY (portTickType) 0xFFFFFFFFF
#endif


/*----------------------------------------------------------------------------*/
/* Architecture Definitions                                                   */

#define portSTACK_GROWTH    (-1)
#define portTICK_RATE_MS    ((portTickType) 1000 / configTICK_RATE_HZ)		
#define portBYTE_ALIGNMENT  8

/*----------------------------------------------------------------------------*/
/* External Functions                                                         */

extern void vPortEnterCritical(void);
extern void vPortExitCritical(void);

/*----------------------------------------------------------------------------*/
/* Functions Macros                                                           */

#define portYIELD()              _call_swi(0)
#define portYIELD_WITHIN_API()   { *(volatile unsigned *)0xFFFFFFB0 = 0x7500;  *(volatile unsigned *)0xFFFFFFB0; }
#define portYIELD_FROM_ISR()     { *(volatile unsigned *)0xFFFFFFB0 = 0x7500;  *(volatile unsigned *)0xFFFFFFB0; }
#define portENTER_CRITICAL()     vPortEnterCritical()
#define portEXIT_CRITICAL()      vPortExitCritical()
#define portDISABLE_INTERRUPTS() asm(" CPSID I")
#define portENABLE_INTERRUPTS()	 asm(" CPSIE I")

#define portTASK_FUNCTION(vFunction, pvParameters)       void vFunction(void *pvParameters)
#define portTASK_FUNCTION_PROTO(vFunction, pvParameters) void vFunction(void *pvParameters)

#if (configGENERATE_RUN_TIME_STATS == 1)
#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() \
{ \
    RTI->GCTRL         = 0x00000000U; \
    RTI->TBCTRL        = 0x00000000U; \
    RTI->COMPCTRL      = 0x00000000U; \
    RTI->CNT[1U].UCx   = 0x00000000U; \
    RTI->CNT[1U].FRCx  = 0x00000000U; \
    RTI->CNT[1U].CPUCx = (configCPU_CLOCK_HZ / 2 / configTICK_RATE_HZ) / 16; \
    RTI->CMP[1U].UDCPx = (configCPU_CLOCK_HZ / 2 / configTICK_RATE_HZ) / 16; \
    RTI->GCTRL         = 0x00000002U; \
}
#define portGET_RUN_TIME_COUNTER_VALUE() (RTI->CNT[1].FRCx)
#endif

#endif

/*----------------------------------------------------------------------------*/
