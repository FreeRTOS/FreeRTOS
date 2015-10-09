/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcHardwarePort.h
 *
 * The hardware abstraction layer for the trace recorder library.
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
 *
 * Disclaimer
 * The trace tool and recorder library is being delivered to you AS IS and
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does
 * not and cannot warrant the performance or results you may obtain by using the
 * software or documentation. Percepio AB make no warranties, express or
 * implied, as to noninfringement of third party rights, merchantability, or
 * fitness for any particular purpose. In no event will Percepio AB, its
 * technology partners, or distributors be liable to you for any consequential,
 * incidental or special damages, including any lost profits or lost savings,
 * even if a representative of Percepio AB has been advised of the possibility
 * of such damages, or for any claim by any third party. Some jurisdictions do
 * not allow the exclusion or limitation of incidental, consequential or special
 * damages, or the exclusion of implied warranties or limitations on how long an
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_HARDWARE_PORT_H
#define TRC_HARDWARE_PORT_H

#ifdef __cplusplus
extern “C” {
#endif

#include <stdint.h>

/******************************************************************************
 * Hardware ports
 * To get accurate timestamping, a hardware timer is necessary. Below are the
 * available ports. Some of these are "unofficial", meaning that
 * they have not yet been verified by Percepio but have been contributed by
 * external developers. They should work, otherwise let us know by emailing
 * support@percepio.com. Some work on any OS platform, while other are specific
 * to a certain operating system.
 *****************************************************************************/


/****** Port Name ***************************** Code */
#define TRC_PORT_APPLICATION_DEFINED			-1
#define TRC_PORT_NOT_SET						0
#define TRC_PORT_ARM_Cortex_M					1
#define TRC_PORT_ARM_CORTEX_A9					2
#define TRC_PORT_Renesas_RX600					3
#define TRC_PORT_TEXAS_INSTRUMENTS_TMS570_RM48	4
#define TRC_PORT_MICROCHIP_PIC32_MX_MZ			5

/*******************************************************************************
 *
 * HWTC Macros - Hardware Timer/Counter Isolation Layer
 *
 * These two HWTC macros provides a hardware isolation layer representing a
 * generic hardware timer/counter used for the timestamping.
 *
 * HWTC_COUNT: The current value of the counter. This is expected to be reset
 * a each tick interrupt. Thus, when the tick handler starts, the counter has
 * already wrapped.
 *
 * HWTC_TYPE: Defines the type of timer/counter used for HWTC_COUNT:
 *
 * - FREE_RUNNING_32BIT_INCR:
 *   Free-running 32-bit timer, counting upwards from 0 - > 0xFFFFFFFF
 *
 * - FREE_RUNNING_32BIT_DECR
 *   Free-running 32-bit counter, counting downwards from 0xFFFFFFFF -> 0
 *
 * - OS_TIMER_INCR
 *	 Interrupt timer, counts upwards from 0 until HWTC_PERIOD-1
 *
 * - OS_TIMER_DECR
 *   Interrupt timer, counts downwards from HWTC_PERIOD-1 until 0
 *
 *******************************************************************************
 *
 * IRQ_PRIORITY_ORDER
 *
 * Macro which should be defined as an integer of 0 or 1.
 *
 * It is only used only to sort and colorize the interrupts in priority order,
 * in case you record interrupts using the vTraceStoreISRBegin and
 * vTraceStoreISREnd routines. 1 indicates higher value is more important.
 *
 ******************************************************************************/

#define TRC_FREE_RUNNING_32BIT_INCR 1
#define TRC_FREE_RUNNING_32BIT_DECR 2
#define TRC_OS_TIMER_INCR 3
#define TRC_OS_TIMER_DECR 4

#if (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_ARM_Cortex_M)

	#define HWTC_TYPE TRC_OS_TIMER_DECR
    #define HWTC_COUNT (*((uint32_t*)0xE000E018)) /* SysTick counter */
	#define IRQ_PRIORITY_ORDER 0

#elif (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_Renesas_RX600)

	#include "iodefine.h"

	#define HWTC_TYPE TRC_OS_TIMER_INCR
	#define HWTC_COUNT (CMT0.CMCNT)
	#define IRQ_PRIORITY_ORDER 1

#elif (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_MICROCHIP_PIC32_MX_MZ)

	#define HWTC_TYPE TRC_OS_TIMER_INCR
	#define HWTC_COUNT (TMR1)
	#define IRQ_PRIORITY_ORDER 0

#elif (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_TEXAS_INSTRUMENTS_TMS570_RM48)

	#define RTIFRC0 *((uint32_t *)0xFFFFFC10)
	#define RTICOMP0 *((uint32_t *)0xFFFFFC50)
	#define RTIUDCP0 *((uint32_t *)0xFFFFFC54)

	#define HWTC_TYPE TRC_OS_TIMER_INCR
	#define HWTC_COUNT (RTIFRC0 - (RTICOMP0 - RTIUDCP0))
	#define IRQ_PRIORITY_ORDER 0

#elif (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_ARM_CORTEX_A9)
	/* INPUT YOUR PERIPHERAL BASE ADDRESS HERE */
	#define CA9_MPCORE_PERIPHERAL_BASE_ADDRESS	0xSOMETHING
	
	#define CA9_MPCORE_PRIVATE_MEMORY_OFFSET	0x0600
	#define CA9_MPCORE_PRIVCTR_PERIOD_REG	(*(volatile uint32_t*)(CA9_MPCORE_PERIPHERAL_BASE_ADDRESS + CA9_MPCORE_PRIVATE_MEMORY_OFFSET + 0x00))
	#define CA9_MPCORE_PRIVCTR_COUNTER_REG	(*(volatile uint32_t*)(CA9_MPCORE_PERIPHERAL_BASE_ADDRESS + CA9_MPCORE_PRIVATE_MEMORY_OFFSET + 0x04))
	#define CA9_MPCORE_PRIVCTR_CONTROL_REG	(*(volatile uint32_t*)(CA9_MPCORE_PERIPHERAL_BASE_ADDRESS + CA9_MPCORE_PRIVATE_MEMORY_OFFSET + 0x08))
	
	#define CA9_MPCORE_PRIVCTR_CONTROL_PRESCALER_MASK    0x0000FF00
	#define CA9_MPCORE_PRIVCTR_CONTROL_PRESCALER_SHIFT   8
	#define CA9_MPCORE_PRIVCTR_PRESCALER        (((CA9_MPCORE_PRIVCTR_CONTROL_REG & CA9_MPCORE_PRIVCTR_CONTROL_PRESCALER_MASK) >> CA9_MPCORE_PRIVCTR_CONTROL_PRESCALER_SHIFT) + 1)

    #define HWTC_TYPE 							TRC_OS_TIMER_DECR
    #define HWTC_COUNT                          CA9_MPCORE_PRIVCTR_COUNTER_REG
    #define IRQ_PRIORITY_ORDER 0

#elif (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_APPLICATION_DEFINED)

	#if !( defined (HWTC_TYPE) && defined (HWTC_COUNT) && defined (IRQ_PRIORITY_ORDER))
		#error RECORDER_HARDWARE_PORT is PORT_APPLICATION_DEFINED but not all of the necessary constants have been defined.
	#endif

#elif (TRC_RECORDER_HARDWARE_PORT != TRC_PORT_NOT_SET)

	#error "RECORDER_HARDWARE_PORT had unsupported value!"
	#define TRC_RECORDER_HARDWARE_PORT PORT_NOT_SET

#endif

#if (TRC_RECORDER_HARDWARE_PORT != TRC_PORT_NOT_SET)

	#ifndef HWTC_COUNT
	#error "HWTC_COUNT is not set!"
	#endif

	#ifndef HWTC_TYPE
	#error "HWTC_TYPE is not set!"
	#endif

	#ifndef IRQ_PRIORITY_ORDER
	#error "IRQ_PRIORITY_ORDER is not set!"
	#elif (IRQ_PRIORITY_ORDER != 0) && (IRQ_PRIORITY_ORDER != 1)
	#error "IRQ_PRIORITY_ORDER has bad value!"
	#endif

#endif

#ifdef __cplusplus
}
#endif

#endif /* TRC_HARDWARE_PORT_H */
