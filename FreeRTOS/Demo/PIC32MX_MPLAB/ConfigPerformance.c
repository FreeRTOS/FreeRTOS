/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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

/*
 * This file implements functions to access and manipulate the PIC32 hardware
 * without reliance on third party library functions that may be liable to
 * change.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "ConfigPerformance.h"

/* Hardware specific definitions. */
#define hwCHECON_PREFEN_BITS	  		( 0x03UL << 0x04UL )
#define hwCHECON_WAIT_STAT_BITS			( 0x07UL << 0UL )
#define hwMAX_FLASH_SPEED		  		( 30000000UL )
#define hwPERIPHERAL_CLOCK_DIV_BY_2		( 1UL << 0x13UL )
#define hwUNLOCK_KEY_0					( 0xAA996655UL )
#define hwUNLOCK_KEY_1					( 0x556699AAUL )
#define hwLOCK_KEY						( 0x33333333UL )
#define hwGLOBAL_INTERRUPT_BIT			( 0x01UL )
#define hwBEV_BIT 						( 0x00400000 )
#define hwEXL_BIT 						( 0x00000002 )
#define hwIV_BIT 						( 0x00800000 )

/*
 * Set the flash wait states for the configured CPU clock speed.
 */
static void prvConfigureWaitStates( void );

/*
 * Use a divisor of 2 on the peripheral bus.
 */
static void prvConfigurePeripheralBus( void );

/*
 * Enable the cache.
 */
static void __attribute__ ((nomips16)) prvKSeg0CacheOn( void );

/*-----------------------------------------------------------*/

void vHardwareConfigurePerformance( void )
{
unsigned long ulStatus;
#ifdef _PCACHE
	unsigned long ulCacheStatus;
#endif

	/* Disable interrupts - note taskDISABLE_INTERRUPTS() cannot be used here as
	FreeRTOS does not globally disable interrupt. */
	ulStatus = _CP0_GET_STATUS();
	_CP0_SET_STATUS( ulStatus & ~hwGLOBAL_INTERRUPT_BIT );

	prvConfigurePeripheralBus();
	prvConfigureWaitStates();

	/* Disable DRM wait state. */
	BMXCONCLR = _BMXCON_BMXWSDRM_MASK;

	#ifdef _PCACHE
	{
		/* Read the current CHECON value. */
		ulCacheStatus = CHECON;

		/* All the PREFEN bits are being set, so no need to clear first. */
		ulCacheStatus |= hwCHECON_PREFEN_BITS;

		/* Write back the new value. */
		CHECON = ulCacheStatus;
		prvKSeg0CacheOn();
	}
	#endif

	/* Reset the status register back to its original value so the original
	interrupt enable status is retored. */
	_CP0_SET_STATUS( ulStatus );
}
/*-----------------------------------------------------------*/

void vHardwareUseMultiVectoredInterrupts( void )
{
unsigned long ulStatus, ulCause;
extern unsigned long _ebase_address[];

	/* Get current status. */
	ulStatus = _CP0_GET_STATUS();

	/* Disable interrupts. */
	ulStatus &= ~hwGLOBAL_INTERRUPT_BIT;

	/* Set BEV bit. */
	ulStatus |= hwBEV_BIT;

	/* Write status back. */
	_CP0_SET_STATUS( ulStatus );

	/* Setup EBase. */
	_CP0_SET_EBASE( ( unsigned long ) _ebase_address );
	
	/* Space vectors by 0x20 bytes. */
	_CP0_XCH_INTCTL( 0x20 );

	/* Set the IV bit in the CAUSE register. */
	ulCause = _CP0_GET_CAUSE();
	ulCause |= hwIV_BIT;
	_CP0_SET_CAUSE( ulCause );

	/* Clear BEV and EXL bits in status. */
	ulStatus &= ~( hwBEV_BIT | hwEXL_BIT );
	_CP0_SET_STATUS( ulStatus );

	/* Set MVEC bit. */
	INTCONbits.MVEC = 1;
	
	/* Finally enable interrupts again. */
	ulStatus |= hwGLOBAL_INTERRUPT_BIT;
	_CP0_SET_STATUS( ulStatus );
}
/*-----------------------------------------------------------*/

static void prvConfigurePeripheralBus( void )
{
unsigned long ulDMAStatus;
__OSCCONbits_t xOSCCONBits;

	/* Unlock after suspending. */
	ulDMAStatus = DMACONbits.SUSPEND;
	if( ulDMAStatus == 0 )
	{
		DMACONSET = _DMACON_SUSPEND_MASK;

		/* Wait until actually suspended. */
		while( DMACONbits.SUSPEND == 0 );
	}

	SYSKEY = 0;
	SYSKEY = hwUNLOCK_KEY_0;
	SYSKEY = hwUNLOCK_KEY_1;

	/* Read to start in sync. */
	xOSCCONBits.w = OSCCON;
	xOSCCONBits.PBDIV = 0;
	xOSCCONBits.w |= hwPERIPHERAL_CLOCK_DIV_BY_2;

	/* Write back. */
	OSCCON = xOSCCONBits.w;

	/* Ensure the write occurred. */
	xOSCCONBits.w = OSCCON;

	/* Lock again. */
	SYSKEY = hwLOCK_KEY;

	/* Resume DMA activity. */
	if( ulDMAStatus == 0 )
	{
		DMACONCLR=_DMACON_SUSPEND_MASK;
	}
}
/*-----------------------------------------------------------*/

static void prvConfigureWaitStates( void )
{
unsigned long ulSystemClock = configCPU_CLOCK_HZ - 1;
unsigned long ulWaitStates, ulCHECONVal;

	/* 1 wait state for every hwMAX_FLASH_SPEED MHz. */
	ulWaitStates = 0;

	while( ulSystemClock > hwMAX_FLASH_SPEED )
	{
		ulWaitStates++;
		ulSystemClock -= hwMAX_FLASH_SPEED;
	}

	/* Obtain current CHECON value. */
	ulCHECONVal = CHECON;

	/* Clear the wait state bits, then set the calculated wait state bits. */
	ulCHECONVal &= ~hwCHECON_WAIT_STAT_BITS;
	ulCHECONVal |= ulWaitStates;

	/* Write back the new value. */
	CHECON = ulWaitStates;
}
/*-----------------------------------------------------------*/

static void __attribute__ ((nomips16)) prvKSeg0CacheOn( void )
{
unsigned long ulValue;

	__asm volatile( "mfc0 %0, $16, 0" :  "=r"( ulValue ) );
	ulValue = ( ulValue & ~0x07) | 0x03;
	__asm volatile( "mtc0 %0, $16, 0" :: "r" ( ulValue ) );
}


