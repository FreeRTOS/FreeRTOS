/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

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
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest versions, license 
    and contact details.  
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*-----------------------------------------------------------
 * Portable layer API.  Each function must be defined for each port.
 *----------------------------------------------------------*/

#ifndef PORTABLE_H
#define PORTABLE_H

/* Include the macro file relevant to the port being used. */

#ifdef OPEN_WATCOM_INDUSTRIAL_PC_PORT
	#include "..\..\Source\portable\owatcom\16bitdos\pc\portmacro.h"
	typedef void ( __interrupt __far *pxISR )();
#endif

#ifdef OPEN_WATCOM_FLASH_LITE_186_PORT
	#include "..\..\Source\portable\owatcom\16bitdos\flsh186\portmacro.h"
	typedef void ( __interrupt __far *pxISR )();
#endif

#ifdef GCC_MEGA_AVR
	#include "../portable/GCC/ATMega323/portmacro.h"
#endif

#ifdef IAR_MEGA_AVR
	#include "../portable/IAR/ATMega323/portmacro.h"
#endif

#ifdef MPLAB_PIC24_PORT
	#include "..\..\Source\portable\MPLAB\PIC24_dsPIC\portmacro.h"
#endif

#ifdef MPLAB_DSPIC_PORT
	#include "..\..\Source\portable\MPLAB\PIC24_dsPIC\portmacro.h"
#endif

#ifdef MPLAB_PIC18F_PORT
	#include "..\..\Source\portable\MPLAB\PIC18F\portmacro.h"
#endif

#ifdef MPLAB_PIC32MX_PORT
	#include "..\..\Source\portable\MPLAB\PIC32MX\portmacro.h"
#endif

#ifdef _FEDPICC
	#include "libFreeRTOS/Include/portmacro.h"
#endif

#ifdef SDCC_CYGNAL
	#include "../../Source/portable/SDCC/Cygnal/portmacro.h"
#endif

#ifdef GCC_ARM7
	#include "../../Source/portable/GCC/ARM7_LPC2000/portmacro.h"
#endif

#ifdef GCC_ARM7_ECLIPSE
	#include "portmacro.h"
#endif

#ifdef ROWLEY_LPC23xx
	#include "../../Source/portable/GCC/ARM7_LPC23xx/portmacro.h"
#endif

#ifdef IAR_MSP430
	#include "..\..\Source\portable\IAR\MSP430\portmacro.h"	
#endif
	
#ifdef GCC_MSP430
	#include "../../Source/portable/GCC/MSP430F449/portmacro.h"
#endif

#ifdef ROWLEY_MSP430
	#include "../../Source/portable/Rowley/MSP430F449/portmacro.h"
#endif

#ifdef ARM7_LPC21xx_KEIL_RVDS
	#include "..\..\Source\portable\RVDS\ARM7_LPC21xx\portmacro.h"
#endif

#ifdef SAM7_GCC
	#include "../../Source/portable/GCC/ARM7_AT91SAM7S/portmacro.h"
#endif

#ifdef SAM7_IAR
	#include "..\..\Source\portable\IAR\AtmelSAM7S64\portmacro.h"
#endif

#ifdef SAM9XE_IAR
	#include "..\..\Source\portable\IAR\AtmelSAM9XE\portmacro.h"
#endif

#ifdef LPC2000_IAR
	#include "..\..\Source\portable\IAR\LPC2000\portmacro.h"
#endif

#ifdef STR71X_IAR
	#include "..\..\Source\portable\IAR\STR71x\portmacro.h"
#endif

#ifdef STR75X_IAR
	#include "..\..\Source\portable\IAR\STR75x\portmacro.h"
#endif
	
#ifdef STR75X_GCC
	#include "..\..\Source\portable\GCC\STR75x\portmacro.h"
#endif

#ifdef STR91X_IAR
	#include "..\..\Source\portable\IAR\STR91x\portmacro.h"
#endif
	
#ifdef GCC_H8S
	#include "../../Source/portable/GCC/H8S2329/portmacro.h"
#endif

#ifdef GCC_AT91FR40008
	#include "../../Source/portable/GCC/ARM7_AT91FR40008/portmacro.h"
#endif

#ifdef RVDS_ARMCM3_LM3S102
	#include "../../Source/portable/RVDS/ARM_CM3/portmacro.h"
#endif

#ifdef GCC_ARMCM3_LM3S102
	#include "../../Source/portable/GCC/ARM_CM3/portmacro.h"
#endif

#ifdef GCC_ARMCM3
	#include "../../Source/portable/GCC/ARM_CM3/portmacro.h"
#endif

#ifdef IAR_ARM_CM3
	#include "../../Source/portable/IAR/ARM_CM3/portmacro.h"
#endif

#ifdef IAR_ARMCM3_LM
	#include "../../Source/portable/IAR/ARM_CM3/portmacro.h"
#endif
	
#ifdef HCS12_CODE_WARRIOR
	#include "../../Source/portable/CodeWarrior/HCS12/portmacro.h"
#endif	

#ifdef MICROBLAZE_GCC
	#include "../../Source/portable/GCC/MicroBlaze/portmacro.h"
#endif

#ifdef TERN_EE
	#include "..\..\Source\portable\Paradigm\Tern_EE\small\portmacro.h"
#endif

#ifdef GCC_HCS12
	#include "../../Source/portable/GCC/HCS12/portmacro.h"
#endif

#ifdef GCC_MCF5235
    #include "../../Source/portable/GCC/MCF5235/portmacro.h"
#endif

#ifdef COLDFIRE_V2_GCC
	#include "../../../Source/portable/GCC/ColdFire_V2/portmacro.h"
#endif

#ifdef COLDFIRE_V2_CODEWARRIOR
	#include "../../Source/portable/CodeWarrior/ColdFire_V2/portmacro.h"
#endif

#ifdef GCC_PPC405
	#include "../../Source/portable/GCC/PPC405_Xilinx/portmacro.h"
#endif

#ifdef GCC_PPC440
	#include "../../Source/portable/GCC/PPC440_Xilinx/portmacro.h"
#endif

#ifdef _16FX_SOFTUNE
	#include "..\..\Source\portable\Softune\MB96340\portmacro.h"
#endif

#ifdef BCC_INDUSTRIAL_PC_PORT
	/* A short file name has to be used in place of the normal
	FreeRTOSConfig.h when using the Borland compiler. */
	#include "frconfig.h"
	#include "..\portable\BCC\16BitDOS\PC\prtmacro.h"
    typedef void ( __interrupt __far *pxISR )();
#endif

#ifdef BCC_FLASH_LITE_186_PORT
	/* A short file name has to be used in place of the normal
	FreeRTOSConfig.h when using the Borland compiler. */
	#include "frconfig.h"
	#include "..\portable\BCC\16BitDOS\flsh186\prtmacro.h"
    typedef void ( __interrupt __far *pxISR )();
#endif

#ifdef __GNUC__
   #ifdef __AVR32_AVR32A__
	   #include "portmacro.h"
   #endif
#endif

#ifdef __ICCAVR32__
   #ifdef __CORE__
      #if __CORE__ == __AVR32A__
	      #include "portmacro.h"
      #endif
   #endif
#endif

#ifdef __91467D
	#include "portmacro.h"
#endif

#ifdef __96340
	#include "portmacro.h"
#endif


#ifdef __IAR_V850ES_Fx3__
	#include "../../Source/portable/IAR/V850ES/portmacro.h"
#endif

#ifdef __IAR_V850ES_Jx3__
	#include "../../Source/portable/IAR/V850ES/portmacro.h"
#endif

#ifdef __IAR_V850ES_Jx3_L__
	#include "../../Source/portable/IAR/V850ES/portmacro.h"
#endif

#ifdef __IAR_V850ES_Jx2__
	#include "../../Source/portable/IAR/V850ES/portmacro.h"
#endif

#ifdef __IAR_V850ES_Hx2__
	#include "../../Source/portable/IAR/V850ES/portmacro.h"
#endif

#ifdef __IAR_78K0R_Kx3__
	#include "../../Source/portable/IAR/78K0R/portmacro.h"
#endif
	
#ifdef __IAR_78K0R_Kx3L__
	#include "../../Source/portable/IAR/78K0R/portmacro.h"
#endif
	
/* Catch all to ensure portmacro.h is included in the build.  Newer demos
have the path as part of the project options, rather than as relative from
the project location.  If portENTER_CRITICAL() has not been defined then
portmacro.h has not yet been included - as every portmacro.h provides a
portENTER_CRITICAL() definition.  Check the demo application for your demo
to find the path to the correct portmacro.h file. */
#ifndef portENTER_CRITICAL
	#include "portmacro.h"	
#endif
	
#if portBYTE_ALIGNMENT == 8
	#define portBYTE_ALIGNMENT_MASK ( 0x0007 )
#endif

#if portBYTE_ALIGNMENT == 4
	#define portBYTE_ALIGNMENT_MASK	( 0x0003 )
#endif

#if portBYTE_ALIGNMENT == 2
	#define portBYTE_ALIGNMENT_MASK	( 0x0001 )
#endif

#if portBYTE_ALIGNMENT == 1
	#define portBYTE_ALIGNMENT_MASK	( 0x0000 )
#endif

#ifndef portBYTE_ALIGNMENT_MASK
	#error "Invalid portBYTE_ALIGNMENT definition"
#endif

#ifndef portNUM_CONFIGURABLE_REGIONS
	#define portNUM_CONFIGURABLE_REGIONS 1
#endif

#ifdef __cplusplus
extern "C" {
#endif

#include "mpu_wrappers.h"

/*
 * Setup the stack of a new task so it is ready to be placed under the
 * scheduler control.  The registers have to be placed on the stack in
 * the order that the port expects to find them.
 *
 */
#if( portUSING_MPU_WRAPPERS == 1 )
	portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters, portBASE_TYPE xRunPrivileged ) PRIVILEGED_FUNCTION;
#else
	portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters );
#endif

/*
 * Map to the memory management routines required for the port.
 */
void *pvPortMalloc( size_t xSize ) PRIVILEGED_FUNCTION;
void vPortFree( void *pv ) PRIVILEGED_FUNCTION;
void vPortInitialiseBlocks( void ) PRIVILEGED_FUNCTION;
size_t xPortGetFreeHeapSize( void ) PRIVILEGED_FUNCTION;

/*
 * Setup the hardware ready for the scheduler to take control.  This generally
 * sets up a tick interrupt and sets timers for the correct tick frequency.
 */
portBASE_TYPE xPortStartScheduler( void ) PRIVILEGED_FUNCTION;

/*
 * Undo any hardware/ISR setup that was performed by xPortStartScheduler() so
 * the hardware is left in its original condition after the scheduler stops
 * executing.
 */
void vPortEndScheduler( void ) PRIVILEGED_FUNCTION;

/*
 * The structures and methods of manipulating the MPU are contained within the
 * port layer.
 *
 * Fills the xMPUSettings structure with the memory region information
 * contained in xRegions.
 */
#if( portUSING_MPU_WRAPPERS == 1 ) 
	struct xMEMORY_REGION;
	void vPortStoreTaskMPUSettings( xMPU_SETTINGS *xMPUSettings, const struct xMEMORY_REGION * const xRegions, portSTACK_TYPE *pxBottomOfStack, unsigned short usStackDepth ) PRIVILEGED_FUNCTION;
#endif

#ifdef __cplusplus
}
#endif

#endif /* PORTABLE_H */

