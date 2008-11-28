/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http:www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

/*-----------------------------------------------------------
 * Portable layer API.  Each function must be defined for each port.
 *----------------------------------------------------------*/

#ifndef PORTABLE_H
#define PORTABLE_H

/* Include the macro file relevant to the port being used. */

#ifdef OPEN_WATCOM_INDUSTRIAL_PC_PORT
	#include "..\..\source\portable\owatcom\16bitdos\pc\portmacro.h"
	typedef void ( __interrupt __far *pxISR )();
#endif

#ifdef OPEN_WATCOM_FLASH_LITE_186_PORT
	#include "..\..\source\portable\owatcom\16bitdos\flsh186\portmacro.h"
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
	#include "..\..\source\portable\MPLAB\PIC18F\portmacro.h"
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
	#include "../../../source/portable/GCC/ColdFire_V2/portmacro.h"
#endif

#ifdef COLDFIRE_V2_CODEWARRIOR
	#include "../../Source/portable/CodeWarrior/ColdFire_V2/portmacro.h"
#endif

#ifdef GCC_PPC405
	#include "../../Source/portable/GCC/PPC405_Xilinx/portmacro.h"
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

#ifdef __cplusplus
extern "C" {
#endif
/*
 * Setup the stack of a new task so it is ready to be placed under the
 * scheduler control.  The registers have to be placed on the stack in
 * the order that the port expects to find them.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters );

/*
 * Map to the memory management routines required for the port.
 */
void *pvPortMalloc( size_t xSize );
void vPortFree( void *pv );
void vPortInitialiseBlocks( void );

/*
 * Setup the hardware ready for the scheduler to take control.  This generally
 * sets up a tick interrupt and sets timers for the correct tick frequency.
 */
portBASE_TYPE xPortStartScheduler( void );

/*
 * Undo any hardware/ISR setup that was performed by xPortStartScheduler() so
 * the hardware is left in its original condition after the scheduler stops
 * executing.
 */
void vPortEndScheduler( void );

#ifdef __cplusplus
}
#endif

#endif /* PORTABLE_H */

