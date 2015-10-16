/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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
Changes from V3.0.0

Changes from V3.0.1
*/

/*
** Here are the configuration words set. See the PIC datasheet
** and the wizC manual for an explanation
*/
#include <pic.h>

/*
** These fuses are for PIC18F4620
*/
#pragma __config _CONFIG1H,_IESO_OFF_1H & _FCMEN_OFF_1H & _OSC_HSPLL_1H
#pragma __config _CONFIG2L,_BORV_21_2L & _BOREN_SBORDIS_2L & _PWRT_ON_2L
#pragma __config _CONFIG2H,_WDTPS_32768_2H & _WDT_OFF_2H
#pragma __config _CONFIG3H,_MCLRE_ON_3H & _LPT1OSC_OFF_3H & _PBADEN_OFF_3H & _CCP2MX_PORTC_3H
#pragma __config _CONFIG4L,_DEBUG_OFF_4L & _XINST_OFF_4L & _LVP_OFF_4L & _STVREN_OFF_4L
#pragma __config _CONFIG5L,_CP3_OFF_5L & _CP2_OFF_5L & _CP1_OFF_5L & _CP0_OFF_5L
#pragma __config _CONFIG5H,_CPD_OFF_5H & _CPB_OFF_5H
#pragma __config _CONFIG6L,_WRT3_OFF_6L & _WRT2_OFF_6L & _WRT1_OFF_6L & _WRT0_OFF_6L
#pragma __config _CONFIG6H,_WRTD_OFF_6H & _WRTB_OFF_6H & _WRTC_OFF_6H
#pragma __config _CONFIG7L,_EBTR3_OFF_7L & _EBTR2_OFF_7L & _EBTR1_OFF_7L & _EBTR0_OFF_7L
#pragma __config _CONFIG7H,_EBTRB_OFF_7H
