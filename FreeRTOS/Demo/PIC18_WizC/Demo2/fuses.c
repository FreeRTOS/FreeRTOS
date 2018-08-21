/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
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
