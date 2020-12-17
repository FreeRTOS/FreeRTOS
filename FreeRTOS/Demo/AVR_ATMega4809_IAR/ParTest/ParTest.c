/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

#define partstALL_BITS_OUTPUT   ( ( unsigned char ) 0xff )
#define partstALL_OUTPUTS_OFF   ( ( unsigned char ) 0xff )
#define partstMAX_OUTPUT_LED    ( ( unsigned char ) 7 )

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
    PORTF.DIRSET = partstALL_BITS_OUTPUT;
    PORTF.OUTCLR = partstALL_OUTPUTS_OFF;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( UBaseType_t uxLED, BaseType_t xValue )
{
unsigned char ucBit = ( unsigned char ) 1;

    if( uxLED <= partstMAX_OUTPUT_LED )
    {
        ucBit <<= uxLED;

        vTaskSuspendAll();
        {
            if( xValue == pdTRUE )
            {
                PORTF.OUTSET = ucBit;
            }
            else
            {
                PORTF.OUTCLR = ucBit;
            }

        }
        xTaskResumeAll();
    }
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( UBaseType_t uxLED )
{
unsigned char ucBit;

    if( uxLED <= partstMAX_OUTPUT_LED )
    {
        ucBit = ( ( unsigned char ) 1 ) << uxLED;

        vTaskSuspendAll();
        {
            PORTF.OUTTGL = ucBit;
        }
        xTaskResumeAll();
    }
}