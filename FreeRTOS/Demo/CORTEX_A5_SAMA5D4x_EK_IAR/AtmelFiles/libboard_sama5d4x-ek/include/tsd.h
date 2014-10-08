/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file */

/**
 * \addtogroup tsd_module TouchScreen Driver
 *
 * \section Purpose
 * 
 * This unit provides a very powerful touchscreen driver which handles all the
 * complexity. This includes touchscreen calibration, retrieving measurements,
 * configuring the TSADC, etc.
 * 
 * \section Usage
 *
 * -# Implement ADC interrupt handler in application, to invoke TSD_Handler()
 *    to handle ADC sampling events for touchscreen monitor.
 * -# Call TSD_Initialize() to initialize ADC used for touchscreen.
 * -# Call TSD_Calibrate() to do touchscreen calibration with LCD, and enable
 *    touchscreen monitor if calibration success.
 * -# Call TSD_Enable() to enable or disable touchscreen monitoring.
 * -# Declare a global TSD_PenPressed() function anywhere in your code. This
 *    function will get called every time the pen is pressed on the screen.
 * -# Declare a global TSD_PenMoved() function, which will get called whenever
 *    the pen stays in contact with the screen but changes position.
 * -# Declare a global TSD_PenReleased() function, which will be invoked as the
 *    pen is lifted from the screen.
 */

#ifndef TSD_H
#define TSD_H

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

extern void TSD_Handler(uint32_t dwAdcStatus);
extern void TSD_Initialize(void);
extern void TSD_DeInitialize(void);
extern void TSD_Enable(uint8_t bEnDis);
extern uint8_t TSD_Calibrate(void);

/* calibration used functions */
extern void TSD_GetRawMeasurement(uint32_t * pData);
extern void TSD_WaitPenPressed(void);
extern void TSD_WaitPenReleased(void);

/* callbacks */
extern void TSD_PenPressed(uint32_t x, uint32_t y, uint32_t pressure);
extern void TSD_PenMoved(uint32_t x, uint32_t y, uint32_t pressure);
extern void TSD_PenReleased(uint32_t x, uint32_t y);

#endif //#ifndef TSD_H
