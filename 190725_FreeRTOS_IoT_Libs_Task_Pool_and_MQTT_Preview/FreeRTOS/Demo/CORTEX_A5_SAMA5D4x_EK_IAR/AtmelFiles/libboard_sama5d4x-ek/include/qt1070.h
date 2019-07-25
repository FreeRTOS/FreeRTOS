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


/**
  * \file
  *
  * Implementation QT1070 driver.
  *
  */

#ifndef QT1070_H
#define QT1070_H

#include "board.h"

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/
/** Slave address */
#define QT1070_SLAVE_ADDRESS    0x1B

/** Internal Register Address Allocation */

/** Chip ID register*/
#define QT1070_CHIP_ID          0
/** Firmware version register*/
#define QT1070_REG_FIRMWARE_VERSION 1
/** Detection status*/
#define QT1070_REG_DETECTION_STATUS 2
/** Key status*/
#define QT1070_REG_KEY_STATUS       3 
/** Key signal */
#define QT1070_REG_KEY0_SIGNAL_MSB  4
#define QT1070_REG_KEY0_SIGNAL_LSB  5
#define QT1070_REG_KEY1_SIGNAL_MSB  6
#define QT1070_REG_KEY1_SIGNAL_LSB  7
#define QT1070_REG_KEY2_SIGNAL_MSB  8
#define QT1070_REG_KEY2_SIGNAL_LSB  9
#define QT1070_REG_KEY3_SIGNAL_MSB  10
#define QT1070_REG_KEY3_SIGNAL_LSB  11
#define QT1070_REG_KEY4_SIGNAL_MSB  12
#define QT1070_REG_KEY4_SIGNAL_LSB  13
#define QT1070_REG_KEY5_SIGNAL_MSB  14
#define QT1070_REG_KEY5_SIGNAL_LSB  15
#define QT1070_REG_KEY6_SIGNAL_MSB  16
#define QT1070_REG_KEY6_SIGNAL_LSB  17

/** Reference date */
#define QT1070_REG_REFDATA0_MSB     18
#define QT1070_REG_REFDATA0_LSB     19
#define QT1070_REG_REFDATA1_MSB     20
#define QT1070_REG_REFDATA1_LSB     21
#define QT1070_REG_REFDATA2_MSB     22
#define QT1070_REG_REG_REFDATA2_LSB 23
#define QT1070_REG_REFDATA3_MSB     24
#define QT1070_REG_REG_REFDATA3_LSB 25
#define QT1070_REG_REFDATA4_MSB     26
#define QT1070_REG_REFDATA4_LSB     27
#define QT1070_REG_REFDATA5_MSB     28
#define QT1070_REG_REFDATA5_LSB     29
#define QT1070_REG_REFDATA6_MSB     30
#define QT1070_REG_REFDATA6_LSB     31

/** Negative threshold level */
#define QT1070_REG_NTHR_KEY0        32
#define QT1070_REG_NTHR_KEY1        33
#define QT1070_REG_NTHR_KEY2        34
#define QT1070_REG_NTHR_KEY3        35
#define QT1070_REG_NTHR_KEY4        36
#define QT1070_REG_NTHR_KEY5        37
#define QT1070_REG_NTHR_KEY6        38

/** Adjacent key suppression level */
#define QT1070_REG_AVEAKS_KEY0      39
#define QT1070_REG_AVEAKS_KEY1      40
#define QT1070_REG_AVEAKS_KEY2      41
#define QT1070_REG_AVEAKS_KEY3      42
#define QT1070_REG_AVEAKS_KEY4      43
#define QT1070_REG_AVEAKS_KEY5      44
#define QT1070_REG_AVEAKS_KEY6      45

/** Detection interator conter for key*/
#define QT1070_REG_DI_KEY0          46
#define QT1070_REG_DI_KEY1          47
#define QT1070_REG_DI_KEY2          48
#define QT1070_REG_DI_KEY3          49
#define QT1070_REG_DI_KEY4          50
#define QT1070_REG_DI_KEY5          51
#define QT1070_REG_DI_KEY6          52

/** Low power mode */
#define QT1070_REG_LOWPOWER_MODE    54
/** Maximum on duration */
#define QT1070_REG_MAX_DURATION     55
/** Calibrate */
#define QT1070_REG_CALIRATE         56
/** Reset */
#define QT1070_REG_RESET            57

/** Detection Status. */
/** This bit is set during a calibration sequence.*/
#define QT_CALIBRATE_BIT        7
/** This bit is set if the time to acquire all key signals exceeds 8 ms*/
#define QT_OVERFLOW_BIT         6
/** This bit is set if Comms mode is enabled. */
#define QT_COMMSENABLED_BIT     5
/** This bit is set if any keys are in detect. */
#define QT_TOUCH_BIT            0


/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

extern uint8_t QT1070_GetChipId(Twid *pTwid);
extern uint8_t QT1070_GetFirmwareVersion(Twid *pTwid);
extern uint8_t QT1070_GetDetection_Status(Twid *pTwid);
extern uint8_t QT1070_GetKey_Status(Twid *pTwid);
extern uint16_t QT1070_GetKey_Signal(Twid *pTwid, uint8_t key);
extern uint16_t QT1070_GetKey_Reference(Twid *pTwid, uint8_t key);
extern void QT1070_SetThreshold(Twid *pTwid, uint8_t key, uint8_t threshold);
extern void QT1070_SetAveAks(Twid *pTwid, uint8_t key, uint8_t Ave, uint8_t Aks);
extern void QT1070_SetDetectionIntegrator(Twid *pTwid, uint8_t key, uint8_t di);
extern void QT1070_StartCalibrate(Twid *pTwid);
extern void QT1070_StartReset(Twid *pTwid);
#endif // QT1070_H


