/**************************************************************************//**
 * @file
 * @brief EFM32 Segment LCD Display driver, header file
 * @version 4.2.1
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/


#ifndef __SEGMENTLCD_H
#define __SEGMENTLCD_H

#include <stdint.h>
#include <stdbool.h>

#include "segmentlcdconfig.h"

/***************************************************************************//**
 * @addtogroup Drivers
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup SegmentLcd
 * @{
 ******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

/* Regular functions */
void SegmentLCD_AllOff(void);
void SegmentLCD_AllOn(void);
void SegmentLCD_AlphaNumberOff(void);
void SegmentLCD_ARing(int anum, int on);
void SegmentLCD_Battery(int batteryLevel);
void SegmentLCD_Disable(void);
void SegmentLCD_EnergyMode(int em, int on);
void SegmentLCD_Init(bool useBoost);
void SegmentLCD_LowerHex( uint32_t num );
void SegmentLCD_LowerNumber( int num );
void SegmentLCD_Number(int value);
void SegmentLCD_NumberOff(void);
void SegmentLCD_Symbol(lcdSymbol s, int on);
void SegmentLCD_UnsignedHex(uint16_t value);
void SegmentLCD_Write(char *string);

#ifdef __cplusplus
}
#endif

/** @} (end group SegmentLcd) */
/** @} (end group Drivers) */

#endif
