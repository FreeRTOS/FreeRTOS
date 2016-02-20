/***************************************************************************//**
 * @file em_bitband.h
 * @brief Bitband Peripheral API
 * @version 4.2.1
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2015 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Silicon Labs has no
 * obligation to support this Software. Silicon Labs is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Silicon Labs will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 ******************************************************************************/

#ifndef __SILICON_LABS_EM_BITBAND_H__
#define __SILICON_LABS_EM_BITBAND_H__

#include "em_bus.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup BITBAND
 * @brief BITBAND Peripheral API (deprecated - use em_bus.h)
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @brief
 *   Perform bit-band operation on peripheral memory location.
 *
 * @details
 *   Bit-banding provides atomic read-modify-write cycle for single bit
 *   modification. Please refer to the reference manual for further details
 *   about bit-banding.
 *
 * @note
 *   This function is only atomic on cores which fully support bitbanding.
 *
 * @param[in] addr Peripheral address location to modify bit in.
 *
 * @param[in] bit Bit position to modify, 0-31.
 *
 * @param[in] val Value to set bit to, 0 or 1.
 ******************************************************************************/
#define BITBAND_Peripheral(addr, bit, val) BUS_RegBitWrite(addr, bit, val)


/***************************************************************************//**
 * @brief
 *   Perform a read operation on the peripheral bit-band memory location.
 *
 * @details
 *   This function reads a single bit from the peripheral bit-band alias region.
 *   Bit-banding provides atomic read-modify-write cycle for single bit
 *   modification. Please refer to the reference manual for further details
 *   about bit-banding.
 *
 * @param[in] addr   Peripheral address location to read.
 *
 * @param[in] bit    Bit position to read, 0-31.
 *
 * @return           Value of the requested bit.
 ******************************************************************************/
#define BITBAND_PeripheralRead(addr, bit) BUS_RegBitRead(addr, bit)


/***************************************************************************//**
 * @brief
 *   Perform bit-band operation on SRAM memory location.
 *
 * @details
 *   Bit-banding provides atomic read-modify-write cycle for single bit
 *   modification. Please refer to the reference manual for further details
 *   about bit-banding.
 *
 * @note
 *   This function is only atomic on cores which fully support bitbanding.
 *
 * @param[in] addr SRAM address location to modify bit in.
 *
 * @param[in] bit Bit position to modify, 0-31.
 *
 * @param[in] val Value to set bit to, 0 or 1.
 ******************************************************************************/
#define BITBAND_SRAM(addr, bit, val) BUS_RamBitWrite(addr, bit, val)


/***************************************************************************//**
 * @brief
 *   Read a single bit from the SRAM bit-band alias region.
 *
 * @details
 *   This function reads a single bit from the SRAM bit-band alias region.
 *   Bit-banding provides atomic read-modify-write cycle for single bit
 *   modification. Please refer to the reference manual for further details
 *   about bit-banding.
 *
 * @param[in] addr    SRAM address location to modify bit in.
 *
 * @param[in] bit     Bit position to modify, 0-31.
 *
 * @return            Value of the requested bit.
 ******************************************************************************/
#define BITBAND_SRAMRead(addr, bit) BUS_RamBitRead(addr, bit)

/** @} (end addtogroup BITBAND) */
/** @} (end addtogroup EM_Library) */

#ifdef __cplusplus
}
#endif

#endif /* __SILICON_LABS_EM_BITBAND_H__ */
