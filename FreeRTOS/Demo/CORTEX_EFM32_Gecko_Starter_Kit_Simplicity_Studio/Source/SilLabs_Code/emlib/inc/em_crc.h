/***************************************************************************//**
 * @file
 * @brief Cyclic Redundancy Check (CRC) API.
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

#ifndef __SILICON_LABS_EM_CRC_H__
#define __SILICON_LABS_EM_CRC_H__

#include "em_device.h"
#if defined(CRC_COUNT) && (CRC_COUNT > 0)

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup CRC
 * @{
 ******************************************************************************/

/*******************************************************************************
 ********************************   ENUMS   ************************************
 ******************************************************************************/

/** CRC width values. */
typedef enum
{
  /** 8 bit (1 byte) CRC code. */
  crcWidth8 = CRC_CTRL_CRCWIDTH_CRCWIDTH8,

  /** 16 bit (2 byte) CRC code. */
  crcWidth16 = CRC_CTRL_CRCWIDTH_CRCWIDTH16,

  /** 24 bit (3 byte) CRC code. */
  crcWidth24 = CRC_CTRL_CRCWIDTH_CRCWIDTH24,

  /** 32 bit (4 byte) CRC code. */
  crcWidth32 = CRC_CTRL_CRCWIDTH_CRCWIDTH32
} CRC_Width_TypeDef;


/** CRC byte reverse values. */
typedef enum
{
  /** Most significant CRC bytes are transferred first over air via the Frame
   *  Controller (FRC). */
  crcByteOrderNormal = CRC_CTRL_BYTEREVERSE_NORMAL,

  /** Least significant CRC bytes are transferred first over air via the Frame
   *  Controller (FRC). */
  crcByteOrderReversed = CRC_CTRL_BYTEREVERSE_REVERSED
} CRC_ByteOrder_TypeDef;


/** CRC bit order values. */
typedef enum
{
  /** Least significant data bit (LSB) is fed first to the CRC generator. */
  crcBitOrderLSBFirst = CRC_CTRL_INPUTBITORDER_LSBFIRST,

  /** Most significant data bit (MSB) is fed first to the CRC generator. */
  crcBitOrderMSBFirst = CRC_CTRL_INPUTBITORDER_MSBFIRST
} CRC_BitOrder_TypeDef;


/** CRC bit reverse values. */
typedef enum
{
  /** The bit ordering of CRC data is the same as defined by the BITORDER field
   *  in the Frame Controller. */
  crcBitReverseNormal = CRC_CTRL_BITREVERSE_NORMAL,

  /** The bit ordering of CRC data is the opposite as defined by the BITORDER
   *  field in the Frame Controller. */
  crcBitReverseReversed = CRC_CTRL_BITREVERSE_REVERSED
} CRC_BitReverse_TypeDef;


/*******************************************************************************
 *******************************   STRUCTS   ***********************************
 ******************************************************************************/

/** CRC initialization structure. */
typedef struct
{
  /** Width of the CRC code. */
  CRC_Width_TypeDef         crcWidth;

  /** CRC polynomial value. This value defines POLY[31:0], which is used as the
   *  polynomial (in reversed order) during the CRC calculation. If the CRC
   *  width is less than 32 bits, the most significant part of this register
   *  remains unused.
   *  - Set the bit to 1 in the register to get the corresponding degree term
   *  appear in the polynomial with a coefficient of 1.
   *  - Set the bit to 0 in the register to get the corresponding degree term
   *  appear in the polynomial with a coefficient of 0.
   *  Note: If a CRC polynomial of size less than 32 bits is to be used, the
   *  polynomial value must be shifted so that the highest degree term is
   *  located in DATA[0]!
   *  Please refer to the CRC sub-chapter "CRC Polynomial" in the documentation
   *  for more details! */
  uint32_t                   crcPoly;

  /** CRC initialization value. Loaded into the CRC_DATA register upon issuing
   *  the INIT command by calling CRC_InitCommand(), or when the Frame
   *  Controller (FRC) uses the CRC for automatic CRC calculation and
   *  verification. */
  uint32_t                   initValue;

  /** Number of bits per input word. This value defines the number of valid
   *  input bits in the CRC_INPUTDATA register, or in data coming from the Frame
   *  Controller (FRC). The number of bits in each word equals to
   *  (BITSPERWORD + EXTRABITSPERWORD + 1), where EXTRABITSPERWORD is taken from
   *  the currently active Frame Control Descriptor (FCD). */
  uint8_t                    bitsPerWord;

  /** If true, the byte order is reversed and the least significant CRC bytes
   *  are transferred first over the air. (description TBD) */
  CRC_ByteOrder_TypeDef      byteReverse;

  /** Bit order. Defines the order in which bits are fed to the CRC generator.
   *  This setting applies both to data written to the CRC_INPUTDATA register,
   *  and data coming from the Frame Controller (FRC). */
  CRC_BitOrder_TypeDef       inputBitOrder;

  /** Output bit reverse. In most cases, the bit ordering of the CRC value
   *  corresponds to the bit ordering of other data transmitted over air. When
   *  set, the BITREVERSE field has the possibility to reverse this bit ordering
   *  to comply with some protocols. Note that this field does not affect the
   *  way the CRC value is calculated, only how it is transmitted over air. */
  CRC_BitReverse_TypeDef     bitReverse;

  /** Enable/disable CRC input data padding. When set, CRC input data is zero-
   *  padded, such that the number of bytes over which the CRC value is
   *  calculated at least equals the length of the calculated CRC value. If not
   *  set, no zero-padding of CRC input data is applied. */
  bool                       inputPadding;

  /** If true, CRC input is inverted. */
  bool                       invInput;

  /** If true, CRC output to the Frame Controller (FRC) is inverted. */
  bool                       invOutput;
} CRC_Init_TypeDef;

/** Default configuration for CRC_Init_TypeDef structure. */
#define CRC_INIT_DEFAULT                                              \
{                                                                     \
  crcWidth16,           /* CRC width is 16 bits. */                   \
  0x00008408UL,         /* Polynomial value of IEEE 802.15.4-2006. */ \
  0x00000000UL,         /* Initialization value. */                   \
  8U,                   /* 8 bits per word. */                        \
  crcByteOrderNormal,   /* Byte order is normal. */                   \
  crcBitOrderLSBFirst,  /* Bit order (TBD). */                        \
  crcBitReverseNormal,  /* Bit order is not reversed on output. */    \
  false,                /* No zero-padding. */                        \
  false,                /* Input is not inverted. */                  \
  false                 /* Output is not inverted. */                 \
}


/*******************************************************************************
 ******************************   PROTOTYPES   *********************************
 ******************************************************************************/

void CRC_Init(CRC_Init_TypeDef const *init);
void CRC_Reset(void);

/***************************************************************************//**
 * @brief
 *   Issues a command to initialize the CRC calculation.
 *
 * @details
 *   This function issues the command INITIALIZE in CRC_CMD that initializes the
 *   CRC calculation by writing the initial values to the DATA register.
 *
 * @note
 *   Internal notes:
 *   Initialize in CRC_CMD
 *   Conclude on reference of parameters. Register names or config struct members?
 ******************************************************************************/
__STATIC_INLINE void CRC_InitCommand(void)
{
  CRC->CMD = CRC_CMD_INITIALIZE;
}


/***************************************************************************//**
 * @brief
 *   Set the initialization value of the CRC.
 ******************************************************************************/
__STATIC_INLINE void CRC_InitValueSet(uint32_t initValue)
{
  CRC->INIT = initValue;
}


/***************************************************************************//**
 * @brief
 *   Writes data to the input data register of the CRC.
 *
 * @details
 *   Use this function to write input data to the CRC when the FRC is not being
 *   used for automatic handling of the CRC. The CRC calculation is based on
 *   the provided input data using the configured CRC polynomial.
 *
 * @param[in] data
 *   Data to be written to the input data register.
 ******************************************************************************/
__STATIC_INLINE void CRC_InputDataWrite(uint16_t data)
{
  CRC->INPUTDATA = (uint32_t)data;
}


/***************************************************************************//**
 * @brief
 *   Reads the data register of the CRC.
 *
 * @details
 *   Use this function to read the calculated CRC value.
 *
 * @return
 *   Content of the CRC data register.
 ******************************************************************************/
__STATIC_INLINE uint32_t CRC_DataRead(void)
{
  return CRC->DATA;
}


/***************************************************************************//**
 * @brief
 *   Gets if the CRC is busy.
 *
 * @details
 *   Returns true when the CRC module is busy, false otherwise.
 *
 * @return
 *   CRC busy flag.
 *   @li true - CRC module is busy.
 *   @li false - CRC module is not busy.
 ******************************************************************************/
__STATIC_INLINE bool CRC_BusyGet(void)
{
  return (bool)((CRC->STATUS & _CRC_STATUS_BUSY_MASK)
                >> _CRC_STATUS_BUSY_SHIFT);
}


/** @} (end addtogroup CRC) */
/** @} (end addtogroup EM_Library) */

#ifdef __cplusplus
}
#endif

#endif /* defined(CRC_COUNT) && (CRC_COUNT > 0) */
#endif /* __SILICON_LABS_EM_CRC_H__ */
