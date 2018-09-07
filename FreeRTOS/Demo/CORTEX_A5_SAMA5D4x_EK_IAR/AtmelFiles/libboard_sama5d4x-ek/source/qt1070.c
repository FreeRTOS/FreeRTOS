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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Read one byte of data from QT1070 Register.
 *
 * \param pTwid   Pointer to twi driver structure.
 * \param regAddr Register address to read.
 * \return value in the given register.
 */
static uint8_t QT1070_ReadReg(Twid *pTwid, uint8_t regAddr)
{
    uint8_t data;
    TWID_Write(pTwid, QT1070_SLAVE_ADDRESS, 0, 0, &regAddr, 1, 0);
    TWID_Read(pTwid, QT1070_SLAVE_ADDRESS, 0, 0, &data, 1, 0);
    return data;
}

/**
 * \brief  Write one byte of data to QT1070 Register.
 *
 * \param pTwid   Pointer to twi driver structure.
 * \param regAddr Register address to write.
 * \param data    Data to write.
 */
static void QT1070_WriteReg(Twid *pTwid, uint32_t regAddr, uint8_t data)
{
    TWID_Write(pTwid, QT1070_SLAVE_ADDRESS, regAddr, 1, &data, 1, 0);
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief  Get qt1070 chip ID.
 *
 * \param pTwid   Pointer to twi driver structure.
 * \return Chip Id
 */

uint8_t QT1070_GetChipId(Twid *pTwid)
{
    return QT1070_ReadReg( pTwid, QT1070_CHIP_ID);
}

/**
 * \brief  Get qt1070 firmware version number.
 *
 * \param pTwid   Pointer to twi driver structure.
 * \return Firmware version number.
 */

uint8_t QT1070_GetFirmwareVersion(Twid *pTwid)
{
    return QT1070_ReadReg( pTwid, QT1070_REG_FIRMWARE_VERSION);
}

 /**
 * \brief  Get qt1070 detection status.
 *
 * \param pTwid   Pointer to twi driver structure.
 * \return Dectection status.
 */

uint8_t QT1070_GetDetection_Status(Twid *pTwid)
{
    return QT1070_ReadReg( pTwid, QT1070_REG_DETECTION_STATUS);
}

/**
 * \brief  Get qt1070 Key status. 
 *
 * \param pTwid   Pointer to twi driver structure.
 * \return Key status.
 */
uint8_t QT1070_GetKey_Status(Twid *pTwid)
{
    return QT1070_ReadReg( pTwid, QT1070_REG_KEY_STATUS);
}

/**
 * \brief  Get qt1070 key signal value in the given Key. These are the key's
 * of 16-bit key signals which are accessed as two 8-bit bytes,stored MSB first
 *
 * \param pTwid   Pointer to twi driver structure.
 * \param key     Key index.
 * \return Key signal value.
 */
uint16_t QT1070_GetKey_Signal(Twid *pTwid, uint8_t key)
{
    uint8_t data[2];
    data[0] = QT1070_ReadReg( pTwid, QT1070_REG_KEY0_SIGNAL_MSB + key * 2);
    data[1] = QT1070_ReadReg( pTwid, QT1070_REG_KEY0_SIGNAL_LSB + key * 2);
    return (data[0] << 8) | data[1];
}

/**
 * \brief  Get qt1070 key reference data in the given Key. These are the key's
 * of 16-bit key reference data which are accessed as two 8-bit bytes, stored MSB first
 *
 * \param pTwid   Pointer to twi driver structure.
 * \param key     Key index.
 * \return Key reference data.
 */
uint16_t QT1070_GetKey_Reference(Twid *pTwid, uint8_t key)
{
    uint8_t data[2];
    data[0] = QT1070_ReadReg( pTwid, QT1070_REG_REFDATA0_MSB + key * 2);
    data[1] = QT1070_ReadReg( pTwid, QT1070_REG_REFDATA0_LSB + key * 2);
    return (data[0] << 8) | data[1];
}

/**
 * \brief  Set the threshold value for the given Key. 
 *
 * \param pTwid   Pointer to twi driver structure.
 * \param key     Key index.
 * \param threshold Threshold value.
 */
void QT1070_SetThreshold(Twid *pTwid, uint8_t key, uint8_t threshold)
{
    // Do not use a setting of 0 as this causes a key to go into detection 
    // when its signal is equal to its reference.
    if ( threshold ) 
    {
        QT1070_WriteReg(pTwid, QT1070_REG_NTHR_KEY0 + key, threshold);
    }
}

/**
 * \brief  Set Averaging factor and adjacent key suppression for the given Key. 
 *
 * \param pTwid   Pointer to twi driver structure.
 * \param key     Key index.
 * \param Ave     Averaging factor.
 * \param Aks     AKS group index.
 */
void QT1070_SetAveAks(Twid *pTwid, uint8_t key, uint8_t Ave, uint8_t Aks)
{
    QT1070_WriteReg(pTwid, QT1070_REG_AVEAKS_KEY0 + key, (Ave << 3) | Aks ); 
}

/**
 * \brief Set DI level for the given Key. This 8-bit value controls the number
 * of consecutive measurement that must be confirmed as having passed the key threshold
 * before that key is registered as being in detect.
 *
 * \param pTwid   Pointer to twi driver structure.
 * \param key     Key index.
 * \param di      DI level.
 */

void QT1070_SetDetectionIntegrator(Twid *pTwid, uint8_t key, uint8_t di)
{
    QT1070_WriteReg(pTwid, QT1070_REG_DI_KEY0 + key, di); 
}
 
/**
 * \brief Start a calibration cycle, the CALIBTATE flag in the detection status
 * register is set when the calibration begins and clears when the calibration
 * has finished.
 *
 * \param pTwid   Pointer to twi driver structure.
 */

void QT1070_StartCalibrate(Twid *pTwid)
{
    QT1070_WriteReg(pTwid, QT1070_REG_CALIRATE , 1); 
}

/**
 * \brief Reset the qt1070 device.
 *
 * \param pTwid   Pointer to twi driver structure.
 */

void QT1070_StartReset(Twid *pTwid)
{
    QT1070_WriteReg(pTwid, QT1070_REG_RESET , 1); 
}
