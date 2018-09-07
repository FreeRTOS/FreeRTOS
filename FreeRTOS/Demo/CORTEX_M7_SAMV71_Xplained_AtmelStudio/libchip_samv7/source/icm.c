/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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
 * DISCLAIMED. IN NO EVENT ICMLL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \addtogroup icm_module Working with ICM
 * The TWI driver provides the interface to True Random Number Generator (ICM) passes the American NIST Special Publication 800-22 and Diehard
 Random Tests Suites.
 The ICM may be used as an entropy source for seeding an NIST approved DRNG (Deterministic RNG) as required by
 FIPS PUB 140-2 and 140-3. use the TWI
 * peripheral.
 *
 * \section Usage
 * <ul>
 * <li> Configures a TWI peripheral to operate in master mode, at the given
 * frequency (in Hz) using TWI_Configure(). </li>
 * <li> Sends a STOP condition on the TWI using TWI_Stop().</li>
 * <li> Starts a read operation on the TWI bus with the specified slave using
 * TWI_StartRead(). Data must then be read using TWI_ReadByte() whenever
 * a byte is available (poll using TWI_ByteReceived()).</li>
 * <li> Starts a write operation on the TWI to access the selected slave using
 * TWI_StartWrite(). A byte of data must be provided to start the write;
 * other bytes are written next.</li>
 * <li> Sends a byte of data to one of the TWI slaves on the bus using TWI_WriteByte().
 * This function must be called once before TWI_StartWrite() with the first byte of data
 * to send, then it ICMll be called repeatedly after that to send the remaining bytes.</li>
 * <li> Check if a byte has been received and can be read on the given TWI
 * peripheral using TWI_ByteReceived().<
 * Check if a byte has been sent using TWI_ByteSent().</li>
 * <li> Check if the current transmission is complete (the STOP has been sent)
 * using TWI_TransferComplete().</li>
 * <li> Enables & disable the selected interrupts sources on a TWI peripheral
 * using TWI_EnableIt() and TWI_DisableIt().</li>
 * <li> Get current status register of the given TWI peripheral using
 * TWI_GetStatus(). Get current status register of the given TWI peripheral, but
 * masking interrupt sources which are not currently enabled using
 * TWI_GetMaskedStatus().</li>
 * </ul>
 * For more accurate information, please look at the TWI section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref twi.c\n
 * \ref twi.h.\n
 */
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of True Random Number Generator (ICM)
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enable ICM, the ICM controller is activated
 */
void ICM_Enable(void)
{
    ICM->ICM_CTRL = ICM_CTRL_ENABLE;
}

/**
 * \brief Disable ICM, if a region is active, this region is terminated
 */
void ICM_Disable(void)
{
    ICM->ICM_CTRL = ICM_CTRL_DISABLE;
}

/**
 * \brief Resets the ICM controller.
 */
void ICM_SoftReset(void)
{
    ICM->ICM_CTRL = ICM_CTRL_SWRST;
}

/**
 * \brief Recompute Internal hash.
 * \param region, When REHASH[region] is set to one, the region digest is re-computed. 
 * \note This bit is only available when Region monitoring is disabled.
 */
void ICM_ReComputeHash(uint8_t region)
{
    ICM->ICM_CTRL = ICM_CTRL_REHASH(region);
}

/**
 * \brief Enable region monitoring for given region
 * \param region, When bit RMEN[region] is set to one, the monitoring of Region is activated.
 */
void ICM_EnableMonitor(uint8_t region)
{
    ICM->ICM_CTRL = ICM_CTRL_RMEN(region);
}

/**
 * \brief Disable region monitoring for given region
 * \param region, When bit RMDIS[region] is set to one, the monitoring of Region is disabled.
 */
void ICM_DisableMonitor(uint8_t region)
{
    ICM->ICM_CTRL = ICM_CTRL_RMDIS(region);
}

/**
 * \brief Configures an ICM peripheral with the specified parameters.
 *  \param mode  Desired value for the ICM mode register (see the datasheet).
 */
void ICM_Configure(uint32_t mode)
{
    ICM->ICM_CFG = mode; 
}

/**
 * \brief Enables the selected interrupts sources on a ICM peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void ICM_EnableIt(uint32_t sources)
{
    ICM->ICM_IER = sources;
}

/**
 * \brief Disables the selected interrupts sources on a ICM peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void ICM_DisableIt(uint32_t sources)
{
    ICM->ICM_IDR = sources;
}

/**
 * \brief Get the current interrupt status register of the given ICM peripheral.
 * \return  ICM status register.
 */
uint32_t ICM_GetIntStatus(void)
{
    return ICM->ICM_ISR;
}

/**
 * \brief Get the current status register of the given ICM peripheral.
 * \return  ICM status register.
 */
uint32_t ICM_GetStatus(void)
{
    return ICM->ICM_SR;
}


/**
 * \brief Get the undefined access status register of the given ICM peripheral.
 * \return  ICM status register.
 */
uint32_t ICM_GetUStatus(void)
{
    return ICM->ICM_UASR;
}

/**
 * \brief Set descriptor area start address register.
 * \param addr start address
 * \note The start address is a multiple of the total size of the data structure (64 bytes).
 */
void ICM_SetDescStartAddress(uint32_t addr)
{
    ICM->ICM_DSCR = addr;
}

/**
 * \brief Set hash area start address register.
 * \param addr start address
 * \note This field points at the Hash memory location. The address must be a multiple of 128 bytes.
 */
void ICM_SetHashStartAddress(uint32_t addr)
{
    ICM->ICM_HASH = addr;
}

/**
 * \brief Set ICM user initial Hash value register.
 * \param val Initial Hash Value
 */
void ICM_SetInitHashValue(uint32_t val)
{
    ICM->ICM_UIHVAL[0] = ICM_UIHVAL_VAL(val);
}

