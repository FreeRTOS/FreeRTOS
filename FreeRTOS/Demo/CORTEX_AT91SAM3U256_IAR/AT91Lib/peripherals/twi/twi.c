/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
///
/// Interface for configuration the Two Wire Interface (TWI) peripheral.
///
/// !Usage
///
/// -# Configures a TWI peripheral to operate in master mode, at the given
/// frequency (in Hz) using TWI_Configure().
/// -# Sends a STOP condition on the TWI using TWI_Stop().
/// -# Starts a read operation on the TWI bus with the specified slave using
/// TWI_StartRead(). Data must then be read using TWI_ReadByte() whenever
/// a byte is available (poll using TWI_ByteReceived()).
/// -# Starts a write operation on the TWI to access the selected slave using
/// TWI_StartWrite(). A byte of data must be provided to start the write;
/// other bytes are written next.
/// -# Sends a byte of data to one of the TWI slaves on the bus using TWI_WriteByte().
/// This function must be called once before TWI_StartWrite() with the first byte of data
/// to send, then it shall be called repeatedly after that to send the remaining bytes.
/// -# Check if a byte has been received and can be read on the given TWI
/// peripheral using TWI_ByteReceived().
/// Check if a byte has been sent using TWI_ByteSent().
/// -# Check if the current transmission is complete (the STOP has been sent)
/// using TWI_TransferComplete().
/// -# Enables & disable the selected interrupts sources on a TWI peripheral
/// using TWI_EnableIt() and TWI_DisableIt().
/// -# Get current status register of the given TWI peripheral using
/// TWI_GetStatus(). Get current status register of the given TWI peripheral, but
/// masking interrupt sources which are not currently enabled using
/// TWI_GetMaskedStatus().
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "twi.h"
#include <utility/math.h>
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Configures a TWI peripheral to operate in master mode, at the given
/// frequency (in Hz). The duty cycle of the TWI clock is set to 50%.
/// \param pTwi  Pointer to an AT91S_TWI instance.
/// \param twck  Desired TWI clock frequency.
/// \param mck  Master clock frequency.
//------------------------------------------------------------------------------
void TWI_ConfigureMaster(AT91S_TWI *pTwi, unsigned int twck, unsigned int mck)
{
    unsigned int ckdiv = 0;
    unsigned int cldiv;
    unsigned char ok = 0;

    TRACE_DEBUG("TWI_ConfigureMaster()\n\r");
    SANITY_CHECK(pTwi);

#ifdef AT91C_TWI_SVEN  // TWI slave
    // SVEN: TWI Slave Mode Enabled
    pTwi->TWI_CR = AT91C_TWI_SVEN;
#endif
    // Reset the TWI
    pTwi->TWI_CR = AT91C_TWI_SWRST;
    pTwi->TWI_RHR;

    // TWI Slave Mode Disabled, TWI Master Mode Disabled
#ifdef AT91C_TWI_SVEN  // TWI slave
    pTwi->TWI_CR = AT91C_TWI_SVDIS;
#endif
    pTwi->TWI_CR = AT91C_TWI_MSDIS;

    // Set master mode
    pTwi->TWI_CR = AT91C_TWI_MSEN;

    // Configure clock
    while (!ok) {
        cldiv = ((mck / (2 * twck)) - 3) / power(2, ckdiv);
        if (cldiv <= 255) {

            ok = 1;
        }
        else {

            ckdiv++;
        }
    }

    ASSERT(ckdiv < 8, "-F- Cannot find valid TWI clock parameters\n\r");
    TRACE_DEBUG("Using CKDIV = %u and CLDIV/CHDIV = %u\n\r", ckdiv, cldiv);
    pTwi->TWI_CWGR = 0;
    pTwi->TWI_CWGR = (ckdiv << 16) | (cldiv << 8) | cldiv;
}



#ifdef AT91C_TWI_SVEN  // TWI slave
//------------------------------------------------------------------------------
/// Configures a TWI peripheral to operate in slave mode
/// \param pTwi  Pointer to an AT91S_TWI instance.
//------------------------------------------------------------------------------
void TWI_ConfigureSlave(AT91S_TWI *pTwi, unsigned char slaveAddress)
{
    unsigned int i;

    // TWI software reset
    pTwi->TWI_CR = AT91C_TWI_SWRST;
    pTwi->TWI_RHR;

    // Wait at least 10 ms
    for (i=0; i < 1000000; i++);

    // TWI Slave Mode Disabled, TWI Master Mode Disabled
    pTwi->TWI_CR = AT91C_TWI_SVDIS | AT91C_TWI_MSDIS;

    // Slave Address
    pTwi->TWI_SMR = 0;
    pTwi->TWI_SMR = (slaveAddress << 16) & AT91C_TWI_SADR;

    // SVEN: TWI Slave Mode Enabled
    pTwi->TWI_CR = AT91C_TWI_SVEN;

    // Wait at least 10 ms
    for (i=0; i < 1000000; i++);
    ASSERT( (pTwi->TWI_CR & AT91C_TWI_SVDIS)!=AT91C_TWI_SVDIS, "Problem slave mode");
}
#endif

//------------------------------------------------------------------------------
/// Sends a STOP condition on the TWI.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//------------------------------------------------------------------------------
void TWI_Stop(AT91S_TWI *pTwi)
{
    SANITY_CHECK(pTwi);

    pTwi->TWI_CR = AT91C_TWI_STOP;
}

//------------------------------------------------------------------------------
/// Starts a read operation on the TWI bus with the specified slave, and returns
/// immediately. Data must then be read using TWI_ReadByte() whenever a byte is
/// available (poll using TWI_ByteReceived()).
/// \param pTwi  Pointer to an AT91S_TWI instance.
/// \param address  Slave address on the bus.
/// \param iaddress  Optional internal address bytes.
/// \param isize  Number of internal address bytes.
//-----------------------------------------------------------------------------
void TWI_StartRead(
    AT91S_TWI *pTwi,
    unsigned char address,
    unsigned int iaddress,
    unsigned char isize)
{
    //TRACE_DEBUG("TWI_StartRead()\n\r");
    SANITY_CHECK(pTwi);
    SANITY_CHECK((address & 0x80) == 0);
    SANITY_CHECK((iaddress & 0xFF000000) == 0);
    SANITY_CHECK(isize < 4);

    // Set slave address and number of internal address bytes
    pTwi->TWI_MMR = 0;
    pTwi->TWI_MMR = (isize << 8) | AT91C_TWI_MREAD | (address << 16);

    // Set internal address bytes
    pTwi->TWI_IADR = 0;
    pTwi->TWI_IADR = iaddress;

    // Send START condition
    pTwi->TWI_CR = AT91C_TWI_START;
}

//-----------------------------------------------------------------------------
/// Reads a byte from the TWI bus. The read operation must have been started
/// using TWI_StartRead() and a byte must be available (check with
/// TWI_ByteReceived()).
/// Returns the byte read.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//-----------------------------------------------------------------------------
unsigned char TWI_ReadByte(AT91S_TWI *pTwi)
{
    SANITY_CHECK(pTwi);

    return pTwi->TWI_RHR;
}

//-----------------------------------------------------------------------------
/// Sends a byte of data to one of the TWI slaves on the bus. This function
/// must be called once before TWI_StartWrite() with the first byte of data
/// to send, then it shall be called repeatedly after that to send the
/// remaining bytes.
/// \param pTwi  Pointer to an AT91S_TWI instance.
/// \param byte  Byte to send.
//-----------------------------------------------------------------------------
void TWI_WriteByte(AT91S_TWI *pTwi, unsigned char byte)
{
    SANITY_CHECK(pTwi);

    pTwi->TWI_THR = byte;
}

//-----------------------------------------------------------------------------
/// Starts a write operation on the TWI to access the selected slave, then
/// returns immediately. A byte of data must be provided to start the write;
/// other bytes are written next.
/// \param pTwi  Pointer to an AT91S_TWI instance.
/// \param address  Address of slave to acccess on the bus.
/// \param iaddress  Optional slave internal address.
/// \param isize  Number of internal address bytes.
/// \param byte  First byte to send.
//-----------------------------------------------------------------------------
void TWI_StartWrite(
    AT91S_TWI *pTwi,
    unsigned char address,
    unsigned int iaddress,
    unsigned char isize,
    unsigned char byte)
{
    //TRACE_DEBUG("TWI_StartWrite()\n\r");
    SANITY_CHECK(pTwi);
    SANITY_CHECK((address & 0x80) == 0);
    SANITY_CHECK((iaddress & 0xFF000000) == 0);
    SANITY_CHECK(isize < 4);

    // Set slave address and number of internal address bytes
    pTwi->TWI_MMR = 0;
    pTwi->TWI_MMR = (isize << 8) | (address << 16);

    // Set internal address bytes
    pTwi->TWI_IADR = 0;
    pTwi->TWI_IADR = iaddress;

    // Write first byte to send
    TWI_WriteByte(pTwi, byte);
}

//-----------------------------------------------------------------------------
/// Returns 1 if a byte has been received and can be read on the given TWI
/// peripheral; otherwise, returns 0. This function resets the status register
/// of the TWI.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//-----------------------------------------------------------------------------
unsigned char TWI_ByteReceived(AT91S_TWI *pTwi)
{
    return ((pTwi->TWI_SR & AT91C_TWI_RXRDY) == AT91C_TWI_RXRDY);
}

//-----------------------------------------------------------------------------
/// Returns 1 if a byte has been sent, so another one can be stored for
/// transmission; otherwise returns 0. This function clears the status register
/// of the TWI.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//-----------------------------------------------------------------------------
unsigned char TWI_ByteSent(AT91S_TWI *pTwi)
{
    return ((pTwi->TWI_SR & AT91C_TWI_TXRDY) == AT91C_TWI_TXRDY);
}

//-----------------------------------------------------------------------------
/// Returns 1 if the current transmission is complete (the STOP has been sent);
/// otherwise returns 0.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//-----------------------------------------------------------------------------
unsigned char TWI_TransferComplete(AT91S_TWI *pTwi)
{
    return ((pTwi->TWI_SR & AT91C_TWI_TXCOMP) == AT91C_TWI_TXCOMP);
}

//-----------------------------------------------------------------------------
/// Enables the selected interrupts sources on a TWI peripheral.
/// \param pTwi  Pointer to an AT91S_TWI instance.
/// \param sources  Bitwise OR of selected interrupt sources.
//-----------------------------------------------------------------------------
void TWI_EnableIt(AT91S_TWI *pTwi, unsigned int sources)
{
    SANITY_CHECK(pTwi);
    SANITY_CHECK((sources & 0xFFFFF088) == 0);

    pTwi->TWI_IER = sources;
}

//-----------------------------------------------------------------------------
/// Disables the selected interrupts sources on a TWI peripheral.
/// \param pTwi  Pointer to an AT91S_TWI instance.
/// \param sources  Bitwise OR of selected interrupt sources.
//-----------------------------------------------------------------------------
void TWI_DisableIt(AT91S_TWI *pTwi, unsigned int sources)
{
    SANITY_CHECK(pTwi);
    SANITY_CHECK((sources & 0xFFFFF088) == 0);

    pTwi->TWI_IDR = sources;
}

//-----------------------------------------------------------------------------
/// Returns the current status register of the given TWI peripheral. This
/// resets the internal value of the status register, so further read may yield
/// different values.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//-----------------------------------------------------------------------------
unsigned int TWI_GetStatus(AT91S_TWI *pTwi)
{
    SANITY_CHECK(pTwi);

    return pTwi->TWI_SR;
}

//-----------------------------------------------------------------------------
/// Returns the current status register of the given TWI peripheral, but
/// masking interrupt sources which are not currently enabled.
/// This resets the internal value of the status register, so further read may
/// yield different values.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//-----------------------------------------------------------------------------
unsigned int TWI_GetMaskedStatus(AT91S_TWI *pTwi)
{
    unsigned int status;

    SANITY_CHECK(pTwi);

    status = pTwi->TWI_SR;
    status &= pTwi->TWI_IMR;

    return status;
}
//-----------------------------------------------------------------------------
/// Sends a STOP condition. STOP Condition is sent just after completing
/// the current byte transmission in master read mode.
/// \param pTwi  Pointer to an AT91S_TWI instance.
//-----------------------------------------------------------------------------
void TWI_SendSTOPCondition(AT91S_TWI *pTwi)
{
    SANITY_CHECK(pTwi);

    pTwi->TWI_CR |= AT91C_TWI_STOP;
}

