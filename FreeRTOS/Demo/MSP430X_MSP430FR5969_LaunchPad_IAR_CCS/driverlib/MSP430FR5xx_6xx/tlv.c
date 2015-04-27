/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// tlv.c - Driver for the tlv Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup tlv_api tlv
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_TLV__
#include "tlv.h"

#include <assert.h>

void TLV_getInfo(uint8_t tag,
                 uint8_t instance,
                 uint8_t *length,
                 uint16_t **data_address)
{
    // TLV Structure Start Address
    char *TLV_address = (char *)TLV_START;

    while((TLV_address < (char *)TLV_END)
          && ((*TLV_address != tag) || instance) // check for tag and instance
          && (*TLV_address != TLV_TAGEND))       // do range check first
    {
        if(*TLV_address == tag)
        {
            // repeat till requested instance is reached
            instance--;
        }
        // add (Current TAG address + LENGTH) + 2
        TLV_address += *(TLV_address + 1) + 2;
    }

    // Check if Tag match happened..
    if(*TLV_address == tag)
    {
        // Return length = Address + 1
        *length = *(TLV_address + 1);
        // Return address of first data/value info = Address + 2
        *data_address = (uint16_t *)(TLV_address + 2);
    }
    // If there was no tag match and the end of TLV structure was reached..
    else
    {
        // Return 0 for TAG not found
        *length = 0;
        // Return 0 for TAG not found
        *data_address = 0;
    }
}

uint16_t TLV_getDeviceType()
{
    uint16_t *pDeviceType = (uint16_t *)TLV_DEVICE_ID_0;
    // Return Value from TLV Table
    return(pDeviceType[0]);
}

uint16_t TLV_getMemory(uint8_t instance)
{
    uint8_t *pPDTAG;
    uint8_t bPDTAG_bytes;
    uint16_t count;

    // set tag for word access comparison
    instance *= 2;

    // TLV access Function Call
    // Get Peripheral data pointer
    TLV_getInfo(TLV_PDTAG,
                0,
                &bPDTAG_bytes,
                (uint16_t **)&pPDTAG
                );

    for(count = 0; count <= instance; count += 2)
    {
        if(pPDTAG[count] == 0)
        {
            // Return 0 if end reached
            return(0);
        }
        if(count == instance)
        {
            return (pPDTAG[count] | pPDTAG[count + 1] << 8);
        }
    }

    // Return 0: not found
    return(0);
}

uint16_t TLV_getPeripheral(uint8_t tag,
                           uint8_t instance)
{
    uint8_t *pPDTAG;
    uint8_t bPDTAG_bytes;
    uint16_t count = 0;
    uint16_t pcount = 0;

    // Get Peripheral data pointer
    TLV_getInfo(TLV_PDTAG,
                0,
                &bPDTAG_bytes,
                (uint16_t **)&pPDTAG
                );

    // read memory configuration from TLV to get offset for Peripherals
    while(TLV_getMemory(count))
    {
        count++;
    }
    // get number of Peripheral entries
    pcount = pPDTAG[count * 2 + 1];
    // inc count to first Periperal
    count++;
    // adjust point to first address of Peripheral
    pPDTAG += count * 2;
    // set counter back to 0
    count = 0;
    // align pcount for work comparision
    pcount *= 2;

    // TLV access Function Call
    for(count = 0; count <= pcount; count += 2)
    {
        if(pPDTAG[count + 1] == tag)
        {
            // test if required Peripheral is found
            if(instance > 0)
            {
                // test if required instance is found
                instance--;
            }
            else
            {
                // Return found data
                return (pPDTAG[count] | pPDTAG[count + 1] << 8);
            }
        }
    }

    // Return 0: not found
    return(0);
}

uint8_t TLV_getInterrupt(uint8_t tag)
{
    uint8_t *pPDTAG;
    uint8_t bPDTAG_bytes;
    uint16_t count = 0;
    uint16_t pcount = 0;

    // Get Peripheral data pointer
    TLV_getInfo(TLV_PDTAG,
                0,
                &bPDTAG_bytes,
                (uint16_t **)&pPDTAG
                );

    // read memory configuration from TLV to get offset for Peripherals
    while(TLV_getMemory(count))
    {
        count++;
    }

    pcount = pPDTAG[count * 2 + 1];
    // inc count to first Periperal
    count++;
    // adjust point to first address of Peripheral
    pPDTAG += (pcount + count) * 2;
    // set counter back to 0
    count = 0;

    // TLV access Function Call
    for(count = 0; count <= tag; count += 2)
    {
        if(pPDTAG[count] == 0)
        {
            // Return 0: not found/end of table
            return(0);
        }
        if(count == tag)
        {
            // Return found data
            return (pPDTAG[count]);
        }
    }

    // Return 0: not found
    return(0);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for tlv_api
//! @}
//
//*****************************************************************************
