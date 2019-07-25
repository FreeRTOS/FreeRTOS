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
// dma.c - Driver for the dma Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup dma_api dma
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#if defined(__MSP430_HAS_DMAX_3__) || defined(__MSP430_HAS_DMAX_6__)
#include "dma.h"

#include <assert.h>

void DMA_init(DMA_initParam *param){
    uint8_t triggerOffset = (param->channelSelect >> 4);

    //Reset and Set DMA Control 0 Register
    HWREG16(DMA_BASE + param->channelSelect + OFS_DMA0CTL) =
        param->transferModeSelect //Set Transfer Mode
        + param->transferUnitSelect //Set Transfer Unit Size
        + param->triggerTypeSelect; //Set Trigger Type

    //Set Transfer Size Amount
    HWREG16(DMA_BASE + param->channelSelect + OFS_DMA0SZ) = param->transferSize;

    if(triggerOffset & 0x01)     //Odd Channel
    {
        HWREG16(DMA_BASE + (triggerOffset & 0x0E)) &= 0x00FF; //Reset Trigger Select
        HWREG16(DMA_BASE +
                (triggerOffset & 0x0E)) |= (param->triggerSourceSelect << 8);
    }
    else       //Even Channel
    {
        HWREG16(DMA_BASE + (triggerOffset & 0x0E)) &= 0xFF00; //Reset Trigger Select
        HWREG16(DMA_BASE +
                (triggerOffset & 0x0E)) |= param->triggerSourceSelect;
    }
}

void DMA_setTransferSize(uint8_t channelSelect,
                         uint16_t transferSize)
{
    //Set Transfer Size Amount
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0SZ) = transferSize;
}

uint16_t DMA_getTransferSize(uint8_t channelSelect)
{
    //Get Transfer Size Amount
    return(HWREG16(DMA_BASE + channelSelect + OFS_DMA0SZ));
}

void DMA_setSrcAddress(uint8_t channelSelect,
                       uint32_t srcAddress,
                       uint16_t directionSelect)
{
    //Set the Source Address
    __data16_write_addr((unsigned short)(DMA_BASE + channelSelect + OFS_DMA0SA),
                        srcAddress);

    //Reset bits before setting them
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) &= ~(DMASRCINCR_3);
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) |= directionSelect;
}

void DMA_setDstAddress(uint8_t channelSelect,
                       uint32_t dstAddress,
                       uint16_t directionSelect)
{
    //Set the Destination Address
    __data16_write_addr((unsigned short)(DMA_BASE + channelSelect + OFS_DMA0DA),
                        dstAddress);

    //Reset bits before setting them
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) &= ~(DMADSTINCR_3);
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) |= (directionSelect << 2);
}

void DMA_enableTransfers(uint8_t channelSelect)
{
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) |= DMAEN;
}

void DMA_disableTransfers(uint8_t channelSelect)
{
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) &= ~(DMAEN);
}

void DMA_startTransfer(uint8_t channelSelect)
{
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) |= DMAREQ;
}

void DMA_enableInterrupt(uint8_t channelSelect)
{
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) |= DMAIE;
}

void DMA_disableInterrupt(uint8_t channelSelect)
{
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) &= ~(DMAIE);
}

uint16_t DMA_getInterruptStatus(uint8_t channelSelect)
{
    return (HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) & DMAIFG);
}

void DMA_clearInterrupt(uint8_t channelSelect)
{
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) &= ~(DMAIFG);
}

uint16_t DMA_getNMIAbortStatus(uint8_t channelSelect)
{
    return (HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) & DMAABORT);
}

void DMA_clearNMIAbort(uint8_t channelSelect)
{
    HWREG16(DMA_BASE + channelSelect + OFS_DMA0CTL) &= ~(DMAABORT);
}

void DMA_disableTransferDuringReadModifyWrite(void)
{
    HWREG16(DMA_BASE + OFS_DMACTL4) |= DMARMWDIS;
}

void DMA_enableTransferDuringReadModifyWrite(void)
{
    HWREG16(DMA_BASE + OFS_DMACTL4) &= ~(DMARMWDIS);
}

void DMA_enableRoundRobinPriority(void)
{
    HWREG16(DMA_BASE + OFS_DMACTL4) |= ROUNDROBIN;
}

void DMA_disableRoundRobinPriority(void)
{
    HWREG16(DMA_BASE + OFS_DMACTL4) &= ~(ROUNDROBIN);
}

void DMA_enableNMIAbort(void)
{
    HWREG16(DMA_BASE + OFS_DMACTL4) |= ENNMI;
}

void DMA_disableNMIAbort(void)
{
    HWREG16(DMA_BASE + OFS_DMACTL4) &= ~(ENNMI);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for dma_api
//! @}
//
//*****************************************************************************
