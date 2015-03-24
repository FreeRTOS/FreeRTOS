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

/** \file
 *
 * Implementation of High Speed MultiMedia Card Interface (HSMCI) controller.
 */

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"
#include <assert.h>

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

/** \addtogroup hsmci_functions
 *@{
 */

/**
 * \brief Enable Multi-Media Interface
 *
 * \param pRMci Pointer to a Hsmci instance
 */
extern void HSMCI_Enable(Hsmci* pRMci)
{
    pRMci->HSMCI_CR = HSMCI_CR_MCIEN;
}

/**
 * \brief Disable Multi-Media Interface
 *
 * \param pRMci Pointer to a Hsmci instance
 */
extern void HSMCI_Disable(Hsmci* pRMci)
{
    pRMci->HSMCI_CR = HSMCI_CR_MCIDIS;
}

/**
 * \brief Reset (& Disable) Multi-Media Interface
 *
 * \param mci Pointer to a Hsmci instance
 * \param bBackup Backup registers values to keep previous settings, including
 *                _MR, _SDCR, _DTOR, _CSTOR, _DMA and _CFG.
 */
extern void HSMCI_Reset(Hsmci* pRMci, uint8_t bBackup)
{
    if (bBackup)
    {
        uint32_t mr    = pRMci->HSMCI_MR;
        uint32_t dtor  = pRMci->HSMCI_DTOR;
        uint32_t sdcr  = pRMci->HSMCI_SDCR;
        uint32_t cstor = pRMci->HSMCI_CSTOR;
        uint32_t dma   = pRMci->HSMCI_DMA;
        uint32_t cfg   = pRMci->HSMCI_CFG;

        pRMci->HSMCI_CR = HSMCI_CR_SWRST;

        pRMci->HSMCI_MR    = mr;
        pRMci->HSMCI_DTOR  = dtor;
        pRMci->HSMCI_SDCR  = sdcr;
        pRMci->HSMCI_CSTOR = cstor;
        pRMci->HSMCI_DMA   = dma;
        pRMci->HSMCI_CFG   = cfg;
    }
    else
    {
        pRMci->HSMCI_CR = HSMCI_CR_SWRST;
    }
}

/**
 * \brief Select slot
 * \param pRMci Pointer to a Hsmci instance
 * \param bSlot Slot ID (0~3 for A~D).
 */
extern void HSMCI_Select(Hsmci *pRMci, uint8_t bSlot, uint8_t bBusWidth)
{
    uint32_t dwSdcr;
    dwSdcr = (HSMCI_SDCR_SDCSEL_Msk & bSlot);
    switch(bBusWidth)
    {
        case 1:
            pRMci->HSMCI_SDCR = dwSdcr | HSMCI_SDCR_SDCBUS_1;
            break;
        case 4:
            pRMci->HSMCI_SDCR = dwSdcr | HSMCI_SDCR_SDCBUS_4;
            break;
        case 8:
            pRMci->HSMCI_SDCR = dwSdcr | HSMCI_SDCR_SDCBUS_8;
            break;
    }
}

/**
 * \brief Set slot
 * \param pRMci Pointer to a Hsmci instance
 * \param bSlot Slot ID (0~3 for A~D).
 */
extern void HSMCI_SetSlot(Hsmci *pRMci, uint8_t bSlot)
{
    uint32_t dwSdcr = pRMci->HSMCI_SDCR & ~HSMCI_SDCR_SDCSEL_Msk;
    pRMci->HSMCI_SDCR = dwSdcr | (HSMCI_SDCR_SDCSEL_Msk & bSlot);
}

/**
 * \brief Set bus width of MCI
 * \param pRMci Pointer to a Hsmci instance
 * \param bBusWidth 1,4 or 8 (bits).
 */
extern void HSMCI_SetBusWidth(Hsmci * pRMci,uint8_t bBusWidth)
{
    uint32_t dwSdcr = pRMci->HSMCI_SDCR & ~HSMCI_SDCR_SDCBUS_Msk;
    switch(bBusWidth)
    {
        case 1:
            pRMci->HSMCI_SDCR = dwSdcr | HSMCI_SDCR_SDCBUS_1;
            break;
        case 4:
            pRMci->HSMCI_SDCR = dwSdcr | HSMCI_SDCR_SDCBUS_4;
            break;
        case 8:
            pRMci->HSMCI_SDCR = dwSdcr | HSMCI_SDCR_SDCBUS_8;
            break;
    }
}

/**
 * \brief Return bus width setting.
 *
 * \param pRMci  Pointer to an MCI instance.
 * \return 1, 4 or 8.
 */
extern uint8_t HSMCI_GetBusWidth(Hsmci * pRMci)
{
    switch(pRMci->HSMCI_SDCR & HSMCI_SDCR_SDCBUS_Msk)
    {
        case HSMCI_SDCR_SDCBUS_1: return 1;
        case HSMCI_SDCR_SDCBUS_4: return 4;
        case HSMCI_SDCR_SDCBUS_8: return 8;
    }
    return 0;
}

/**
 * \brief Configures a MCI peripheral as specified.
 *
 * \param pRMci  Pointer to an MCI instance.
 * \param dwMode Value of the MCI Mode register.
 */
extern void HSMCI_ConfigureMode(Hsmci *pRMci, uint32_t dwMode)
{
    pRMci->HSMCI_MR = dwMode;
}

/**
 * \brief Return mode register
 * \param pRMci  Pointer to an MCI instance.
 */
extern uint32_t HSMCI_GetMode(Hsmci * pRMci)
{
    return pRMci->HSMCI_MR;
}

/**
 * \brief Enable/Disable R/W proof
 *
 * \param pRMci    Pointer to an MCI instance.
 * \param bRdProof Read proof enable/disable.
 * \param bWrProof Write proof enable/disable.
 */
extern void HSMCI_ProofEnable(Hsmci *pRMci, uint8_t bRdProof, uint8_t bWrProof)
{
    uint32_t mr = pRMci->HSMCI_MR;
    pRMci->HSMCI_MR = (mr & (~(HSMCI_MR_WRPROOF | HSMCI_MR_RDPROOF)))
                    | (bRdProof ? HSMCI_MR_RDPROOF : 0)
                    | (bWrProof ? HSMCI_MR_WRPROOF : 0)
                    ;
}

/**
 * \brief Padding value setting.
 *
 * \param pRMci    Pointer to an MCI instance.
 * \param bPadvEn  Padding value 0xFF/0x00.
 */
extern void HSMCI_PadvCtl(Hsmci *pRMci, uint8_t bPadv)
{
    if (bPadv)
    {
        pRMci->HSMCI_MR |= HSMCI_MR_PADV;
    }
    else
    {
        pRMci->HSMCI_MR &= ~HSMCI_MR_PADV;
    }
}

/**
 * \brief Force byte transfer enable/disable.
 *
 * \param pRMci    Pointer to an MCI instance.
 * \param bFByteEn FBYTE enable/disable.
 */
extern void HSMCI_FByteEnable(Hsmci *pRMci, uint8_t bFByteEn)
{
    if (bFByteEn)
    {
        pRMci->HSMCI_MR |= HSMCI_MR_FBYTE;
    }
    else
    {
        pRMci->HSMCI_MR &= ~HSMCI_MR_FBYTE;
    }
}

/**
 * \brief Check if Force Byte mode enabled.
 *
 * \param pRMci    Pointer to an MCI instance.
 * \return 1 if _FBYTE is enabled.
 */
extern uint8_t HSMCI_IsFByteEnabled(Hsmci *pRMci)
{
    return ((pRMci->HSMCI_MR & HSMCI_MR_FBYTE) > 0);
}

/**
 * \brief Set Clock Divider & Power save divider for MCI.
 *
 * \param pRMci    Pointer to an MCI instance.
 * \param bClkDiv  Clock Divider value (0 ~ 255).
 * \param bPwsDiv  Power Saving Divider (1 ~ 7).
 */
extern void HSMCI_DivCtrl(Hsmci *pRMci, uint32_t bClkDiv, uint8_t bPwsDiv)
{
    uint32_t mr = pRMci->HSMCI_MR;
    uint32_t clkdiv ,clkodd;
    clkdiv = bClkDiv - 2 ;
    clkodd = (bClkDiv & 1)? HSMCI_MR_CLKODD: 0;
    clkdiv = clkdiv >> 1;

    pRMci->HSMCI_MR = (mr & ~(HSMCI_MR_CLKDIV_Msk | HSMCI_MR_PWSDIV_Msk))
                    | HSMCI_MR_CLKDIV(clkdiv)
                    | HSMCI_MR_PWSDIV(bPwsDiv)
                    | clkodd
                    ;
}

/**
 * \brief Enables one or more interrupt sources of MCI peripheral.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \param sources Bitwise OR of selected interrupt sources.
 */
extern void HSMCI_EnableIt(Hsmci *pRMci, uint32_t dwSources)
{
    pRMci->HSMCI_IER = dwSources;
}

/**
 * \brief Disable one or more interrupt sources of MCI peripheral.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \param sources Bitwise OR of selected interrupt sources.
 */
extern void HSMCI_DisableIt(Hsmci *pRMci, uint32_t dwSources)
{
    pRMci->HSMCI_IDR = dwSources;
}

/**
 * \brief Return the interrupt mask register.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \return MCI interrupt mask register.
 */
extern uint32_t HSMCI_GetItMask(Hsmci *pRMci)
{
    return (pRMci->HSMCI_IMR) ;
}

/**
 * \brief Set block len & count for transfer
 * 
 * \param pRMci     Pointer to an Hsmci instance.
 * \param wBlkLen   Block size.
 * \param wCnt      Block(byte) count.
 */
extern void HSMCI_ConfigureTransfer(Hsmci *pRMci,
                                    uint16_t wBlkLen,
                                    uint16_t wCnt)
{
    pRMci->HSMCI_BLKR = (wBlkLen << 16) | wCnt;
}

/**
 * \brief Set block length
 *
 *  Count is reset to 0.
 *
 * \param pRMci     Pointer to an Hsmci instance.
 * \param wBlkSize  Block size.
 */
extern void HSMCI_SetBlockLen(Hsmci *pRMci, uint16_t wBlkSize)
{
    pRMci->HSMCI_BLKR = wBlkSize << 16;
}

/**
 * \brief Set block (byte) count
 *
 * \param pRMci     Pointer to an Hsmci instance.
 * \param wBlkCnt   Block(byte) count.
 */
extern void HSMCI_SetBlockCount(Hsmci *pRMci, uint16_t wBlkCnt)
{
    pRMci->HSMCI_BLKR |= wBlkCnt;
}

/**
 * \brief Configure the Completion Signal Timeout
 *
 * \param pRMci Pointer to an Hsmci instance.
 * \param dwConfigure Completion Signal Timeout configure.
 */
extern void HSMCI_ConfigureCompletionTO(Hsmci *pRMci, uint32_t dwConfigure)
{
    pRMci->HSMCI_CSTOR = dwConfigure;
}

/**
 * \brief Configure the Data Timeout
 *
 * \param pRMci Pointer to an Hsmci instance.
 * \param dwConfigure Data Timeout configure.
 */
extern void HSMCI_ConfigureDataTO(Hsmci *pRMci, uint32_t dwConfigure)
{
    pRMci->HSMCI_DTOR = dwConfigure;
}

/**
 * \brief Send command
 *
 * \param pRMci Pointer to an Hsmci instance.
 * \param dwCmd Command register value.
 * \param dwArg Argument register value.
 */
extern void HSMCI_SendCmd(Hsmci *pRMci, uint32_t dwCmd, uint32_t dwArg)
{
    pRMci->HSMCI_ARGR = dwArg;
    pRMci->HSMCI_CMDR = dwCmd;
}


/**
 * \brief Return the response register.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \return MCI response register.
 */
extern uint32_t HSMCI_GetResponse(Hsmci *pRMci)
{
    return pRMci->HSMCI_RSPR[0];
}

/**
 * \brief Return the receive data register.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \return MCI receive data register.
 */
extern uint32_t HSMCI_Read(Hsmci *pRMci)
{
    return pRMci->HSMCI_RDR;
}

/**
 * \brief Read from FIFO
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \param pdwData Pointer to data buffer.
 * \param dwSize  Size of data buffer (in DWord).
 */
extern void HSMCI_ReadFifo(Hsmci *pRMci, uint8_t *pdwData, uint32_t dwSize)
{
    volatile uint32_t *pFIFO = (volatile uint32_t*)(pRMci->HSMCI_FIFO);
    register uint32_t c4, c1;

    if (dwSize == 0)
        return;

    c4 = dwSize >> 2;
    c1 = dwSize & 0x3;

    for(;c4;c4 --)
    {
        *pdwData ++ = *pFIFO ++;
        *pdwData ++ = *pFIFO ++;
        *pdwData ++ = *pFIFO ++;
        *pdwData ++ = *pFIFO ++;
    }
    for(;c1;c1 --)
    {
        *pdwData ++ = *pFIFO ++;
    }
}

/**
 * \brief Sends data through MCI peripheral.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \param
 */
extern void HSMCI_Write(Hsmci *pRMci, uint32_t dwData)
{
    pRMci->HSMCI_TDR = dwData;
}

/**
 * \brief Write to FIFO
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \param pdwData Pointer to data buffer.
 * \param dwSize  Size of data buffer (In DWord).
 */
extern void HSMCI_WriteFifo(Hsmci *pRMci, uint8_t *pdwData, uint32_t dwSize)
{
    volatile uint32_t *pFIFO = (volatile uint32_t*)(pRMci->HSMCI_FIFO);
    register uint32_t c4, c1;

    if (dwSize == 0)
        return;

    c4 = dwSize >> 2;
    c1 = dwSize & 0x3;

    for(;c4;c4 --)
    {
        *pFIFO ++ = *pdwData ++;
        *pFIFO ++ = *pdwData ++;
        *pFIFO ++ = *pdwData ++;
        *pFIFO ++ = *pdwData ++;
    }
    for(;c1;c1 --)
    {
        *pFIFO ++ = *pdwData ++;
    }
}

/**
 * \brief Return the status register.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \return MCI status register.
 */
extern uint32_t HSMCI_GetStatus(Hsmci *pRMci)
{
    return pRMci->HSMCI_SR;
}

/**
 * \brief Configure the HSMCI DMA
 *  
 * \param pRMci Pointer to an Hsmci instance.
 * \param dwConfigure Configure value. 
 */
extern void HSMCI_ConfigureDma(Hsmci *pRMci, uint32_t dwConfigure)
{
    pRMci->HSMCI_DMA = dwConfigure;
}

/**
 * \brief Enable the HSMCI DMA
 *  
 * \param pRMci Pointer to an Hsmci instance.
 * \param bEnable 1 to enable, 0 to disable.
 */
extern void HSMCI_EnableDma(Hsmci *pRMci, uint8_t bEnable)
{
    if (bEnable)
    {
        pRMci->HSMCI_DMA |= HSMCI_DMA_DMAEN ;//| HSMCI_DMA_CHKSIZE_32;
    }
    else
    {
        pRMci->HSMCI_DMA &= ~HSMCI_DMA_DMAEN;
    }
}

/**
 * \brief Configure the HSMCI
 *  
 * \param pRMci   Pointer to an Hsmci instance.
 * \param dwConfigure Configure value. 
 */
extern void HSMCI_Configure(Hsmci *pRMci, uint32_t dwConfigure)
{
    pRMci->HSMCI_CFG = dwConfigure;
}

/**
 * \brief Enable/Disable High-Speed mode for MCI
 * 
 * \param pRMci Pointer to an Hsmci instance.
 * \param bHsEnable Enable/Disable high-speed.
 */
extern void HSMCI_HsEnable(Hsmci *pRMci, uint8_t bHsEnable)
{
    if (bHsEnable)
    {
        pRMci->HSMCI_CFG |= HSMCI_CFG_HSMODE;
    }
    else
    {
        pRMci->HSMCI_CFG &= ~HSMCI_CFG_HSMODE;
    }
}

/**
 * \brief Check if High-speed mode is enabled on MCI
 * \param pRMci Pointer to an Hsmci instance.
 * \return 1 
 */
extern uint8_t HSMCI_IsHsEnabled(Hsmci * pRMci)
{
    return ((pRMci->HSMCI_CFG & HSMCI_CFG_HSMODE) > 0);
}

/**
 * \brief Configure the Write Protection Mode
 *  
 * \param pRMci   Pointer to an Hsmci instance.
 * \param dwConfigure WP mode configure value. 
 */
extern void HSMCI_ConfigureWP(Hsmci *pRMci, uint32_t dwConfigure)
{
    pRMci->HSMCI_WPMR = dwConfigure;
}

/**
 * \brief Return the write protect status register.
 *
 * \param pRMci   Pointer to an Hsmci instance.
 * \return MCI write protect status register.
 */
extern uint32_t HSMCI_GetWPStatus(Hsmci *pRMci)
{
    return pRMci->HSMCI_WPSR;
}

/**@}*/

