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
//         Headers
//------------------------------------------------------------------------------

#include "mci_hs.h"
#include <utility/assert.h>
#include <utility/trace.h>

#include <dmad/dmad.h>
#include <dma/dma.h>

//------------------------------------------------------------------------------
//         Local constants
//------------------------------------------------------------------------------

/// Bit mask for status register errors.
#define STATUS_ERRORS (AT91C_MCI_UNRE  \
                       | AT91C_MCI_OVRE \
                       | AT91C_MCI_BLKOVRE \
                       | AT91C_MCI_CSTOE \
                       | AT91C_MCI_DTOE \
                       | AT91C_MCI_DCRCE \
                       | AT91C_MCI_RTOE \
                       | AT91C_MCI_RENDE \
                       | AT91C_MCI_RCRCE \
                       | AT91C_MCI_RDIRE \
                       | AT91C_MCI_RINDE)

#define STATUS_ERRORS_RESP (AT91C_MCI_CSTOE \
                            | AT91C_MCI_RTOE \
                            | AT91C_MCI_RENDE \
                            | AT91C_MCI_RCRCE \
                            | AT91C_MCI_RDIRE \
                            | AT91C_MCI_RINDE)

#define STATUS_ERRORS_DATA (AT91C_MCI_UNRE \
                            | AT91C_MCI_OVRE \
                            | AT91C_MCI_BLKOVRE \
                            | AT91C_MCI_CSTOE \
                            | AT91C_MCI_DTOE \
                            | AT91C_MCI_DCRCE)


/// MCI data timeout configuration with 1048576 MCK cycles between 2 data transfers.
#define DTOR_1MEGA_CYCLES           (AT91C_MCI_DTOCYC | AT91C_MCI_DTOMUL)

/// MCI MR: disable MCI Clock when FIFO is full
#ifndef AT91C_MCI_WRPROOF
    #define AT91C_MCI_WRPROOF 0
#endif
#ifndef AT91C_MCI_RDPROOF
    #define AT91C_MCI_RDPROOF 0
#endif

#define SDCARD_APP_OP_COND_CMD      (41 | AT91C_MCI_SPCMD_NONE  | AT91C_MCI_RSPTYP_48   | AT91C_MCI_TRCMD_NO )
#define MMC_SEND_OP_COND_CMD        (1  | AT91C_MCI_TRCMD_NO    | AT91C_MCI_SPCMD_NONE  | AT91C_MCI_RSPTYP_48 | AT91C_MCI_OPDCMD)


#define DISABLE    0    // Disable MCI interface
#define ENABLE     1    // Enable MCI interface


//------------------------------------------------------------------------------
//         Local macros
//------------------------------------------------------------------------------

/// Used to write in PMC registers.
#define WRITE_PMC(pPmc, regName, value)     pPmc->regName = (value)

/// Used to write in MCI registers.
#define WRITE_MCI(pMci, regName, value)     pMci->regName = (value)

/// Used to read from MCI registers.
#define READ_MCI(pMci, regName)             (pMci->regName)

/// Enable MCI Clock
#define MCICK_ENABLE(pMciHw)      WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIEN)

/// Disable MCI Clock
#define MCICK_DISABLE(pMciHw)     WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIDIS)


//------------------------------------------------------------------------------
//         Local variables
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Internal Functions
//------------------------------------------------------------------------------
#if defined(MCI_DMA_ENABLE)
#define FIFO_SIZE (0x4000 - 0x200)
static DmaLinkList  LLI_CH [4];
#define     LAST_ROW            0x100
static void AT91F_Prepare_Multiple_Transfer(unsigned int Channel,
                                            unsigned int LLI_rownumber,
                                            unsigned int LLI_Last_Row,
                                            unsigned int From_add,
                                            unsigned int To_add,
                                            unsigned int Ctrla,
                                            unsigned int Ctrlb)
{
    LLI_CH[LLI_rownumber].sourceAddress =  From_add;
    LLI_CH[LLI_rownumber].destAddress =  To_add;
    LLI_CH[LLI_rownumber].controlA =  Ctrla;
    LLI_CH[LLI_rownumber].controlB =  Ctrlb;
    if (LLI_Last_Row != LAST_ROW)
        LLI_CH[LLI_rownumber].descriptor =
             (unsigned int)&LLI_CH[LLI_rownumber + 1] + 0;
    else
        LLI_CH[LLI_rownumber].descriptor = 0;
}

static unsigned int DMACH_MCI_P2M(unsigned int channel_index,
                                  unsigned int* src_addr,
                                  unsigned int* dest_addr,
                                  unsigned int trans_size,
                                  unsigned char fifoForP)
{
    unsigned int srcAddress;
    unsigned int destAddress;
    unsigned int buffSize;
    unsigned int LLI_rownumber = 0;
    unsigned int srcAddressMode = fifoForP ?
                                  (AT91C_HDMA_SRC_ADDRESS_MODE_INCR)
                                : (AT91C_HDMA_SRC_ADDRESS_MODE_FIXED);

    // Disable dma channel
    DMA_DisableChannel(channel_index);

    // DMA channel configuration
    srcAddress  = (unsigned int)src_addr;    // Set the data start address
    destAddress = (unsigned int)dest_addr; //(unsigned int)SSC_THR_ADD; 
    buffSize    = trans_size;

    if(buffSize >= 0x10000){
        buffSize = 0xffff;
    }

    // Set DMA channel source address
    DMA_SetSourceAddr(channel_index, srcAddress);

    // Set DMA channel destination address
    DMA_SetDestinationAddr(channel_index,destAddress);

    // Set DMA channel DSCR
    DMA_SetDescriptorAddr(channel_index, (unsigned int)&LLI_CH[0]);

    // Set DMA channel control A 
    DMA_SetSourceBufferSize(channel_index, buffSize,
            (AT91C_HDMA_SRC_WIDTH_WORD >> 24),
            (AT91C_HDMA_DST_WIDTH_WORD >> 28), 0);

	//Set DMA channel control B
    DMA_SetSourceBufferMode(channel_index, DMA_TRANSFER_LLI,
                            srcAddressMode >> 24);
    DMA_SetDestBufferMode(channel_index, DMA_TRANSFER_LLI,
                            (AT91C_HDMA_DST_ADDRESS_MODE_INCR >> 28));

    // Set DMA channel config
    DMA_SetConfiguration(channel_index, BOARD_SD_DMA_HW_SRC_REQ_ID \
                                        | BOARD_SD_DMA_HW_DEST_REQ_ID \
                                        | AT91C_HDMA_SRC_REP_CONTIGUOUS_ADDR \
                                        | AT91C_HDMA_SRC_H2SEL_HW \
                                        | AT91C_HDMA_DST_REP_CONTIGUOUS_ADDR \
                                        | AT91C_HDMA_DST_H2SEL_SW \
                                        | AT91C_HDMA_SOD_DISABLE \
                                        | AT91C_HDMA_FIFOCFG_LARGESTBURST);

    // Set link list
    while(destAddress < ((unsigned int)(dest_addr + buffSize))) {
        if(((unsigned int)(dest_addr + buffSize)) - destAddress <= (4*0xFFF) )
        {
            AT91F_Prepare_Multiple_Transfer(channel_index, LLI_rownumber, LAST_ROW,
                                        srcAddress,
                                        destAddress,
                                        (((((unsigned int)(dest_addr + buffSize))
                                               - destAddress)/4)
                                                | AT91C_HDMA_SRC_WIDTH_WORD
                                                | AT91C_HDMA_DST_WIDTH_WORD),
                                        ( AT91C_HDMA_SIF_0
                                           | AT91C_HDMA_DIF_0
                                           | AT91C_HDMA_DST_DSCR_FETCH_FROM_MEM
                                           //| AT91C_HDMA_DST_DSCR_FETCH_DISABLE
                                           | AT91C_HDMA_DST_ADDRESS_MODE_INCR
                                           //| AT91C_HDMA_SRC_DSCR_FETCH_FROM_MEM
                                           | AT91C_HDMA_SRC_DSCR_FETCH_DISABLE
                                           | srcAddressMode
                                           | AT91C_HDMA_AUTO_DISABLE
                                           | AT91C_HDMA_FC_PER2MEM));
        }
        else
        {
            AT91F_Prepare_Multiple_Transfer(channel_index, LLI_rownumber, 0,
                                        srcAddress,
                                        destAddress,
                                        ( 0xFFF
                                            | AT91C_HDMA_SRC_WIDTH_WORD
                                            | AT91C_HDMA_DST_WIDTH_WORD),
                                        (AT91C_HDMA_SIF_0
                                            | AT91C_HDMA_DIF_0
                                            | AT91C_HDMA_DST_DSCR_FETCH_FROM_MEM
                                            //| AT91C_HDMA_DST_DSCR_FETCH_DISABLE
                                            | AT91C_HDMA_DST_ADDRESS_MODE_INCR
                                            //| AT91C_HDMA_SRC_DSCR_FETCH_FROM_MEM
                                            | AT91C_HDMA_SRC_DSCR_FETCH_DISABLE
                                            | srcAddressMode
                                            | AT91C_HDMA_AUTO_DISABLE
                                            | AT91C_HDMA_FC_PER2MEM));

        }

        destAddress += 4*0xFFF;

        LLI_rownumber++;
    }

    return 0;
}


static unsigned int DMACH_MCI_M2P(unsigned int channel_index,
                                  unsigned int* src_addr,
                                  unsigned int* dest_addr,
                                  unsigned int trans_size,
                                  unsigned char fifoForP)
{
    unsigned int srcAddress;
    unsigned int destAddress;
    unsigned int buffSize;
    unsigned int LLI_rownumber = 0;
    unsigned int dstAddressMode = fifoForP ?
                                  (AT91C_HDMA_DST_ADDRESS_MODE_INCR)
                                : (AT91C_HDMA_DST_ADDRESS_MODE_FIXED);

    // Disable dma channel
    DMA_DisableChannel(channel_index);

    buffSize = trans_size;
    if(buffSize >= 0x10000){
        buffSize = 0xffff;
    }

    // DMA channel configuration
    srcAddress  = (unsigned int)src_addr;    // Set the data start address
    destAddress = (unsigned int)dest_addr;

    // Set DMA channel source address
    DMA_SetSourceAddr(channel_index, srcAddress);

    // Set DMA channel destination address
    DMA_SetDestinationAddr(channel_index,destAddress);

    // Set DMA channel DSCR
    DMA_SetDescriptorAddr(channel_index, (unsigned int)&LLI_CH[0]);

    // Set DMA channel control A 
    DMA_SetSourceBufferSize(channel_index, buffSize,
                              (AT91C_HDMA_SRC_WIDTH_WORD >> 24),
                              (AT91C_HDMA_DST_WIDTH_WORD >> 28), 0);

    //Set DMA channel control B
    DMA_SetSourceBufferMode(channel_index,
                            DMA_TRANSFER_LLI,
                            (AT91C_HDMA_SRC_ADDRESS_MODE_INCR >> 24));
    DMA_SetDestBufferMode(channel_index,
                          DMA_TRANSFER_LLI,
                          dstAddressMode >> 28);

    // Set DMA channel config
    DMA_SetConfiguration(channel_index, BOARD_SD_DMA_HW_SRC_REQ_ID \
                                        | BOARD_SD_DMA_HW_DEST_REQ_ID \
                                        | AT91C_HDMA_SRC_REP_CONTIGUOUS_ADDR \
                                        | AT91C_HDMA_SRC_H2SEL_SW \
                                        | AT91C_HDMA_DST_REP_CONTIGUOUS_ADDR \
                                        | AT91C_HDMA_DST_H2SEL_HW \
                                        | AT91C_HDMA_SOD_DISABLE \
                                        | AT91C_HDMA_FIFOCFG_LARGESTBURST);

    // Set link list
    while(srcAddress < ((unsigned int)(src_addr + buffSize)))
    {
        if(((unsigned int)(src_addr + buffSize)) - srcAddress <= (4*0xFFF) )
        {
            AT91F_Prepare_Multiple_Transfer(channel_index, LLI_rownumber, LAST_ROW,
                                        srcAddress,
                                        destAddress,
                                        (((((unsigned int)(src_addr + buffSize))
                                                - srcAddress)/4)
                                                  | AT91C_HDMA_SRC_WIDTH_WORD
                                                  | AT91C_HDMA_DST_WIDTH_WORD),
                                        ( AT91C_HDMA_SIF_0
                                        | AT91C_HDMA_DIF_0
                                        //| AT91C_HDMA_DST_DSCR_FETCH_FROM_MEM
                                        | AT91C_HDMA_DST_DSCR_FETCH_DISABLE
                                        | dstAddressMode
                                        //| AT91C_HDMA_SRC_DSCR_FETCH_FROM_MEM
                                        | AT91C_HDMA_SRC_DSCR_FETCH_DISABLE
                                        | AT91C_HDMA_SRC_ADDRESS_MODE_INCR
                                        | AT91C_HDMA_AUTO_DISABLE
                                        | AT91C_HDMA_FC_MEM2PER));
        }
        else
        {
            AT91F_Prepare_Multiple_Transfer(channel_index, LLI_rownumber, 0,
                                        srcAddress,
                                        destAddress,
                                        ( 0xFFF
                                            | AT91C_HDMA_SRC_WIDTH_WORD
                                            | AT91C_HDMA_DST_WIDTH_WORD),
                                        ( AT91C_HDMA_SIF_0
                                        | AT91C_HDMA_DIF_0
                                        //| AT91C_HDMA_DST_DSCR_FETCH_FROM_MEM
                                        | AT91C_HDMA_DST_DSCR_FETCH_DISABLE
                                        | dstAddressMode
                                        | AT91C_HDMA_SRC_DSCR_FETCH_FROM_MEM
                                        //| AT91C_HDMA_SRC_DSCR_FETCH_DISABLE
                                        | AT91C_HDMA_SRC_ADDRESS_MODE_INCR
                                        | AT91C_HDMA_AUTO_DISABLE
                                        | AT91C_HDMA_FC_MEM2PER));

        }

        srcAddress += 4*0xFFF;

        
        LLI_rownumber++;
    }
    
    return 0;
}

static inline void DMACH_EnableIt(AT91S_MCI *pMciHw,
                                 unsigned int channel)
{
    unsigned int intFlag;

    intFlag = DMA_GetInterruptMask();
    intFlag |= (AT91C_HDMA_BTC0 << channel);
    DMA_EnableIt(intFlag);
}
#endif

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Enable/disable a MCI driver instance.
/// \param pMci  Pointer to a MCI driver instance.
/// \param enb  0 for disable MCI and 1 for enable MCI.
//------------------------------------------------------------------------------
void MCI_Enable(Mci *pMci, unsigned char enb)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    // Set the Control Register: Enable/Disable MCI interface clock
    if(enb == DISABLE) {
        MCICK_DISABLE(pMciHw);
    }
    else {
        MCICK_ENABLE(pMciHw);
    }
}

//------------------------------------------------------------------------------
/// Initializes a MCI driver instance and the underlying peripheral.
/// \param pMci    Pointer to a MCI driver instance.
/// \param pMciHw  Pointer to a MCI peripheral.
/// \param mciId   MCI peripheral identifier.
/// \param mode    Slot and type of supported card (max bus width).
//------------------------------------------------------------------------------
void MCI_Init(
    Mci *pMci,
    AT91S_MCI *pMciHw,
    unsigned char mciId,
    unsigned int mode)
{
    unsigned short clkDiv;
    unsigned int mciCfg = 0;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);
    SANITY_CHECK(   (mode == MCI_MMC_SLOTA)  || (mode == MCI_SD_SLOTA)
                 || (mode == MCI_MMC_SLOTB)  || (mode == MCI_SD_SLOTB)
                 || (mode == MCI_MMC4_SLOTA) || (mode == MCI_MMC4_SLOTB));

    // Initialize the MCI driver structure
    pMci->pMciHw    = pMciHw;
    pMci->mciId     = mciId;
    pMci->mciMode   = mode;
    pMci->semaphore = 1;
    pMci->pCommand  = 0;

    // Enable the MCI clock
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCER, (1 << mciId));

     // Reset the MCI
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_SWRST);

    // Disable the MCI
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIDIS | AT91C_MCI_PWSDIS);

    // Disable all the interrupts
    WRITE_MCI(pMciHw, MCI_IDR, 0xFFFFFFFF);

    // Set the Data Timeout Register
    WRITE_MCI(pMciHw, MCI_DTOR, DTOR_1MEGA_CYCLES);

    // Set the Mode Register: 400KHz for MCK = 48MHz (CLKDIV = 58)
    clkDiv = (BOARD_MCK / (MCI_INITIAL_SPEED * 2)) - 1;
    WRITE_MCI(pMciHw, MCI_MR, (clkDiv | (AT91C_MCI_PWSDIV & (0x7 << 8))));

    // Set the SDCard Register
    WRITE_MCI(pMciHw, MCI_SDCR, mode);

    // Enable the MCI and the Power Saving
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIEN);

    // Disable the DMA interface
    WRITE_MCI(pMciHw, MCI_DMA, AT91C_MCI_DMAEN_DISABLE);

    // Configure MCI
    //mciCfg = AT91C_MCI_FIFOMODE_AMOUNTDATA | AT91C_MCI_FERRCTRL_RWCMD;
    mciCfg = AT91C_MCI_FIFOMODE_ONEDATA | AT91C_MCI_FERRCTRL_RWCMD;
    
    WRITE_MCI(pMciHw, MCI_CFG, mciCfg);

    // Disable the MCI peripheral clock.
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCDR, (1 << mciId));
}

//------------------------------------------------------------------------------
/// Close a MCI driver instance and the underlying peripheral.
/// \param pMci  Pointer to a MCI driver instance.
/// \param pMciHw  Pointer to a MCI peripheral.
/// \param mciId  MCI peripheral identifier.
//------------------------------------------------------------------------------
void MCI_Close(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);

    // Initialize the MCI driver structure
    pMci->semaphore = 1;
    pMci->pCommand = 0;

    // Disable the MCI peripheral clock.
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCDR, (1 << pMci->mciId));

    // Disable the MCI
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIDIS);

    // Disable all the interrupts
    WRITE_MCI(pMciHw, MCI_IDR, 0xFFFFFFFF);
}

//------------------------------------------------------------------------------
/// Get the  MCI CLKDIV in the MCI_MR register. The max. for MCI clock is
/// MCK/2 and corresponds to CLKDIV = 0
/// \param pMci  Pointer to the low level MCI driver.
/// \param mciSpeed  MCI clock speed in Hz.
//------------------------------------------------------------------------------
unsigned int MCI_GetSpeed(Mci *pMci, unsigned int *mciDiv)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int mciMr;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    // Get the Mode Register
    mciMr  = READ_MCI(pMciHw, MCI_MR);
    mciMr &= AT91C_MCI_CLKDIV;
    if (mciDiv) *mciDiv = mciMr;
    return (BOARD_MCK / 2 / (mciMr + 1));
}

//------------------------------------------------------------------------------
/// Configure the  MCI CLKDIV in the MCI_MR register. The max. for MCI clock is
/// MCK/2 and corresponds to CLKDIV = 0
/// \param pMci  Pointer to the low level MCI driver.
/// \param mciSpeed  MCI clock speed in Hz.
/// \param mciLimit  MCI clock limit in Hz, if not limit, set mciLimit to zero.
/// \return The actual speed used, 0 for fail.
//------------------------------------------------------------------------------
unsigned int MCI_SetSpeed(Mci *pMci,
                          unsigned int mciSpeed,
                          unsigned int mciLimit)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int mciMr;
    unsigned int clkdiv;
    unsigned int divLimit = 0;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    mciMr = READ_MCI(pMciHw, MCI_MR) & (~AT91C_MCI_CLKDIV);

    // Multimedia Card Interface clock (MCCK or MCI_CK) is Master Clock (MCK)
    // divided by (2*(CLKDIV+1))
    // mciSpeed = MCK / (2*(CLKDIV+1))
    if (mciLimit)   divLimit = (BOARD_MCK / 2 / mciLimit);
    if (mciSpeed > 0) {
        clkdiv = (BOARD_MCK / 2 / mciSpeed);
        if (mciLimit && clkdiv < divLimit)
            clkdiv = divLimit;
        if (clkdiv > 0) 
            clkdiv -= 1;
        ASSERT( (clkdiv & 0xFFFFFF00) == 0, "mciSpeed too small");
    }
    else    clkdiv = 0;

    WRITE_MCI(pMciHw, MCI_MR, mciMr | clkdiv);
    return (BOARD_MCK / 2 / (clkdiv + 1));
}

//------------------------------------------------------------------------------
/// Configure the MCI_CFG to enable the HS mode
/// \param pMci     Pointer to the low level MCI driver.
/// \param hsEnable 1 to enable, 0 to disable HS mode.
//------------------------------------------------------------------------------
void MCI_EnableHsMode(Mci *pMci, unsigned char hsEnable)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int cfgr;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    cfgr = READ_MCI(pMciHw, MCI_CFG);
    if (hsEnable)   cfgr |=  AT91C_MCI_HSMODE_ENABLE;
    else            cfgr &= ~AT91C_MCI_HSMODE_ENABLE;
}

//------------------------------------------------------------------------------
/// Configure the  MCI SDCBUS in the MCI_SDCR register. Only two modes available
///
/// \param pMci  Pointer to the low level MCI driver.
/// \param busWidth  MCI bus width mode.
//------------------------------------------------------------------------------
void MCI_SetBusWidth(Mci *pMci, unsigned char busWidth)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int mciSdcr;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    mciSdcr = (READ_MCI(pMciHw, MCI_SDCR) & ~(AT91C_MCI_SCDBUS));

    WRITE_MCI(pMciHw, MCI_SDCR, mciSdcr | busWidth);
}

//------------------------------------------------------------------------------
/// Starts a MCI  transfer. This is a non blocking function. It will return
/// as soon as the transfer is started.
/// Return 0 if successful; otherwise returns MCI_ERROR_LOCK if the driver is
/// already in use.
/// \param pMci  Pointer to an MCI driver instance.
/// \param pCommand  Pointer to the command to execute.
//------------------------------------------------------------------------------
unsigned char MCI_SendCommand(Mci *pMci, MciCmd *pCommand)
{
    AT91PS_MCI pMciHw = pMci->pMciHw;
    unsigned int mciIer, mciMr;
    unsigned int transSize;
    unsigned int mciBlkr;

  #if defined(MCI_DMA_ENABLE)
    unsigned int mciDma;
  #endif

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);
    SANITY_CHECK(pCommand);

    // Try to acquire the MCI semaphore
    if (pMci->semaphore == 0) {

        return MCI_ERROR_LOCK;
    }
    pMci->semaphore--;

    // Command is now being executed
    pMci->pCommand = pCommand;
    pCommand->status = MCI_STATUS_PENDING;

    // Enable the MCI peripheral clock
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCER, (1 << pMci->mciId));

    // Disable MCI clock, for multi-block data transfer
    MCICK_DISABLE(pMciHw);

    // Set Default Mode register value
    mciMr = READ_MCI(pMciHw, MCI_MR) & (~( AT91C_MCI_WRPROOF
                                          |AT91C_MCI_RDPROOF
                                          |AT91C_MCI_BLKLEN));
    // Command with DATA stage
    if (pCommand->blockSize && pCommand->nbBlock) {
        // Enable dma
      #if defined(MCI_DMA_ENABLE)
        mciDma = READ_MCI(pMciHw, MCI_DMA) | AT91C_MCI_DMAEN_ENABLE;
        WRITE_MCI(pMciHw, MCI_DMA, mciDma);
      #endif

        // New transfer
        if(pCommand->tranType == MCI_NEW_TRANSFER) {

            // Set block size
            WRITE_MCI(pMciHw, MCI_MR, mciMr | AT91C_MCI_RDPROOF
                                            | AT91C_MCI_WRPROOF
                                            |(pCommand->blockSize << 16));

            mciBlkr = READ_MCI(pMciHw, MCI_BLKR) & (~AT91C_MCI_BCNT);
            WRITE_MCI(pMciHw, MCI_BLKR, mciBlkr | pCommand->nbBlock);
        }

        transSize = (pCommand->nbBlock * pCommand->blockSize) / 4;
        if ((pCommand->blockSize & 0x3) != 0)
            transSize++;

        // DATA transfer from card to host
        if (pCommand->isRead) {
            
          #if defined(MCI_DMA_ENABLE)
            DMACH_MCI_P2M(BOARD_MCI_DMA_CHANNEL,
                          (unsigned int*)&pMciHw->MCI_FIFO,
                          (unsigned int*) pCommand->pData,
                          transSize, 1);
            DMACH_EnableIt(pMciHw, BOARD_MCI_DMA_CHANNEL);
            DMA_EnableChannel(BOARD_MCI_DMA_CHANNEL);
            mciIer = AT91C_MCI_DMADONE | STATUS_ERRORS;
          #else 
            mciIer = AT91C_MCI_CMDRDY | STATUS_ERRORS;
          #endif
        }
        // DATA transfer from host to card
        else {

          #if defined(MCI_DMA_ENABLE)
            DMACH_MCI_M2P(BOARD_MCI_DMA_CHANNEL,
                          (unsigned int*) pCommand->pData,
                          (unsigned int*)&pMciHw->MCI_FIFO,
                          transSize, 1);
            DMACH_EnableIt(pMciHw, BOARD_MCI_DMA_CHANNEL);
            DMA_EnableChannel(BOARD_MCI_DMA_CHANNEL);
            mciIer = AT91C_MCI_DMADONE | STATUS_ERRORS;
          #else
            mciIer = AT91C_MCI_CMDRDY | STATUS_ERRORS;
          #endif
        }
    }
    // Start an infinite block transfer (but no data in current command)
    else if (pCommand->dataTran) {
        // Set block size
        WRITE_MCI(pMciHw, MCI_MR, mciMr | AT91C_MCI_RDPROOF
                                        | AT91C_MCI_WRPROOF
                                        |(pCommand->blockSize << 16));
        // Set data length: 0
        mciBlkr = READ_MCI(pMciHw, MCI_BLKR) & (~AT91C_MCI_BCNT);
        WRITE_MCI(pMciHw, MCI_BLKR, mciBlkr);
        mciIer = AT91C_MCI_CMDRDY | STATUS_ERRORS;
    }
    // No data transfer: stop at the end of the command
    else{
        WRITE_MCI(pMciHw, MCI_MR, mciMr);
        mciIer = AT91C_MCI_CMDRDY | STATUS_ERRORS;
    }

    // Enable MCI clock
    MCICK_ENABLE(pMciHw);

    // Send the command
    if((pCommand->tranType != MCI_CONTINUE_TRANSFER)
        || (pCommand->blockSize == 0)) {

        WRITE_MCI(pMciHw, MCI_ARGR, pCommand->arg);
        WRITE_MCI(pMciHw, MCI_CMDR, pCommand->cmd);
    }

    // Ignore data error
    mciIer &= ~(  AT91C_MCI_UNRE
                | AT91C_MCI_OVRE
                | AT91C_MCI_DTOE
                | AT91C_MCI_DCRCE
                | AT91C_MCI_BLKOVRE
                | AT91C_MCI_CSTOE);

    // Interrupt enable shall be done after PDC TXTEN and RXTEN
    WRITE_MCI(pMciHw, MCI_IER, mciIer);

    return 0;
}

//------------------------------------------------------------------------------
/// Check NOTBUSY and DTIP bits of status register on the given MCI driver.
/// Return value, 0 for bus ready, 1 for bus busy
/// \param pMci  Pointer to a MCI driver instance.
//------------------------------------------------------------------------------
unsigned char MCI_CheckBusy(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    volatile unsigned int status;

    // Enable MCI clock
    MCICK_ENABLE(pMciHw);

    status = READ_MCI(pMciHw, MCI_SR);

    if(    ((status & AT91C_MCI_NOTBUSY)!=0)
        && ((status & AT91C_MCI_DTIP)==0)
        ) {

        // Disable MCI clock
        MCICK_DISABLE(pMciHw);

        return 0;
    }
    else {
        return 1;
    }
}

//------------------------------------------------------------------------------
/// Check BLKE bit of status register on the given MCI driver.
/// \param pMci  Pointer to a MCI driver instance.
//------------------------------------------------------------------------------
unsigned char MCI_CheckBlke(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int status;

    status = READ_MCI(pMciHw, MCI_SR);
    // TRACE_DEBUG("status %x\n\r",status);

    if((status & AT91C_MCI_BLKE)!=0) {
        return 0;
    }
    else {
        return 1;
    }
}

//------------------------------------------------------------------------------
/// Processes pending events on the given MCI driver.
/// \param pMci  Pointer to a MCI driver instance.
//------------------------------------------------------------------------------
void MCI_Handler(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    volatile MciCmd *pCommand = pMci->pCommand;
    volatile unsigned int status, status0, mask;
    unsigned char i;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);
    SANITY_CHECK(pCommand);

    // Read the status register
    status0 = READ_MCI(pMciHw, MCI_SR);
    mask    = READ_MCI(pMciHw, MCI_IMR);
    //TRACE_INFO("iST %x\n\r", status);
    status  = status0 & mask;
    //TRACE_INFO("iSM %x\n\r", status);

    // Check if an error has occured
    if ((status & STATUS_ERRORS) != 0) {

        // Check error code
        if ((status & STATUS_ERRORS) == AT91C_MCI_RTOE) {

            pCommand->status = MCI_STATUS_NORESPONSE;
        }
        // if the command is SEND_OP_COND the CRC error flag is always present
        // (cf : R3 response)
        else if ((   (status & STATUS_ERRORS) != AT91C_MCI_RCRCE)
                  || (   (pCommand->cmd != SDCARD_APP_OP_COND_CMD)
                      && (pCommand->cmd != MMC_SEND_OP_COND_CMD))) {

            pCommand->status = MCI_STATUS_ERROR;
        }
        // printf("iErr%x\n\r", (status & STATUS_ERRORS));
    }
    mask &= ~STATUS_ERRORS;

    // Check if a command has been completed
    if (status & AT91C_MCI_CMDRDY) {

        WRITE_MCI(pMciHw, MCI_IDR, AT91C_MCI_CMDRDY);
        if (pCommand->isRead == 0 &&
            pCommand->tranType == MCI_STOP_TRANSFER) {
            if (status0 & AT91C_MCI_XFRDONE) {
                MCICK_DISABLE(pMciHw);
            }
            else {
                WRITE_MCI(pMciHw, MCI_IER, AT91C_MCI_XFRDONE);
            }
        }
        else {
            mask &= ~AT91C_MCI_CMDRDY;
            if (pCommand->dataTran == 0) {
                MCICK_DISABLE(pMciHw);
            }
        }
    }

    // Check if transfer stopped
    if (status & AT91C_MCI_XFRDONE) {
        mask &= ~AT91C_MCI_XFRDONE;
        MCICK_DISABLE(pMciHw);
    }

#if defined(MCI_DMA_ENABLE)

    // Check FIFOEMPTY
    if (status & AT91C_MCI_FIFOEMPTY) {
        mask &= ~AT91C_MCI_FIFOEMPTY;
        MCICK_DISABLE(pMciHw);
    }

    // Check if a DMA transfer has been completed
    if (status & AT91C_MCI_DMADONE) {

        unsigned int intFlag;
        intFlag = DMA_GetInterruptMask();
        intFlag = ~intFlag;
        intFlag |= (AT91C_HDMA_BTC0 << BOARD_MCI_DMA_CHANNEL);
        DMA_DisableIt(intFlag);

        WRITE_MCI(pMciHw, MCI_IDR, AT91C_MCI_DMADONE);
        if ( pCommand->isRead == 0 &&
            (status0 & AT91C_MCI_FIFOEMPTY) == 0 ) {
            WRITE_MCI(pMciHw, MCI_IER, AT91C_MCI_FIFOEMPTY);
        }
        else {
            MCICK_DISABLE(pMciHw);
            mask &= ~AT91C_MCI_DMADONE;
        }
    }
#endif

    // All non-error mask done, complete the command
    if (!mask || pCommand->status != MCI_STATUS_PENDING) {

        // Store the card response in the provided buffer
        if (pCommand->pResp) {
            unsigned char resSize;
            switch (pCommand->resType) {
            case 1: case 3: case 4: case 5: case 6: case 7:
                     resSize = 1;           break;
            case 2:  resSize = 4;           break;
            default: resSize = 0;           break;
            }
            for (i=0; i < resSize; i++) {
                pCommand->pResp[i] = READ_MCI(pMciHw, MCI_RSPR[0]);
            }
        }

        // If no error occured, the transfer is successful
        if (pCommand->status == MCI_STATUS_PENDING)
            pCommand->status = 0;

        // Disable interrupts
        WRITE_MCI(pMciHw, MCI_IDR, READ_MCI(pMciHw, MCI_IMR));
        
        // Release the semaphore
        pMci->semaphore++;

        // Invoke the callback associated with the current command (if any)
        if (pCommand->callback) {
            (pCommand->callback)(pCommand->status, (void*)pCommand);
        }
    }
}

//------------------------------------------------------------------------------
/// Returns 1 if the given MCI transfer is complete; otherwise returns 0.
/// \param pCommand  Pointer to a MciCmd instance.
//------------------------------------------------------------------------------
unsigned char MCI_IsTxComplete(MciCmd *pCommand)
{
    if (pCommand->status != MCI_STATUS_PENDING) {
        if (pCommand->status != 0) {
            TRACE_DEBUG("MCI_IsTxComplete %d\n\r", pCommand->status);
        }
        return 1;
    }
    else {
        return 0;
    }
}

//------------------------------------------------------------------------------
/// Check whether the MCI is using the FIFO transfer mode
/// \param pMci  Pointer to a Mci instance.
/// \param pCommand  Pointer to a MciCmd instance.
//------------------------------------------------------------------------------
unsigned int MCI_FifoTransfer(Mci *pMci, MciCmd *pCommand)
{
    unsigned int status=0;
    unsigned int nbTransfer=0;
    unsigned int i;
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int *pMem;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pCommand);

    // If using DMA mode, return
#if defined(MCI_DMA_ENABLE)
    return 0;
#endif

    TRACE_DEBUG("MCIFifo:%d,%d\n\r", pCommand->isRead, pCommand->nbBlock);

    if (pCommand->nbBlock == 0 || pCommand->blockSize == 0)
        return 0;

    pMem = (unsigned int*)pCommand->pData;

    // Get transfer size
    nbTransfer = (pCommand->blockSize) * (pCommand->nbBlock) / 4;
    if((pCommand->blockSize) * (pCommand->nbBlock) % 4) {
        nbTransfer++;
    }

    if (pCommand->isRead) {

        // Read RDR loop
        for(i=0; i<nbTransfer; i++) {
            while(1) {
                status = READ_MCI(pMciHw, MCI_SR);
                if (status & AT91C_MCI_RXRDY)
                    break;
              #if 1
                if (status & STATUS_ERRORS_DATA) {
                    TRACE_ERROR("MCI_FifoTransfer.R: 0x%x\n\r", status);
                    return status;
                }
              #endif
            }
            *pMem = READ_MCI(pMciHw, MCI_RDR);
            pMem++;
        }
    }
    else {

        // Write TDR loop
        for(i=0; i<nbTransfer; i++) {
            while(1) {
                status = READ_MCI(pMciHw, MCI_SR);
                if (status & (AT91C_MCI_TXRDY | AT91C_MCI_NOTBUSY))
                    break;
              #if 0
                if (status & STATUS_ERRORS_DATA) {
                    TRACE_ERROR("MCI_FifoTransfer.W: 0x%x\n\r", status);
                    return status;
                }
              #endif
            }
            WRITE_MCI(pMciHw, MCI_TDR, *pMem);
            pMem++;
        }
    }

    status = READ_MCI(pMciHw, MCI_SR);
    TRACE_DEBUG("MCI_FifoTransfer : All status %x\n\r", status);
    status &= READ_MCI(pMciHw, MCI_IMR);
    TRACE_DEBUG("MCI_FifoTransfer : Masked status %x\n\r", status);

  #if 0
  { unsigned int old = status;
    while(status & AT91C_MCI_DTIP) {
        status = READ_MCI(pMciHw, MCI_SR);
        if (status != old) {
            old = status;
            TRACE_DEBUG_WP(" -> %x", status);
        }
    }
    TRACE_DEBUG_WP("\n\r");
    TRACE_DEBUG(" DPIT 0 stat %x\n\r", status);
    while((status & (AT91C_MCI_FIFOEMPTY
                        | AT91C_MCI_BLKE
                        | AT91C_MCI_XFRDONE)) == 0) {
        status = READ_MCI(pMciHw, MCI_SR);
    }
    TRACE_DEBUG(" FIFO EMPTY stat %x\n\r", status);
  }
  #endif

    return status;
}
