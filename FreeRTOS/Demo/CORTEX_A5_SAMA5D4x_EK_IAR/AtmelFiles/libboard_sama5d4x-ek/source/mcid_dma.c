/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 *  Implement for SD/MMC low level commands.
 *
 *  \sa \ref hsmci_module, \ref sdmmc_module
 */

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "board.h"
#include "libsdmmc.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *         Local constants
 *----------------------------------------------------------------------------*/
/** \addtorgoup mcid_defines
 *      @{*/

/** Enable MCI */
#define MCI_ENABLE(pMciHw)     HSMCI_Enable(pMciHw)
/** Disable MCI */
#define MCI_DISABLE(pMciHw)    HSMCI_Disable(pMciHw)
/** Reset MCI */
#define MCI_RESET(pMciHw)      HSMCI_Reset(pMciHw, 0)

/** Return halfword(16-bit) count from byte count */
#define toHWCOUNT(byteCnt) (((byteCnt)&0x1) ? (((byteCnt)/2)+1) : ((byteCnt)/2))
/** Return word(32-bit) count from byte count */
#define toWCOUNT(byteCnt)  (((byteCnt)&0x3) ? (((byteCnt)/4)+1) : ((byteCnt)/4))


/** Bit mask for status register errors. */
#define STATUS_ERRORS ((uint32_t)(HSMCI_SR_UNRE  \
                       | HSMCI_SR_OVRE \
                       | HSMCI_SR_ACKRCVE \
                       | HSMCI_SR_CSTOE \
                       | HSMCI_SR_DTOE \
                       | HSMCI_SR_DCRCE \
                       | HSMCI_SR_RTOE \
                       | HSMCI_SR_RENDE \
                       | HSMCI_SR_RCRCE \
                       | HSMCI_SR_RDIRE \
                       | HSMCI_SR_RINDE))

/** Bit mask for response errors */
#define STATUS_ERRORS_RESP ((uint32_t)(HSMCI_SR_CSTOE \
                            | HSMCI_SR_RTOE \
                            | HSMCI_SR_RENDE \
                            | HSMCI_SR_RCRCE \
                            | HSMCI_SR_RDIRE \
                            | HSMCI_SR_RINDE))

/** Bit mask for data errors */
#define STATUS_ERRORS_DATA ((uint32_t)(HSMCI_SR_UNRE \
                            | HSMCI_SR_OVRE \
                            | HSMCI_SR_DTOE \
                            | HSMCI_SR_DCRCE))

/** Max DMA size in a single transfer */
#define MAX_DMA_SIZE                (XDMAC_MAX_BT_SIZE & 0xFFFFFF00)

/** SD/MMC memory Single block */
#define _CMDR_SDMEM_SINGLE  \
    (HSMCI_CMDR_TRCMD_START_DATA | HSMCI_CMDR_TRTYP_SINGLE)
/** SD/MMC memory Multi block */
#define _CMDR_SDMEM_MULTI   \
    (HSMCI_CMDR_TRCMD_START_DATA | HSMCI_CMDR_TRTYP_MULTIPLE)
/** SDIO byte transfer */
#define _CMDR_SDIO_BYTE     \
    (HSMCI_CMDR_TRCMD_START_DATA | HSMCI_CMDR_TRTYP_BYTE)
/** SDIO block transfer */
#define _CMDR_SDIO_BLOCK    \
    (HSMCI_CMDR_TRCMD_START_DATA | HSMCI_CMDR_TRTYP_BLOCK)

/**     @}*/
/*---------------------------------------------------------------------------
 *         Local types
 *---------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *         Local variable
 *----------------------------------------------------------------------------*/

//#define MCID_DBG  0
//static uint8_t bMcidDBG = 0;

/** HAL for SD/MMC bus mode (MCI interface) */
static sSdHalFunctions sdHal = {
    (fSdmmcLock)MCID_Lock,
    (fSdmmcRelease)MCID_Release,
    (fSdmmcSendCommand)MCID_SendCmd,
    (fSdmmcIOCtrl)MCID_IOCtrl
};

/*---------------------------------------------------------------------------
 *         Internal functions
 *---------------------------------------------------------------------------*/

/** \addtogroup mcid_functions
 *@{
 */

/**
 * Enable MCI peripheral access clock
 */
static uint8_t _PeripheralEnable(uint32_t id)
{
    if (PMC_IsPeriphEnabled(id)) return 0;
    PMC_EnablePeripheral(id);
    return 1;
}


/**
 * HSMCI DMA R/W prepare
 */
static uint32_t _MciDMAPrepare(sMcid *pMcid, uint8_t bRd)
{
    sXdmad *pXdmad = pMcid->pXdmad;
    /* Allocate a channel */
    if (bRd){
        pMcid->dwDmaCh = XDMAD_AllocateChannel(pXdmad, pMcid->bID, XDMAD_TRANSFER_MEMORY);
    }
    else { 
        pMcid->dwDmaCh = XDMAD_AllocateChannel(pXdmad, XDMAD_TRANSFER_MEMORY, pMcid->bID);
    }
    if (pMcid->dwDmaCh == XDMAD_ALLOC_FAILED)
    {
        return SDMMC_ERROR_BUSY;
    }
    XDMAD_SetCallback(pXdmad, pMcid->dwDmaCh, NULL, NULL);
    XDMAD_PrepareChannel( pXdmad, pMcid->dwDmaCh );
    return SDMMC_SUCCESS;
}

/**
 * HSMCI DMA R/W
 * \return 1 if DMA started.
 */

/* Linked lists for multi transfer buffer chaining structure instance. */

#if defined ( __ICCARM__ ) /* IAR Ewarm */
#pragma location = "region_dma_nocache"
#elif defined (  __GNUC__  ) /* GCC CS3 */
__attribute__((__section__(".region_dma_nocache")))
#endif
static LinkedListDescriporView1 dmaLinkList[256];

static uint32_t _MciDMA(sMcid *pMcid, uint32_t bFByte, uint8_t bRd)
{
    Hsmci *pHw = pMcid->pMciHw;
    sXdmad *pXdmad = pMcid->pXdmad;
    sSdmmcCommand *pCmd = pMcid->pCmd;
    sXdmadCfg xdmadRxCfg,xdmadTxCfg;
    uint32_t xdmaCndc;
    uint32_t hsmciId;
    uint8_t i;
    uint32_t totalSize = pCmd->wNbBlocks * pCmd->wBlockSize;
    uint32_t maxXSize;
    uint32_t memAddress;
    uint8_t  bMByte;

    if (pMcid->dwXfrNdx >= totalSize) return 0;
    /* Prepare DMA transfer */
    if(pCmd->wBlockSize != 1){
        pMcid->dwXSize = totalSize - pMcid->dwXfrNdx;
        hsmciId = ((unsigned int)pHw == (unsigned int)HSMCI0 )? ID_HSMCI0: ID_HSMCI1;
        if (bRd){
            //printf("_MciDMA read %d,%d \n\r",pCmd->wBlockSize, pCmd->bCmd );
            for ( i = 0; i < pCmd->wNbBlocks; i++){
                dmaLinkList[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 
                                        | (( i == pCmd->wNbBlocks - 1) ? 0: XDMA_UBC_NDE_FETCH_EN)
                                        | XDMA_UBC_NDEN_UPDATED 
                                        | pCmd->wBlockSize /4 ;
                dmaLinkList[i].mbr_sa  = (uint32_t)&(pHw->HSMCI_FIFO[i]);
                dmaLinkList[i].mbr_da = (uint32_t)&pCmd->pData[i * pCmd->wBlockSize];
                if ( i == pCmd->wNbBlocks - 1)
                    dmaLinkList[i].mbr_nda = 0;
                else
                    dmaLinkList[i].mbr_nda = (uint32_t)&dmaLinkList[ i + 1 ];
            }
            xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN 
                               | XDMAC_CC_MBSIZE_SINGLE 
                               | XDMAC_CC_DSYNC_PER2MEM 
                               | XDMAC_CC_CSIZE_CHK_1 
                               | XDMAC_CC_DWIDTH_WORD
                               | XDMAC_CC_SIF_AHB_IF1 
                               | XDMAC_CC_DIF_AHB_IF0 
                               | XDMAC_CC_SAM_FIXED_AM 
                               | XDMAC_CC_DAM_INCREMENTED_AM 
                               | XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 0, hsmciId, XDMAD_TRANSFER_RX ));
            xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 
                     | XDMAC_CNDC_NDE_DSCR_FETCH_EN 
                     | XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED
                     | XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
            if (XDMAD_ConfigureTransfer( pXdmad, pMcid->dwDmaCh, &xdmadRxCfg, xdmaCndc, (uint32_t)&dmaLinkList[0])) {
                return 0;
            }
            if (XDMAD_StartTransfer(pXdmad,pMcid->dwDmaCh)) {
                return 0;
            }
        //Write
        } else {
            //printf("_MciDMA write %d,%d \n\r",pCmd->wBlockSize, pCmd->bCmd );
            for ( i = 0; i < pCmd->wNbBlocks; i++){
                dmaLinkList[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 
                                       |(( i == pCmd->wNbBlocks - 1) ? 0: XDMA_UBC_NDE_FETCH_EN)
                                       | XDMA_UBC_NDEN_UPDATED 
                                       | pCmd->wBlockSize /4 ;
                dmaLinkList[i].mbr_sa = (uint32_t)&pCmd->pData[i * pCmd->wBlockSize];
                dmaLinkList[i].mbr_da = (uint32_t)&(pHw->HSMCI_FIFO[i]);
                if ( i == pCmd->wNbBlocks - 1) dmaLinkList[i].mbr_nda = 0;
                else dmaLinkList[i].mbr_nda = (uint32_t)&dmaLinkList[ i + 1 ];
            }
            xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN 
                               | XDMAC_CC_MBSIZE_SINGLE 
                               | XDMAC_CC_DSYNC_MEM2PER 
                               | XDMAC_CC_CSIZE_CHK_1 
                               | XDMAC_CC_DWIDTH_WORD
                               | XDMAC_CC_SIF_AHB_IF0 
                               | XDMAC_CC_DIF_AHB_IF1 
                               | XDMAC_CC_SAM_INCREMENTED_AM 
                               | XDMAC_CC_DAM_FIXED_AM 
                               | XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 0, hsmciId, XDMAD_TRANSFER_TX ));
            xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 
                     | XDMAC_CNDC_NDE_DSCR_FETCH_EN 
                     | XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED
                     | XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
            if(XDMAD_ConfigureTransfer( pXdmad, pMcid->dwDmaCh, &xdmadTxCfg, xdmaCndc, (uint32_t)&dmaLinkList[0])){
                 return 0;
            }
            if (XDMAD_StartTransfer(pXdmad,pMcid->dwDmaCh)) {
                return 0;
            }
        }
    } else {
   /* Memory address and alignment */
        memAddress = (uint32_t)&pCmd->pData[pMcid->dwXfrNdx];
        bMByte = bFByte ? 1 : (((memAddress & 0x3) || (totalSize & 0x3)));
        /* P to M: Max size is P size */
        if (bRd)
        {
            maxXSize = bFByte ? MAX_DMA_SIZE : (MAX_DMA_SIZE * 4);
        }
        /* M to P: Max size is M size */
        else
        {
            maxXSize = bMByte ? MAX_DMA_SIZE : (MAX_DMA_SIZE * 4);
        }
        /* Update index */
        pMcid->dwXSize = totalSize - pMcid->dwXfrNdx;
        if (pMcid->dwXSize > maxXSize)
        {
            pMcid->dwXSize = maxXSize;
        }
        /* Prepare DMA transfer */
        if (bRd)
        {
            xdmadRxCfg.mbr_ubc = bFByte ? pMcid->dwXSize : toWCOUNT(pMcid->dwXSize);
            xdmadRxCfg.mbr_sa = (uint32_t)&(pHw->HSMCI_RDR);
            xdmadRxCfg.mbr_da = (uint32_t)memAddress;
            xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
                               XDMAC_CC_MEMSET_NORMAL_MODE |
                               XDMAC_CC_DSYNC_PER2MEM|
                               XDMAC_CC_CSIZE_CHK_1 |
                               (bFByte ? XDMAC_CC_DWIDTH_BYTE : XDMAC_CC_DWIDTH_WORD) |
                               XDMAC_CC_SIF_AHB_IF1 |
                               XDMAC_CC_DIF_AHB_IF0 |
                               XDMAC_CC_SAM_FIXED_AM |
                               XDMAC_CC_DAM_INCREMENTED_AM;
            xdmadRxCfg.mbr_bc = 0;
            XDMAD_ConfigureTransfer( pXdmad, pMcid->dwDmaCh, &xdmadRxCfg, 0, 0);
            //CP15_coherent_dcache_for_dma ((uint32_t)memAddress, ((uint32_t)memAddress + (pMcid->dwXSize)));
        }
        else
        {
            xdmadTxCfg.mbr_ubc = toWCOUNT(pMcid->dwXSize);
            xdmadTxCfg.mbr_sa = (uint32_t)memAddress; 
            xdmadTxCfg.mbr_da = (uint32_t)&(pHw->HSMCI_TDR);
            xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
                               XDMAC_CC_MEMSET_NORMAL_MODE |
                               XDMAC_CC_DSYNC_MEM2PER |
                               XDMAC_CC_CSIZE_CHK_1 |
                               (bFByte ? XDMAC_CC_DWIDTH_BYTE : XDMAC_CC_DWIDTH_WORD) |
                               XDMAC_CC_SIF_AHB_IF0 |
                               XDMAC_CC_DIF_AHB_IF1 |
                               XDMAC_CC_SAM_INCREMENTED_AM |
                               XDMAC_CC_DAM_FIXED_AM;
            xdmadTxCfg.mbr_bc = 0;
            XDMAD_ConfigureTransfer( pXdmad, pMcid->dwDmaCh, &xdmadTxCfg, 0, 0);
        }
        XDMAD_StartTransfer(pXdmad, pMcid->dwDmaCh);
    }

    return 1;
}

/*----------------------------------------------------------------------------
 *         Local functions
 *----------------------------------------------------------------------------*/

/**
 * Reset MCI HW interface and disable it.
 * \param keepSettings Keep old register settings, including
 *                     _MR, _SDCR, _DTOR, _CSTOR, _DMA and _CFG.
 */
static void MCI_Reset(sMcid *pMci, uint8_t keepSettings)
{
    Hsmci *pMciHw = pMci->pMciHw;

    assert(pMci);
    assert(pMci->pMciHw);

    HSMCI_Reset( pMciHw, keepSettings );
}

/**
 * Configure the  MCI CLKDIV in the MCI_MR register. The max. for MCI clock is
 * MCK/2 and corresponds to CLKDIV = 0
 * \param pMci  Pointer to the low level MCI driver.
 * \param mciSpeed  MCI clock speed in Hz, 0 will not change current speed.
 * \param mck       MCK to generate MCI Clock, in Hz
 * \return The actual speed used, 0 for fail.
 */
static uint32_t MCI_SetSpeed( sMcid* pMci, uint32_t mciSpeed, uint32_t mck )
{
    Hsmci *pMciHw = pMci->pMciHw;
    uint32_t clkdiv;
    assert(pMci);
    assert(pMciHw);

    if((mck % mciSpeed) == 0)
    {
        clkdiv = mck /mciSpeed;
    } 
    else 
    {
        clkdiv = ((mck + mciSpeed)/mciSpeed);
    }
    mciSpeed = mck / clkdiv;

    /* Modify MR */
    HSMCI_DivCtrl( pMciHw, clkdiv, 0x7);
    return (mciSpeed);
}

/**
 */
static void _FinishCmd( sMcid* pMcid, uint8_t bStatus )
{
    sSdmmcCommand *pCmd = pMcid->pCmd;
    sXdmad *pXdmad = pMcid->pXdmad;
    //uint32_t memAddress;
    /* Release DMA channel (if used) */
    if (pMcid->dwDmaCh != XDMAD_ALLOC_FAILED)
    {
        if (XDMAD_FreeChannel(pXdmad, pMcid->dwDmaCh)) printf("-E- Can't free channel \n\r");
        pMcid->dwDmaCh = XDMAD_ALLOC_FAILED;
    }
    /* Release command */
    pMcid->pCmd   = NULL;
    pMcid->bState = MCID_LOCKED;
    pCmd->bStatus = bStatus;
    /* Invoke callback */
    if (pCmd->fCallback)
    {
        (pCmd->fCallback)(pCmd->bStatus, pCmd->pArg);
    }
}

/*---------------------------------------------------------------------------
 *      Exported functions
 *---------------------------------------------------------------------------*/

/**
 * Select MCI slot.
 */
void MCID_SetSlot(Hsmci *pMci, uint8_t slot)

{
    HSMCI_SetSlot(pMci, slot);
}

/**
 * Initialize MCI driver.
 */
void MCID_Init(sMcid *pMcid,
               Hsmci *pMci, uint8_t bID, uint32_t dwMck,
               sXdmad *pXdmad,
               uint8_t bPolling)
{
    uint16_t clkDiv;

    assert(pMcid);
    assert(pMci);

    /* Initialize driver struct */
    pMcid->pMciHw    = pMci;
    pMcid->pCmd      = NULL;

    pMcid->pXdmad         = pXdmad;
    pMcid->dwDmaCh       = XDMAD_ALLOC_FAILED;
    pMcid->dwXfrNdx      = 0;

    pMcid->dwMck     = dwMck;

    pMcid->bID       = bID;
    pMcid->bPolling  = bPolling;
    pMcid->bState    = MCID_IDLE;

    _PeripheralEnable( bID );

    MCI_RESET( pMci );
    MCI_DISABLE ( pMci );
    HSMCI_DisableIt( pMci, 0xFFFFFFFF );
    HSMCI_ConfigureDataTO( pMci, HSMCI_DTOR_DTOCYC(0xFF)
                                |HSMCI_DTOR_DTOMUL_1048576 );
    HSMCI_ConfigureCompletionTO( pMci , HSMCI_CSTOR_CSTOCYC(0xFF)
                                       |HSMCI_CSTOR_CSTOMUL_1048576 );
    /* Set the Mode Register: 400KHz */
    clkDiv = (dwMck / (MCI_INITIAL_SPEED << 1)) - 1;
    HSMCI_ConfigureMode( pMci, (clkDiv | HSMCI_MR_PWSDIV(0x7)) );

    HSMCI_Enable( pMci );
    HSMCI_Configure( pMci, HSMCI_CFG_FIFOMODE | HSMCI_CFG_FERRCTRL );
    /* Enable DMA */
    HSMCI_EnableDma( pMci, 1 );
    //_PeripheralDisable( bID );
}

/**
 * Lock the MCI driver for slot N access
 */
uint32_t MCID_Lock(sMcid *pMcid, uint8_t bSlot)
{
    Hsmci *pHw = pMcid->pMciHw;
    uint32_t sdcr;

    assert(pMcid);
    assert(pMcid->pMciHw);

    if (bSlot > 0)
    {
        return SDMMC_ERROR_PARAM;
    }
    if (pMcid->bState >= MCID_LOCKED)
    {
        return SDMMC_ERROR_LOCKED;
    }
    pMcid->bState = MCID_LOCKED;
    sdcr = pHw->HSMCI_SDCR & ~(uint32_t)HSMCI_SDCR_SDCSEL_Msk;
    pHw->HSMCI_SDCR = sdcr | (bSlot << HSMCI_SDCR_SDCSEL_Pos);
    return SDMMC_OK;
}

/**
 * Release the driver.
 */
uint32_t MCID_Release(sMcid *pMcid)
{
    assert(pMcid);

    if (pMcid->bState >= MCID_CMD)
    {
        return SDMMC_ERROR_BUSY;
    }
    pMcid->bState = MCID_IDLE;
    return SDMMC_OK;
}

/**
 * SD/MMC command.
 */
uint32_t MCID_SendCmd(sMcid *pMcid, void *pCommand)
{
    Hsmci *pHw = pMcid->pMciHw;
    sSdmmcCommand *pCmd = pCommand;
    uint32_t mr, ier;
    uint32_t cmdr;

    assert(pMcid);
    assert(pMcid->pMciHw);
    assert(pCmd);
    //printf("cmd = %d \n\r",pCmd->bCmd);
    if (!MCID_IsCmdCompleted(pMcid))
    {
        return SDMMC_ERROR_BUSY;
    }
    pMcid->bState = MCID_CMD;
    pMcid->pCmd   = pCmd;

    //_PeripheralEnable(pMcid->bID);
    MCI_DISABLE(pHw);
    mr = HSMCI_GetMode(pHw) & (~(uint32_t)(HSMCI_MR_WRPROOF | HSMCI_MR_RDPROOF |HSMCI_MR_FBYTE));
    /* Special: PowerON Init */
    if (pCmd->cmdOp.wVal == SDMMC_CMD_POWERONINIT){
        HSMCI_ConfigureMode(pHw, mr);
        ier = HSMCI_IER_XFRDONE;
    }
    /* Normal command: idle the bus */
    else if (pCmd->cmdOp.bmBits.xfrData == SDMMC_CMD_STOPXFR)
    {
        HSMCI_ConfigureMode(pHw, mr);
        ier = HSMCI_IER_XFRDONE | STATUS_ERRORS_RESP;
    }
    /* No data transfer */
    else if ((pCmd->cmdOp.wVal & SDMMC_CMD_CNODATA(0xF)) == SDMMC_CMD_CNODATA(0))
    {
        ier = HSMCI_IER_XFRDONE | STATUS_ERRORS_RESP;
        /* R3 response, no CRC */
        if (pCmd->cmdOp.bmBits.respType == 3)
        {
            ier &= ~(uint32_t)HSMCI_IER_RCRCE;
        }
    }
    /* Data command but no following */
    else if (pCmd->wNbBlocks == 0 || pCmd->pData == 0)
    {
        HSMCI_ConfigureMode(pHw, mr | HSMCI_MR_WRPROOF
                                    | HSMCI_MR_RDPROOF);
        HSMCI_ConfigureTransfer(pHw, pCmd->wBlockSize, pCmd->wNbBlocks);
        ier = HSMCI_IER_CMDRDY | STATUS_ERRORS_RESP;
    }
    /* Command with data */
    else
    {
        /* Setup block size */
        if (pCmd->cmdOp.bmBits.sendCmd)
        {
            HSMCI_ConfigureTransfer(pHw, pCmd->wBlockSize, pCmd->wNbBlocks);
        }
        /* Block size is 0, force byte */
        if (pCmd->wBlockSize == 0)
            pCmd->wBlockSize = 1;

        /* Force byte transfer */
        if (pCmd->wBlockSize & 0x3)
        {
            mr |= HSMCI_MR_FBYTE;
        }
        /* Set block size & MR */
        HSMCI_ConfigureMode(pHw, mr | HSMCI_MR_WRPROOF
                                    | HSMCI_MR_RDPROOF
                                    | (pCmd->wBlockSize << 16));
        /* DMA write */
        if (pCmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX)
        {
            if (_MciDMAPrepare(pMcid, 0))
            {
                _FinishCmd(pMcid, SDMMC_ERROR_BUSY);
                return SDMMC_ERROR_BUSY;
            }
            _MciDMA(pMcid, (mr & HSMCI_MR_FBYTE),0);
            ier = HSMCI_IER_XFRDONE | STATUS_ERRORS_DATA;
            if( pCmd->wNbBlocks > 1 ) ier |= HSMCI_IER_FIFOEMPTY;
        }
        else
        {
            if (_MciDMAPrepare(pMcid, 1))
            {
                _FinishCmd(pMcid, SDMMC_ERROR_BUSY);
                return SDMMC_ERROR_BUSY;
            }
            _MciDMA(pMcid, (mr & HSMCI_MR_FBYTE),1);
            ier = HSMCI_IER_XFRDONE | STATUS_ERRORS_DATA;
            if( pCmd->wNbBlocks > 1 ) ier |= HSMCI_IER_FIFOEMPTY;
        }
    }
    MCI_ENABLE(pHw);
    if (pCmd->cmdOp.wVal & (SDMMC_CMD_bmPOWERON | SDMMC_CMD_bmCOMMAND))
    {
        cmdr = pCmd->bCmd;

        if (pCmd->cmdOp.bmBits.powerON)
        {
            cmdr |= (HSMCI_CMDR_OPDCMD | HSMCI_CMDR_SPCMD_INIT);
        }
        if (pCmd->cmdOp.bmBits.odON)
        {
            cmdr |= HSMCI_CMDR_OPDCMD;
        }
        if (pCmd->cmdOp.bmBits.sendCmd)
        {
            cmdr |= HSMCI_CMDR_MAXLAT;
        }
        switch(pCmd->cmdOp.bmBits.xfrData)
        {
            case SDMMC_CMD_TX:
                if (pCmd->cmdOp.bmBits.ioCmd)
                {
                    cmdr |= (pCmd->wBlockSize == 1) ?
                            _CMDR_SDIO_BYTE :
                            _CMDR_SDIO_BLOCK;
                }
                else
                {
                    cmdr |= (pCmd->wNbBlocks == 1) ?
                            _CMDR_SDMEM_SINGLE :
                            _CMDR_SDMEM_MULTI;
                }
                break;

            case SDMMC_CMD_RX:
                if (pCmd->cmdOp.bmBits.ioCmd)
                {
                    cmdr |= HSMCI_CMDR_TRDIR_READ
                            |((pCmd->wBlockSize == 1) ?
                               _CMDR_SDIO_BYTE :
                               _CMDR_SDIO_BLOCK)
                            ;
                }
                else
                {
                    cmdr |= HSMCI_CMDR_TRDIR_READ
                            |((pCmd->wNbBlocks == 1) ?
                               _CMDR_SDMEM_SINGLE :
                               _CMDR_SDMEM_MULTI)
                            ;
                }
                break;

            case SDMMC_CMD_STOPXFR:
                cmdr |= HSMCI_CMDR_TRCMD_STOP_DATA;
                break;
        }
        switch(pCmd->cmdOp.bmBits.respType)
        {
            case 3: case 4:
                /* ignore CRC error */
                ier &= ~(uint32_t)HSMCI_IER_RCRCE;
            case 1: case 5: case 6: case 7:
                cmdr |= HSMCI_CMDR_RSPTYP_48_BIT;
                break;
            case 2:
                cmdr |= HSMCI_CMDR_RSPTYP_136_BIT;
                break;
            /* No response, ignore RTOE */
            default:
                ier &= ~(uint32_t)HSMCI_IER_RTOE;
        }

        pHw->HSMCI_ARGR = pCmd->dwArg;
        pHw->HSMCI_CMDR = cmdr;
    }
    
    /* Ignore CRC error for R3 & R4 */
    if (pCmd->cmdOp.bmBits.xfrData == SDMMC_CMD_STOPXFR)
    {
        ier &= ~STATUS_ERRORS_DATA;
    }

    /* Enable status flags */
    HSMCI_EnableIt(pHw, ier);
    
    return SDMMC_OK;
}
static uint32_t dwMsk;
/**
 * Process pending events on the given MCI driver.
 */
void MCID_Handler(sMcid *pMcid)
{
    Hsmci *pHw = pMcid->pMciHw;
    sSdmmcCommand *pCmd = pMcid->pCmd;
    //uint32_t dwSr, dwMsk, dwMaskedSr;
    uint32_t dwSr, dwMaskedSr;
    assert(pMcid);
    assert(pMcid->pMciHw);

    /* Do nothing if no pending command */
    if (pCmd == NULL)
    {
        if (pMcid->bState >= MCID_CMD)
        {
            pMcid->bState = MCID_LOCKED;
        }
        return;
    }

    /* Read status */
    dwSr  = HSMCI_GetStatus(pHw);
    dwMsk = HSMCI_GetItMask(pHw);
    dwMaskedSr = dwSr & dwMsk;
    /* Check errors */
    if (dwMaskedSr & STATUS_ERRORS)
    {
        if (dwMaskedSr & HSMCI_SR_RTOE)
        {
            pCmd->bStatus = SDMMC_ERROR_NORESPONSE;
        }
      
        if (pCmd->bCmd != 12) pMcid->bState = MCID_ERROR;
        //pMcid->bState = MCID_ERROR;
    }
    dwMsk &= ~STATUS_ERRORS;

    /* Check command complete */
    if (dwMaskedSr & HSMCI_SR_CMDRDY)
    {   
        //printf("HSMCI_SR_CMDRDY \n\r");
        HSMCI_DisableIt(pHw, HSMCI_IDR_CMDRDY);
        dwMsk &= ~(uint32_t)HSMCI_IMR_CMDRDY;
    }
   
    /* Check if not busy */
    if (dwMaskedSr & HSMCI_SR_NOTBUSY)
    {
       //printf("NOTBUSY ");
        HSMCI_DisableIt(pHw, HSMCI_IDR_NOTBUSY);
        dwMsk &= ~(uint32_t)HSMCI_IMR_NOTBUSY;
    }
    /* Check if TX ready */
    if (dwMaskedSr & HSMCI_SR_TXRDY)
    {    
       // printf("TXRDY ");
        dwMsk &= ~(uint32_t)HSMCI_IMR_TXRDY;
    }
     /* Check if FIFO empty (all data sent) */
    if (dwMaskedSr & HSMCI_SR_FIFOEMPTY)
    {
       
        /* Disable FIFO empty */
        HSMCI_DisableIt(pHw, HSMCI_IDR_FIFOEMPTY);
        dwMsk &= ~(uint32_t)HSMCI_IMR_FIFOEMPTY;
         //printf("FIFOEMPTY %x \n\r",dwMsk);
    }
    
    /* Check if DMA finished */
    if (dwMaskedSr & HSMCI_SR_XFRDONE)
    {
        
        HSMCI_DisableIt(pHw, HSMCI_IDR_XFRDONE);
        dwMsk &= ~(uint32_t)HSMCI_IMR_XFRDONE;
        //printf("HSMCI_SR_XFRDONE %x \n\r",dwMsk);
    }
   
    /* All none error mask done, complete the command */
    if (0 == dwMsk || pMcid->bState == MCID_ERROR)
    {
        /* Error reset */
        if (pMcid->bState == MCID_ERROR)
        {
            MCI_Reset(pMcid, 1);
        }
        else 
        {
            pCmd->bStatus = SDMMC_SUCCESS;

            if (pCmd->pResp)
            {
                uint8_t bRspSize, i;
                switch(pCmd->cmdOp.bmBits.respType)
                {
                    case 1: case 3: case 4: case 5: case 6: case 7:
                        bRspSize = 1;
                        break;

                    case 2:
                        bRspSize = 4;
                        break;

                    default:
                        bRspSize = 0;
                }
                for (i = 0; i < bRspSize; i ++)
                {
                    pCmd->pResp[i] = HSMCI_GetResponse(pHw);
                }
            }
        }
        /* Disable interrupts */
        HSMCI_DisableIt(pHw, HSMCI_GetItMask(pHw));
        /* Disable peripheral */
        //_PeripheralDisable(pMcid->bID);
        /* Command is finished */
        _FinishCmd(pMcid, pCmd->bStatus);
    }
}

/**
 * Cancel pending SD/MMC command.
 */
uint32_t MCID_CancelCmd(sMcid *pMcid)
{
    if (pMcid->bState == MCID_IDLE)
    {
        return SDMMC_ERROR_STATE;
    }
    if (pMcid->bState == MCID_CMD)
    {
        /* Cancel ... */
        MCI_Reset(pMcid, 1);
        /* Command is finished */
        _FinishCmd(pMcid, SDMMC_ERROR_USER_CANCEL);
    }
    return SDMMC_OK;
}

/**
 * Reset MCID and disable HW
 */
void MCID_Reset(sMcid * pMcid)
{
    Hsmci *pHw = pMcid->pMciHw;

    MCID_CancelCmd(pMcid);

    //_PeripheralEnable(pMcid->bID);

    /* Disable */
    MCI_DISABLE(pHw);
    /* MR reset */
    HSMCI_ConfigureMode(pHw, HSMCI_GetMode(pHw) & (HSMCI_MR_CLKDIV_Msk
                                                 | HSMCI_MR_PWSDIV_Msk));
    /* BLKR reset */
    HSMCI_ConfigureTransfer(pHw, 0, 0);
    
    /* Cancel ... */
    MCI_Reset(pMcid, 1);
    //_PeripheralDisable(pMcid->bID);

    if (pMcid->bState == MCID_CMD)
    {
        /* Command is finished */
        _FinishCmd(pMcid, SDMMC_ERROR_USER_CANCEL);
    }
}

/**
 * Check if the command is finished
 */
uint32_t MCID_IsCmdCompleted(sMcid *pMcid)
{
    sSdmmcCommand *pCmd = pMcid->pCmd;

    if (pMcid->bPolling)
    {
        MCID_Handler(pMcid);
    }
    if (pMcid->bState == MCID_CMD)
    {
        return 0;
    }
    if (pCmd)
    {
        return 0;
    }
    return 1;
}

/**
 * IO control functions
 */
uint32_t MCID_IOCtrl(sMcid *pMcid, uint32_t bCtl, uint32_t param)
{
    Hsmci *pMciHw = pMcid->pMciHw;
    assert(pMcid);
    assert(pMcid->pMciHw);

    //mciDis = _PeripheralEnable(pMcid->bID);

    switch (bCtl)
    {
        case SDMMC_IOCTL_BUSY_CHECK:
            *(uint32_t*)param = !MCID_IsCmdCompleted(pMcid);
            break;

        case SDMMC_IOCTL_POWER:
            return SDMMC_ERROR_NOT_SUPPORT;

        case SDMMC_IOCTL_RESET:
            MCID_Reset(pMcid);
            return SDMMC_SUCCESS;

        case SDMMC_IOCTL_CANCEL_CMD:
            return MCID_CancelCmd(pMcid);

        case SDMMC_IOCTL_SET_CLOCK:
            *(uint32_t*)param = MCI_SetSpeed(pMcid,
                                             *(uint32_t*)param,
                                             pMcid->dwMck);
            break;

        case SDMMC_IOCTL_SET_HSMODE:
            HSMCI_HsEnable( pMciHw, *(uint32_t*)param );
            *(uint32_t*)param = HSMCI_IsHsEnabled( pMciHw );

            break;

        case SDMMC_IOCTL_SET_BUSMODE:
            HSMCI_SetBusWidth( pMciHw, *(uint32_t*)param );
            break;

        case SDMMC_IOCTL_GET_BUSMODE:
            //*(uint32_t*)param = 8; /* Max 4-bit bus */
            break;

        case SDMMC_IOCTL_GET_HSMODE:
            *(uint32_t*)param = 1; /* Supported */
            break;

        default:
            return SDMMC_ERROR_NOT_SUPPORT;
        
    }
    return SDMMC_OK;
}

/**
 * Initialize the SD/MMC card driver struct for SD/MMC bus mode
 * \note defined in SD/MMC bus mode low level (Here uses MCI interface)
 */
void SDD_InitializeSdmmcMode(sSdCard * pSd,void * pDrv,uint8_t bSlot)
{
    SDD_Initialize(pSd, pDrv, bSlot, &sdHal);
}

/**@}*/

