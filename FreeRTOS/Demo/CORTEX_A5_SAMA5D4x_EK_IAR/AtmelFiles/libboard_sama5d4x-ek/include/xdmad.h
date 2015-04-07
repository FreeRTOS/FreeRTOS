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
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _XDMAD_H
#define _XDMAD_H

 
/*----------------------------------------------------------------------------
 *        Includes
 *----------------------------------------------------------------------------*/

#include "board.h"
#include <assert.h>


/** \addtogroup dmad_defines DMA Driver Defines
        @{*/
/*----------------------------------------------------------------------------
 *        Consts
 *----------------------------------------------------------------------------*/
#define XDMAD_TRANSFER_MEMORY  0xFF   /**< DMA transfer from or to memory */
#define XDMAD_ALLOC_FAILED     0xFFFF /**< Channel allocate failed */

#define XDMAD_TRANSFER_TX      0
#define XDMAD_TRANSFER_RX      1

/* XDMA_MBR_UBC */
#define XDMA_UBC_NDE (0x1u << 24)
#define   XDMA_UBC_NDE_FETCH_DIS (0x0u << 24)
#define   XDMA_UBC_NDE_FETCH_EN  (0x1u << 24)
#define XDMA_UBC_NSEN (0x1u << 25)
#define   XDMA_UBC_NSEN_UNCHANGED (0x0u << 25)
#define   XDMA_UBC_NSEN_UPDATED (0x1u << 25)
#define XDMA_UBC_NDEN (0x1u << 26)
#define   XDMA_UBC_NDEN_UNCHANGED (0x0u << 26)
#define   XDMA_UBC_NDEN_UPDATED (0x1u << 26)
#define XDMA_UBC_NVIEW_Pos 27
#define    XDMA_UBC_NVIEW_Msk (0x3u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV0 (0x0u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV1 (0x1u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV2 (0x2u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV3 (0x3u << XDMA_UBC_NVIEW_Pos)

/*----------------------------------------------------------------------------
 *        MACRO
 *----------------------------------------------------------------------------*/

/**     @}*/

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/
/** \addtogroup dmad_structs DMA Driver Structs
        @{*/

/** DMA status or return code */
typedef enum _XdmadStatus {
    XDMAD_OK = 0,        /**< Operation is sucessful */
    XDMAD_PARTIAL_DONE,
    XDMAD_DONE,
    XDMAD_BUSY,          /**< Channel occupied or transfer not finished */
    XDMAD_ERROR,         /**< Operation failed */
    XDMAD_CANCELED       /**< Operation canceled */
} eXdmadStatus, eXdmadRC;

/** DMA state for channel */
typedef enum _XdmadState {
    XDMAD_STATE_FREE = 0,      /**< Free channel */
    XDMAD_STATE_ALLOCATED,     /**< Allocated to some peripheral */
    XDMAD_STATE_START,         /**< DMA started */ 
    XDMAD_STATE_IN_XFR,        /**< DMA in trasfering */
    XDMAD_STATE_DONE,          /**< DMA transfer done */
} eXdmadState;

/** DMA transfer callback */
typedef void (*XdmadTransferCallback)(uint32_t status, void* pArg);

/** DMA driver channel */
typedef struct _XdmadChannel {
    XdmadTransferCallback fCallback; /**< Callback */
    void* pArg;                     /**< Callback argument */
    uint8_t bIrqOwner;              /**< Uses DMA handler or external one */
    uint8_t bSrcPeriphID;           /**< HW ID for source */
    uint8_t bDstPeriphID;           /**< HW ID for destination */
    uint8_t bSrcTxIfID;             /**< DMA Tx Interface ID for source */
    uint8_t bSrcRxIfID;             /**< DMA Rx Interface ID for source */
    uint8_t bDstTxIfID;             /**< DMA Tx Interface ID for destination */
    uint8_t bDstRxIfID;             /**< DMA Rx Interface ID for destination */
    volatile uint8_t state;         /**< DMA channel state */
} sXdmadChannel;

/** DMA driver instance */
typedef struct _Xdmad {
    Xdmac *pXdmacs[2];
    sXdmadChannel XdmaChannels[2][16];
    uint8_t  numControllers;
    uint8_t  numChannels;
    uint8_t  pollingMode;
    uint8_t  pollingTimeout;
} sXdmad;

typedef struct _XdmadCfg {
    /** Microblock Control Member. */
    uint32_t mbr_ubc;
    /** Source Address Member. */
    uint32_t mbr_sa;
    /** Destination Address Member. */
    uint32_t mbr_da;
    /** Configuration Register. */
    uint32_t mbr_cfg;
    /** Block Control Member. */
    uint32_t mbr_bc;
    /** Data Stride Member. */
    uint32_t mbr_ds;
    /** Source Microblock Stride Member. */
    uint32_t mbr_sus;
    /** Destination Microblock Stride Member. */
    uint32_t mbr_dus;
} sXdmadCfg;

/** \brief Structure for storing parameters for DMA view0 that can be
 * performed by the DMA Master transfer.*/
typedef struct _LinkedListDescriporView0 
{
    /** Next Descriptor Address number. */
    uint32_t mbr_nda;
    /** Microblock Control Member. */
    uint32_t mbr_ubc;
    /** Transfer Address Member. */
    uint32_t mbr_ta;
}LinkedListDescriporView0;

/** \brief Structure for storing parameters for DMA view1 that can be
 * performed by the DMA Master transfer.*/
typedef struct _LinkedListDescriporView1
{
    /** Next Descriptor Address number. */
    uint32_t mbr_nda;
    /** Microblock Control Member. */
    uint32_t mbr_ubc;
    /** Source Address Member. */
    uint32_t mbr_sa;
    /** Destination Address Member. */
    uint32_t mbr_da;
}LinkedListDescriporView1;

/** \brief Structure for storing parameters for DMA view2 that can be
 * performed by the DMA Master transfer.*/
typedef struct _LinkedListDescriporView2
{
    /** Next Descriptor Address number. */
    uint32_t mbr_nda;
    /** Microblock Control Member. */
    uint32_t mbr_ubc;
    /** Source Address Member. */
    uint32_t mbr_sa;
    /** Destination Address Member. */
    uint32_t mbr_da;
    /** Configuration Register. */
    uint32_t mbr_cfg;
}LinkedListDescriporView2;

/** \brief Structure for storing parameters for DMA view3 that can be
 * performed by the DMA Master transfer.*/
typedef struct _LinkedListDescriporView3
{
    /** Next Descriptor Address number. */
    uint32_t mbr_nda;
    /** Microblock Control Member. */
    uint32_t mbr_ubc;
    /** Source Address Member. */
    uint32_t mbr_sa;
    /** Destination Address Member. */
    uint32_t mbr_da;
    /** Configuration Register. */
    uint32_t mbr_cfg;
    /** Block Control Member. */
    uint32_t mbr_bc;
    /** Data Stride Member. */
    uint32_t mbr_ds;
    /** Source Microblock Stride Member. */
    uint32_t mbr_sus;
    /** Destination Microblock Stride Member. */
    uint32_t mbr_dus;
}LinkedListDescriporView3;

/**     @}*/

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/** \addtogroup dmad_functions DMA Driver Functionos
        @{*/
extern void XDMAD_Initialize( sXdmad *pXdmad,
                             uint8_t bPollingMode );

extern void XDMAD_Handler( sXdmad *pDmad);

extern uint32_t XDMAD_AllocateChannel( sXdmad *pXdmad,
                                      uint8_t bSrcID, uint8_t bDstID);
extern eXdmadRC XDMAD_FreeChannel( sXdmad *pXdmad, uint32_t dwChannel );

extern eXdmadRC XDMAD_ConfigureTransfer( sXdmad *pXdmad,
                                         uint32_t dwChannel,
                                         sXdmadCfg *pXdmaParam,
                                         uint32_t dwXdmaDescCfg,
                                         uint32_t dwXdmaDescAddr);

extern eXdmadRC XDMAD_PrepareChannel( sXdmad *pXdmad, uint32_t dwChannel);

extern eXdmadRC XDMAD_IsTransferDone( sXdmad *pXdmad, uint32_t dwChannel );

extern eXdmadRC XDMAD_StartTransfer( sXdmad *pXdmad, uint32_t dwChannel );

extern eXdmadRC XDMAD_SetCallback( sXdmad *pXdmad, 
                                   uint32_t dwChannel,
                                   XdmadTransferCallback fCallback, 
                                   void* pArg );

extern eXdmadRC XDMAD_StopTransfer( sXdmad *pXdmad, uint32_t dwChannel );
/**     @}*/
/**@}*/
#endif //#ifndef _XDMAD_H

