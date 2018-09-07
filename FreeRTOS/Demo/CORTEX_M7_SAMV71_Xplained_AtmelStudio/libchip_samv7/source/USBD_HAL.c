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

/**

 \file

    Implementation of USB device functions on a UDP controller.

    See \ref usbd_api_method USBD API Methods.
*/

/** \addtogroup usbd_hal
 *@{*/

/*---------------------------------------------------------------------------
 *      Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"
#include "USBD_HAL.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/*---------------------------------------------------------------------------
 *      Definitions
 *---------------------------------------------------------------------------*/

#define DMA

/** Maximum number of endpoints interrupts. */
#define NUM_IT_MAX       11
/** Maximum number of endpoint DMA interrupts */
#define NUM_IT_MAX_DMA   \
    ((USBHS->UDPHS_IPFEATURES \
        & UDPHS_IPFEATURES_DMA_CHANNEL_NBR_Msk) \
      >>UDPHS_IPFEATURES_DMA_CHANNEL_NBR_Pos)

/** Bits that should be shifted to access interrupt bits. */
#define SHIFT_INTERUPT   12

/** Max size of the FMA FIFO */
#define DMA_MAX_FIFO_SIZE     (65536/1)
/** fifo space size in DW */
#define EPT_VIRTUAL_SIZE      16384

/**
 * \section endpoint_states_sec "UDP Endpoint states"
 *
 *  This page lists the endpoint states.
 *
 *  \subsection States
 *  - UDPHS_ENDPOINT_DISABLED
 *  - UDPHS_ENDPOINT_HALTED
 *  - UDPHS_ENDPOINT_IDLE
 *  - UDPHS_ENDPOINT_SENDING
 *  - UDPHS_ENDPOINT_RECEIVING
 *  - UDPHS_ENDPOINT_SENDINGM
 *  - UDPHS_ENDPOINT_RECEIVINGM
 */

/**  Endpoint states: Endpoint is disabled */
#define UDPHS_ENDPOINT_DISABLED       0
/**  Endpoint states: Endpoint is halted (i.e. STALLs every request) */
#define UDPHS_ENDPOINT_HALTED         1
/**  Endpoint states: Endpoint is idle (i.e. ready for transmission) */
#define UDPHS_ENDPOINT_IDLE           2
/**  Endpoint states: Endpoint is sending data */
#define UDPHS_ENDPOINT_SENDING        3
/**  Endpoint states: Endpoint is receiving data */
#define UDPHS_ENDPOINT_RECEIVING      4
/**  Endpoint states: Endpoint is sending MBL */
#define UDPHS_ENDPOINT_SENDINGM       5
/**  Endpoint states: Endpoint is receiving MBL */
#define UDPHS_ENDPOINT_RECEIVINGM     6
      

/** Get Number of buffer in Multi-Buffer-List
 *  \param i    input index
 *  \param o    output index
 *  \param size list size
 */
#define MBL_NbBuffer(i, o, size) (((i)>(o))?((i)-(o)):((i)+(size)-(o)))

/** Buffer list is full */
#define MBL_FULL        1
/** Buffer list is null */
#define MBL_NULL        2

/*---------------------------------------------------------------------------
 *      Types
 *---------------------------------------------------------------------------*/

/**  Describes header for UDP endpoint transfer. */
typedef struct {
    /**  Optional callback to invoke when the transfer completes. */
    void*   fCallback;
    /**  Optional argument to the callback function. */
    void*   pArgument;
    /**  Transfer type */
    uint8_t transType;
    /* Reserved to 32-b aligned */
    uint8_t reserved[3];
} TransferHeader;

/**  Describes a transfer on a UDP endpoint. */
typedef struct {

    /**  Optional callback to invoke when the transfer completes. */
    TransferCallback fCallback;
    /**  Optional argument to the callback function. */
    void             *pArgument;
    /**  Transfer type */
    uint8_t          transType;
    uint8_t          reserved[3];
    /**  Number of bytes which have been written into the UDP internal FIFO
     *   buffers. */
    int32_t          buffered;
    /**  Pointer to a data buffer used for emission/reception. */
    uint8_t          *pData;
    /**  Number of bytes which have been sent/received. */
    int32_t          transferred;
    /**  Number of bytes which have not been buffered/transferred yet. */
    int32_t          remaining;
} Transfer;

/**  Describes Multi Buffer List transfer on a UDP endpoint. */
typedef struct {
    /**  Optional callback to invoke when the transfer completes. */
    MblTransferCallback fCallback;
    /**  Optional argument to the callback function. */
    void                *pArgument;
    /** Transfer type */
    uint8_t             transType;
    /** List state (OK, FULL, NULL) (run time) */
    uint8_t             listState;
    /**  Multi-Buffer List size */
    uint16_t            listSize;
    /**  Pointer to multi-buffer list */
    USBDTransferBuffer *pMbl;
    /**  Offset number of buffers to start transfer */
    uint16_t            offsetSize;
    /**  Current processing buffer index (run time) */
    uint16_t            outCurr;
    /**  Loaded buffer index (run time) */
    uint16_t            outLast;
    /**  Current buffer for input (run time) */
    uint16_t            inCurr;
} MblTransfer;

/**
 *  Describes the state of an endpoint of the UDP controller.
 */
typedef struct {

    /* CSR */
    /**  Current endpoint state. */
    volatile uint8_t  state;
    /**  Current reception bank (0 or 1). */
    volatile uint8_t  bank;
    /**  Maximum packet size for the endpoint. */
    volatile uint16_t size;
    /**  Describes an ongoing transfer (if current state is either
     *   UDPHS_ENDPOINT_SENDING or UDPHS_ENDPOINT_RECEIVING) */
    union {
        TransferHeader transHdr;
        Transfer       singleTransfer;
        MblTransfer    mblTransfer;
    } transfer;
    /** Special case for send a ZLP */
    uint32_t sendZLP;
} Endpoint;

/**
 * DMA Descriptor.
 */
typedef struct {
    void    *pNxtDesc;
    void    *pAddr;
    uint32_t dwCtrl;
    uint32_t dw;
} UdphsDmaDescriptor;

/*---------------------------------------------------------------------------
 *      Internal variables
 *---------------------------------------------------------------------------*/

/** Holds the internal state for each endpoint of the UDP. */
static Endpoint endpoints[CHIP_USB_NUMENDPOINTS];

/** 7.1.20 Test Mode Support
 * Test codes for the USB HS test mode. */
static const char test_packet_buffer[] = {
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,                // JKJKJKJK * 9
    0xAA,0xAA,0xAA,0xAA,0xAA,0xAA,0xAA,0xAA,                     // JJKKJJKK * 8
    0xEE,0xEE,0xEE,0xEE,0xEE,0xEE,0xEE,0xEE,                     // JJJJKKKK * 8
    0xFE,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF, // JJJJJJJKKKKKKK * 8
    0x7F,0xBF,0xDF,0xEF,0xF7,0xFB,0xFD,                          // JJJJJJJK * 8
    0xFC,0x7E,0xBF,0xDF,0xEF,0xF7,0xFB,0xFD,0x7E                 // {JKKKKKKK * 10}, JK
};



/** DMA link list */
COMPILER_ALIGNED(16) static UdphsDmaDescriptor  dmaLL[5];
COMPILER_ALIGNED(16) static UdphsDmaDescriptor *pDmaLL;

/*---------------------------------------------------------------------------
 *      Internal Functions
 *---------------------------------------------------------------------------*/

/**
 * Handles a completed transfer on the given endpoint, invoking the
 * configured callback if any.
 * \param bEndpoint Number of the endpoint for which the transfer has completed.
 * \param bStatus   Status code returned by the transfer operation
 */
static void UDPHS_EndOfTransfer(uint8_t bEndpoint, uint8_t bStatus)
{
    Endpoint *pEp = &(endpoints[bEndpoint]);

    /* Check that endpoint was sending or receiving data */
    if ( (pEp->state == UDPHS_ENDPOINT_RECEIVING)
            || (pEp->state == UDPHS_ENDPOINT_SENDING) )
    {
        Transfer *pXfr = (Transfer*)&(pEp->transfer);
        uint32_t transferred = pXfr->transferred;
        uint32_t remaining   = pXfr->remaining + pXfr->buffered;
        
        TRACE_DEBUG_WP("EoT ");
        if (pEp->state == UDPHS_ENDPOINT_SENDING)
            pEp->sendZLP = 0;
        pEp->state = UDPHS_ENDPOINT_IDLE;
        pXfr->pData = 0;
        pXfr->transferred = -1;
        pXfr->buffered    = -1;
        pXfr->remaining   = -1;

        /* Invoke callback */
        if (pXfr->fCallback)
        {
            pXfr->fCallback(pXfr->pArgument, bStatus, transferred, remaining);
        }
        else
        {
            TRACE_DEBUG_WP("NoCB ");
        }
    }
    else if ( (pEp->state == UDPHS_ENDPOINT_RECEIVINGM)
                || (pEp->state == UDPHS_ENDPOINT_SENDINGM) )
    {
        MblTransfer *pXfr = (MblTransfer*)&(pEp->transfer);
        TRACE_DEBUG_WP("EoMT ");

        pEp->state = UDPHS_ENDPOINT_IDLE;
        pXfr->listState = 0;
        pXfr->outCurr = pXfr->inCurr = pXfr->outLast = 0;
        /* Invoke callback */
        if (pXfr->fCallback)
        {
            pXfr->fCallback(pXfr->pArgument, bStatus);
        }
        else
        {
            TRACE_DEBUG_WP("NoCB ");
        }
    }
}

/**
 * Update multi-buffer-transfer descriptors.
 * \param pTransfer Pointer to instance MblTransfer.
 * \param size      Size of bytes that processed.
 * \param forceEnd  Force the buffer END.
 * \return 1 if current buffer ended.
 */
static uint8_t UDPHS_MblUpdate(MblTransfer *pTransfer,
                          USBDTransferBuffer * pBi,
                          uint16_t size,
                          uint8_t forceEnd)
{
    /* Update transfer descriptor */
    pBi->remaining -= size;
    /* Check if list NULL */
    if (pTransfer->listState == MBL_NULL) {
        return 1;
    }
    /* Check if current buffer ended */
    if (pBi->remaining == 0 || forceEnd || size == 0) {

        /* Process to next buffer */
        if ((++ pTransfer->outCurr) == pTransfer->listSize)
            pTransfer->outCurr = 0;
        /* Check buffer NULL case */
        if (pTransfer->outCurr == pTransfer->inCurr)
            pTransfer->listState = MBL_NULL;
        else {
            pTransfer->listState = 0;
            /* Continue transfer, prepare for next operation */
            pBi = &pTransfer->pMbl[pTransfer->outCurr];
            pBi->buffered    = 0;
            pBi->transferred = 0;
            pBi->remaining   = pBi->size;
        }
        return 1;
    }
    return 0;
}

/**
 * Transfers a data payload from the current transfer buffer to the endpoint
 * FIFO
 * \param bEndpoint Number of the endpoint which is sending data.
 */
static uint8_t UDPHS_MblWriteFifo(uint8_t bEndpoint)
{
    Endpoint    *pEndpoint   = &(endpoints[bEndpoint]);
    MblTransfer *pTransfer   = (MblTransfer*)&(pEndpoint->transfer);
    USBDTransferBuffer *pBi = &(pTransfer->pMbl[pTransfer->outCurr]);
    uint8_t *pFifo;
    int32_t size;

    volatile uint8_t * pBytes;
    volatile uint8_t bufferEnd = 1;

    /* Get the number of bytes to send */
    size = pEndpoint->size;
    if (size > pBi->remaining) size = pBi->remaining;

    TRACE_DEBUG_WP("w%d.%d ", pTransfer->outCurr, size);

    /* Record last accessed buffer */
    pTransfer->outLast = pTransfer->outCurr;

    pBytes = &(pBi->pBuffer[pBi->transferred + pBi->buffered]);
    pBi->buffered += size;
    bufferEnd = UDPHS_MblUpdate(pTransfer, pBi, size, 0);

    /* Write packet in the FIFO buffer */
    pFifo = (uint8_t*)((uint32_t*)USBHS_RAM_ADDR
                                    + (EPT_VIRTUAL_SIZE * bEndpoint));
    memory_sync();
    if (size) {
        int32_t c8 = size >> 3;
        int32_t c1 = size & 0x7;
        for (; c8; c8 --) {
            *(pFifo++) = *(pBytes ++);
            *(pFifo++) = *(pBytes ++);
            *(pFifo++) = *(pBytes ++);
            *(pFifo++) = *(pBytes ++);

            *(pFifo++) = *(pBytes ++);
            *(pFifo++) = *(pBytes ++);
            *(pFifo++) = *(pBytes ++);
            *(pFifo++) = *(pBytes ++);
        }
        for (; c1; c1 --) {
            *(pFifo++) = *(pBytes ++);
        }
    }
    return bufferEnd;
}

#if 0
/**
 *  Transfers a data payload from an endpoint FIFO to the current transfer
 *  buffer, if NULL packet received, the current buffer is ENDed.
 *  \param bEndpoint Endpoint number.
 *  \param wPacketSize Size of received data packet */
 *  \return 1 if the buffer ENDed. */
 */
static uint8_t UDPHS_MblReadFifo(uint8_t bEndpoint, uint16_t wPacketSize)
{
   
    return 0;
}
*/
#endif
/**
 * Transfers a data payload from the current transfer buffer to the endpoint
 * FIFO
 * \param bEndpoint Number of the endpoint which is sending data.
 */
static void UDPHS_WritePayload(uint8_t bEndpoint, int32_t size)
{
    Endpoint *pEndpoint = &(endpoints[bEndpoint]);
    Transfer *pTransfer = (Transfer*)&(pEndpoint->transfer);
    uint8_t  *pFifo;

    /* Get the number of bytes to send */
    if (size > pTransfer->remaining)
    {
        size = pTransfer->remaining;
    }

    /* Update transfer descriptor information */
    pTransfer->buffered += size;
    pTransfer->remaining -= size;

    /* Write packet in the FIFO buffer */
    pFifo = (uint8_t*)((uint32_t*)USBHS_RAM_ADDR
                                    + (EPT_VIRTUAL_SIZE * bEndpoint));
    memory_sync();
    for (; size; size --)
    {
        *(pFifo ++) = *(pTransfer->pData ++);
    }
    memory_sync();
   
}

/**
 * Transfers a data payload from an endpoint FIFO to the current transfer buffer
 * \param bEndpoint Endpoint number.
 * \param wPacketSize Size of received data packet
 */
static void UDPHS_ReadPayload(uint8_t bEndpoint, int32_t wPacketSize)
{
    Endpoint *pEndpoint = &(endpoints[bEndpoint]);
    Transfer *pTransfer = (Transfer*)&(pEndpoint->transfer);
    uint8_t  *pFifo;
    /* Check that the requested size is not bigger than the remaining transfer */
    if (wPacketSize > pTransfer->remaining) {

        pTransfer->buffered += wPacketSize - pTransfer->remaining;
        wPacketSize = pTransfer->remaining;
    }

    /* Update transfer descriptor information */
    pTransfer->remaining -= wPacketSize;
    pTransfer->transferred += wPacketSize;

    /* Retrieve packet */
    pFifo = (uint8_t*)((uint32_t*)USBHS_RAM_ADDR
                                    + (EPT_VIRTUAL_SIZE * bEndpoint));
    while (wPacketSize > 0)
    {
        *(pTransfer->pData ++) = *(pFifo ++);
        memory_sync();
        wPacketSize--;
    }
    
}

/**
 * Received SETUP packet from endpoint 0 FIFO
 * \param pRequest Generic USB SETUP request sent over Control endpoints
 */
static void UDPHS_ReadRequest(USBGenericRequest *pRequest)
{
    uint32_t *pData = (uint32_t *)(void*)pRequest;
    volatile uint32_t *pFifo;
    pFifo = (volatile uint32_t*)USBHS_RAM_ADDR;
    *pData ++ = *pFifo;
    memory_sync();
    pFifo = (volatile uint32_t*)USBHS_RAM_ADDR;
    *pData    = *pFifo;
    memory_sync();
}


/**
 * Endpoint interrupt handler.
 * Handle IN/OUT transfers, received SETUP packets and STALLing
 * \param bEndpoint Index of endpoint
 */
static void UDPHS_EndpointHandler(uint8_t bEndpoint)
{
    Usbhs    *pUdp = USBHS;
    
    //UdphsDma *pDma = &pUdp->USBHS_DEVDMA[bEndpoint];

    Endpoint *pEp      = &(endpoints[bEndpoint]);
    Transfer *pXfr     = (Transfer*)&(pEp->transfer);
    //MblTransfer *pMblt = (MblTransfer*)&(pEp->transfer);
    uint32_t status = USBHS_ReadEPStatus(pUdp, bEndpoint, 0xFFFFFFFF);
    uint32_t type   = USBHS_GetEpType(pUdp, bEndpoint);
    uint32_t reqBuf[2];
    USBGenericRequest *pReq = (USBGenericRequest *)reqBuf;
    uint16_t wPktSize;

    
    TRACE_DEBUG_WP("Ep%d ", bEndpoint);
    /* IN packet sent */
    if ( (  status & USBHS_DEVEPTISR_TXINI) && USBHS_IsEpIntEnable(pUdp, bEndpoint, USBHS_DEVEPTIMR_TXINE))
    {
        TRACE_DEBUG_WP("Wr ");

        /* Multi-buffer-list transfer state */
        if ( pEp->state == UDPHS_ENDPOINT_SENDINGM )
        {
        }
        /* Sending state */
        else if ( pEp->state == UDPHS_ENDPOINT_SENDING )
        {
            if (pXfr->buffered)
            {
                pXfr->transferred += pXfr->buffered;
                pXfr->buffered = 0;
            }
            if((pXfr->transferred % pEp->size == 0) && ( pXfr->remaining == 0) && ( pXfr->transferred > 0)&&(pEp->sendZLP == 0)) 
            { 
              pEp->sendZLP = 1; // Force ZLP transmission in total length is  a multiple of endpoint size  
            } 
            if (   pXfr->buffered == 0
                && pXfr->transferred == 0
                && pXfr->remaining == 0
                && pEp->sendZLP == 0 )
            {
                pEp->sendZLP = 1;
            }

            /* End of Xfr ? */
            if (   pXfr->remaining  || pEp->sendZLP == 1)
            {
              if(pEp->sendZLP == 1)
              { 
                // A null packet will be send, keep trace of it : Change this value only if ZLP will be send!!! 
                pEp->sendZLP = 2;
              } 

              /* Transfer remaining */
              TRACE_DEBUG_WP("%d ", pEp->size);
              /* Send next packet */
              UDPHS_WritePayload(bEndpoint, pEp->size);
              USBHS_AckEpInterrupt(USBHS, 0, USBHS_DEVEPTICR_TXINIC);
              
            }
            else
            {
                TRACE_DEBUG_WP("l%d ", pXfr->transferred);
                /* Disable interrupt on non-control EP */
                if (type != USBHS_DEVEPTCFG_EPTYPE_CTRL)
                {
                    USBHS_DisableIntEP(pUdp, bEndpoint);
                }

                USBHS_DisableEPIntType(pUdp, bEndpoint, USBHS_DEVEPTIDR_TXINEC);
                
                UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_SUCCESS);
                
                pEp->sendZLP = 0;
            }
        }
        else
        {
            TRACE_DEBUG("Err Wr %d\n\r", pEp->sendZLP);
        }
    }
    /* OUT packet received */
    if ( USBHS_DEVEPTISR_RXOUTI & status )
    {
        TRACE_DEBUG_WP("Rd ");

        /* NOT in receiving state */
        if (pEp->state != UDPHS_ENDPOINT_RECEIVING)
        {
            /* Check if ACK received on a Control EP */
            if (   (USBHS_DEVEPTCFG_EPTYPE_CTRL == type)
                && (0 == (status & USBHS_DEVEPTISR_BYCT_Msk)) )
            {
                TRACE_INFO_WP("Ack ");
                USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_RXOUTIC);
                UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_SUCCESS);
                
            }
            /* data has been STALLed */
            else if (USBHS_DEVEPTISR_STALLEDI & status)
            {
                TRACE_INFO_WP("Discard ");
                USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_RXOUTIC);
            }
            /* NAK the data */
            else
            {
                TRACE_INFO_WP("Nak ");
                USBHS_DisableIntEP(pUdp, bEndpoint);
            }
        }
        /* In read state */
        else
        {
            wPktSize = USBHS_ByteCount(pUdp, bEndpoint);

            TRACE_DEBUG_WP("%d ", wPktSize);
            UDPHS_ReadPayload(bEndpoint, wPktSize);
            USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_RXOUTIC);
            
            /* Check if transfer is finished */
            if (pXfr->remaining == 0 || wPktSize < pEp->size)
            {
                USBHS_DisableEPIntType(pUdp, bEndpoint, USBHS_DEVEPTIDR_RXOUTEC);

                /* Disable interrupt if not control EP */
                if (USBHS_DEVEPTCFG_EPTYPE_CTRL != type)
                {
                    USBHS_DisableIntEP(pUdp, bEndpoint);
                }
                UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_SUCCESS);    
                USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_NAKINIC);
                USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_TXINIC);
            }
        }
    }
    /* STALL sent */
    if ( USBHS_DEVEPTISR_STALLEDI & status )
    {
        /* Acknowledge */
        USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_STALLEDIC);

        /* ISO error */
        if (type == USBHS_DEVEPTCFG_EPTYPE_ISO)
        {
            TRACE_WARNING("IsoE[%d]\n\r", bEndpoint);

            UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_ABORTED);
        }
        /* If EP is not halted, clear STALL */
        else
        {
            TRACE_WARNING("Stall[%d]\n\r", bEndpoint);

            if (pEp->state != UDPHS_ENDPOINT_HALTED)
            {
                USBHS_DisableEPIntType(pUdp, bEndpoint, USBHS_DEVEPTIDR_STALLRQC);
            }
        }
    }
    /* SETUP packet received */
    if ( USBHS_DEVEPTISR_RXSTPI & status )
    {
        /* If a transfer was pending, complete it
           Handles the case where during the status phase of a control write
           transfer, the host receives the device ZLP and ack it, but the ack
           is not received by the device */
        if (pEp->state == UDPHS_ENDPOINT_RECEIVING
            || pEp->state == UDPHS_ENDPOINT_RECEIVINGM
            || pEp->state == UDPHS_ENDPOINT_SENDING
            || pEp->state == UDPHS_ENDPOINT_SENDINGM)
        {
            UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_SUCCESS);
        }

        /* ISO Err Flow */
        if (type == USBHS_DEVEPTCFG_EPTYPE_ISO)
        {
            TRACE_WARNING("IsoFE[%d]\n\r", bEndpoint);
            /* Acknowledge setup packet */
            USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_RXSTPIC);            
        }
        else
        {
            TRACE_DEBUG_WP("Stup ");            
            /* Copy setup */
            UDPHS_ReadRequest(pReq);            
            /* Acknowledge setup packet */
            USBHS_AckEpInterrupt(pUdp, bEndpoint, USBHS_DEVEPTICR_RXSTPIC);
            
            /* Handler */
            USBD_RequestHandler(bEndpoint, pReq);   
            
        }
    }
}
#ifdef DMA
/**
 * DMA Single transfer
 * \param bEndpoint EP number.
 * \pXfr  Pointer to transfer instance.
 * \dwCfg DMA Control configuration (excluding length).
 */
static inline void UDPHS_DmaSingle(uint8_t bEndpoint, Transfer *pXfr, uint32_t dwCfg)
{
    Usbhs *pUdp = USBHS;
    UsbhsDevdma *pUsbDma = &pUdp->USBHS_DEVDMA[bEndpoint];

    /* Single transfer */
    SCB_CleanInvalidateDCache();
    
    USBHS_SetDmaBuffAdd(pUsbDma,  (uint32_t)&pXfr->pData[pXfr->transferred]);
    USBHS_GetDmaStatus(pUsbDma);
    
    
    TRACE_DEBUG_WP("Dma[B%d:T%d] ", pXfr->buffered, pXfr->transferred);
    /* DMA Configure */
    USBHS_ConfigureDma(pUsbDma, 0);
    USBHS_ConfigureDma(pUsbDma, (USBHS_DEVDMACONTROL_BUFF_LENGTH(pXfr->buffered) | dwCfg) );
    
    /* Interrupt enable */
    USBHS_EnableDMAIntEP(pUdp, bEndpoint);
}
/**
 * Endpoint DMA interrupt handler.
 * This function handles DMA interrupts.
 * \param bEndpoint Index of endpoint
 */
static void UDPHS_DmaHandler(uint8_t bEndpoint)
{
    Usbhs    *pUdp  = USBHS;
    uint8_t bDmaEndpoint = bEndpoint -1;

    Endpoint *pEp  = &(endpoints[bEndpoint]);
    Transfer *pXfr = (Transfer*)&(pEp->transfer);

    uint32_t dwDmaSr;
    int32_t iRemain, iXfred;
    uint8_t bRc = USBD_STATUS_SUCCESS;
    UsbhsDevdma *pUsbDma = &pUdp->USBHS_DEVDMA[bDmaEndpoint];
    
    dwDmaSr = USBHS_GetDmaStatus(pUsbDma);
    TRACE_DEBUG_WP("iDma%d,%x ", bDmaEndpoint, dwDmaSr);
    /* Mbl transfer */
    if (pEp->state == UDPHS_ENDPOINT_SENDINGM)
    {
        /* Not implemented */
        return;
    }
    else if (pEp->state == UDPHS_ENDPOINT_RECEIVINGM)
    {
        /* Not implemented */
        return;
    }

    /* Disable DMA interrupt to avoid receiving 2 (B_EN and TR_EN) */
    pUdp->USBHS_DEVDMA[bDmaEndpoint].USBHS_DEVDMACONTROL &= ~(USBHS_DEVDMACONTROL_END_TR_EN
                                                    |USBHS_DEVDMACONTROL_END_B_EN);
    SCB_CleanInvalidateDCache();
    if (USBHS_DEVDMASTATUS_END_BF_ST & dwDmaSr)
    {
        TRACE_DEBUG_WP("EoDmaB ");
        /* BUFF_COUNT holds the number of untransmitted bytes.
           BUFF_COUNT is equal to zero in case of good transfer */
        iRemain = (dwDmaSr & USBHS_DEVDMASTATUS_BUFF_COUNT_Msk)
                        >> USBHS_DEVDMASTATUS_BUFF_COUNT_Pos;
        TRACE_DEBUG_WP("C%d ", iRemain);
        iXfred  = pXfr->buffered - iRemain;

        pXfr->transferred += iXfred;
        pXfr->buffered     = iRemain;
        pXfr->remaining   -= iXfred;
        TRACE_DEBUG_WP("[B%d:T%d:R%d] ", pXfr->buffered, pXfr->transferred, pXfr->remaining);
        /* There is still data */
        if (pXfr->remaining + pXfr->buffered > 0)
        {   
            if (pXfr->remaining > DMA_MAX_FIFO_SIZE)
            {
                pXfr->buffered = DMA_MAX_FIFO_SIZE;
            }
            else
            {
                pXfr->buffered = pXfr->remaining;
            }
            /* Single transfer again */
            UDPHS_DmaSingle(bDmaEndpoint, pXfr, USBHS_DEVDMACONTROL_END_TR_EN
                                             | USBHS_DEVDMACONTROL_END_TR_IT
                                             | USBHS_DEVDMACONTROL_END_B_EN
                                             | USBHS_DEVDMACONTROL_END_BUFFIT
                                             | USBHS_DEVDMACONTROL_CHANN_ENB);
        }
    }
    else if (USBHS_DEVDMASTATUS_END_TR_ST & dwDmaSr)
    {
        TRACE_DEBUG_WP("EoDmaT ");
        pXfr->transferred = pXfr->buffered -
            ((dwDmaSr & USBHS_DEVDMASTATUS_BUFF_COUNT_Msk)
                    >> USBHS_DEVDMASTATUS_BUFF_COUNT_Pos);
        pXfr->remaining = 0;

        TRACE_DEBUG_WP("[B%d:T%d] ", pXfr->buffered, pXfr->transferred);
    }
    else
    {
        TRACE_ERROR("UDPHS_DmaHandler: ST 0x%X\n\r", (unsigned int)dwDmaSr);
        bRc = USBD_STATUS_ABORTED;
    }
    /* Callback */
    if (pXfr->remaining == 0)
    {
        UDPHS_EndOfTransfer(bEndpoint, bRc);
        
    }
    
}
#endif
/**
 * Sends data through a USB endpoint. Sets up the transfer descriptor,
 * writes one or two data payloads (depending on the number of FIFO bank
 * for the endpoint) and then starts the actual transfer. The operation is
 * complete when all the data has been sent.
 *
 * *If the size of the buffer is greater than the size of the endpoint
 *  (or twice the size if the endpoint has two FIFO banks), then the buffer
 *  must be kept allocated until the transfer is finished*. This means that
 *  it is not possible to declare it on the stack (i.e. as a local variable
 *  of a function which returns after starting a transfer).
 *
 * \param pEndpoint Pointer to Endpoint struct.
 * \param pData Pointer to a buffer with the data to send.
 * \param dLength Size of the data buffer.
 * \return USBD_STATUS_SUCCESS if the transfer has been started;
 *         otherwise, the corresponding error status code.
 */
static inline uint8_t UDPHS_Write(uint8_t    bEndpoint,
                                const void *pData,
                                uint32_t   dLength)
{
    Usbhs    *pUdp  = USBHS;
    uint8_t bDmaEndpoint = bEndpoint -1;
      
    Endpoint *pEp  = &(endpoints[bEndpoint]);
    Transfer *pXfr = (Transfer*)&(pEp->transfer);
    /* Return if busy */
    if (pEp->state != UDPHS_ENDPOINT_IDLE)
    {
        return USBD_STATUS_LOCKED;
    }
    /* Sending state */
    pEp->state = UDPHS_ENDPOINT_SENDING;
    TRACE_DEBUG_WP("Wr%d(%d) ", bEndpoint, dLength);
    pEp->sendZLP = 0;
    /* Setup transfer descriptor */
    pXfr->pData       = (void*) pData;
    pXfr->remaining   = dLength;
    pXfr->buffered    = 0;
    pXfr->transferred = 0;
    
  #ifdef DMA
    SCB_CleanInvalidateDCache();
    /* 1. DMA supported, 2. Not ZLP */
    if (CHIP_USB_ENDPOINTS_DMA(bEndpoint)
        && pXfr->remaining > 0)
    {
        if (pXfr->remaining > DMA_MAX_FIFO_SIZE)
        {
            /* Transfer the max */
            pXfr->buffered = DMA_MAX_FIFO_SIZE;
        }
        else
        {
            /* Good size */
            pXfr->buffered = pXfr->remaining;
        }
        /* Single transfer */
        UDPHS_DmaSingle(bDmaEndpoint, pXfr, USBHS_DEVDMACONTROL_END_B_EN
                                         | USBHS_DEVDMACONTROL_END_BUFFIT
                                         | USBHS_DEVDMACONTROL_CHANN_ENB);
        return USBD_STATUS_SUCCESS;
    }
  #endif

    /* Enable IT */
    USBHS_EnableIntEP(pUdp, bEndpoint );
    USBHS_EnableEPIntType(pUdp, bEndpoint,  USBHS_DEVEPTIER_TXINES);
    return USBD_STATUS_SUCCESS;
}

/**
 * Sends data through a USB endpoint. Sets up the transfer descriptor list,
 * writes one or two data payloads (depending on the number of FIFO bank
 * for the endpoint) and then starts the actual transfer. The operation is
 * complete when all the transfer buffer in the list has been sent.
 *
 * *If the size of the buffer is greater than the size of the endpoint
 *  (or twice the size if the endpoint has two FIFO banks), then the buffer
 *  must be kept allocated until the transfer is finished*. This means that
 *  it is not possible to declare it on the stack (i.e. as a local variable
 *  of a function which returns after starting a transfer).
 *
 * \param pEndpoint Pointer to Endpoint struct.
 * \param pData Pointer to a buffer with the data to send.
 * \param dLength Size of the data buffer.
 * \return USBD_STATUS_SUCCESS if the transfer has been started;
 *         otherwise, the corresponding error status code.
 */
static inline uint8_t UDPHS_AddWr(uint8_t   bEndpoint,
                                const void *pData,
                                uint32_t    dLength)
{
    Usbhs    *pUdp  = USBHS;
    
    Endpoint *pEp  = &(endpoints[bEndpoint]);
    MblTransfer *pMbl = (MblTransfer*)&(pEp->transfer);
    USBDTransferBuffer *pTx;
    /* Check parameter */
    if (dLength >= 0x10000)
    {
        return USBD_STATUS_INVALID_PARAMETER;
    }
    /* Data in process */
    if (pEp->state > UDPHS_ENDPOINT_IDLE)
    {   /* MBL transfer */
        if (pMbl->transType)
        {
            if (pMbl->listState == MBL_FULL)
            {
                return USBD_STATUS_LOCKED;
            }
        }
        else
        {
            return USBD_STATUS_LOCKED;
        }
    }

    TRACE_DEBUG_WP("AddW%d(%d) ", bEndpoint, dLength);
    /* Add buffer to buffer list and update index */
    pTx = &(pMbl->pMbl[pMbl->inCurr]);
    pTx->pBuffer = (uint8_t*)pData;
    pTx->size = pTx->remaining = dLength;
    pTx->transferred = pTx->buffered = 0;
    /* Update input index */
    if (pMbl->inCurr >= (pMbl->listSize-1)) pMbl->inCurr = 0;
    else                                    pMbl->inCurr ++;
    if (pMbl->inCurr == pMbl->outCurr)      pMbl->listState = MBL_FULL;
    else                                    pMbl->listState = 0;
    /* Start sending when offset achieved */
    if (MBL_NbBuffer(pMbl->inCurr, pMbl->outCurr, pMbl->listSize)
            >= pMbl->offsetSize
        && pEp->state == UDPHS_ENDPOINT_IDLE)
    {
        uint8_t nbBanks = CHIP_USB_ENDPOINTS_BANKS(bEndpoint);

        /* Change state */
        pEp->state = UDPHS_ENDPOINT_SENDINGM;

        TRACE_DEBUG_WP("StartM ");

        /* Fill data into FIFO */
        for (;
             nbBanks && pMbl->pMbl[pMbl->inCurr].remaining;
             nbBanks --)
        {
            UDPHS_MblWriteFifo(bEndpoint);
            USBHS_RaiseEPInt(pUdp, bEndpoint, USBHS_DEVEPTIFR_TXINIS);
        }

        /* Enable interrupt */
        USBHS_EnableIntEP(pUdp, bEndpoint);
        USBHS_EnableEPIntType(pUdp, bEndpoint,  USBHS_DEVEPTIER_TXINES);

    }

    return USBD_STATUS_SUCCESS;
}

/**
 * Reads incoming data on an USB endpoint This methods sets the transfer
 * descriptor and activate the endpoint interrupt. The actual transfer is
 * then carried out by the endpoint interrupt handler. The Read operation
 * finishes either when the buffer is full, or a short packet (inferior to
 * endpoint maximum  size) is received.
 *
 * *The buffer must be kept allocated until the transfer is finished*.
 * \param bEndpoint Endpoint number.
 * \param pData Pointer to a data buffer.
 * \param dLength Size of the data buffer in bytes.
 * \return USBD_STATUS_SUCCESS if the read operation has been started;
 *         otherwise, the corresponding error code.
 */
static inline uint8_t UDPHS_Read(uint8_t  bEndpoint,
                                 void     *pData,
                                 uint32_t dLength)
{
    Usbhs    *pUdp  = USBHS;
    uint8_t bDmaEndpoint = (bEndpoint-1);
    Endpoint *pEp  = &(endpoints[bEndpoint]);
    Transfer *pXfr = (Transfer*)&(pEp->transfer);
    /* Return if busy */
    if (pEp->state != UDPHS_ENDPOINT_IDLE)
    {
        return USBD_STATUS_LOCKED;
    }
    /* Receiving state */
    pEp->state = UDPHS_ENDPOINT_RECEIVING;

    TRACE_DEBUG_WP("Rd%d(%d) ", bEndpoint, dLength);
    /* Setup transfer descriptor */
    pXfr->pData       = (void*) pData;
    pXfr->remaining   = dLength;
    pXfr->buffered    = 0;
    pXfr->transferred = 0;
    
  #ifdef DMA
    SCB_CleanInvalidateDCache();
    /* If: 1. DMA supported, 2. Has data */
    if (CHIP_USB_ENDPOINTS_DMA(bEndpoint)
        && pXfr->remaining > 0)
    {
        /* DMA XFR size adjust */
        if (pXfr->remaining > DMA_MAX_FIFO_SIZE)
            pXfr->buffered = DMA_MAX_FIFO_SIZE;
        else
            pXfr->buffered = pXfr->remaining;
        /* Single transfer */
        UDPHS_DmaSingle(bDmaEndpoint, pXfr, USBHS_DEVDMACONTROL_END_TR_EN
                                         | USBHS_DEVDMACONTROL_END_TR_IT
                                         | USBHS_DEVDMACONTROL_END_B_EN
                                         | USBHS_DEVDMACONTROL_END_BUFFIT
                                         | USBHS_DEVDMACONTROL_CHANN_ENB);
        return USBD_STATUS_SUCCESS;
    }
  #endif

    /* Enable IT */
    USBHS_EnableIntEP(pUdp, bEndpoint);
    USBHS_EnableEPIntType(pUdp, bEndpoint,  USBHS_DEVEPTIER_RXOUTES);
    
    return USBD_STATUS_SUCCESS;
}
#if 0
/**
 * Reads incoming data on an USB endpoint This methods sets the transfer
 * descriptor and activate the endpoint interrupt. The actual transfer is
 * then carried out by the endpoint interrupt handler. The Read operation
 * finishes either when the buffer is full, or a short packet (inferior to
 * endpoint maximum  size) is received.
 *
 * *The buffer must be kept allocated until the transfer is finished*.
 * \param bEndpoint Endpoint number.
 * \param pData Pointer to a data buffer.
 * \param dLength Size of the data buffer in bytes.
 * \return USBD_STATUS_SUCCESS if the read operation has been started;
 *         otherwise, the corresponding error code.
 */
static inline uint8_t UDPHS_AddRd(uint8_t  bEndpoint,
                                void     *pData,
                                uint32_t dLength)
{
    return USBD_STATUS_SW_NOT_SUPPORTED;
}
#endif
/*---------------------------------------------------------------------------
 *      Exported functions
 *---------------------------------------------------------------------------*/
/**
 * USBD (UDP) interrupt handler
 * Manages device resume, suspend, end of bus reset.
 * Forwards endpoint events to the appropriate handler.
 */
void USBHS_Handler(void)
{
    Usbhs *pUdp = USBHS;

    uint32_t status, IntStatus;
    uint8_t  numIt;

    status  = USBHS_ReadIntStatus(pUdp, 0xFFFFFFFF);
    IntStatus = status & USBHS_IsIntEnable(pUdp, 0xFFFFFFFF);

    
    /* Handle all USBHS interrupts */
    TRACE_DEBUG_WP("\n\r%c ", USBD_HAL_IsHighSpeed() ? 'H' : 'F');
    //while( status )
    {
        /* SOF */
        if (IntStatus & USBHS_DEVISR_SOF)
        {
            TRACE_DEBUG_WP("SOF ");
            /* SOF handler */

            /* Acknowledge interrupt */
            USBHS_AckInt(pUdp,  USBHS_DEVICR_SOFC);
            status &= ~(uint32_t)USBHS_DEVISR_SOF;
        }
         /* MSOF*/
        else if (IntStatus & USBHS_DEVISR_MSOF)
        {
            TRACE_DEBUG_WP("Mosf ");
            
            /* Acknowledge interrupt */
            USBHS_AckInt(pUdp,  USBHS_DEVICR_MSOFC);
            
        }
        /* Suspend, treated last */
        else if (IntStatus & USBHS_DEVISR_SUSP)
        {
            TRACE_WARNING_WP("Susp ");
            USBHS_FreezeClock(pUdp, false);
            USBHS_DisableInt(pUdp, USBHS_DEVIDR_SUSPEC);
            
            /* Enable wakeup */
            USBHS_EnableInt(pUdp, USBHS_DEVIER_WAKEUPES  );
            
            USBHS_FreezeClock(pUdp, true);      // Mandatory to exit of sleep mode after a wakeup event
            /* Acknowledge interrupt */
            //USBHS_AckInt(pUdp,  (USBHS_DEVICR_SUSPC | USBHS_DEVICR_WAKEUPC) );

            USBD_SuspendHandler();
        }
        /* Wake up */
        else if (IntStatus & USBHS_DEVISR_WAKEUP)
        {

            TRACE_INFO_WP("Rsm ");
            USBHS_FreezeClock(pUdp, false);

            while( !USBHS_ISUsableClock(pUdp) ) 
            {
              if(status & USBHS_DEVISR_SUSP)
              {
                break;   // In case of USB state change in HS
              }
            }
        
            /* Acknowledge interrupt */
            /*USBHS_AckInt(pUdp,  (USBHS_DEVICR_SUSPC |
                                 USBHS_DEVICR_WAKEUPC |
                                 USBHS_DEVICR_EORSMC) );*/

            USBHS_DisableInt(pUdp, USBHS_DEVIDR_WAKEUPEC);
            USBHS_EnableInt(pUdp, USBHS_DEVIER_SUSPES );
            //USBHS_AckInt(pUdp,  (USBHS_DEVIER_EORSMES | USBHS_DEVICR_WAKEUPC) );
            
            
        }
        /* Bus reset */
        else if (IntStatus & USBHS_DEVISR_EORST)
        {
            TRACE_DEBUG_WP("EoB ");
            
            /* Acknowledge interrupt */
            USBHS_AckInt(pUdp,  USBHS_DEVICR_EORSTC);
            /* Flush and enable the suspend interrupt */
            USBHS_AckInt(pUdp,  (USBHS_DEVICR_SUSPC | USBHS_DEVICR_WAKEUPC) );
            USBHS_EnableInt(pUdp, USBHS_DEVIER_SUSPES );

            /* Reset handler */
            USBD_ResetHandler();

            
        }
        /* Upstream resume */
        else if (IntStatus & USBHS_DEVISR_UPRSM)
        {
            TRACE_DEBUG_WP("ExtRes ");
            /* Acknowledge interrupt */
            USBHS_AckInt(pUdp,  USBHS_DEVICR_UPRSMC);
        }
        
        /* Endpoints */
        else
        {
          #ifdef DMA
            for (numIt = 0; numIt < NUM_IT_MAX; numIt ++)
            {
                if (CHIP_USB_ENDPOINTS_DMA(numIt))
                {
                  if (IntStatus & (USBHS_DEVIMR_DMA_1 << (numIt - 1) ))
                  {
                      UDPHS_DmaHandler(numIt);
                  }
                }
                else if (IntStatus & (USBHS_DEVISR_PEP_0 << numIt))
                {
                    UDPHS_EndpointHandler(numIt);
                }
                memory_sync();
            }

          #else
            for (numIt = 0; numIt < NUM_IT_MAX; numIt ++)
            {
                if (IntStatus & (USBHS_DEVISR_PEP_0 << numIt))
                {
                    UDPHS_EndpointHandler(numIt);
                }
                memory_sync();
            }
          #endif
        }
        
        /* Update interrupt status */
        //status  = USBHS_ReadIntStatus(pUdp, 0xFFFFFFFF);
        //status &= USBHS_IsIntEnable(pUdp, 0xFFFFFFFF);

        TRACE_DEBUG_WP("\n\r");
        if (status)
        {
            TRACE_DEBUG_WP(" - ");
        }
    }
    //NVIC_ClearPendingIRQ(USBHS_IRQn); //  clear l'IRQ
    memory_sync();
    
}

/**
 * \brief Reset endpoints and disable them.
 * -# Terminate transfer if there is any, with given status;
 * -# Reset the endpoint & disable it.
 * \param bmEPs    Bitmap for endpoints to reset.
 * \param bStatus  Status passed to terminate transfer on endpoint.
 * \param bKeepCfg 1 to keep old endpoint configuration.
 * \note Use USBD_HAL_ConfigureEP() to configure and enable endpoint
         if not keeping old configuration.
 * \sa USBD_HAL_ConfigureEP().
 */
void USBD_HAL_ResetEPs(uint32_t bmEPs, uint8_t bStatus, uint8_t bKeepCfg)
{
    Usbhs *pUdp = USBHS;

    Endpoint *pEndpoint;
    uint32_t tmp = bmEPs & ((1<<CHIP_USB_NUMENDPOINTS)-1);
    uint8_t  ep;
    uint32_t epBit, epCfg;

    for (ep = 0, epBit = 1; ep < CHIP_USB_NUMENDPOINTS; ep ++)
    {
        if (tmp & epBit)
        {
            

            /* Disable ISR */
            pUdp->USBHS_DEVIDR |= (epBit << SHIFT_INTERUPT);
            /* Kill pending Banks ?? */
            #if 0
            while(USBHS_IsBankFree(pUdp, ep) > 0)
             {
               USBHS_KillBank(pUdp, ep);
               while(USBHS_IsBankKilled(pUdp, ep));
             }
            #endif
            
            /* Reset transfer information */
            pEndpoint = &(endpoints[ep]);
            /* Reset endpoint state */
            pEndpoint->bank = 0;
            /* Endpoint configure */
            epCfg = pUdp->USBHS_DEVEPTCFG[ep];
            /* Reset endpoint */
//            USBHS_ResetEP(pUdp, epBit);
            /* Restore configure */
            if (bKeepCfg)
            {
                pUdp->USBHS_DEVEPTCFG[ep] = epCfg;
            }
            else
            {
                pEndpoint->state = UDPHS_ENDPOINT_DISABLED;
            }

            /* Terminate transfer on this EP */
            UDPHS_EndOfTransfer(ep, bStatus);
        }
        epBit <<= 1;
    }
}

/**
 * Cancel pending READ/WRITE
 * \param bmEPs    Bitmap for endpoints to reset.
 * \note EP callback is invoked with USBD_STATUS_CANCELED.
 */
void USBD_HAL_CancelIo(uint32_t bmEPs)
{
    Usbhs *pUdp = USBHS;
    //UdphsEpt *pHwEp = NULL;

    uint32_t tmp = bmEPs & ((1<<CHIP_USB_NUMENDPOINTS)-1);
    uint8_t  ep;
    uint32_t epBit;
    for (ep = 0, epBit = 1; ep < CHIP_USB_NUMENDPOINTS; ep ++)
    {
        if (tmp & epBit)
        {
            //pHwEp = &pUdp->UDPHS_EPT[ep];

            /* Disable ISR */
            pUdp->USBHS_DEVIDR |= (epBit << SHIFT_INTERUPT);
            /* Kill pending Banks ?? */
            #if 0
            pHwEp->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_KILL_BANK;
            pHwEp->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_KILL_BANK;
            pHwEp->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_KILL_BANK;
            #endif

            /* Terminate transfer on this EP */
            UDPHS_EndOfTransfer(ep, USBD_STATUS_CANCELED);
        }
        epBit <<= 1;
    }
}

/**
 * Configures an endpoint according to its endpoint Descriptor.
 * \param pDescriptor Pointer to an endpoint descriptor.
 * \return The endpoint address.
 */
uint8_t USBD_HAL_ConfigureEP(const USBEndpointDescriptor *pDescriptor)
{
    Usbhs    *pUdp = USBHS;
    
    Endpoint *pEndpoint;
    uint8_t  bEndpoint;
    uint8_t  bType;
    uint8_t  bEndpointDir;
    uint8_t  bNbTrans  = 1;
    uint8_t  bSizeEpt  = 0;
    uint8_t  bHs = ((USBHS_GetUsbSpeed(pUdp) == USBHS_SR_SPEED_HIGH_SPEED)? true: false );

    /* NULL descriptor -> Control endpoint 0 */
    if (pDescriptor == 0)
    {

        bEndpoint = 0;
        pEndpoint = &(endpoints[bEndpoint]);
        bType = USBEndpointDescriptor_CONTROL;
        bEndpointDir = 0;
        pEndpoint->size = CHIP_USB_ENDPOINTS_MAXPACKETSIZE(0);
        pEndpoint->bank = CHIP_USB_ENDPOINTS_BANKS(0);
    }
    /* Device descriptor -> Control endpoint 0 */
    else if (pDescriptor->bDescriptorType == USBGenericDescriptor_DEVICE)
    {
        USBDeviceDescriptor *pDevDesc = (USBDeviceDescriptor*)pDescriptor;
        bEndpoint = 0;
        pEndpoint = &(endpoints[bEndpoint]);
        bType = USBEndpointDescriptor_CONTROL;
        bEndpointDir = 0;
        pEndpoint->size =pDevDesc->bMaxPacketSize0;
        pEndpoint->bank = CHIP_USB_ENDPOINTS_BANKS(0);
    }
    /* Endpoint descriptor */
    else
    {
        /* The endpoint number */
        bEndpoint = USBEndpointDescriptor_GetNumber(pDescriptor);
        pEndpoint = &(endpoints[bEndpoint]);
        /* Transfer type: Control, Isochronous, Bulk, Interrupt */
        bType = USBEndpointDescriptor_GetType(pDescriptor);
        /* Direction, ignored for control endpoints */
        bEndpointDir = USBEndpointDescriptor_GetDirection(pDescriptor);
        pEndpoint->size = USBEndpointDescriptor_GetMaxPacketSize(pDescriptor);
        pEndpoint->bank = CHIP_USB_ENDPOINTS_BANKS(bEndpoint);

        /* Convert descriptor value to EP configuration */
        if (bHs) {  /* HS Interval, *125us */

            /* MPS: Bit12,11 specify NB_TRANS, as USB 2.0 Spec. */
            bNbTrans = ((pEndpoint->size >> 11) & 0x3);
            if(CHIP_USB_ENDPOINTS_HBW(bEndpoint))
            {
              if (bNbTrans == 3)
                bNbTrans = 1;
              else
                bNbTrans ++;
            }
            else
            {
                bNbTrans = 0;
            }
            

            /* Mask, bit 10..0 is the size */
            pEndpoint->size &= 0x7FF;
        }
    }

    TRACE_DEBUG_WP("CfgE%d ", bEndpoint);

    /* Abort the current transfer is the endpoint was configured and in
       Write or Read state */
    if( (pEndpoint->state == UDPHS_ENDPOINT_RECEIVING)
     || (pEndpoint->state == UDPHS_ENDPOINT_SENDING)
     || (pEndpoint->state == UDPHS_ENDPOINT_RECEIVINGM)
     || (pEndpoint->state == UDPHS_ENDPOINT_SENDINGM) ) {

        UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_RESET);
    }
    pEndpoint->state = UDPHS_ENDPOINT_IDLE;
    
    
    /* Configure endpoint size */
    if( pEndpoint->size <= 8 )
        bSizeEpt = 0;
    else if ( pEndpoint->size <= 16 )
        bSizeEpt = 1;
    else if ( pEndpoint->size <= 32 )
        bSizeEpt = 2;
    else if ( pEndpoint->size <= 64 )
        bSizeEpt = 3;
    else if ( pEndpoint->size <= 128 )
        bSizeEpt = 4;
    else if ( pEndpoint->size <= 256 )
        bSizeEpt = 5;
    else if ( pEndpoint->size <= 512 )
        bSizeEpt = 6;
    else if ( pEndpoint->size <= 1024 )
        bSizeEpt = 7;
   
    /* Configure endpoint */
    if (bType == USBEndpointDescriptor_CONTROL)
    {        
        USBHS_EnableIntEP(pUdp, bEndpoint);
    }

    USBHS_ConfigureEPs(pUdp, bEndpoint, bType, bEndpointDir, bSizeEpt, ((pEndpoint->bank) - 1));
    
    USBHS_AllocateMemory(pUdp, bEndpoint);
    while( (USBHS_DEVEPTISR_CFGOK & pUdp->USBHS_DEVEPTISR[bEndpoint]) == 0 ) {

        /* resolved by clearing the reset IT in good place */
        TRACE_ERROR("PB bEndpoint: 0x%X\n\r", bEndpoint);
        TRACE_ERROR("PB bSizeEpt: 0x%X\n\r", bSizeEpt);
        TRACE_ERROR("PB bEndpointDir: 0x%X\n\r", bEndpointDir);
        TRACE_ERROR("PB bType: 0x%X\n\r", bType);
        TRACE_ERROR("PB pEndpoint->bank: 0x%X\n\r", pEndpoint->bank);
        TRACE_ERROR("PB UDPHS_EPTCFG: 0x%X\n\r", (unsigned int)pUdp->USBHS_DEVEPTCFG[bEndpoint]);
        for(;;);
    }

    if (bType == USBEndpointDescriptor_CONTROL)
    {
        // enable Endpoint
        USBHS_EnableEP(pUdp, bEndpoint, true);
        // Enable Ep interrupt type
        USBHS_EnableEPIntType(pUdp, bEndpoint, USBHS_DEVEPTIER_RXOUTES | USBHS_DEVEPTIER_RXSTPES );
        // enable endpoint interrupt
        USBHS_EnableIntEP(pUdp, bEndpoint);
    }
    else
    {
#ifndef DMA
        USBHS_EnableEP(pUdp, bEndpoint, true);
#else
        USBHS_EnableEP(pUdp, bEndpoint, true);
        if (bType == USBEndpointDescriptor_ISOCHRONOUS)
        {
            USBHS_SetIsoTrans(pUdp, bEndpoint, bNbTrans);
        }
        USBHS_AutoSwitchBankEnable(pUdp, bEndpoint, true);
#endif
    }

    //TRACE_DEBUG_WP("<%x,%x,%x> ", pEpt->UDPHS_EPTCFG, pEpt->UDPHS_EPTCTL, pEpt->UDPHS_EPTSTA);
    return bEndpoint;
}

/**
 * Set callback for a USB endpoint for transfer (read/write).
 *
 * \param bEP       Endpoint number.
 * \param fCallback Optional callback function to invoke when the transfer is
 *                  complete.
 * \param pCbData   Optional pointer to data to the callback function.
 * \return USBD_STATUS_SUCCESS or USBD_STATUS_LOCKED if endpoint is busy.
 */
uint8_t USBD_HAL_SetTransferCallback(uint8_t          bEP,
                                  TransferCallback fCallback,
                                  void             *pCbData)
{
    Endpoint *pEndpoint = &(endpoints[bEP]);
    TransferHeader *pTransfer = (TransferHeader*)&(pEndpoint->transfer);
    /* Check that the endpoint is not transferring */
    if (pEndpoint->state > UDPHS_ENDPOINT_IDLE) {
        return USBD_STATUS_LOCKED;
    }
    TRACE_DEBUG_WP("sXfrCb ");
    /* Setup the transfer callback and extension data */
    pTransfer->fCallback = (void*)fCallback;
    pTransfer->pArgument = pCbData;
    return USBD_STATUS_SUCCESS;
}

/**
 * Configure an endpoint to use multi-buffer-list transfer mode.
 * The buffers can be added by _Read/_Write function.
 * \param pMbList  Pointer to a multi-buffer list used, NULL to disable MBL.
 * \param mblSize  Multi-buffer list size (number of buffers can be queued)
 * \param startOffset When number of buffer achieve this offset transfer start
 */
uint8_t USBD_HAL_SetupMblTransfer( uint8_t bEndpoint,
                                   USBDTransferBuffer* pMbList,
                                   uint16_t mblSize,
                                   uint16_t startOffset)
{
    Endpoint *pEndpoint = &(endpoints[bEndpoint]);
    MblTransfer *pXfr = (MblTransfer*)&(pEndpoint->transfer);
    uint16_t i;
    /* Check that the endpoint is not transferring */
    if (pEndpoint->state > UDPHS_ENDPOINT_IDLE) {
        return USBD_STATUS_LOCKED;
    }
    TRACE_DEBUG_WP("sMblXfr ");
    /* Enable Multi-Buffer Transfer List */
    if (pMbList) {
        /* Reset list items */
        for (i = 0; i < mblSize; i --) {
            pMbList[i].pBuffer     = NULL;
            pMbList[i].size        = 0;
            pMbList[i].transferred = 0;
            pMbList[i].buffered    = 0;
            pMbList[i].remaining   = 0;
        }
        /* Setup transfer */
        pXfr->transType  = 1;
        pXfr->listState  = 0; /* OK */
        pXfr->listSize   = mblSize;
        pXfr->pMbl       = pMbList;
        pXfr->outCurr = pXfr->outLast = 0;
        pXfr->inCurr  = 0;
        pXfr->offsetSize = startOffset;
    }
    /* Disable Multi-Buffer Transfer */
    else {
        pXfr->transType  = 0;
        pXfr->pMbl       = NULL;
        pXfr->listSize   = 0;
        pXfr->offsetSize = 1;
    }
    return USBD_STATUS_SUCCESS;
}

/**
 * Sends data through a USB endpoint. Sets up the transfer descriptor,
 * writes one or two data payloads (depending on the number of FIFO bank
 * for the endpoint) and then starts the actual transfer. The operation is
 * complete when all the data has been sent.
 *
 * *If the size of the buffer is greater than the size of the endpoint
 *  (or twice the size if the endpoint has two FIFO banks), then the buffer
 *  must be kept allocated until the transfer is finished*. This means that
 *  it is not possible to declare it on the stack (i.e. as a local variable
 *  of a function which returns after starting a transfer).
 *
 * \param bEndpoint Endpoint number.
 * \param pData Pointer to a buffer with the data to send.
 * \param dLength Size of the data buffer.
 * \return USBD_STATUS_SUCCESS if the transfer has been started;
 *         otherwise, the corresponding error status code.
 */
uint8_t USBD_HAL_Write( uint8_t          bEndpoint,
                        const void       *pData,
                        uint32_t         dLength)
{
    if (endpoints[bEndpoint].transfer.transHdr.transType)
        return UDPHS_AddWr(bEndpoint, pData, dLength);
    else
        return UDPHS_Write(bEndpoint, pData, dLength);
}

/**
 * Special write function.
 * Sends data through a USB endpoint. Sets up the transfer descriptor,
 * writes header and one or two data payloads (depending on the number of
 * FIFO bank for the endpoint) and then starts the actual transfer. The
 * operation is complete when all the data has been sent.
 *
 * *If the size of the buffer is greater than the size of the endpoint
 *  (or twice the size if the endpoint has two FIFO banks), then the buffer
 *  must be kept allocated until the transfer is finished*. This means that
 *  it is not possible to declare it on the stack (i.e. as a local variable
 *  of a function which returns after starting a transfer).
 *
 * \param bEndpoint Endpoint number.
 * \param pData Pointer to a buffer with the data to send.
 * \param dLength Size of the data buffer.
 * \return USBD_STATUS_SUCCESS if the transfer has been started;
 *         otherwise, the corresponding error status code.
 */
uint8_t USBD_HAL_WrWithHdr(uint8_t bEndpoint,
                           const void * pHdr, uint8_t bHdrLen,
                           const void * pData,uint32_t dLength)
{
    Usbhs    *pUdp  = USBHS;
    
    Endpoint *pEp  = &(endpoints[bEndpoint]);
    uint8_t bDmaEndpoint = (bEndpoint-1);
    Transfer *pXfr = (Transfer*)&(pEp->transfer);
    /* Return if DMA is not supported */
    if (!CHIP_USB_ENDPOINTS_DMA(bEndpoint))
    {
       return USBD_STATUS_HW_NOT_SUPPORTED;
    }

#ifdef DMA
    /* Return if busy */
    if (pEp->state != UDPHS_ENDPOINT_IDLE)
    {
        return USBD_STATUS_LOCKED;
    }
    /* Sending state */
    pEp->state = UDPHS_ENDPOINT_SENDING;
    TRACE_DEBUG_WP("Wr%d(%d+%d) ", bEndpoint, bHdrLen, dLength);

    pEp->sendZLP = 0;

    /* Setup transfer descriptor */
    pXfr->pData       = (void*) pData;
    pXfr->remaining   = bHdrLen + dLength;
    pXfr->buffered    = 0;
    pXfr->transferred = 0;
    
    SCB_CleanInvalidateDCache();
    /* 1. DMA supported always, 2. Not ZLP */
    if (bHdrLen + dLength > 0)
    {
        uint8_t bNbTrans = (USBHS_GetConfigureEPs(pUdp, bEndpoint, USBHS_DEVEPTCFG_NBTRANS_Msk)
                                                  >> USBHS_DEVEPTCFG_NBTRANS_Pos);
        if (pXfr->remaining > DMA_MAX_FIFO_SIZE)
        {
            /* Transfer the max */
            pXfr->buffered = DMA_MAX_FIFO_SIZE;
        }
        else
        {
            /* Good size, total size */
            pXfr->buffered = pXfr->remaining;
        }

        /* LD1: header - load to fifo without interrupt */
        /* Header discarded if exceed the DMA FIFO length */
        //if (bHdrLen > DMA_MAX_FIFO_SIZE) bHdrLen = DMA_MAX_FIFO_SIZE;
        pDmaLL[0].pNxtDesc = (void*)&pDmaLL[1];
        pDmaLL[0].pAddr    = (void*)pHdr;
        pDmaLL[0].dwCtrl   = USBHS_DEVDMACONTROL_CHANN_ENB
                           | USBHS_DEVDMACONTROL_BUFF_LENGTH(bHdrLen)
                           | USBHS_DEVDMACONTROL_LDNXT_DSC;
        /* High bandwidth ISO EP, max size n*ep_size */
        if (bNbTrans > 1) {
            uint8_t* pU8 = (uint8_t*)pData;
            uint32_t maxSize = bNbTrans * pEp->size;
            dLength = pXfr->buffered - bHdrLen;
            if (dLength > maxSize) dLength = maxSize;
          #if 0 /* Prepare banks by 1 DMA descriptor -- NK if not standard EP size, works! */
            /* LD2: data   -  load to fifo with interrupt */
            pDmaLL[1].pNxtDesc = (void*)NULL;
            pDmaLL[1].pAddr    = (void*)pU8;
            pDmaLL[1].dwCtrl   = USBHS_DEVDMACONTROL_CHANN_ENB
                               | USBHS_DEVDMACONTROL_BUFF_LENGTH(dLength)
                               | USBHS_DEVDMACONTROL_END_B_EN
                               | USBHS_DEVDMACONTROL_END_BUFFIT;
          #else
            uint32_t pktLen, ndxData = 0;
            /* LD2: data   -  bank 0 */
            pktLen = pEp->size - bHdrLen;
            if (pktLen >= dLength) { /* It's the last DMA LLI */
                pDmaLL[1].pNxtDesc = (void*)NULL;
                pDmaLL[1].pAddr    = (void*)pU8;
                pDmaLL[1].dwCtrl   =  USBHS_DEVDMACONTROL_CHANN_ENB
                               | USBHS_DEVDMACONTROL_BUFF_LENGTH(dLength)
                               | USBHS_DEVDMACONTROL_END_B_EN
                               | USBHS_DEVDMACONTROL_END_BUFFIT;
            }
            else {
                pDmaLL[1].pNxtDesc = (void*)&pDmaLL[2];
                pDmaLL[1].pAddr    = (void*)pU8;
                pDmaLL[1].dwCtrl   =  USBHS_DEVDMACONTROL_CHANN_ENB
                               | USBHS_DEVDMACONTROL_BUFF_LENGTH(pktLen)
                               | USBHS_DEVDMACONTROL_END_B_EN
                               | USBHS_DEVDMACONTROL_LDNXT_DSC;
                
                dLength -= pktLen; ndxData += pktLen;
                /* LD3: data  - bank 1 */
                pktLen = pEp->size;
                if (pktLen >= dLength) { /* It's the last */
                    pDmaLL[1].pNxtDesc = (void*) NULL;
                    pDmaLL[1].pAddr    = (void*)&pU8[ndxData];
                    pDmaLL[1].dwCtrl   = USBHS_DEVDMACONTROL_CHANN_ENB
                                       | USBHS_DEVDMACONTROL_BUFF_LENGTH(dLength)
                                       | USBHS_DEVDMACONTROL_END_B_EN
                                       | USBHS_DEVDMACONTROL_END_BUFFIT;
                }
                else {
                    pDmaLL[2].pNxtDesc = (void*)&pDmaLL[3];
                    pDmaLL[2].pAddr    = (void*)&pU8[ndxData];
                    pDmaLL[2].dwCtrl   = USBHS_DEVDMACONTROL_CHANN_ENB
                                       | USBHS_DEVDMACONTROL_BUFF_LENGTH(pktLen)
                                       | USBHS_DEVDMACONTROL_END_B_EN
                                       | USBHS_DEVDMACONTROL_LDNXT_DSC;
                    dLength -= pktLen; ndxData += pktLen;
                    /* LD4: data  - bank 2 */
                    pDmaLL[3].pNxtDesc = (void*) NULL;
                    pDmaLL[3].pAddr    = (void*)&pU8[ndxData];
                    pDmaLL[3].dwCtrl   = USBHS_DEVDMACONTROL_CHANN_ENB
                                       | USBHS_DEVDMACONTROL_BUFF_LENGTH(dLength)
                                       | USBHS_DEVDMACONTROL_END_B_EN
                                       | USBHS_DEVDMACONTROL_END_BUFFIT;
                }
            }
          #endif
        }
        else { /* Normal, fill all data */
            /* LD2: data   -  load to fifo with interrupt */
            dLength = pXfr->buffered - bHdrLen;
            pDmaLL[1].pNxtDesc = (void*)NULL;
            pDmaLL[1].pAddr    = (void*)pData;
            pDmaLL[1].dwCtrl   = USBHS_DEVDMACONTROL_CHANN_ENB
                               | USBHS_DEVDMACONTROL_BUFF_LENGTH(dLength)
                               | USBHS_DEVDMACONTROL_END_B_EN
                               | USBHS_DEVDMACONTROL_END_BUFFIT;
        }
        /* Interrupt enable */
        pUdp->USBHS_DEVIER |= (USBHS_DEVIMR_DMA_1 << bDmaEndpoint);
        /* Start transfer with LLI */
        pUdp->USBHS_DEVDMA[bDmaEndpoint].USBHS_DEVDMANXTDSC  = (uint32_t)pDmaLL;
        pUdp->USBHS_DEVDMA[bDmaEndpoint].USBHS_DEVDMACONTROL = 0;
        pUdp->USBHS_DEVDMA[bDmaEndpoint].USBHS_DEVDMACONTROL = USBHS_DEVDMACONTROL_LDNXT_DSC;
        return USBD_STATUS_SUCCESS;
    }
#endif
    
    /* Enable IT */
    USBHS_EnableIntEP( pUdp, bEndpoint );
    USBHS_EnableEPIntType(pUdp, bEndpoint, USBHS_DEVEPTIER_TXINES);
    return USBD_STATUS_SUCCESS;
}

/**
 * Reads incoming data on an USB endpoint This methods sets the transfer
 * descriptor and activate the endpoint interrupt. The actual transfer is
 * then carried out by the endpoint interrupt handler. The Read operation
 * finishes either when the buffer is full, or a short packet (inferior to
 * endpoint maximum  size) is received.
 *
 * *The buffer must be kept allocated until the transfer is finished*.
 * \param bEndpoint Endpoint number.
 * \param pData Pointer to a data buffer.
 * \param dLength Size of the data buffer in bytes.
 * \return USBD_STATUS_SUCCESS if the read operation has been started;
 *         otherwise, the corresponding error code.
 */
uint8_t USBD_HAL_Read(uint8_t    bEndpoint,
                      void       *pData,
                      uint32_t   dLength)
{
    if (endpoints[bEndpoint].transfer.transHdr.transType)
        return USBD_STATUS_SW_NOT_SUPPORTED;
    else
        return UDPHS_Read(bEndpoint, pData, dLength);
}

/**
 *  \brief Enable Pull-up, connect.
 *
 *  -# Enable HW access if needed
 *  -# Enable Pull-Up
 *  -# Disable HW access if needed
 */
void USBD_HAL_Connect(void)
{
    
    // At startup the USB bus state is unknown, 
    // therefore the state is considered IDLE to not miss any USB event
    
    USBHS_FreezeClock(USBHS, false);
    
    // Authorize attach
    USBHS_DetachUsb(USBHS, false);

    // (RESET_AND_WAKEUP)
    // After the attach and the first USB suspend, the following USB Reset time can be inferior to CPU restart clock time.
    // Thus, the USB Reset state is not detected and endpoint control is not allocated
    // In this case, a Reset is do automatically after attach.
    USBD_HAL_ConfigureEP(0);
    
    // Enable USB line events
    USBHS_EnableInt(USBHS,  (USBHS_DEVIER_EORSTES  | USBHS_DEVIER_WAKEUPES | USBHS_DEVIER_SUSPES | USBHS_DEVIER_SOFES) );
    
#ifdef USB_DEVICE_HS_SUPPORT
    USBHS_EnableInt(USBHS, USBHS_DEVIER_MSOFES);
#endif
    
    // Reset following interrupts flag
    USBHS_AckInt(USBHS, ( USBHS_DEVICR_EORSTC | USBHS_DEVICR_SOFC | USBHS_DEVICR_MSOFC ) );
    
   
     // The first suspend interrupt is not detected else raise it
    USBHS_RaiseInt(USBHS, USBHS_DEVIFR_SUSPS);
   
    USBHS_AckInt(USBHS, USBHS_DEVICR_WAKEUPC);
    
    USBHS_FreezeClock(USBHS, true);
}

/**
 *  \brief Disable Pull-up, disconnect.
 *
 *  -# Enable HW access if needed
 *  -# Disable PULL-Up
 *  -# Disable HW access if needed
 */
void USBD_HAL_Disconnect(void)
{
    USBHS_FreezeClock(USBHS, ENABLE);
    // Detach device from the bus
    USBHS_DetachUsb(USBHS, true);
}

/**
 * Starts a remote wake-up procedure.
 */
void USBD_HAL_RemoteWakeUp(void)
{
    Usbhs *pUdp = USBHS;

    TRACE_INFO_WP("RWUp ");

    /* Activates a remote wakeup (edge on ESR), then clear ESR */
    USBHS_SetRemoteWakeUp(pUdp);
    while(pUdp->USBHS_DEVCTRL & USBHS_DEVCTRL_RMWKUP);
    {
        TRACE_DEBUG_WP("w");
    }
}

/**
 * Sets the device address to the given value.
 * \param address New device address.
 */
void USBD_HAL_SetAddress(uint8_t address)
{
    Usbhs *pUdp = USBHS;

    if (address)
    {
        USBHS_SetAddress(pUdp, address);
    }
    else
    {
        USBHS_EnableAddress(pUdp, false);
    }
}

/**
 * Sets the current device configuration.
 * \param cfgnum - Configuration number to set.
 */
void USBD_HAL_SetConfiguration(uint8_t cfgnum)
{
    /* Nothing to do now */
    cfgnum = cfgnum;
}

/**
 * Initializes the USB HW Access driver.
 */
void USBD_HAL_Init(void)
{
  
#ifdef DMA
    /* DMA Link list should be 16-bytes aligned */
    if ((uint32_t)dmaLL & 0xFFFFFFF0)
        pDmaLL = (UdphsDmaDescriptor*)((uint32_t)&dmaLL[1] & 0xFFFFFFF0);
    else
        pDmaLL = (UdphsDmaDescriptor*)((uint32_t)&dmaLL[0]);
#endif
/** Disable USB hardware */
    USBHS_UsbEnable(USBHS, false);
    
    USBHS_UsbMode(USBHS, DEVICE_MODE);
    
    /** Enable USB hardware*/
    USBHS_UsbEnable(USBHS, true);
    
    USBHS_FreezeClock(USBHS, false);

    if(ForceFS)
    {
         USBHS_EnableHighSpeed(USBHS, false);
    }
    else
    {
         USBHS_EnableHighSpeed(USBHS, true);
    }
        /*  Check USB clock */
    while( !USBHS_ISUsableClock(USBHS) );
    
    USBHS_FreezeClock(USBHS, true);
    
    /* Clear IRQ */
    NVIC_ClearPendingIRQ(USBHS_IRQn);
    /* IRQ */
    NVIC_EnableIRQ(USBHS_IRQn) ;
    
}

/**
 * Causes the given endpoint to acknowledge the next packet it receives
 * with a STALL handshake except setup request.
 * \param bEP Endpoint number.
 * \return USBD_STATUS_SUCCESS or USBD_STATUS_LOCKED.
 */
uint8_t USBD_HAL_Stall(uint8_t bEP)
{
    Usbhs    *pUdp = USBHS;

    Endpoint *pEndpoint = &(endpoints[bEP]);

    /* Check that endpoint is in Idle state */
    if (pEndpoint->state != UDPHS_ENDPOINT_IDLE)
    {
        TRACE_WARNING("UDP_Stall: EP%d locked\n\r", bEP);
        return USBD_STATUS_LOCKED;
    }
    /* STALL endpoint */
    USBHS_EnableEPIntType(pUdp, bEP, USBHS_DEVEPTIER_STALLRQS);

    TRACE_INFO_WP("Stall%d ", bEP);
    return USBD_STATUS_SUCCESS;
}

/**
 * Sets/Clear/Get the HALT state on the endpoint.
 * In HALT state, the endpoint should keep stalling any packet.
 * \param bEndpoint Endpoint number.
 * \param ctl       Control code CLR/HALT/READ.
 *                  0: Clear HALT state;
 *                  1: Set HALT state;
 *                  .: Return HALT status.
 * \return USBD_STATUS_INVALID_PARAMETER if endpoint not exist,
 *         otherwise endpoint halt status.
 */
uint8_t USBD_HAL_Halt(uint8_t bEndpoint, uint8_t ctl)
{
    Usbhs    *pUdp = USBHS;

    Endpoint *pEndpoint = &(endpoints[bEndpoint]);
    uint8_t bDmaEndpoint = (bEndpoint-1);
    uint8_t status = 0;
    /* SET Halt */
    if (ctl == 1)
    {      
        /* Check that endpoint is enabled and not already in Halt state */
        if ((pEndpoint->state != UDPHS_ENDPOINT_DISABLED)
            && (pEndpoint->state != UDPHS_ENDPOINT_HALTED))
        {

             TRACE_INFO_WP("Halt%d ", bEndpoint);
           
             /* Abort the current transfer if necessary */
             UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_ABORTED);
            
             /* Put endpoint into Halt state */
             pEndpoint->state = UDPHS_ENDPOINT_HALTED;
             memory_sync();
             //SCB_CleanInvalidateDCache();
             
             while(!USBHS_IsBankFree(pUdp, bEndpoint))
             {
               USBHS_KillBank(pUdp, bEndpoint);
               while(USBHS_IsBankKilled(pUdp, bEndpoint));
             }
             
             if(USBHS_IsBankFree(pUdp, bEndpoint))
             {
               USBHS_AutoSwitchBankEnable(pUdp, bEndpoint, false);
               USBHS_EnableEPIntType(pUdp, bEndpoint, (USBHS_DEVEPTIER_STALLRQS | USBHS_DEVEPTIER_RSTDTS) );               
             }
             else
             {              
               USBHS_EnableEPIntType(pUdp, bEndpoint, USBHS_DEVEPTIER_NBUSYBKES );               
#ifdef DMA
               if (CHIP_USB_ENDPOINTS_DMA(bDmaEndpoint))
               {
                   /* Enable the endpoint DMA interrupt */
                   USBHS_EnableDMAIntEP(pUdp, bDmaEndpoint);
               }
               else
               {
                   /* Enable the endpoint interrupt */
                   USBHS_EnableIntEP( pUdp, bEndpoint );
               }
#else
               /* Enable the endpoint interrupt */
               USBHS_EnableIntEP( pUdp, bEndpoint );
#endif
             }
        }

    }
    /* CLEAR Halt */
    else if (ctl == 0)
    {
         /* Check if the endpoint is halted */
         if ((pEndpoint->state == UDPHS_ENDPOINT_HALTED)  || (USBHS_IsEpIntEnable(pUdp, bEndpoint, USBHS_DEVEPTIMR_STALLRQ)) )
         {

             TRACE_INFO_WP("Unhalt%d ", bEndpoint);
             /* Return endpoint to Idle state */
             pEndpoint->state = UDPHS_ENDPOINT_IDLE;

             /* Clear FORCESTALL flag */
             USBHS_DisableEPIntType(pUdp, bEndpoint, USBHS_DEVEPTIDR_STALLRQC);
             USBHS_AutoSwitchBankEnable(pUdp, bEndpoint, true);
         }
    }

    /* Return Halt status */
    if (pEndpoint->state == UDPHS_ENDPOINT_HALTED)
    {
         status = 1;
    }
    return( status );
}

/**
 * Indicates if the device is running in high or full-speed. Always returns 0
 * since UDP does not support high-speed mode.
 */
uint8_t USBD_HAL_IsHighSpeed(void)
{
    Usbhs    *pUdp = USBHS; 
    uint32_t tmp = USBHS_GetUsbSpeed(pUdp);
    return ((tmp & USBHS_SR_SPEED_HIGH_SPEED) >> USBHS_SR_SPEED_Pos) ;
}

/**
 * Suspend USB Device HW Interface
 *
 * -# Disable transceiver
 * -# Disable USB Clock
 * -# Disable USB Peripheral
 */
void USBD_HAL_Suspend(void)
{
    /* The device enters the Suspended state */
    USBHS_FreezeClock(USBHS, ENABLE);
}

/**
 * Activate USB Device HW Interface
 * -# Enable USB Peripheral
 * -# Enable USB Clock
 * -# Enable transceiver
 */
void USBD_HAL_Activate(void)
{
    USBHS_FreezeClock(USBHS, DISABLE);
}

void USBD_HAL_Disable(void)
{
    //** Disable USB hardware
    USBHS_UsbEnable(USBHS, false);
       
    /* Clear IRQ */
    NVIC_ClearPendingIRQ(USBHS_IRQn);
    /* IRQ */
    NVIC_DisableIRQ(USBHS_IRQn) ;
}


/**
 * Certification test for High Speed device.
 * \param bIndex Test to be done
 */
void USBD_HAL_Test( uint8_t bIndex )
{
    Usbhs *pUdp = USBHS;
    uint8_t      *pFifo;
    uint32_t      i;

    /* remove suspend for TEST */
    USBHS_DisableInt(pUdp, USBHS_DEVIDR_SUSPEC);
    /* force High Speed (remove suspend) */
    pUdp->USBHS_DEVCTRL |= USBHS_DEVCTRL_SPDCONF_HIGH_SPEED;
    
    USBHS_EnableTestMode(pUdp, USBHS_DEVCTRL_OPMODE2);

    switch( bIndex ) {

        case USBFeatureRequest_TESTPACKET:
            TRACE_DEBUG_WP("TEST_PACKET ");

            pUdp->USBHS_DEVDMA[1].USBHS_DEVDMACONTROL = 0;
            pUdp->USBHS_DEVDMA[2].USBHS_DEVDMACONTROL = 0;

            /* Configure endpoint 2, 64 bytes, direction IN, type BULK, 1 bank */
            pUdp->USBHS_DEVEPTCFG[2]= USBHS_DEVEPTCFG_EPSIZE_64_BYTE
                                            | USBHS_DEVEPTCFG_EPDIR
                                            | USBHS_DEVEPTCFG_EPTYPE_BLK
                                            | USBHS_DEVEPTCFG_EPBK_1_BANK;
            USBHS_AllocateMemory(pUdp, 2);
            while( (USBHS_DEVEPTISR_CFGOK & pUdp->USBHS_DEVEPTISR[2]) != USBHS_DEVEPTISR_CFGOK);
            USBHS_EnableEP(pUdp, 2, true);

            /* Write FIFO */
            pFifo = (uint8_t*)((uint32_t *)(USBHS_RAM_ADDR) + (EPT_VIRTUAL_SIZE * 2));
            for( i=0; i<sizeof(test_packet_buffer); i++) {
                pFifo[i] = test_packet_buffer[i];
            }
            /* Tst PACKET */
            USBHS_EnableTestMode(pUdp, USBHS_DEVCTRL_TSTPCKT);
            /* Send packet */
            USBHS_RaiseEPInt(pUdp, 2, USBHS_DEVEPTIFR_TXINIS);
            break;

        case USBFeatureRequest_TESTJ:
            TRACE_DEBUG_WP("TEST_J ");
            USBHS_EnableTestMode(pUdp, USBHS_DEVCTRL_TSTJ);
            break;

        case USBFeatureRequest_TESTK:
            TRACE_DEBUG_WP("TEST_K ");
            USBHS_EnableTestMode(pUdp, USBHS_DEVCTRL_TSTK);
            break;

        case USBFeatureRequest_TESTSE0NAK:
            TRACE_DEBUG_WP("TEST_SEO_NAK ");
            USBHS_DisableInt(pUdp, 0xFFFFFFFF);  // for test
            break;

        case USBFeatureRequest_TESTSENDZLP:
            USBHS_RaiseEPInt(pUdp, 0, USBHS_DEVEPTIFR_TXINIS);
            TRACE_DEBUG_WP("SEND_ZLP ");
            break;
    }
    TRACE_DEBUG_WP("\n\r");
}



/**@}*/

