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

/**

 \file

 \section Purpose

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
#define NUM_IT_MAX       \
    (UDPHS->UDPHS_IPFEATURES & UDPHS_IPFEATURES_EPT_NBR_MAX_Msk)
/** Maximum number of endpoint DMA interrupts */
#define NUM_IT_MAX_DMA   \
    ((UDPHS->UDPHS_IPFEATURES \
        & UDPHS_IPFEATURES_DMA_CHANNEL_NBR_Msk) \
      >>UDPHS_IPFEATURES_DMA_CHANNEL_NBR_Pos)
/** Bits that should be shifted to access DMA control bits. */
#define SHIFT_DMA        24
/** Bits that should be shifted to access interrupt bits. */
#define SHIFT_INTERUPT    8

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
    /**  Loast loaded buffer index (run time) */
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

/** Force FS mode */
static const uint8_t forceUsbFS = 0;

/** DMA link list */
static UdphsDmaDescriptor  dmaLL[5];
static UdphsDmaDescriptor *pDmaLL;

/*---------------------------------------------------------------------------
 *      Internal Functions
 *---------------------------------------------------------------------------*/

/**
 * Enables the clock of the UDP peripheral.
 * \return 1 if peripheral status changed.
 */
static uint8_t UDPHS_EnablePeripheralClock(void)
{
    if (!PMC_IsPeriphEnabled(ID_UDPHS)) {
        PMC_EnablePeripheral(ID_UDPHS);
        return 1;
    }
    return 0;
}

/**
 * Disables the UDP peripheral clock.
 */
static inline void UDPHS_DisablePeripheralClock(void)
{
    PMC_DisablePeripheral(ID_UDPHS);
}

/**
 * Enables the 480MHz USB clock.
 */
static inline void UDPHS_EnableUsbClock(void)
{
    Pmc *pPmc = PMC;
    /* Enable 480Mhz UPLL */
    pPmc->CKGR_UCKR |= CKGR_UCKR_UPLLEN
                       | CKGR_UCKR_UPLLCOUNT(0x3)
                       | CKGR_UCKR_BIASCOUNT(0x1);
    /* Wait until UPLL is locked */
    while((pPmc->PMC_SR & PMC_SR_LOCKU) == 0);
}

/**
 *  Disables the 480MHz USB clock.
 */
static inline void UDPHS_DisableUsbClock(void)
{
    Pmc *pPmc = PMC;
    pPmc->CKGR_UCKR &= ~(uint32_t)CKGR_UCKR_UPLLEN;
}

/**
 * Enables the BIAS.
 */
static inline void UDPHS_EnableBIAS(void)
{
    Pmc *pPmc = PMC;
    pPmc->CKGR_UCKR |= CKGR_UCKR_BIASEN;
}

/**
 * Disables the BIAS.
 */
static inline void UDPHS_DisableBIAS(void)
{
    Pmc *pPmc = PMC;
    pPmc->CKGR_UCKR &= ~(uint32_t)CKGR_UCKR_BIASEN;
}

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
 * Transfers a data payload from the current tranfer buffer to the endpoint
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
    pFifo = (uint8_t*)((uint32_t*)UDPHS_RAM_ADDR
                                    + (EPT_VIRTUAL_SIZE * bEndpoint));
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
 * Transfers a data payload from the current tranfer buffer to the endpoint
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
    pFifo = (uint8_t*)((uint32_t*)UDPHS_RAM_ADDR
                                    + (EPT_VIRTUAL_SIZE * bEndpoint));
    for (; size; size --)
    {
        *(pFifo ++) = *(pTransfer->pData ++);
    }
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
    pFifo = (uint8_t*)((uint32_t*)UDPHS_RAM_ADDR
                                    + (EPT_VIRTUAL_SIZE * bEndpoint));
    while (wPacketSize > 0)
    {
        *(pTransfer->pData ++) = *(pFifo ++);
        wPacketSize--;
    }
}

/**
 * Received SETUP packet from endpoint 0 FIFO
 * \param pRequest Generic USB SETUP request sent over Control endpoints
 */
static void UDPHS_ReadRequest(USBGenericRequest *pRequest)
{
    uint32_t *pData = (uint32_t *)pRequest;
    volatile uint32_t *pFifo;
    pFifo = (volatile uint32_t*)UDPHS_RAM_ADDR;
    *pData ++ = *pFifo;
    pFifo = (volatile uint32_t*)UDPHS_RAM_ADDR;
    *pData    = *pFifo;
    //printf("REQ: %08x %08x\n\r", pData[0], pData[1]);
}

/**
 * Endpoint interrupt handler.
 * Handle IN/OUT transfers, received SETUP packets and STALLing
 * \param bEndpoint Index of endpoint
 */
static void UDPHS_EndpointHandler(uint8_t bEndpoint)
{
    Udphs    *pUdp = UDPHS;
    UdphsEpt *pEpt = &pUdp->UDPHS_EPT[bEndpoint];
    //UdphsDma *pDma = &pUdp->UDPHS_DMA[bEndpoint];

    Endpoint *pEp      = &(endpoints[bEndpoint]);
    Transfer *pXfr     = (Transfer*)&(pEp->transfer);
    //MblTransfer *pMblt = (MblTransfer*)&(pEp->transfer);
    uint32_t status = pEpt->UDPHS_EPTSTA;
    uint32_t type   = pEpt->UDPHS_EPTCFG & UDPHS_EPTCFG_EPT_TYPE_Msk;
    uint32_t reqBuf[2];
    USBGenericRequest *pReq = (USBGenericRequest *)reqBuf;
    uint16_t wPktSize;

    TRACE_DEBUG_WP("Ep%d ", bEndpoint);
    //TRACE_DEBUG_WP("St:%x ", status);

    /* IN packet sent */
    if (   (pEpt->UDPHS_EPTCTL & UDPHS_EPTCTL_TX_PK_RDY)
        && (0 == (status & UDPHS_EPTSTA_TX_PK_RDY)) )
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
            if (   pXfr->buffered == 0
                && pXfr->transferred == 0
                && pXfr->remaining == 0
                && pEp->sendZLP == 0 )
            {
                pEp->sendZLP = 1;
            }

            /* End of Xfr ? */
            if (   pXfr->remaining
                || pEp->sendZLP == 1)
            {
                pEp->sendZLP = 2;

                /* Transfer remaining */
                TRACE_DEBUG_WP("%d ", pEp->size);
                /* Send next packet */
                UDPHS_WritePayload(bEndpoint, pEp->size);
                pEpt->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_TX_PK_RDY;
            }
            else
            {
                TRACE_DEBUG_WP("l%d ", pXfr->transferred);
                /* Disable interrupt on none-control EP */
                if (type != UDPHS_EPTCFG_EPT_TYPE_CTRL8)
                {
                    pUdp->UDPHS_IEN &= ~(UDPHS_IEN_EPT_0 << bEndpoint);
                }
                pEpt->UDPHS_EPTCTLDIS = UDPHS_EPTCTLDIS_TX_PK_RDY;

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
    if ( UDPHS_EPTSTA_RX_BK_RDY & status )
    {
        TRACE_DEBUG_WP("Rd ");

        /* NOT in receiving state */
        if (pEp->state != UDPHS_ENDPOINT_RECEIVING)
        {
            /* Check if ACK received on a Control EP */
            if (   (UDPHS_EPTCFG_EPT_TYPE_CTRL8 == type)
                && (0 == (status & UDPHS_EPTSTA_BYTE_COUNT_Msk)) )
            {
                TRACE_DEBUG_WP("Ack ");
                pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_RX_BK_RDY;
                UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_SUCCESS);
            }
            /* data has been STALLed */
            else if (UDPHS_EPTSTA_FRCESTALL & status)
            {
                TRACE_DEBUG_WP("Discard ");
                pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_RX_BK_RDY;
            }
            /* NAK the data */
            else
            {
                TRACE_DEBUG_WP("Nak ");
                pUdp->UDPHS_IEN &= ~(UDPHS_IEN_EPT_0 << bEndpoint);
            }
        }
        /* In read state */
        else
        {
            wPktSize = (uint16_t)((status & UDPHS_EPTSTA_BYTE_COUNT_Msk) >> UDPHS_EPTSTA_BYTE_COUNT_Pos);

            TRACE_DEBUG_WP("%d ", wPktSize);
            UDPHS_ReadPayload(bEndpoint, wPktSize);
            pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_RX_BK_RDY;
            /* Check if transfer is finished */
            if (pXfr->remaining == 0 || wPktSize < pEp->size)
            {
                pEpt->UDPHS_EPTCTLDIS = UDPHS_EPTCTLDIS_RX_BK_RDY;

                /* Disable interrupt if not control EP */
                if (UDPHS_EPTCFG_EPT_TYPE_CTRL8 != type)
                {
                    pUdp->UDPHS_IEN &= ~(UDPHS_IEN_EPT_0 << bEndpoint);
                }
                UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_SUCCESS);
            }
        }
    }
    /* STALL sent */
    if ( UDPHS_EPTSTA_STALL_SNT & status )
    {
        /* Acknowledge */
        pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_STALL_SNT;

        /* ISO error */
        if (type == UDPHS_EPTCFG_EPT_TYPE_ISO)
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
                pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_FRCESTALL;
            }
        }
    }
    /* SETUP packet received */
    if ( UDPHS_EPTSTA_RX_SETUP & status )
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
        if (type == UDPHS_EPTCFG_EPT_TYPE_ISO)
        {
            TRACE_WARNING("IsoFE[%d]\n\r", bEndpoint);
            /* Acknowledge setup packet */
            pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_RX_SETUP;
        }
        else
        {
            TRACE_DEBUG_WP("Stup ");
            
            /* Copy setup */
            UDPHS_ReadRequest(pReq);
            /* Acknowledge setup packet */
            pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_RX_SETUP;
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
    Udphs *pUdp = UDPHS;

    /* Single transfer */
    pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMAADDRESS =
                (uint32_t)&pXfr->pData[pXfr->transferred];
    pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMASTATUS;
    /* Interrupt enable */
    pUdp->UDPHS_IEN |= (1 << SHIFT_DMA << bEndpoint);
    
    TRACE_DEBUG_WP("Dma[B%d:T%d] ", pXfr->buffered, pXfr->transferred);
    /* DMA Configure */
    pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMACONTROL = 0;
    pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMACONTROL = 0
                            | UDPHS_DMACONTROL_BUFF_LENGTH(pXfr->buffered)
                            | dwCfg;
}
/**
 * Endpoint DMA interrupt handler.
 * This function handles DMA interrupts.
 * \param bEndpoint Index of endpoint
 */
static void UDPHS_DmaHandler(uint8_t bEndpoint)
{
    Udphs    *pUdp  = UDPHS;
    //UdphsEpt *pHwEp = &pUdp->UDPHS_EPT[bEndpoint];

    Endpoint *pEp  = &(endpoints[bEndpoint]);
    Transfer *pXfr = (Transfer*)&(pEp->transfer);

    uint32_t dwDmaSr;
    int32_t iRemain, iXfred;
    uint8_t bRc = USBD_STATUS_SUCCESS;

    dwDmaSr = pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMASTATUS;
    TRACE_DEBUG_WP("iDma%d,%x ", bEndpoint, dwDmaSr);
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
    pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMACONTROL &= ~(UDPHS_DMACONTROL_END_TR_EN
                                                    |UDPHS_DMACONTROL_END_B_EN);
    if (UDPHS_DMASTATUS_END_BF_ST & dwDmaSr)
    {
        TRACE_DEBUG_WP("EoDmaB ");
        /* BUFF_COUNT holds the number of untransmitted bytes.
           BUFF_COUNT is equal to zero in case of good transfer */
        iRemain = (dwDmaSr & UDPHS_DMASTATUS_BUFF_COUNT_Msk)
                        >> UDPHS_DMASTATUS_BUFF_COUNT_Pos;

        TRACE_DEBUG_WP("C%d ", iRemain);
        iXfred  = pXfr->buffered - iRemain;

        pXfr->transferred += iXfred;
        pXfr->buffered     = iRemain;
        pXfr->remaining   -= iXfred;

        TRACE_DEBUG_WP("[B%d:T%d:R%d] ",
            pXfr->buffered, pXfr->transferred, pXfr->remaining);

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
            UDPHS_DmaSingle(bEndpoint, pXfr, UDPHS_DMACONTROL_END_TR_EN
                                             | UDPHS_DMACONTROL_END_TR_IT
                                             | UDPHS_DMACONTROL_END_B_EN
                                             | UDPHS_DMACONTROL_END_BUFFIT
                                             | UDPHS_DMACONTROL_CHANN_ENB);
        }
    }
    else if (UDPHS_DMASTATUS_END_TR_ST & dwDmaSr)
    {
        TRACE_DEBUG_WP("EoDmaT ");
        pXfr->transferred = pXfr->buffered -
            ((dwDmaSr & UDPHS_DMASTATUS_BUFF_COUNT_Msk)
                    >> UDPHS_DMASTATUS_BUFF_COUNT_Pos);
        pXfr->remaining = 0;

        TRACE_DEBUG_WP("[B%d:T%d] ", pXfr->buffered, pXfr->transferred);
    }
    else
    {
        TRACE_ERROR("UDPHS_DmaHandler: ST 0x%X\n\r", dwDmaSr);
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
    Udphs    *pUdp  = UDPHS;
    UdphsEpt *pHwEp = &pUdp->UDPHS_EPT[bEndpoint];

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
        UDPHS_DmaSingle(bEndpoint, pXfr, UDPHS_DMACONTROL_END_B_EN
                                         | UDPHS_DMACONTROL_END_BUFFIT
                                         | UDPHS_DMACONTROL_CHANN_ENB);
        return USBD_STATUS_SUCCESS;
    }
  #endif

    /* Enable IT */
    pUdp->UDPHS_IEN |= ( UDPHS_IEN_EPT_0 << bEndpoint );
    pHwEp->UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_TX_PK_RDY;
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
    Udphs    *pUdp  = UDPHS;
    UdphsEpt *pHwEp = &pUdp->UDPHS_EPT[bEndpoint];

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
            pHwEp->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_TX_PK_RDY;
        }

        /* Enable interrupt */
        pUdp->UDPHS_IEN |= (UDPHS_IEN_EPT_0 << bEndpoint);
        pHwEp->UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_TX_PK_RDY;

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
    Udphs    *pUdp  = UDPHS;
    UdphsEpt *pHwEp = &pUdp->UDPHS_EPT[bEndpoint];

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
        UDPHS_DmaSingle(bEndpoint, pXfr, UDPHS_DMACONTROL_END_TR_EN
                                         | UDPHS_DMACONTROL_END_TR_IT
                                         | UDPHS_DMACONTROL_END_B_EN
                                         | UDPHS_DMACONTROL_END_BUFFIT
                                         | UDPHS_DMACONTROL_CHANN_ENB);
        return USBD_STATUS_SUCCESS;
    }
  #endif

    /* Enable IT */
    pUdp->UDPHS_IEN |= ( UDPHS_IEN_EPT_0 << bEndpoint );
    pHwEp->UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_RX_BK_RDY;
    
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
extern void USBD_IrqHandler(void);
/**
 * USBD (UDP) interrupt handler
 * Manages device resume, suspend, end of bus reset.
 * Forwards endpoint events to the appropriate handler.
 */
void USBD_IrqHandler(void)
{
    Udphs *pUdp = UDPHS;

    uint32_t status;
    uint8_t  numIt;

    status  = pUdp->UDPHS_INTSTA;
    status &= pUdp->UDPHS_IEN;

    /* Handle all UDPHS interrupts */
    TRACE_DEBUG_WP("\n\r%c ", USBD_HAL_IsHighSpeed() ? 'H' : 'F');
    while( status )
    {
        /* SOF */
        if (status & UDPHS_INTSTA_INT_SOF)
        {
            TRACE_DEBUG_WP("SOF ");
            /* SOF handler */
            //USBD_SofHandler();

            /* Acknowledge interrupt */
            pUdp->UDPHS_CLRINT = UDPHS_CLRINT_INT_SOF;
            status &= ~(uint32_t)UDPHS_INTSTA_INT_SOF;
        }
        /* Suspend, treated last */
        else if (status == UDPHS_INTSTA_DET_SUSPD)
        {
            TRACE_WARNING_WP("Susp ");

            /* Enable wakeup */
            pUdp->UDPHS_IEN |= (UDPHS_IEN_WAKE_UP | UDPHS_IEN_ENDOFRSM);
            pUdp->UDPHS_IEN &= ~(uint32_t)UDPHS_IEN_DET_SUSPD;

            /* Acknowledge interrupt */
            pUdp->UDPHS_CLRINT = UDPHS_CLRINT_DET_SUSPD | UDPHS_CLRINT_WAKE_UP;

            USBD_SuspendHandler();
        }
        /* Resume */
        else if ( (status & UDPHS_INTSTA_WAKE_UP)
               || (status & UDPHS_INTSTA_ENDOFRSM) )
        {
            USBD_ResumeHandler();

            TRACE_INFO_WP("Rsm ");

            /* Acknowledge interrupt */
            pUdp->UDPHS_CLRINT = UDPHS_CLRINT_WAKE_UP
                               | UDPHS_CLRINT_ENDOFRSM
                               | UDPHS_CLRINT_DET_SUSPD;

            pUdp->UDPHS_IEN |= UDPHS_IEN_ENDOFRSM | UDPHS_IEN_DET_SUSPD;
            pUdp->UDPHS_CLRINT = UDPHS_CLRINT_WAKE_UP | UDPHS_CLRINT_ENDOFRSM;
            pUdp->UDPHS_IEN &= ~(uint32_t)UDPHS_IEN_WAKE_UP;
        }
        /* Bus reset */
        else if (status & UDPHS_INTSTA_ENDRESET)
        {
            TRACE_DEBUG_WP("EoB ");

            /* Flush and enable the suspend interrupt */
            pUdp->UDPHS_CLRINT = UDPHS_CLRINT_WAKE_UP | UDPHS_CLRINT_DET_SUSPD;
            pUdp->UDPHS_IEN |= UDPHS_IEN_DET_SUSPD;

            /* Reset handler */
            USBD_ResetHandler();

            /* Acknowledge interrupt */
            pUdp->UDPHS_CLRINT = UDPHS_CLRINT_ENDRESET;
        }
        /* Upstream resume */
        else if (status & UDPHS_INTSTA_UPSTR_RES)
        {
            TRACE_DEBUG_WP("ExtRes ");
            
            /* Acknowledge interrupt */
            pUdp->UDPHS_CLRINT = UDPHS_CLRINT_UPSTR_RES;
        }
        /* Endpoints */
        else
        {
          #ifdef DMA
            for (numIt = 0; numIt < NUM_IT_MAX; numIt ++)
            {
                if (status & (1 << SHIFT_DMA << numIt))
                {
                    UDPHS_DmaHandler(numIt);
                }
                else if (status & (UDPHS_INTSTA_EPT_0 << numIt))
                {
                    UDPHS_EndpointHandler(numIt);
                }
            }
          #else
            for (numIt = 0; numIt < NUM_IT_MAX; numIt ++)
            {
                if (status & (UDPHS_INTSTA_EPT_0 << numIt))
                {
                    UDPHS_EndpointHandler(numIt);
                }
            }
          #endif
        }

        /* Update interrupt status */
        status  = pUdp->UDPHS_INTSTA;
        status &= pUdp->UDPHS_IEN;

        TRACE_DEBUG_WP("\n\r");
        if (status)
        {
            TRACE_DEBUG_WP(" - ");
        }
    }
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
    Udphs *pUdp = UDPHS;
    UdphsEpt *pHwEp;

    Endpoint *pEndpoint;
    uint32_t tmp = bmEPs & ((1<<CHIP_USB_NUMENDPOINTS)-1);
    uint8_t  ep;
    uint32_t epBit, epCfg;

    for (ep = 0, epBit = 1; ep < CHIP_USB_NUMENDPOINTS; ep ++)
    {
        if (tmp & epBit)
        {
            pHwEp = &pUdp->UDPHS_EPT[ep];

            /* Disable ISR */
            pUdp->UDPHS_IEN &= ~(epBit << SHIFT_INTERUPT);
            /* Kill pending Banks ?? */
            #if 0
            pHwEp->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_KILL_BANK;
            pHwEp->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_KILL_BANK;
            pHwEp->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_KILL_BANK;
            #endif
            
            /* Reset transfer information */
            pEndpoint = &(endpoints[ep]);
            /* Reset endpoint state */
            pEndpoint->bank = 0;
            /* Endpoint configure */
            epCfg = pHwEp->UDPHS_EPTCFG;
            /* Reset endpoint */
            pUdp->UDPHS_EPTRST = epBit;
            /* Restore configure */
            if (bKeepCfg)
            {
                pHwEp->UDPHS_EPTCFG = epCfg;
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
    Udphs *pUdp = UDPHS;
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
            pUdp->UDPHS_IEN &= ~(epBit << SHIFT_INTERUPT);
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
    Udphs    *pUdp = UDPHS;
    UdphsEpt *pEpt;
    //UdphsDma *pDma;

    Endpoint *pEndpoint;
    uint8_t  bEndpoint;
    uint8_t  bType;
    uint8_t  bEndpointDir;
    //uint8_t bInterval = 0;
    uint8_t  bNbTrans  = 1;
    uint8_t  bSizeEpt  = 0;
    uint8_t  bHs = ((pUdp->UDPHS_INTSTA & UDPHS_INTSTA_SPEED) > 0);

    /* NULL descriptor -> Control endpoint 0 */
    if (pDescriptor == 0)
    {

        bEndpoint = 0;
        pEndpoint = &(endpoints[bEndpoint]);
        pEpt      = &(pUdp->UDPHS_EPT[0]);
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
        pEpt      = &(pUdp->UDPHS_EPT[0]);
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
        pEpt      = &(pUdp->UDPHS_EPT[bEndpoint]);
        /* Transfer type: Control, Isochronous, Bulk, Interrupt */
        bType = USBEndpointDescriptor_GetType(pDescriptor);
        /* interval */
        //bInterval = USBEndpointDescriptor_GetInterval(pDescriptor);
        /* Direction, ignored for control endpoints */
        bEndpointDir = USBEndpointDescriptor_GetDirection(pDescriptor);
        pEndpoint->size = USBEndpointDescriptor_GetMaxPacketSize(pDescriptor);
        pEndpoint->bank = CHIP_USB_ENDPOINTS_BANKS(bEndpoint);

        /* Convert descriptor value to EP configuration */
        if (bHs) {  /* HS Interval, *125us */

            /* MPS: Bit12,11 specify NB_TRANS, as USB 2.0 Spec. */
            bNbTrans = ((pEndpoint->size >> 11) & 0x3);
            if (bNbTrans == 3)
                bNbTrans = 1;
            else
                bNbTrans ++;

            /* Mask, bit 10..0 is the size */
            pEndpoint->size &= 0x7FF;
        }
    }

    //TRACE_DEBUG_WP("CfgE%d ", bEndpoint);

    /* Abort the current transfer is the endpoint was configured and in
       Write or Read state */
    if( (pEndpoint->state == UDPHS_ENDPOINT_RECEIVING)
     || (pEndpoint->state == UDPHS_ENDPOINT_SENDING)
     || (pEndpoint->state == UDPHS_ENDPOINT_RECEIVINGM)
     || (pEndpoint->state == UDPHS_ENDPOINT_SENDINGM) ) {

        UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_RESET);
    }
    pEndpoint->state = UDPHS_ENDPOINT_IDLE;

    /* Disable endpoint */
    pEpt->UDPHS_EPTCTLDIS = UDPHS_EPTCTLDIS_SHRT_PCKT
                          | UDPHS_EPTCTLDIS_BUSY_BANK
                          | UDPHS_EPTCTLDIS_NAK_OUT
                          | UDPHS_EPTCTLDIS_NAK_IN
                          | UDPHS_EPTCTLDIS_STALL_SNT
                          | UDPHS_EPTCTLDIS_RX_SETUP
                          | UDPHS_EPTCTLDIS_TX_PK_RDY
                          | UDPHS_EPTCTLDIS_RX_BK_RDY
                          | UDPHS_EPTCTLDIS_ERR_OVFLW
                          | UDPHS_EPTCTLDIS_MDATA_RX
                          | UDPHS_EPTCTLDIS_DATAX_RX
                          | UDPHS_EPTCTLDIS_NYET_DIS
                          | UDPHS_EPTCTLDIS_INTDIS_DMA
                          | UDPHS_EPTCTLDIS_AUTO_VALID
                          | UDPHS_EPTCTLDIS_EPT_DISABL
                          ;
    /* Reset Endpoint Fifos */
    pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_TOGGLESQ | UDPHS_EPTCLRSTA_FRCESTALL;
    pUdp->UDPHS_EPTRST = 1 << bEndpoint;
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
        pUdp->UDPHS_IEN |= (UDPHS_IEN_EPT_0 << bEndpoint);
    }

    pEpt->UDPHS_EPTCFG =    bSizeEpt 
                        | ( bEndpointDir << 3) 
                        | ( bType << 4) 
                        | ((pEndpoint->bank) << 6)
                        | ( bNbTrans << 8)
                        ;

    while( (UDPHS_EPTCFG_EPT_MAPD & pEpt->UDPHS_EPTCFG) == 0 ) {

        /* resolved by clearing the reset IT in good place */
        TRACE_ERROR("PB bEndpoint: 0x%X\n\r", bEndpoint);
        TRACE_ERROR("PB bSizeEpt: 0x%X\n\r", bSizeEpt);
        TRACE_ERROR("PB bEndpointDir: 0x%X\n\r", bEndpointDir);
        TRACE_ERROR("PB bType: 0x%X\n\r", bType);
        TRACE_ERROR("PB pEndpoint->bank: 0x%X\n\r", pEndpoint->bank);
        TRACE_ERROR("PB UDPHS_EPTCFG: 0x%X\n\r", pEpt->UDPHS_EPTCFG);
        for(;;);
    }

    if (bType == USBEndpointDescriptor_CONTROL)
    {
        pEpt->UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_RX_BK_RDY 
                              | UDPHS_EPTCTLENB_RX_SETUP
                              | UDPHS_EPTCTLENB_EPT_ENABL;
    }
    else
    {
#ifndef DMA
        pEpt->UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_EPT_ENABL;
#else
        pEpt->UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_AUTO_VALID | UDPHS_EPTCTLENB_EPT_ENABL;
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
    Udphs    *pUdp  = UDPHS;
    UdphsEpt *pHwEp = &pUdp->UDPHS_EPT[bEndpoint];
   
    Endpoint *pEp  = &(endpoints[bEndpoint]);
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
    //printf("Wr%d(%d+%d) ", bEndpoint, bHdrLen, dLength);

    pEp->sendZLP = 0;

    /* Setup transfer descriptor */
    pXfr->pData       = (void*) pData;
    pXfr->remaining   = bHdrLen + dLength;
    pXfr->buffered    = 0;
    pXfr->transferred = 0;

    /* 1. DMA supported always, 2. Not ZLP */
    if (bHdrLen + dLength > 0)
    {
        uint8_t bNbTrans = (pHwEp->UDPHS_EPTCFG & UDPHS_EPTCFG_NB_TRANS_Msk)
                                                  >> UDPHS_EPTCFG_NB_TRANS_Pos;
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
        pDmaLL[0].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                           | UDPHS_DMACONTROL_BUFF_LENGTH(bHdrLen)
                           | UDPHS_DMACONTROL_LDNXT_DSC;
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
            pDmaLL[1].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                               | UDPHS_DMACONTROL_BUFF_LENGTH(dLength)
                               | UDPHS_DMACONTROL_END_B_EN
                               | UDPHS_DMACONTROL_END_BUFFIT;
          #else
            uint32_t pktLen, ndxData = 0;
            /* LD2: data   -  bank 0 */
            pktLen = pEp->size - bHdrLen;
            if (pktLen >= dLength) { /* It's the last DMA LLI */
                pDmaLL[1].pNxtDesc = (void*)NULL;
                pDmaLL[1].pAddr    = (void*)pU8;
                pDmaLL[1].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                                   | UDPHS_DMACONTROL_BUFF_LENGTH(dLength)
                                   | UDPHS_DMACONTROL_END_B_EN
                                   | UDPHS_DMACONTROL_END_BUFFIT;
            }
            else {
                pDmaLL[1].pNxtDesc = (void*)&pDmaLL[2];
                pDmaLL[1].pAddr    = (void*)pU8;
                pDmaLL[1].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                                   | UDPHS_DMACONTROL_BUFF_LENGTH(pktLen)
                                   | UDPHS_DMACONTROL_END_B_EN
                                   | UDPHS_DMACONTROL_LDNXT_DSC;
                dLength -= pktLen; ndxData += pktLen;
                /* LD3: data  - bank 1 */
                pktLen = pEp->size;
                if (pktLen >= dLength) { /* It's the last */
                    pDmaLL[1].pNxtDesc = (void*) NULL;
                    pDmaLL[1].pAddr    = (void*)&pU8[ndxData];
                    pDmaLL[1].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                                       | UDPHS_DMACONTROL_BUFF_LENGTH(dLength)
                                       | UDPHS_DMACONTROL_END_B_EN
                                       | UDPHS_DMACONTROL_END_BUFFIT;
                }
                else {
                    pDmaLL[2].pNxtDesc = (void*)&pDmaLL[3];
                    pDmaLL[2].pAddr    = (void*)&pU8[ndxData];
                    pDmaLL[2].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                                       | UDPHS_DMACONTROL_BUFF_LENGTH(pktLen)
                                       | UDPHS_DMACONTROL_END_B_EN
                                       | UDPHS_DMACONTROL_LDNXT_DSC;
                    dLength -= pktLen; ndxData += pktLen;
                    /* LD4: data  - bank 2 */
                    pDmaLL[3].pNxtDesc = (void*) NULL;
                    pDmaLL[3].pAddr    = (void*)&pU8[ndxData];
                    pDmaLL[3].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                                       | UDPHS_DMACONTROL_BUFF_LENGTH(dLength)
                                       | UDPHS_DMACONTROL_END_B_EN
                                       | UDPHS_DMACONTROL_END_BUFFIT;
                }
            }
          #endif
        }
        else { /* Normal, fill all data */
            /* LD2: data   -  load to fifo with interrupt */
            dLength = pXfr->buffered - bHdrLen;
            pDmaLL[1].pNxtDesc = (void*)NULL;
            pDmaLL[1].pAddr    = (void*)pData;
            pDmaLL[1].dwCtrl   = UDPHS_DMACONTROL_CHANN_ENB
                               | UDPHS_DMACONTROL_BUFF_LENGTH(dLength)
                               | UDPHS_DMACONTROL_END_B_EN
                               | UDPHS_DMACONTROL_END_BUFFIT;
        }

        /* Interrupt enable */
        pUdp->UDPHS_IEN |= (1 << SHIFT_DMA << bEndpoint);
        /* Start transfer with LLI */
        pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMANXTDSC  = (uint32_t)pDmaLL;
        pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMACONTROL = 0;
        pUdp->UDPHS_DMA[bEndpoint].UDPHS_DMACONTROL = UDPHS_DMACONTROL_LDNXT_DSC;
        return USBD_STATUS_SUCCESS;
    }
#endif
    
    /* Enable IT */
    pUdp->UDPHS_IEN |= ( UDPHS_IEN_EPT_0 << bEndpoint );
    pHwEp->UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_TX_PK_RDY;
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
    Udphs *pUdp = UDPHS;

    uint8_t dis = UDPHS_EnablePeripheralClock();
    pUdp->UDPHS_CTRL |= UDPHS_CTRL_PULLD_DIS;
    pUdp->UDPHS_CTRL &= ~(uint32_t)UDPHS_CTRL_DETACH;
    if (dis) UDPHS_DisablePeripheralClock();
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
    Udphs *pUdp = UDPHS;

    uint8_t dis = UDPHS_EnablePeripheralClock();
    pUdp->UDPHS_CTRL |= UDPHS_CTRL_DETACH;
    pUdp->UDPHS_CTRL &= ~(uint32_t)UDPHS_CTRL_PULLD_DIS;
    if (dis) UDPHS_DisablePeripheralClock();
}

/**
 * Starts a remote wake-up procedure.
 */
void USBD_HAL_RemoteWakeUp(void)
{
    Udphs *pUdp = UDPHS;

    UDPHS_EnablePeripheralClock();
    UDPHS_EnableUsbClock();

    TRACE_INFO_WP("RWUp ");

    /* Activates a remote wakeup (edge on ESR), then clear ESR */
    pUdp->UDPHS_CTRL |= UDPHS_CTRL_REWAKEUP;
    while(pUdp->UDPHS_CTRL & UDPHS_CTRL_REWAKEUP)
    {
        TRACE_DEBUG_WP("w");
    }
    UDPHS_EnableBIAS();
}

/**
 * Sets the device address to the given value.
 * \param address New device address.
 */
void USBD_HAL_SetAddress(uint8_t address)
{
    Udphs *pUdp = UDPHS;

    if (address)
    {
        pUdp->UDPHS_CTRL &= ~(uint32_t)UDPHS_CTRL_DEV_ADDR_Msk;
        pUdp->UDPHS_CTRL |= address | UDPHS_CTRL_FADDR_EN;
    }
    else
    {
        pUdp->UDPHS_CTRL &= ~(uint32_t)UDPHS_CTRL_FADDR_EN;
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
    Udphs *pUdp = UDPHS;
    UdphsEpt *pEpt;
    UdphsDma *pDma;
    uint32_t i;
#ifdef DMA
    /* DMA Link list should be 16-bytes aligned */
    if ((uint32_t)dmaLL & 0xFFFFFFF0)
        pDmaLL = (UdphsDmaDescriptor*)((uint32_t)&dmaLL[1] & 0xFFFFFFF0);
    else
        pDmaLL = (UdphsDmaDescriptor*)((uint32_t)&dmaLL[0]);
#endif
    /* Must before USB & TXVC access! */
    UDPHS_EnablePeripheralClock();

    /* Reset & disable endpoints */
    USBD_HAL_ResetEPs(0xFFFFFFFF, USBD_STATUS_RESET, 0);

    /* Configure the pull-up on D+ and disconnect it */
    pUdp->UDPHS_CTRL |= UDPHS_CTRL_DETACH;
    pUdp->UDPHS_CTRL |= UDPHS_CTRL_PULLD_DIS;

    /* Reset IP */
    pUdp->UDPHS_CTRL &= ~(uint32_t)UDPHS_CTRL_EN_UDPHS;
    pUdp->UDPHS_CTRL |= UDPHS_CTRL_EN_UDPHS;

    /* (XCHQ[2010.1.21], IP recomendation, setup clock after reset IP) */
    UDPHS_EnableUsbClock();

    /* Initialize DMA */
    for (i = 1;
         i < ((pUdp->UDPHS_IPFEATURES & UDPHS_IPFEATURES_DMA_CHANNEL_NBR_Msk) >> 4);
         i ++)
    {
        pEpt = &pUdp->UDPHS_EPT[i];
        pDma = &pUdp->UDPHS_DMA[i];
        /* DMA stop */
        pDma->UDPHS_DMACONTROL = 0;
        /* Disable endpoint */
        pEpt->UDPHS_EPTCTLDIS = (uint32_t)UDPHS_EPTCTLDIS_SHRT_PCKT
                              | UDPHS_EPTCTLDIS_BUSY_BANK
                              | UDPHS_EPTCTLDIS_NAK_OUT
                              | UDPHS_EPTCTLDIS_NAK_IN
                              | UDPHS_EPTCTLDIS_STALL_SNT
                              | UDPHS_EPTCTLDIS_RX_SETUP
                              | UDPHS_EPTCTLDIS_TX_PK_RDY
                              | UDPHS_EPTCTLDIS_TX_COMPLT
                              | UDPHS_EPTCTLDIS_RX_BK_RDY
                              | UDPHS_EPTCTLDIS_ERR_OVFLW
                              | UDPHS_EPTCTLDIS_MDATA_RX
                              | UDPHS_EPTCTLDIS_DATAX_RX
                              | UDPHS_EPTCTLDIS_NYET_DIS
                              | UDPHS_EPTCTLDIS_INTDIS_DMA
                              | UDPHS_EPTCTLDIS_AUTO_VALID
                              | UDPHS_EPTCTLDIS_EPT_DISABL
                              ;
        /* Clear status endpoint */
        pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_TOGGLESQ
                              | UDPHS_EPTCLRSTA_FRCESTALL
                              | UDPHS_EPTCLRSTA_RX_BK_RDY
                              | UDPHS_EPTCLRSTA_TX_COMPLT
                              | UDPHS_EPTCLRSTA_RX_SETUP
                              | UDPHS_EPTCLRSTA_STALL_SNT
                              | UDPHS_EPTCLRSTA_NAK_IN
                              | UDPHS_EPTCLRSTA_NAK_OUT
                              ;
        /* Reset endpoint config */
        pEpt->UDPHS_EPTCTLENB = 0;
        /* Reset DMA channel (Buffer count and Control field) */
        pDma->UDPHS_DMACONTROL = UDPHS_DMACONTROL_LDNXT_DSC;
        /* Reset DMA channel */
        pDma->UDPHS_DMACONTROL = 0;
        /* Clear DMA channel status (read to clear) */
        pDma->UDPHS_DMASTATUS = pDma->UDPHS_DMASTATUS;
    }

    /* Force Full-Speed */
    pUdp->UDPHS_TST = forceUsbFS ? UDPHS_TST_SPEED_CFG_FULL_SPEED : 0;

    pUdp->UDPHS_IEN = 0;
    pUdp->UDPHS_CLRINT = UDPHS_CLRINT_UPSTR_RES
                       | UDPHS_CLRINT_ENDOFRSM
                       | UDPHS_CLRINT_WAKE_UP
                       | UDPHS_CLRINT_ENDRESET
                       | UDPHS_CLRINT_INT_SOF
                       | UDPHS_CLRINT_MICRO_SOF
                       | UDPHS_CLRINT_DET_SUSPD
                       ;

    /* Enable interrupts */
    pUdp->UDPHS_IEN = UDPHS_IEN_ENDOFRSM
                    | UDPHS_IEN_WAKE_UP
                    | UDPHS_IEN_DET_SUSPD;

    /* Disable USB clocks */
    UDPHS_DisableUsbClock();
}

/**
 * Causes the given endpoint to acknowledge the next packet it receives
 * with a STALL handshake except setup request.
 * \param bEP Endpoint number.
 * \return USBD_STATUS_SUCCESS or USBD_STATUS_LOCKED.
 */
uint8_t USBD_HAL_Stall(uint8_t bEP)
{
    Udphs    *pUdp = UDPHS;
    UdphsEpt *pEpt = &pUdp->UDPHS_EPT[bEP];

    Endpoint *pEndpoint = &(endpoints[bEP]);

    /* Check that endpoint is in Idle state */
    if (pEndpoint->state != UDPHS_ENDPOINT_IDLE)
    {
        TRACE_WARNING("UDP_Stall: EP%d locked\n\r", bEP);
        return USBD_STATUS_LOCKED;
    }
    /* STALL endpoint */
    pEpt->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_FRCESTALL;

    TRACE_DEBUG_WP("Stall%d ", bEP);
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
    Udphs    *pUdp = UDPHS;
    UdphsEpt *pEpt = &pUdp->UDPHS_EPT[bEndpoint];

    Endpoint *pEndpoint = &(endpoints[bEndpoint]);
    uint8_t status = 0;

    /* SET Halt */
    if (ctl == 1)
    {
        /* Check that endpoint is enabled and not already in Halt state */
        if ((pEndpoint->state != UDPHS_ENDPOINT_DISABLED)
            && (pEndpoint->state != UDPHS_ENDPOINT_HALTED))
        {

            TRACE_DEBUG_WP("Halt%d ", bEndpoint);

            /* Abort the current transfer if necessary */
            UDPHS_EndOfTransfer(bEndpoint, USBD_STATUS_ABORTED);

            /* Put endpoint into Halt state */
            pEndpoint->state = UDPHS_ENDPOINT_HALTED;
            pEpt->UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_FRCESTALL;

          #ifdef DMA
            if (CHIP_USB_ENDPOINTS_DMA(bEndpoint))
            {
                /* Enable the endpoint DMA interrupt */
                pUdp->UDPHS_IEN |= ( 1 << SHIFT_DMA << bEndpoint );
            }
            else
            {
                /* Enable the endpoint interrupt */
                pUdp->UDPHS_IEN |= ( UDPHS_IEN_EPT_0 << bEndpoint );
            }
          #else
            /* Enable the endpoint interrupt */
            pUdp->UDPHS_IEN |= ( UDPHS_IEN_EPT_0 << bEndpoint );
          #endif
        }
    }
    /* CLEAR Halt */
    else if (ctl == 0)
    {
        /* Check if the endpoint is halted */
        if (pEndpoint->state == UDPHS_ENDPOINT_HALTED)
        {

            TRACE_DEBUG_WP("Unhalt%d ", bEndpoint);

            /* Return endpoint to Idle state */
            pEndpoint->state = UDPHS_ENDPOINT_IDLE;

            /* Clear FORCESTALL flag */
            pEpt->UDPHS_EPTCLRSTA = UDPHS_EPTCLRSTA_TOGGLESQ
                                  | UDPHS_EPTCLRSTA_FRCESTALL;

            /* Reset Endpoint Fifos */
            pUdp->UDPHS_EPTRST = (1 << bEndpoint);
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
    Udphs    *pUdp = UDPHS;
    return (pUdp->UDPHS_INTSTA & UDPHS_INTSTA_SPEED);
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
    UDPHS_DisableBIAS();
    UDPHS_DisableUsbClock();
    UDPHS_DisablePeripheralClock();
}

/**
 * Activate USB Device HW Interface
 * -# Enable USB Peripheral
 * -# Enable USB Clock
 * -# Enable transceiver
 */
void USBD_HAL_Activate(void)
{
    UDPHS_EnablePeripheralClock();
    UDPHS_EnableUsbClock();
    UDPHS_EnableBIAS();
}

/**
 * Certification test for High Speed device.
 * \param bIndex Test to be done
 */
void USBD_HAL_Test( uint8_t bIndex )
{
    Udphs *pUdp = UDPHS;
    uint8_t      *pFifo;
    uint32_t      i;

    /* remove suspend for TEST */
    pUdp->UDPHS_IEN &= ~UDPHS_IEN_DET_SUSPD;
    /* force High Speed (remove suspend) */
    pUdp->UDPHS_TST |= UDPHS_TST_SPEED_CFG_HIGH_SPEED;

    switch( bIndex ) {

        case USBFeatureRequest_TESTPACKET:
            TRACE_DEBUG_WP("TEST_PACKET ");

            pUdp->UDPHS_DMA[1].UDPHS_DMACONTROL = 0;
            pUdp->UDPHS_DMA[2].UDPHS_DMACONTROL = 0;

            /* Configure endpoint 2, 64 bytes, direction IN, type BULK, 1 bank */
            pUdp->UDPHS_EPT[2].UDPHS_EPTCFG = UDPHS_EPTCFG_EPT_SIZE_64
                                            | UDPHS_EPTCFG_EPT_DIR
                                            | UDPHS_EPTCFG_EPT_TYPE_BULK
                                            | UDPHS_EPTCFG_BK_NUMBER_1;
            while( (pUdp->UDPHS_EPT[2].UDPHS_EPTCFG & UDPHS_EPTCFG_EPT_MAPD) != UDPHS_EPTCFG_EPT_MAPD );
            pUdp->UDPHS_EPT[2].UDPHS_EPTCTLENB = UDPHS_EPTCTLENB_EPT_ENABL;

            /* Write FIFO */
            pFifo = (uint8_t*)((uint32_t *)(UDPHS_RAM_ADDR) + (EPT_VIRTUAL_SIZE * 2));
            for( i=0; i<sizeof(test_packet_buffer); i++) {
                pFifo[i] = test_packet_buffer[i];
            }
            /* Tst PACKET */
            pUdp->UDPHS_TST |= UDPHS_TST_TST_PKT;
            /* Send packet */
            pUdp->UDPHS_EPT[2].UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_TX_PK_RDY;
            break;

        case USBFeatureRequest_TESTJ:
            TRACE_DEBUG_WP("TEST_J ");
            pUdp->UDPHS_TST = UDPHS_TST_TST_J;
            break;

        case USBFeatureRequest_TESTK:
            TRACE_DEBUG_WP("TEST_K ");
            pUdp->UDPHS_TST = UDPHS_TST_TST_K;
            break;

        case USBFeatureRequest_TESTSE0NAK:
            TRACE_DEBUG_WP("TEST_SEO_NAK ");
            pUdp->UDPHS_IEN = 0;  // for test
            break;

        case USBFeatureRequest_TESTSENDZLP:
            //while( 0 != (pUdp->UDPHS_EPT[0].UDPHS_EPTSTA & UDPHS_EPTSETSTA_TX_PK_RDY ) ) {}
            pUdp->UDPHS_EPT[0].UDPHS_EPTSETSTA = UDPHS_EPTSETSTA_TX_PK_RDY;
            //while( 0 != (pUdp->UDPHS_EPT[0].UDPHS_EPTSTA & UDPHS_EPTSETSTA_TX_PK_RDY ) ) {}
            TRACE_DEBUG_WP("SEND_ZLP ");
            break;
    }
    TRACE_DEBUG_WP("\n\r");
}

/**@}*/

