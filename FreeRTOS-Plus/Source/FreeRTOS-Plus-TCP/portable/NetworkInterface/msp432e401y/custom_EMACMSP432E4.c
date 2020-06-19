/*
 * Copyright (c) 2017-2019 Texas Instruments Incorporated
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
 */

/*
 *  ======== EMACMSP432E4.c ========
 *  This driver currently supports only 1 EMACMSP432E4 port. In the future
 *  when multiple ports are required, this driver needs to move all the
 *  EMACMSP432E4_Data fields into the EMACMSP432E4_Object structure. The APIs
 *  need to get to the fields via the pvt_data field in the NETIF_DEVICE that
 *  is passed in. ROV must be changed to support the change also.
 *  The NETIF_DEVICE structure should go into the EMACMSP432E4_Object also.
 *
 *  These changes are not being done at this time because of the impact on
 *  the complexity of the code.
 */
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include <ti/devices/msp432e4/inc/msp432.h>

#include <ti/devices/msp432e4/driverlib/emac.h>
#include <ti/devices/msp432e4/driverlib/flash.h>
#include <ti/devices/msp432e4/driverlib/gpio.h>
#include <ti/devices/msp432e4/driverlib/pin_map.h>
#include <ti/devices/msp432e4/driverlib/sysctl.h>

#include <ti/drivers/dpl/ClockP.h>
#include <ti/drivers/dpl/HwiP.h>

#include "custom_EMACMSP432E4.h"
#include <ti/drivers/gpio/GPIOMSP432E4.h>
#include <ti/drivers/Power.h>
#include <ti/drivers/power/PowerMSP432E4.h>

/* FreeRTOS includes. */
#include "NetworkBufferManagement.h"
#include "FreeRTOS_IP_Private.h"
#include "queue.h"
#include "FreeRTOSIPConfig.h"

//phisical address 0 for internal PHY.
#define PHY_PHYS_ADDR 0
#define NUM_RX_DESCRIPTORS 4
#define NUM_TX_DESCRIPTORS 4
#define EMAC_PHY_CONFIG         (EMAC_PHY_TYPE_INTERNAL |                     \
                                 EMAC_PHY_INT_MDIX_EN |                       \
                                 EMAC_PHY_AN_100B_T_FULL_DUPLEX)

/* The size of the CRC stored at the end of the received frames */
#define CRC_SIZE_BYTES 4

/* The receive descriptor buffer size must be a multiple of 4 bytes */
#define RX_BUFFER_SIZE_MULTIPLE 4

#define RX_BUFFER_SIZE_ROUNDUP(X) ((((X) + \
        (RX_BUFFER_SIZE_MULTIPLE - 1)) / RX_BUFFER_SIZE_MULTIPLE) * \
        RX_BUFFER_SIZE_MULTIPLE)

/*
 * Define checksum related macros that are missing from driverlib
 *
 * The following bits in the RX DES0 descriptor have different meanings when
 * h/w checksum calculations are enabled. Define them here based on the default
 * macro values (default == h/w checksums disabled).
 */
/* RX DES0 bit 0 has payload checksum error status if EMACCFG IPC bit set */
#define EMAC_DES0_RX_STAT_PAYLOAD_CHKSM_ERR  DES0_RX_STAT_MAC_ADDR

/* RX DES0 bit 7 has IP header checksum error status if EMACCFG IPC bit set */
#define EMAC_DES0_RX_STAT_IPHDR_CHKSM_ERR  DES0_RX_STAT_TS_AVAILABLE

/*
 *  The buffer size for receive descriptors to allow for receipt of a maximum
 *  length Ethernet payload (ETH_MAX_PAYLOAD) allowing for:
 *
 *  - The CRC also being stored by the EMACMSP432E4 port
 *  - Rounding up the size to the multiple required by the EMACMSP432E4 port
 */
//#define RX_BUFFER_SIZE RX_BUFFER_SIZE_ROUNDUP (ETH_MAX_PAYLOAD + CRC_SIZE_BYTES)

/*
 * pxGetNetworkBufferWithDescriptor does not use buffesr size...see surce, then define a dummy  buffersize
 */
#define GET_BUFFER_SIZE 0
/*
 *  Helper struct holding a DMA descriptor and the pbuf it currently refers
 *  to.
 */
typedef struct {
    tEMACDMADescriptor Desc;
    NetworkBufferDescriptor_t *hPkt;
} tDescriptor;

typedef struct {
    tDescriptor *pDescriptors;
    uint32_t     ulNumDescs;
    uint32_t     ulWrite;
    uint32_t     ulRead;
} tDescriptorList;

/*
 * The struct is used to store the private data for the EMACMSP432E4 controller.
 */
typedef struct {
    uint32_t         rxCount;
    uint32_t         rxDropped;
    uint32_t         rxIpHdrChksmErrors;
    uint32_t         rxPayloadChksmErrors;
    uint32_t         txSent;
    uint32_t         txDropped;
    uint32_t         txIpHdrChksmErrors;
    uint32_t         txPayloadChksmErrors;
    uint32_t         pbmAllocErrors;
    uint32_t         descriptorLoopCount[NUM_RX_DESCRIPTORS];
    uint32_t         abnormalInts;
    uint32_t         isrCount;
    uint32_t         linkUp;
    tDescriptorList *pTxDescList;
    tDescriptorList *pRxDescList;
    HwiP_Handle      hwi;
} EMACMSP432E4_Data;

/*
 * Static global variables for this interface's private data.
 */
static tDescriptor g_pTxDescriptors[NUM_TX_DESCRIPTORS];
static tDescriptor g_pRxDescriptors[NUM_RX_DESCRIPTORS];

static tDescriptorList g_TxDescList = {
    g_pTxDescriptors, NUM_TX_DESCRIPTORS, 0, 0
};

static tDescriptorList g_RxDescList = {
    g_pRxDescriptors, NUM_RX_DESCRIPTORS, 0, 0
};

/* Application is required to provide this variable */
extern const EMACMSP432E4_HWAttrs EMACMSP432E4_hwAttrs;

/* Only supporting one EMACMSP432E4 device */
static EMACMSP432E4_Data EMACMSP432E4_private;

/* Function prototypes */
static void EMACMSP432E4_handleRx();
static void EMACMSP432E4_processTransmitted();
static int EMACMSP432E4_initDMADescriptors(void);
static int EMACMSP432E4_emacStop();

static BaseType_t xSendEventStructToIPTaskFromISR( const IPStackEvent_t *pxEvent);

/*
 *  ======== xSendEventStructToIPTaskFromISR ========
 *  Signal the stack with IPStackEvent_t from ISR.
 *  see xSendEventStructToIPTask in extern/FreeRTOS/FreeRTOS-Plus/Source/FreeRTOS-Plus-TCP/FreeRTOS_IP.c
 *  this implementation is only for eNetworkRxEvent events. 
 */
extern QueueHandle_t xNetworkEventQueue;
static BaseType_t xSendEventStructToIPTaskFromISR( const IPStackEvent_t *pxEvent){
        return xQueueSendToBackFromISR( xNetworkEventQueue, pxEvent,pdFALSE );
}

/*
 *  ======== signalLinkChange ========
 *  Signal the stack based on linkUp parameter.
 */
static void signalLinkChange()
{
}

/*
 *  ======== EMACMSP432E4_processPendingTx ========
 */

int EMACMSP432E4_processPendingTx(NetworkBufferDescriptor_t *hPkt)
{
    tDescriptor *pDesc;
    /*
     *  If there are pending packets, send one.
     *  Otherwise quit the loop.
     */
    pDesc = &(EMACMSP432E4_private.pTxDescList->pDescriptors[EMACMSP432E4_private.pTxDescList->ulWrite]);
    //return  false if no dma buffer available
    if (pDesc->hPkt) {
        vReleaseNetworkBufferAndDescriptor(hPkt);
        EMACMSP432E4_private.txDropped++;
        return 0;
    }

    /* Fill in the buffer pointer and length */
    pDesc->Desc.ui32Count = hPkt->xDataLength;
    pDesc->Desc.pvBuffer1 = hPkt->pucEthernetBuffer;
    pDesc->Desc.ui32CtrlStatus = DES0_TX_CTRL_FIRST_SEG;

    /* CRC  IP offloading settings */
    #if ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    pDesc->Desc.ui32CtrlStatus |= (DES0_TX_CTRL_IP_ALL_CKHSUMS);
    #endif
    pDesc->Desc.ui32CtrlStatus |= DES0_TX_CTRL_CHAINED;

    pDesc->Desc.ui32CtrlStatus |= (DES0_TX_CTRL_LAST_SEG |
                                    DES0_TX_CTRL_INTERRUPT);
    EMACMSP432E4_private.pTxDescList->ulWrite++;
    if (EMACMSP432E4_private.pTxDescList->ulWrite == NUM_TX_DESCRIPTORS) {
        EMACMSP432E4_private.pTxDescList->ulWrite = 0;
    }
    pDesc->hPkt = hPkt;
    pDesc->Desc.ui32CtrlStatus |= DES0_TX_CTRL_OWN;

    EMACMSP432E4_private.txSent++;

    EMACTxDMAPollDemand(EMAC0_BASE);
    return 1;
}
/*
 *  ======== EMACMSP432E4_processTransmitted ========
 */

static void EMACMSP432E4_processTransmitted()
{
    tDescriptor *pDesc;
    uint32_t     ulNumDescs;

    /*
     * Walk the list until we have checked all descriptors or we reach the
     * write pointer or find a descriptor that the hardware is still working
     * on.
     */
    for (ulNumDescs = 0; ulNumDescs < NUM_TX_DESCRIPTORS; ulNumDescs++) {
        pDesc = &(EMACMSP432E4_private.pTxDescList->pDescriptors[EMACMSP432E4_private.pTxDescList->ulRead]);
        /* Has the buffer attached to this descriptor been transmitted? */
        if (pDesc->Desc.ui32CtrlStatus & DES0_TX_CTRL_OWN) {
            /* No - we're finished. */
            break;
        }

        /*
         * Check this descriptor for transmit errors
         *
         * First, check the error summary to see if there was any error and if
         * so, check to see what type of error it was.
         */
        if (pDesc->Desc.ui32CtrlStatus & DES0_TX_STAT_ERR) {
            /* An error occurred - now look for errors of interest */

            /*
             * Ensure TX Checksum Offload is enabled before checking for IP
             * header error status (this status bit is reserved when TX CS
             * offload is disabled)
             */
            if (((pDesc->Desc.ui32CtrlStatus & DES0_TX_CTRL_IP_HDR_CHKSUM) ||
                (pDesc->Desc.ui32CtrlStatus & DES0_TX_CTRL_IP_ALL_CKHSUMS)) &&
                (pDesc->Desc.ui32CtrlStatus & DES0_TX_STAT_IPH_ERR)) {
                /* Error inserting IP header checksum */
                EMACMSP432E4_private.txIpHdrChksmErrors++;
            }

            if (pDesc->Desc.ui32CtrlStatus & DES0_TX_STAT_PAYLOAD_ERR) {
                /* Error in IP payload checksum (i.e. in UDP, TCP or ICMP) */
                EMACMSP432E4_private.txPayloadChksmErrors++;
            }
        }

        /* Does this descriptor have a buffer attached to it? */
        if (pDesc->hPkt) {
            /* Yes - free it*/
            vNetworkBufferReleaseFromISR(pDesc->hPkt);
            pDesc->hPkt = NULL;
        }
        else {
            /* If the descriptor has no buffer, we are finished. */
            break;
        }

        /* Move on to the next descriptor. */
        EMACMSP432E4_private.pTxDescList->ulRead++;
        if (EMACMSP432E4_private.pTxDescList->ulRead == NUM_TX_DESCRIPTORS) {
            EMACMSP432E4_private.pTxDescList->ulRead = 0;
        }
    }
}

/*
 *  ======== EMACMSP432E4_primeRx ========
 */
static void EMACMSP432E4_primeRx(NetworkBufferDescriptor_t *hPkt, tDescriptor *desc)
{
    desc->hPkt = hPkt;
    desc->Desc.ui32Count = DES1_RX_CTRL_CHAINED;

    /* We got a buffer so fill in the payload pointer and size. */
    desc->Desc.pvBuffer1 = hPkt->pucEthernetBuffer;
    desc->Desc.ui32Count |= (NETWORK_BUFFER_DESCRIPTORS_LEN << DES1_RX_CTRL_BUFF1_SIZE_S);

    /* Give this descriptor back to the hardware */
    desc->Desc.ui32CtrlStatus = DES0_RX_CTRL_OWN;
}

/*
 *  ======== EMACMSP432E4_handleRx ========
 */
static void EMACMSP432E4_handleRx()
{
    NetworkBufferDescriptor_t *hPkt;
    NetworkBufferDescriptor_t *hPktNew;
    int32_t          len;
    tDescriptorList *pDescList;
    uint32_t         ulDescEnd;
    int32_t          descCount = -1;
    uint32_t         ui32Config;
    uint32_t         ui32Mode;
    uint32_t         ui32FrameSz;
    uint32_t         ui32CtrlStatus;

    IPStackEvent_t xRxEvent;

    /* Get a pointer to the receive descriptor list. */
    pDescList = EMACMSP432E4_private.pRxDescList;

    /* Determine where we start and end our walk of the descriptor list */
    ulDescEnd = pDescList->ulRead ?
            (pDescList->ulRead - 1) : (pDescList->ulNumDescs - 1);

    /* Step through the descriptors that are marked for CPU attention. */
    while (pDescList->ulRead != ulDescEnd) {
        descCount++;

        /* Does the current descriptor have a buffer attached to it? */
        hPkt = pDescList->pDescriptors[pDescList->ulRead].hPkt;
        if (hPkt) {
            ui32CtrlStatus = pDescList->pDescriptors[pDescList->ulRead].Desc.ui32CtrlStatus; 

            /* Determine if the host has filled it yet. */
            if (ui32CtrlStatus & DES0_RX_CTRL_OWN) {
                /* The DMA engine still owns the descriptor so we are finished. */
                break;
            }

            /* Yes - does the frame contain errors? */
            if (ui32CtrlStatus & DES0_RX_STAT_ERR) {
                /*
                 *  This is a bad frame. Update the relevant statistics and
                 *  then discard it.
                 */

                /*
                 * Check the EMAC configuration to see if RX h/w checksums are
                 * enabled. (The last 2 parameters are don't cares here)
                 */
                ui32Config = 0;
                EMACConfigGet(EMAC0_BASE, &ui32Config, &ui32Mode, &ui32FrameSz);
                if (ui32Config & EMAC_CONFIG_CHECKSUM_OFFLOAD) {
                    /* RX h/w checksums are enabled, look for checksum errors */

                    /* First check if the Frame Type bit is set */
                    if (ui32CtrlStatus & DES0_RX_STAT_FRAME_TYPE) {
                         /* Now, if bit 7 is reset and bit 0 is set: */
                         if (!(ui32CtrlStatus & EMAC_DES0_RX_STAT_IPHDR_CHKSM_ERR) &&
                             (ui32CtrlStatus & EMAC_DES0_RX_STAT_PAYLOAD_CHKSM_ERR)) {
                             /* Checksum error detected in the IP payload */
                             EMACMSP432E4_private.rxPayloadChksmErrors++;
                         }
                         /* Else if bit 7 and bit 0 are both set */
                         else if ((ui32CtrlStatus & EMAC_DES0_RX_STAT_IPHDR_CHKSM_ERR) &&
                             (ui32CtrlStatus & EMAC_DES0_RX_STAT_PAYLOAD_CHKSM_ERR)) {
                             /* Checksum error in both IP header & payload */
                             EMACMSP432E4_private.rxIpHdrChksmErrors++;
                             EMACMSP432E4_private.rxPayloadChksmErrors++;
                        }
                         
                    }
                }

                EMACMSP432E4_private.rxDropped++;
                EMACMSP432E4_primeRx(hPkt,
                        &(pDescList->pDescriptors[pDescList->ulRead]));
                pDescList->ulRead++;
                break;
            }
            else {
                /* Allocate a new buffer for this descriptor */
                hPktNew = pxNetworkBufferGetFromISR(GET_BUFFER_SIZE);
                if (hPktNew == NULL) {
                    /*
                     *  Leave the packet in the descriptor and owned by the
                     *  driver. Process when the next interrupt occurs.
                     */
                    EMACMSP432E4_private.pbmAllocErrors++;
                    break;
                }

                /* This is a good frame so pass it up the stack. */
                len = (pDescList->pDescriptors[pDescList->ulRead].Desc.ui32CtrlStatus &
                    DES0_RX_STAT_FRAME_LENGTH_M) >> DES0_RX_STAT_FRAME_LENGTH_S;

                /* Remove the CRC */
                hPkt->xDataLength= len - CRC_SIZE_BYTES;
                /*
                 *  Place the packet onto the receive queue to be handled in the
                 *  EMACMSP432E4_pkt_service function (which is called by the
                 *  NDK stack).
                 */
                /* Update internal statistic */
                EMACMSP432E4_private.rxCount++;


                /* Prime the receive descriptor back up for future packets */
                EMACMSP432E4_primeRx(hPktNew,
                        &(pDescList->pDescriptors[pDescList->ulRead]));
                
                xRxEvent.eEventType = eNetworkRxEvent;

                /* pvData is used to point to the network buffer descriptor that
                references the received data. */
                xRxEvent.pvData = ( void * ) hPkt;

                /* Send the data to the TCP/IP stack. */
                if( xSendEventStructToIPTaskFromISR( &xRxEvent) == pdFALSE ){
                    /* The buffer could not be sent to the IP task so the buffer
                    must be released. */
                    vNetworkBufferReleaseFromISR( hPkt );

                    /* Make a call to the standard trace macro to log the
                    occurrence. */
                    //iptraceETHERNET_RX_EVENT_LOST();
                }
                else{
                    /* The message was successfully sent to the TCP/IP stack.
                    Call the standard trace macro to log the occurrence. */
                    //iptraceNETWORK_INTERFACE_RECEIVE();
                }
                                                                    
            }
        }
        /* Move on to the next descriptor in the chain, taking care to wrap. */
        pDescList->ulRead++;
        if (pDescList->ulRead == pDescList->ulNumDescs) {
            pDescList->ulRead = 0;
        }
    }

    /*
     * Update the desciptorLoopCount. This shows how frequently we are cycling
     * through x DMA descriptors, where x is the index of this array. So if
     * descriptorLoopcount[1] = 32, we had to cycle through 2 descriptors here
     * 32 times.
     */
    if(descCount >= 0 && descCount < NUM_RX_DESCRIPTORS) {
        EMACMSP432E4_private.descriptorLoopCount[descCount]++;
    }
}

/*
 *  ======== EMACMSP432E4_processPhyInterrupt ========
 */
static void EMACMSP432E4_processPhyInterrupt()
{
    uint16_t value;
    uint16_t status;
    uint32_t config;
    uint32_t mode;
    uint32_t rxMaxFrameSize;

    /*
     * Read the PHY interrupt status.  This clears all interrupt sources.
     * Note that we are only enabling sources in EPHY_MISR1 so we don't
     * read EPHY_MISR2.
     */
    value = EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1);

    /* Read the current PHY status. */
    status = EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_STS);

    /* Has the link status changed? */
    if (value & EPHY_MISR1_LINKSTAT) {
        /* Is link up or down now? */
        if (status & EPHY_STS_LINK) {
            EMACMSP432E4_private.linkUp = true;
        }
        else {
            EMACMSP432E4_private.linkUp = false;
        }
        /* Signal the stack for this link status change (from ISR) */
        signalLinkChange();//EMACMSP432E4_private.hEvent,EMACMSP432E4_private.linkUp, 1);
    }

    /* Has the speed or duplex status changed? */
    if (value & (EPHY_MISR1_SPEED | EPHY_MISR1_SPEED | EPHY_MISR1_ANC)) {
        /* Get the current MAC configuration. */
        EMACConfigGet(EMAC0_BASE, (uint32_t *)&config, (uint32_t *)&mode,
                        (uint32_t *)&rxMaxFrameSize);

        /* What speed is the interface running at now? */
        if (status & EPHY_STS_SPEED) {
            /* 10Mbps is selected */
            config &= ~EMAC_CONFIG_100MBPS;
        }
        else {
            /* 100Mbps is selected */
            config |= EMAC_CONFIG_100MBPS;
        }

        /* Are we in full- or half-duplex mode? */
        if (status & EPHY_STS_DUPLEX) {
            /* Full duplex. */
            config |= EMAC_CONFIG_FULL_DUPLEX;
        }
        else {
            /* Half duplex. */
            config &= ~EMAC_CONFIG_FULL_DUPLEX;
        }

        /* Reconfigure the MAC */
        EMACConfigSet(EMAC0_BASE, config, mode, rxMaxFrameSize);
    }
}

/*
 *  ======== EMACMSP432E4_hwiIntFxn ========
 */
static void EMACMSP432E4_hwiIntFxn(uintptr_t callbacks)
{
    uint32_t status;

    /* Check link status */
    status = (EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_BMSR) & EPHY_BMSR_LINKSTAT);

    /* Signal the stack if link status changed */
    if (status != EMACMSP432E4_private.linkUp) {
        signalLinkChange();//EMACMSP432E4_private.hEvent, status, 1);
    }

    /* Set the link status */
    EMACMSP432E4_private.linkUp = status;

    EMACMSP432E4_private.isrCount++;

    /* Read and Clear the interrupt. */
    status = EMACIntStatus(EMAC0_BASE, true);
    EMACIntClear(EMAC0_BASE, status);

    /*
     *  Disable the Ethernet interrupts.  Since the interrupts have not been
     *  handled, they are not asserted.  Once they are handled by the Ethernet
     *  interrupt, it will re-enable the interrupts.
     */
    EMACIntDisable(EMAC0_BASE, (EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                     EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                     EMAC_INT_RX_STOPPED | EMAC_INT_PHY));

    if (status & EMAC_INT_ABNORMAL_INT) {
        EMACMSP432E4_private.abnormalInts++;
    }

    if (status & EMAC_INT_PHY) {
        EMACMSP432E4_processPhyInterrupt();
    }

    /* Process the transmit DMA list, freeing any buffers that have been
     * transmitted since our last interrupt.
     */
    if (status & EMAC_INT_TRANSMIT) {
        EMACMSP432E4_processTransmitted();
    }

    /*
     * Process the receive DMA list and pass all successfully received packets
     * up the stack.  We also call this function in cases where the receiver has
     * stalled due to missing buffers since the receive function will attempt to
     * allocate new pbufs for descriptor entries which have none.
     */
    if (status & (EMAC_INT_RECEIVE | EMAC_INT_RX_NO_BUFFER |
        EMAC_INT_RX_STOPPED)) {
        EMACMSP432E4_handleRx();
    }

    EMACIntEnable(EMAC0_BASE, (EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                        EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                        EMAC_INT_RX_STOPPED | EMAC_INT_PHY));
}

/*
 *  ======== EMACMSP432E4_emacStart ========
 *  The function is used to initialize and start the EMACMSP432E4
 *  controller and device.
 */
int EMACMSP432E4_emacStart()
{
    uint16_t value;
    EMACMSP432E4_HWAttrs const *hwAttrs = &EMACMSP432E4_hwAttrs;
    HwiP_Params hwiParams;
    ClockP_FreqHz freq;
    uint32_t key;
    uint32_t pinMap;
    uint8_t  port;
    uint8_t  pin;
    //bool enablePrefetch = false;

    /* set power dependency on peripherals being used */
    Power_setDependency(PowerMSP432E4_PERIPH_EMAC0);
    Power_setDependency(PowerMSP432E4_PERIPH_EPHY0);

    /* Configure the appropriate pins for ethernet led0 */
    pin = GPIOMSP432E4_getPinFromPinConfig(hwAttrs->led0Pin);
    port = GPIOMSP432E4_getPortFromPinConfig(hwAttrs->led0Pin);
    pinMap = GPIOMSP432E4_getPinMapFromPinConfig(hwAttrs->led0Pin);

    Power_setDependency(GPIOMSP432E4_getPowerResourceId(port));
    GPIOPinConfigure(pinMap);
    GPIOPinTypeEthernetLED(GPIOMSP432E4_getGpioBaseAddr(port), pin);

    /* Configure the appropriate pins for ethernet led1 */
    pin = GPIOMSP432E4_getPinFromPinConfig(hwAttrs->led1Pin);
    port = GPIOMSP432E4_getPortFromPinConfig(hwAttrs->led1Pin);
    pinMap = GPIOMSP432E4_getPinMapFromPinConfig(hwAttrs->led1Pin);

    Power_setDependency(GPIOMSP432E4_getPowerResourceId(port));
    GPIOPinConfigure(pinMap);
    GPIOPinTypeEthernetLED(GPIOMSP432E4_getGpioBaseAddr(port), pin);

    ClockP_getCpuFreq(&freq);

    key = HwiP_disable();

    EMACPHYConfigSet(EMAC0_BASE, EMAC_PHY_CONFIG);

    EMACInit(EMAC0_BASE, freq.lo,
             EMAC_BCONFIG_MIXED_BURST | EMAC_BCONFIG_PRIORITY_FIXED, 4, 4, 0);

    /* Set MAC configuration options. */
    EMACConfigSet(EMAC0_BASE, (EMAC_CONFIG_FULL_DUPLEX |
                               EMAC_CONFIG_7BYTE_PREAMBLE |
                               EMAC_CONFIG_IF_GAP_96BITS |
                               EMAC_CONFIG_USE_MACADDR0 |
                               EMAC_CONFIG_SA_FROM_DESCRIPTOR |
                               /* Enable RX Checksum Offload: */
                               EMAC_CONFIG_CHECKSUM_OFFLOAD |
                               EMAC_CONFIG_BO_LIMIT_1024),
                  (EMAC_MODE_RX_STORE_FORWARD |
                   EMAC_MODE_TX_STORE_FORWARD |
                   EMAC_MODE_TX_THRESHOLD_64_BYTES |
                   EMAC_MODE_RX_THRESHOLD_64_BYTES), 0);

    /* Program the MAC address into the Ethernet controller. */
    EMACAddrSet(EMAC0_BASE, 0, (uint8_t *)hwAttrs->macAddress);

    /* Initialize the DMA descriptors. */
    if (EMACMSP432E4_initDMADescriptors() < 0) {
        /*
         *  If fail to initialize DMA descriptor lists:
         *  1. Turns ON the prefetch buffer if it was disabled above
         *  2. call HwiP_restore
         *  3. call emacStop to clean up
         */
        HwiP_restore(key);
        EMACMSP432E4_emacStop();

        return (-1);
    }

    /* Clear any stray PHY interrupts that may be set. */
    value = EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1);
    value = EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR2);

    /* Configure and enable the link status change interrupt in the PHY. */
    value = EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_SCR);
    value |= (EPHY_SCR_INTEN_EXT | EPHY_SCR_INTOE_EXT);
    EMACPHYWrite(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_SCR, value);
    EMACPHYWrite(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1, (EPHY_MISR1_LINKSTATEN |
                 EPHY_MISR1_SPEEDEN | EPHY_MISR1_DUPLEXMEN | EPHY_MISR1_ANCEN));

    /* Read the PHY interrupt status to clear any stray events. */
    value = EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1);

    /*
     *  Set MAC filtering options.  We receive all broadcast and multicast
     *  packets along with those addressed specifically for us.
     */
    EMACFrameFilterSet(EMAC0_BASE, (EMAC_FRMFILTER_HASH_AND_PERFECT |
                       EMAC_FRMFILTER_PASS_MULTICAST));

    /* Clear any pending interrupts. */
    EMACIntClear(EMAC0_BASE, EMACIntStatus(EMAC0_BASE, false));

    /* Enable the Ethernet MAC transmitter and receiver. */
    EMACTxEnable(EMAC0_BASE);
    EMACRxEnable(EMAC0_BASE);

    /* Enable the Ethernet RX and TX interrupt source. */
    EMACIntEnable(EMAC0_BASE, (EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                  EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                  EMAC_INT_RX_STOPPED | EMAC_INT_PHY));

    EMACPHYWrite(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_BMCR, (EPHY_BMCR_ANEN |
                 EPHY_BMCR_RESTARTAN));

    /*
     * Turns ON the prefetch buffer if it was disabled above
     
    if (enablePrefetch) {
        ui32FlashConf = FLASH_CTRL->CONF;
        ui32FlashConf &= ~(FLASH_CONF_FPFOFF);
        ui32FlashConf |= FLASH_CONF_FPFON;
        FLASH_CTRL->CONF = ui32FlashConf;
    }
    */
    HwiP_restore(key);

    /* Create the hardware interrupt */
    HwiP_Params_init(&hwiParams);
    hwiParams.priority = hwAttrs->intPriority;

    EMACMSP432E4_private.hwi = HwiP_create(hwAttrs->intNum,
                                   EMACMSP432E4_hwiIntFxn,
                                   &hwiParams);

    if (EMACMSP432E4_private.hwi == NULL) {
        EMACMSP432E4_emacStop();
        return (-1);
    }

    return (0);
}

/*
 *  ======== EMACMSP432E4_emacStop ========
 *  The function is used to de-initialize and stop the EMACMSP432E4
 *  controller and device.
 */
static int EMACMSP432E4_emacStop()
{
    EMACMSP432E4_HWAttrs const *hwAttrs = &EMACMSP432E4_hwAttrs;
    uint8_t  port;
    int i = 0;



    EMACIntDisable(EMAC0_BASE, (EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                     EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                     EMAC_INT_RX_STOPPED | EMAC_INT_PHY));

    if (EMACMSP432E4_private.hwi != NULL) {
        HwiP_delete(EMACMSP432E4_private.hwi);
    }

    #if 0


    while (PBMQ_count(&EMACMSP432E4_private.PBMQ_rx)) {
        /* Dequeue a packet from the driver receive queue. */
        hPkt = PBMQ_deq(&EMACMSP432E4_private.PBMQ_rx);
        PBM_free(hPkt);
    }

    while (PBMQ_count(&EMACMSP432E4_private.PBMQ_tx)) {
        /* Dequeue a packet from the driver receive queue. */
        hPkt = PBMQ_deq(&EMACMSP432E4_private.PBMQ_tx);
        PBM_free(hPkt);
    }

    #endif

    for (i = 0; i < NUM_RX_DESCRIPTORS; i++) {
        if (g_pRxDescriptors[i].hPkt != NULL) {
            vReleaseNetworkBufferAndDescriptor(g_pRxDescriptors[i].hPkt);
        }
    }

    GPIOMSP432E4_undoPinConfig(hwAttrs->led0Pin);
    port = GPIOMSP432E4_getPortFromPinConfig(hwAttrs->led0Pin);
    Power_releaseDependency(GPIOMSP432E4_getPowerResourceId(port));

    GPIOMSP432E4_undoPinConfig(hwAttrs->led1Pin);
    port = GPIOMSP432E4_getPortFromPinConfig(hwAttrs->led1Pin);
    Power_releaseDependency(GPIOMSP432E4_getPowerResourceId(port));

    Power_releaseDependency(PowerMSP432E4_PERIPH_EPHY0);
    Power_releaseDependency(PowerMSP432E4_PERIPH_EMAC0);

    return (0);
}


/*
 *  ======== EMACMSP432E4_initDMADescriptors ========
 * Initialize the transmit and receive DMA descriptor lists.
 */
static int EMACMSP432E4_initDMADescriptors(void)
{
    int32_t     i;
    NetworkBufferDescriptor_t  *hPkt;

    /* Reset DMA descriptor lists' indexes to 0 */
    EMACMSP432E4_private.pTxDescList->ulRead = 0;
    EMACMSP432E4_private.pTxDescList->ulWrite = 0;
    EMACMSP432E4_private.pRxDescList->ulRead = 0;
    EMACMSP432E4_private.pRxDescList->ulWrite = 0;

    /* Transmit list -  mark all descriptors as not owned by the hardware */
    for (i = 0; i < NUM_TX_DESCRIPTORS; i++) {
        g_pTxDescriptors[i].hPkt = NULL;
        g_pTxDescriptors[i].Desc.ui32Count = 0;
        g_pTxDescriptors[i].Desc.pvBuffer1 = 0;
        g_pTxDescriptors[i].Desc.DES3.pLink = ((i == (NUM_TX_DESCRIPTORS - 1)) ?
               &g_pTxDescriptors[0].Desc : &g_pTxDescriptors[i + 1].Desc);
        g_pTxDescriptors[i].Desc.ui32CtrlStatus = DES0_TX_CTRL_INTERRUPT |
                DES0_TX_CTRL_IP_ALL_CKHSUMS |
                DES0_TX_CTRL_CHAINED;
    }

    /*
     * Receive list - tag each descriptor with a buffer and set all fields to
     * allow packets to be received.
     */
    for (i = 0; i < NUM_RX_DESCRIPTORS; i++) {
        hPkt = pxGetNetworkBufferWithDescriptor(GET_BUFFER_SIZE,0);
        if (hPkt) {
            EMACMSP432E4_primeRx(hPkt, &(g_pRxDescriptors[i]));
        }
        else {
            /*
             *  This is a failing scenario return -1.
             *  emacStop will do the PBM_free for any allocated packet.
             */
            g_pRxDescriptors[i].Desc.pvBuffer1 = 0;
            g_pRxDescriptors[i].Desc.ui32CtrlStatus = 0;
            return (-1);
        }
        g_pRxDescriptors[i].Desc.DES3.pLink =
                ((i == (NUM_RX_DESCRIPTORS - 1)) ?
                &g_pRxDescriptors[0].Desc : &g_pRxDescriptors[i + 1].Desc);
    }

    /* Set the descriptor pointers in the hardware. */
    EMACRxDMADescriptorListSet(EMAC0_BASE, &g_pRxDescriptors[0].Desc);
    EMACTxDMADescriptorListSet(EMAC0_BASE, &g_pTxDescriptors[0].Desc);
    return (0);
}

/*
 *  ======== EMACMSP432E4_NIMUInit ========
 *  The function is used to initialize and register the EMACMSP432E4
 *  with the Network Interface Management Unit (NIMU)
 */
int EMACMSP432E4_Init()
{

    EMACMSP432E4_private.pTxDescList  = &g_TxDescList;
    EMACMSP432E4_private.pRxDescList  = &g_RxDescList;
    EMACMSP432E4_private.rxCount      = 0;
    EMACMSP432E4_private.rxDropped    = 0;
    EMACMSP432E4_private.rxIpHdrChksmErrors = 0;
    EMACMSP432E4_private.rxPayloadChksmErrors = 0;
    EMACMSP432E4_private.txSent       = 0;
    EMACMSP432E4_private.txDropped    = 0;
    EMACMSP432E4_private.txIpHdrChksmErrors = 0;
    EMACMSP432E4_private.txPayloadChksmErrors = 0;
    EMACMSP432E4_private.pbmAllocErrors = 0;
    EMACMSP432E4_private.abnormalInts = 0;
    EMACMSP432E4_private.isrCount = 0;
    EMACMSP432E4_private.linkUp       = false;
    memset(EMACMSP432E4_private.descriptorLoopCount, 0,
            sizeof(EMACMSP432E4_private.descriptorLoopCount));

    return (0);
}

/*
 *  ======== EMACMSP432E4_linkUp ========
 */
bool EMACMSP432E4_isLinkUp()
{
    uint32_t newLinkStatus;

    /* Check link status */
    newLinkStatus =
            (EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_BMSR) & EPHY_BMSR_LINKSTAT);

    /* Signal the stack if link status changed */
    if (newLinkStatus != EMACMSP432E4_private.linkUp) {
        signalLinkChange();//EMACMSP432E4_private.hEvent, newLinkStatus, 0);
    }

    /* Set the link status */
    EMACMSP432E4_private.linkUp = newLinkStatus;

    if (EMACMSP432E4_private.linkUp) {
        return (true);
    }
    else {
        return (false);
    }
}
