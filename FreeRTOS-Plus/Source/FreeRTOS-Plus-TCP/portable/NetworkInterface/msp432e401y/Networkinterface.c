/*
FreeRTOS+TCP V2.0.11
Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

 http://aws.amazon.com/freertos
 http://www.FreeRTOS.org
*/

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include <ti/devices/msp432e4/inc/msp432.h>

#include <ti/devices/msp432e4/driverlib/emac.h>
#include <ti/devices/msp432e4/driverlib/gpio.h>
#include <ti/devices/msp432e4/driverlib/pin_map.h>

#include <ti/drivers/dpl/ClockP.h>
#include <ti/drivers/dpl/HwiP.h>

#include <ti/drivers/gpio/GPIOMSP432E4.h>
#include <ti/drivers/Power.h>
#include <ti/drivers/power/PowerMSP432E4.h>

/* FreeRTOS includes. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_IP.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_IP_Private.h"

#include "MSP432E4_Networkinterface.h"

/* check  FreeRTOSIPConfig.h*/

#if (ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0)
    #warning ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM can be set to 1.
#endif

#if (ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0)
    #warning ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM should be set to 1.
#endif

#if (ipconfigUSE_LINKED_RX_MESSAGES == 1)
    #error ipconfigUSE_LINKED_RX_MESSAGES should be set to 0.
#endif

#if (ipconfigZERO_COPY_TX_DRIVER == 0)
    #error ipconfigZERO_COPY_TX_DRIVER should be set to 1.
#endif

/* 
the msp432 can calculate ICMP checksum in driver. 
settings FIX_ICMP_CHECKSUM_IN_DRIVER to 1 fix frames for a correct ICMP 
calculation in peripheral.
It has only effect if ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM is set to 0
*/
#define FIX_ICMP_CHECKSUM_IN_DRIVER 1

/* PHY linkstatus read in xGetPhyLinkStatus 
 if FORCE_LINK_STATUS_READ_IN_xGetPhyLinkStatus is 0 the linkUp 
 variable is used instead of polling the PHY. 
 The linkup variable is setted in ISR by PHY interrupt events 
 by prvProcessPhyInterrupt 
*/
#ifndef FORCE_LINK_STATUS_READ_IN_xGetPhyLinkStatus
    #define FORCE_LINK_STATUS_READ_IN_xGetPhyLinkStatus 0
#endif

/* PHY phisical address, internal PHY */
#define PHY_PHYS_ADDR       0
#define NUM_RX_DESCRIPTORS  4
#define NUM_TX_DESCRIPTORS  4
#define EMAC_PHY_CONFIG         (EMAC_PHY_TYPE_INTERNAL |                     \
                                 EMAC_PHY_INT_MDIX_EN |                       \
                                 EMAC_PHY_AN_100B_T_FULL_DUPLEX)

/* The size of the CRC stored at the end of the received frames */
#define CRC_SIZE_BYTES 4

/* 
* NETWORK_BUFFER_DESCRIPTORS_LEN is defined as follow:
*
* ipTOTAL_ETHERNET_FRAME_SIZE = eth_header +  ipconfigNETWORK_MTU  + crc + ipSIZE_OF_ETH_OPTIONAL_802_1Q_TAG_BYTES
*                                  14      +  1500                 +  4  + 4 = 1522 
*
* ipBUFFER_PADDING = 8 + ipconfigPACKET_FILLER_SIZE = 10 bytes 
*                                    2
* we get:
* NETWORK_BUFFER_DESCRIPTORS_LEN = 1532
* 
* Understand ipBUFFER_PADDING ipconfigPACKET_FILLER_SIZE and memory alignement.
* we want:
* - aligned ip header
* - using DMA transfer to fill buffers.
* Since eth header is of len 14 the start of the buffer will not be aligned at 32 bit
* boundaries. 
* The MSP432e DMA can write at buffers starting at any places in memory, however the DMA 
* transfer lenght is always a multiple of 4 bytes and dummy bytes are written at the 
* beginning and at the end of the trasferred data.
* thus the 2 bit of ipconfigPACKET_FILLER_SIZE serve as place for the dummy bytes written 
* in front of the start of the non aligned eth frame.
* Making the len of NETWORK_BUFFER_DESCRIPTORS_LEN a multiple of 4 solve the problem of
* the dummy bytes at the end of the buffer.
*/

#ifndef ipconfigPACKET_FILLER_SIZE
    #define ipconfigPACKET_FILLER_SIZE 2
#elif !(ipconfigPACKET_FILLER_SIZE==2)
    #error ipconfigPACKET_FILLER_SIZE has to be 2.
#endif


#define ROUNDUP_4BYTES(X)  ((((X) + 3) / 4) * 4)

#define NETWORK_BUFFER_DESCRIPTORS_LEN  ROUNDUP_4BYTES( (8 + ipconfigPACKET_FILLER_SIZE + ipTOTAL_ETHERNET_FRAME_SIZE) )

/*
 * pxGetNetworkBufferWithDescriptor return a staic allocated buffer of fixed size,
 * thus define a dummy buffersize
 */

#define GET_BUFFER_SIZE 0


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


/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
driver will filter incoming packets and only pass the stack those packets it
considers need processing. */
#if( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eProcessBuffer
#else
#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif


/*For RX operation, if FIFO store-and-forward mode is enabled and a frame is read by the 
DMA only after it is completely written into the RX FIFO. 
In cut-through mode, DMA transfer is started after reaching of a given Threshold.
TX is similar in the other direction.
*/
#define DMA_STORE_FORWARD_RX_OPERATION 0
#if DMA_STORE_FORWARD_RX_OPERATION
#define DMA_OP_MODE (EMAC_MODE_TX_STORE_FORWARD | \ 
                     EMAC_MODE_RX_STORE_FORWARD)
#else /*cut-through mode*/
#define DMA_OP_MODE (EMAC_MODE_TX_STORE_FORWARD | \ 
                     EMAC_MODE_RX_THRESHOLD_128_BYTES)
#endif

/* How error RX framaes are handled depend on the FIFO mode and on some
Register fields in EMACDMAOPMODE. 
In cut-through mode, only frames smaller than DMA transfer threshold, can be dropped before DMA transfers,
store-and-forward mode frames are per default dropped, if FEF bit is set then are not dropped.
The DT fields control forward of frames with error in the tcp/ip payload 
*/
#define DMA_ERR_FORWARD 0
#if DMA_ERR_FORWARD
    #define DMA_ERR_MODE  (EMAC_MODE_KEEP_BAD_CRC | EMAC_MODE_RX_ERROR_FRAMES)
#else
    #define DMA_ERR_MODE 0
#endif

/*
 *  Helper struct holding a DMA descriptor and the Network Buffer Descriptors it currently refers to.
 */
typedef struct {
    tEMACDMADescriptor Desc;
    NetworkBufferDescriptor_t *pxNetworkBuffer;
} DescriptorRef_t;

typedef struct {
    DescriptorRef_t *pxDescriptorRef;
    uint32_t     ulNumDescs;
    uint32_t     ulWrite;
    uint32_t     ulRead;
} DescriptorRefList_t;

/*
 * The struct is used to store the private data for the EMACMSP432E4 controller.
 */
typedef struct {
    uint32_t         ulRxCount;
    uint32_t         ulRxDropped;
    uint32_t         ulRxIpHdrChksmErrors;
    uint32_t         ulRxPayloadChksmErrors;
    uint32_t         ulTxSent;
    uint32_t         ulTxDropped;
    uint32_t         ulTxIpHdrChksmErrors;
    uint32_t         ulTxPayloadChksmErrors;
    uint32_t         ulDescriptorLoopCount[NUM_RX_DESCRIPTORS];
    uint32_t         ulAbnormalInts;
    uint32_t         ulIsrCount;
    uint32_t         linkUp;
    DescriptorRefList_t *pxTxDescList;
    DescriptorRefList_t *pxRxDescList;
    HwiP_Handle      xHwi;
} EMAC_Data;

/*
 *  Signal the stack based on linkUp parameter.
 */
#ifndef SIGNAL_LINK_CHANGE
    #define SIGNAL_LINK_CHANGE(linkUp)
#endif

/* 
 * The function is used to initialize the DMA descriptors 
 */
static BaseType_t prvInitDMADescriptors();

/* 
 *The function is used to initialize and start the EMACMSP432E4
 *  controller and device.
 */
static BaseType_t prvEmacStart();

/* 
 * The function is used to deinitialize and stop the EMACMSP432E4 controller and device. 
 */
static BaseType_t prvEmacStop();


/*
 * prepare DMA Descriptor for RX 
 */
static void prvPrimeRx(NetworkBufferDescriptor_t *pxNetworkBuffer, DescriptorRef_t *desc);


/* 
 * private function called from ISR routine for processing recieve interrupts 
 */
static void prvHandleRx();

/*
 *  Signal the stack with IPStackEvent_t from ISR.
 */
static BaseType_t prvSendEventStructToIPTaskFromISR( const IPStackEvent_t *pxEvent);

/*
 * private function called from ISR routine for processing trasmit interrupts 
 */
static void prvProcessTransmitted();

/*private function called from ISR routine for processing PHY interrupts */
static void prvProcessPhyInterrupt();

/* 
 * EMAC ISR routine.
 * emac rx, tx and phy interrupts are handled by this function.
 */
static void prv_xHwiIntFxn(uintptr_t callbacks);

/*-------------------------------------------*/

/*
 * Static global variables for this interface's private data.
 */

static EMAC_Data xEMAC_prv;

static DescriptorRef_t g_pTxDescriptors[NUM_TX_DESCRIPTORS];
static DescriptorRef_t g_pRxDescriptors[NUM_RX_DESCRIPTORS];

static DescriptorRefList_t g_TxDescList = {
    g_pTxDescriptors, NUM_TX_DESCRIPTORS, 0, 0
};

static DescriptorRefList_t g_RxDescList = {
    g_pRxDescriptors, NUM_RX_DESCRIPTORS, 0, 0
};

/*
 * Static defined network buffers 32 bit aligned.
 */
static uint8_t ucBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS][NETWORK_BUFFER_DESCRIPTORS_LEN] __attribute__ ((aligned(32)));;


/* Application is required to provide this variable */
extern const EMACMSP432E4_DriverAttrs g_EMAC_DriverAttrs;

/* The queue used to pass events into the IP-task for processing. */
extern QueueHandle_t xNetworkEventQueue;

/*-------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
    /* initilaize  EMAC_Data private data */
    xEMAC_prv.pxTxDescList  = &g_TxDescList;
    xEMAC_prv.pxRxDescList  = &g_RxDescList;
    xEMAC_prv.ulRxCount      = 0;
    xEMAC_prv.ulRxDropped    = 0;
    xEMAC_prv.ulRxIpHdrChksmErrors = 0;
    xEMAC_prv.ulRxPayloadChksmErrors = 0;
    xEMAC_prv.ulTxSent       = 0;
    xEMAC_prv.ulTxDropped    = 0;
    xEMAC_prv.ulTxIpHdrChksmErrors = 0;
    xEMAC_prv.ulTxPayloadChksmErrors = 0;
    xEMAC_prv.ulAbnormalInts = 0;
    xEMAC_prv.ulIsrCount = 0;
    xEMAC_prv.linkUp       = 0;
    memset(xEMAC_prv.ulDescriptorLoopCount, 0,
            sizeof(xEMAC_prv.ulDescriptorLoopCount));

    return prvEmacStart();
}
/*-------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer, BaseType_t xReleaseAfterSend )
{
    DescriptorRef_t *pxDescRef;

    /* get next descriptorRef */
    pxDescRef = &(xEMAC_prv.pxTxDescList->pxDescriptorRef[xEMAC_prv.pxTxDescList->ulWrite]);
    /* the pxDescRef contain a reference to a pxNethworkBuffer,
       then the buffer is in use. prvProcessTransmitted will free the buffer.
     */
    if (pxDescRef->pxNetworkBuffer) {
        /* DMA buffer has associated a pxNetworkBuffer*/
        vReleaseNetworkBufferAndDescriptor(pxNetworkBuffer);
        xEMAC_prv.ulTxDropped++;
        
        iptraceWAITING_FOR_TX_DMA_DESCRIPTOR();

        return pdFALSE;
    }
    /* the pxDescRef contain no reference to a pxNethworkBuffer. 
       we can use it to send the frame. 
     */

    /* Fill in the buffer pointer and length */
    pxDescRef->Desc.ui32Count = pxNetworkBuffer->xDataLength;
    pxDescRef->Desc.pvBuffer1 = pxNetworkBuffer->pucEthernetBuffer;
    pxDescRef->Desc.ui32CtrlStatus =  (DES0_TX_CTRL_FIRST_SEG|
                                    DES0_TX_CTRL_CHAINED  |
                                    DES0_TX_CTRL_LAST_SEG |
                                    DES0_TX_CTRL_INTERRUPT);

    /* CRC  IP offloading settings */
    #if ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    /*enable checksum offloading for this frame*/
    pxDescRef->Desc.ui32CtrlStatus |= (DES0_TX_CTRL_IP_ALL_CKHSUMS);
    #if FIX_ICMP_CHECKSUM_IN_DRIVER
    {       
        /*
        freeRTOS TCP always calculate  the ICMP checksum.
        If the peripheral must calculate the checksum, it wants
        the protocol checksum to have a value of zero. 
        */ 
        ProtocolPacket_t *pxPacket;
            
        
        pxPacket = ( ProtocolPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

        if( pxPacket->xICMPPacket.xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
        {
            pxPacket->xICMPPacket.xICMPHeader.usChecksum = ( uint16_t )0u;
        }
	}
    #endif
    #endif

    xEMAC_prv.pxTxDescList->ulWrite++;
    if (xEMAC_prv.pxTxDescList->ulWrite == NUM_TX_DESCRIPTORS) {
        xEMAC_prv.pxTxDescList->ulWrite = 0;
    }
    /* set the reference to the Network Buffer */
    pxDescRef->pxNetworkBuffer = pxNetworkBuffer;
    /* set the Descriptor belonging the DMA */
    pxDescRef->Desc.ui32CtrlStatus |= DES0_TX_CTRL_OWN;

    xEMAC_prv.ulTxSent++;

    EMACTxDMAPollDemand(EMAC0_BASE);
    
    iptraceNETWORK_INTERFACE_TRANSMIT();

    return pdTRUE;
}
/*-------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    BaseType_t x;

    for( x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
    {
        /* pucEthernetBuffer is set to point ipBUFFER_PADDING bytes in from the
        beginning of the allocated buffer. */
        pxNetworkBuffers[ x ].pucEthernetBuffer = &( ucBuffers[ x ][ ipBUFFER_PADDING ] );

        *( ( uint32_t * ) &ucBuffers[ x ][ 0 ] ) = ( uint32_t ) &( pxNetworkBuffers[ x ] );
    }
}
/*-------------------------------------------*/

BaseType_t xGetPhyLinkStatus( void )
{
    #if FORCE_LINK_STATUS_READ_IN_xGetPhyLinkStatus
    {
    uint32_t newLinkStatus;
    /* Check link status */
    newLinkStatus =
            (EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_BMSR) & EPHY_BMSR_LINKSTAT)? 1:0;
    /* Set the link status */
    xEMAC_prv.linkUp = newLinkStatus;
    }
    #endif

    if (xEMAC_prv.linkUp) {
        return pdTRUE;
    }
    else {
        return pdFALSE;
    }
}
/*-------------------------------------------*/

/*
 *  EmacStart
 */
BaseType_t prvEmacStart()
{
    uint16_t value;
    EMACMSP432E4_DriverAttrs const *hwAttrs = &g_EMAC_DriverAttrs;
    HwiP_Params xHwiParams;
    ClockP_FreqHz freq;
    uint32_t key;
    uint32_t pinMap;
    uint8_t  port;
    uint8_t  pin;

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
                               EMAC_CONFIG_BO_LIMIT_1024 ),
                               (DMA_OP_MODE | DMA_ERR_MODE), 
                               0);

    /* Program the MAC address into the Ethernet controller. */
    EMACAddrSet(EMAC0_BASE, 0, (uint8_t *)hwAttrs->macAddress);

    /* Initialize the DMA descriptors. */
    if (prvInitDMADescriptors()==pdFALSE) {
        /*
         *  If fail to initialize DMA descriptor lists:
         *  1. call HwiP_restore
         *  2. call emacStop to clean up
         */
        HwiP_restore(key);
        prvEmacStop();

        return pdFALSE;
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

    HwiP_restore(key);

    /* Create the hardware interrupt */
    HwiP_Params_init(&xHwiParams);
    xHwiParams.priority = hwAttrs->intPriority;

    xEMAC_prv.xHwi = HwiP_create(hwAttrs->intNum,
                                   prv_xHwiIntFxn,
                                   &xHwiParams);

    if (xEMAC_prv.xHwi == NULL) {
        prvEmacStop();
        return pdFALSE;
    }

    return pdTRUE;
}
/*-------------------------------------------*/

/*
 * prvInitDMADescriptors 
 * Initialize the transmit and receive DMA descriptor lists.
 */
static BaseType_t prvInitDMADescriptors(void)
{
    int32_t     i;
    NetworkBufferDescriptor_t  *pxNetworkBuffer;

    /* Reset DMA descriptor lists' indexes to 0 */
    xEMAC_prv.pxTxDescList->ulRead = 0;
    xEMAC_prv.pxTxDescList->ulWrite = 0;
    xEMAC_prv.pxRxDescList->ulRead = 0;
    xEMAC_prv.pxRxDescList->ulWrite = 0;

    /* Transmit list -  mark all descriptors as not owned by the hardware */
    for (i = 0; i < NUM_TX_DESCRIPTORS; i++) {
        g_pTxDescriptors[i].pxNetworkBuffer = NULL;
        g_pTxDescriptors[i].Desc.ui32Count = 0;
        g_pTxDescriptors[i].Desc.pvBuffer1 = 0;
        g_pTxDescriptors[i].Desc.ui32CtrlStatus = 0;
        g_pTxDescriptors[i].Desc.DES3.pLink = ((i == (NUM_TX_DESCRIPTORS - 1)) ?
               &g_pTxDescriptors[0].Desc : &g_pTxDescriptors[i + 1].Desc);
    }

    /*
     * Receive list - tag each descriptor with a buffer and set all fields to
     * allow packets to be received.
     */
    for (i = 0; i < NUM_RX_DESCRIPTORS; i++) {
        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor(GET_BUFFER_SIZE,0);
        if (pxNetworkBuffer) {
            prvPrimeRx(pxNetworkBuffer, &(g_pRxDescriptors[i]));
        }
        else {
            /*
             *  This is a failing scenario return pdFalse.
             */
            g_pRxDescriptors[i].Desc.pvBuffer1 = 0;
            g_pRxDescriptors[i].Desc.ui32CtrlStatus = 0;
            return pdFALSE;
        }
        g_pRxDescriptors[i].Desc.DES3.pLink =
                ((i == (NUM_RX_DESCRIPTORS - 1)) ?
                &g_pRxDescriptors[0].Desc : &g_pRxDescriptors[i + 1].Desc);
    }

    /* Set the descriptor pointers in the hardware. */
    EMACRxDMADescriptorListSet(EMAC0_BASE, &g_pRxDescriptors[0].Desc);
    EMACTxDMADescriptorListSet(EMAC0_BASE, &g_pTxDescriptors[0].Desc);
    return pdTRUE;
}
/*-------------------------------------------*/


/*
 *  prvEmacStop 
 *  The function is used to de-initialize and stop the EMACMSP432E4
 *  controller and device.
 */
static BaseType_t prvEmacStop()
{
    EMACMSP432E4_DriverAttrs const *hwAttrs = &g_EMAC_DriverAttrs;
    uint8_t  port;
    int i = 0;

    EMACIntDisable(EMAC0_BASE, (EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                     EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                     EMAC_INT_RX_STOPPED | EMAC_INT_PHY));

    if (xEMAC_prv.xHwi != NULL) {
        HwiP_delete(xEMAC_prv.xHwi);
    }

    for (i = 0; i < NUM_RX_DESCRIPTORS; i++) {
        if (g_pRxDescriptors[i].pxNetworkBuffer != NULL) {
            vReleaseNetworkBufferAndDescriptor(g_pRxDescriptors[i].pxNetworkBuffer);
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

    return pdTRUE;
}
/*-------------------------------------------*/

/*
 * prvPrimeRx
 */
static void prvPrimeRx(NetworkBufferDescriptor_t *pxNetworkBuffer, DescriptorRef_t *desc)
{
    desc->pxNetworkBuffer = pxNetworkBuffer;
    desc->Desc.ui32Count = DES1_RX_CTRL_CHAINED;

    /* We got a buffer so fill in the payload pointer and size. */
    desc->Desc.pvBuffer1 = pxNetworkBuffer->pucEthernetBuffer;
    desc->Desc.ui32Count |= ((NETWORK_BUFFER_DESCRIPTORS_LEN - 8 )<< DES1_RX_CTRL_BUFF1_SIZE_S);

    /* Give this descriptor back to the hardware */
    desc->Desc.ui32CtrlStatus = DES0_RX_CTRL_OWN;
}
/*-------------------------------------------*/


/*
 * prvHandleRx
 */
static void prvHandleRx()
{
    NetworkBufferDescriptor_t *pxNetworkBuffer;
    NetworkBufferDescriptor_t *pxNetworkBufferNew;
    int32_t          len;
    DescriptorRefList_t *pDescList;
    uint32_t         ulDescEnd;
    int32_t          descCount = -1;
    uint32_t         ui32Config;
    uint32_t         ui32Mode;
    uint32_t         ui32FrameSz;
    uint32_t         ui32CtrlStatus;
    DescriptorRef_t *pxDescRef;

    IPStackEvent_t xRxEvent;

    /* Get a pointer to the receive descriptor list. */
    pDescList = xEMAC_prv.pxRxDescList;

    /* Determine where we start and end our walk of the descriptor list 
     * if the last ulRead was at descriptor 0 then read till NUM_RX_DESCRIPTORS - 1.
     * else take in account to wrap around and read till ulRead -1
     */
    ulDescEnd = pDescList->ulRead ?
            (pDescList->ulRead - 1) : (pDescList->ulNumDescs - 1);

    /* Step through the descriptors that are marked for CPU attention. */
    while (pDescList->ulRead != ulDescEnd) {
        descCount++;
        pxDescRef = &(pDescList->pxDescriptorRef[pDescList->ulRead]);
        /* Does the current descriptor have a buffer attached to it? */
        pxNetworkBuffer = pxDescRef->pxNetworkBuffer;
        if (pxNetworkBuffer) {
            ui32CtrlStatus = pxDescRef->Desc.ui32CtrlStatus; 

            /* Determine who control the descriptor. */
            if (ui32CtrlStatus & DES0_RX_CTRL_OWN) {
                /* The DMA engine still owns the descriptor so we are finished. */
                break;
            }

            #if ( DMA_ERR_FORWARD|(DMA_STORE_FORWARD_RX_OPERATION == 0))
            /* Yes - does the frame contain errors? */
            if (ui32CtrlStatus & DES0_RX_STAT_ERR) {
                /* This is a bad frame.*/

                iptraceETHERNET_RX_EVENT_LOST();
                
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
                             xEMAC_prv.ulRxPayloadChksmErrors++;
                         }
                         /* Else if bit 7 and bit 0 are both set */
                         else if ((ui32CtrlStatus & EMAC_DES0_RX_STAT_IPHDR_CHKSM_ERR) &&
                             (ui32CtrlStatus & EMAC_DES0_RX_STAT_PAYLOAD_CHKSM_ERR)) {
                             /* Checksum error in both IP header & payload */
                             xEMAC_prv.ulRxIpHdrChksmErrors++;
                             xEMAC_prv.ulRxPayloadChksmErrors++;
                        }
                    }
                }
                xEMAC_prv.ulRxDropped++;
                /* we dont' pass the frame to the stack, thus wedon't need a new descriptorbuffer
                 * we can thus reuse the descriptor with the akready present buffer.
                 */
                pxNetworkBufferNew = pxNetworkBuffer;
            }
            else 
            #endif
            if (ipCONSIDER_FRAME_FOR_PROCESSING( pxNetworkBuffer->pucEthernetBuffer ))
            {
            /* This is a good frame so pass it up the stack. */

                /* Allocate a new buffer for this descriptor */
                pxNetworkBufferNew = pxNetworkBufferGetFromISR(GET_BUFFER_SIZE);
                if (pxNetworkBufferNew == NULL) {
                    /*
                     *  Leave the packet in the descriptor and owned by the
                     *  driver. Process when the next interrupt occurs.
                     */
                    iptraceETHERNET_RX_EVENT_LOST();
                    break;
                }

                len = (ui32CtrlStatus &
                    DES0_RX_STAT_FRAME_LENGTH_M) >> DES0_RX_STAT_FRAME_LENGTH_S;

                /* Remove the CRC */
                pxNetworkBuffer->xDataLength= len - CRC_SIZE_BYTES;
                /* Update internal statistic */
                xEMAC_prv.ulRxCount++;
                
                xRxEvent.eEventType = eNetworkRxEvent;

                /* pvData is used to point to the network buffer descriptor that
                references the received data. */
                xRxEvent.pvData = ( void * ) pxNetworkBuffer;

                /* Send the data to the TCP/IP stack. */
                if( prvSendEventStructToIPTaskFromISR( &xRxEvent) == pdFALSE ){
                    /* The buffer could not be sent to the IP task so the buffer
                    must be released. */
                    vNetworkBufferReleaseFromISR( pxNetworkBuffer );

                    iptraceETHERNET_RX_EVENT_LOST();
                }
                else{
                    /* The message was successfully sent to the TCP/IP stack. */
                    iptraceNETWORK_INTERFACE_RECEIVE();
                }                     
            }else 
            {   
                /* we dont' pass the frame to the stack, thus wedon't need a new descriptorbuffer
                 * we can thus reuse the descriptor with the akready present buffer.
                 */
                pxNetworkBufferNew = pxNetworkBuffer;
            }
        }

        /* Prime the receive descriptor back up for future packets */
        prvPrimeRx(pxNetworkBufferNew, pxDescRef);
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
        xEMAC_prv.ulDescriptorLoopCount[descCount]++;
    }
}
/*-------------------------------------------*/


/*
 *   prvProcessTransmitted 
 */

static void prvProcessTransmitted()
{
    DescriptorRef_t *pDesc;
    uint32_t     ulNumDescs;
    /*
     * Walk the list until we have checked all descriptors or we reach the
     * write pointer or find a descriptor that the hardware is still working
     * on.
     */
    for (ulNumDescs = 0; ulNumDescs < NUM_TX_DESCRIPTORS; ulNumDescs++) {
        pDesc = &(xEMAC_prv.pxTxDescList->pxDescriptorRef[xEMAC_prv.pxTxDescList->ulRead]);
        /* Has the buffer attached to this descriptor been transmitted? */
        if (pDesc->Desc.ui32CtrlStatus & DES0_TX_CTRL_OWN) {
            /* No - we're finished. */
            break;
        }
        /* Does this descriptor have a buffer attached to it? */
        if (pDesc->pxNetworkBuffer) {
            /*
            * Check this descriptor for transmit errors
            */
            if (pDesc->Desc.ui32CtrlStatus & DES0_TX_STAT_ERR) {
                /* An error occurred - now look for errors of interest.
                 * Ensure TX Checksum Offload is enabled
                 */
                if (((pDesc->Desc.ui32CtrlStatus & DES0_TX_CTRL_IP_HDR_CHKSUM) ||
                    (pDesc->Desc.ui32CtrlStatus & DES0_TX_CTRL_IP_ALL_CKHSUMS)) &&
                    (pDesc->Desc.ui32CtrlStatus & DES0_TX_STAT_IPH_ERR)) {
                    /* Error inserting IP header checksum */
                    xEMAC_prv.ulTxIpHdrChksmErrors++;
                }

                if (pDesc->Desc.ui32CtrlStatus & DES0_TX_STAT_PAYLOAD_ERR) {
                    /* Error in IP payload checksum (i.e. in UDP, TCP or ICMP) */
                    xEMAC_prv.ulTxPayloadChksmErrors++;
                }
            }
            /* Yes - free it*/
            vNetworkBufferReleaseFromISR(pDesc->pxNetworkBuffer);
            pDesc->pxNetworkBuffer = NULL;
        }
        else {
            /* If the descriptor has no buffer, we are finished. */
            break;
        }

        /* Move on to the next descriptor. Wrap if necessary */
        xEMAC_prv.pxTxDescList->ulRead++;
        if (xEMAC_prv.pxTxDescList->ulRead == NUM_TX_DESCRIPTORS) {
            xEMAC_prv.pxTxDescList->ulRead = 0;
        }
    }
}
/*-------------------------------------------*/


static void prvProcessPhyInterrupt()
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

    /* Has the speed or duplex status changed? */
    if (value & (EPHY_MISR1_SPEED | EPHY_MISR1_DUPLEXM | EPHY_MISR1_ANC)) {
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
    
    /* Has the link status changed? */
    if (value & EPHY_MISR1_LINKSTAT) {
        /* Is link up or down now? */
        if (status & EPHY_STS_LINK) {
            xEMAC_prv.linkUp = 1;
        }
        else {
            xEMAC_prv.linkUp = 0;
            iptraceNETWORK_DOWN()
        }
        /* Signal the stack for this link status change (from ISR) */
        SIGNAL_LINK_CHANGE(xEMAC_prv.linkUp);
    }
}
/*-------------------------------------------*/

/*
 * EMAC ISR routine
 * 
 * this function call:
 * - prvProcessPhyInterrupt in case of PHY Interrupts
 * - prvProcessTransmitted  in case of tx Interrupts
 * - prvHandleRx  in case of rx Interrupts
 */

static void prv_xHwiIntFxn(uintptr_t callbacks)
{
    uint32_t status;

    iptraceNETWORK_EVENT_RECEIVED();

    xEMAC_prv.ulIsrCount++;

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
        xEMAC_prv.ulAbnormalInts++;
    }

    if (status & EMAC_INT_PHY) {
        prvProcessPhyInterrupt();
    }

    /* Process the transmit DMA list, freeing any buffers that have been
     * transmitted since our last interrupt.
     */
    if (status & EMAC_INT_TRANSMIT) {
        prvProcessTransmitted();
    }

    /*
     * Process the receive DMA list and pass all successfully received packets
     * up the stack.  We also call this function in cases where the receiver has
     * stalled due to missing buffers since the receive function will attempt to
     * allocate new pbufs for descriptor entries which have none.
     */
    if (status & (EMAC_INT_RECEIVE | EMAC_INT_RX_NO_BUFFER |
        EMAC_INT_RX_STOPPED)) {
        prvHandleRx();
    }

    EMACIntEnable(EMAC0_BASE, (EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                        EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                        EMAC_INT_RX_STOPPED | EMAC_INT_PHY));
}
/*---------------------------------------*/


/* prvSendEventStructToIPTaskFromISR
 * see xSendEventStructToIPTask in extern/FreeRTOS/FreeRTOS-Plus/Source/FreeRTOS-Plus-TCP/FreeRTOS_IP.c
 * this implementation is only for eNetworkRxEvent events. 
*/
static BaseType_t prvSendEventStructToIPTaskFromISR( const IPStackEvent_t *pxEvent){
        return xQueueSendToBackFromISR( xNetworkEventQueue, pxEvent,pdFALSE );
}
/*---------------------------------------*/

