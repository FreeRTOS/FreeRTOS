/**
 *  \file   emac.h
 *
 *  \brief  EMAC APIs and macros.
 *
 *   This file contains the driver API prototypes and macro definitions.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __EMAC_H__
#define __EMAC_H__

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "sys_common.h"
#include "hw_reg_access.h"
#include "hw_emac.h"
#include "hw_emac_ctrl.h"
#include "mdio.h"
#include "emac_phyConfig.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (1) */
/* USER CODE END */

/*****************************************************************************/
/*
** Macros which can be used as speed parameter to the API EMACRMIISpeedSet
*/
#define EMAC_RMIISPEED_10MBPS           ( 0x00000000U )
#define EMAC_RMIISPEED_100MBPS          ( 0x00008000U )

/* Macros for enabling taken as inputs from HALCoGen GUI. */
#define EMAC_TX_ENABLE                  ( 1U )
#define EMAC_RX_ENABLE                  ( 1U )
#define EMAC_MII_ENABLE                 ( 1U )
#define EMAC_FULL_DUPLEX_ENABLE         ( 1U )
#define EMAC_LOOPBACK_ENABLE            ( 0U )
#define EMAC_BROADCAST_ENABLE           ( 1U )
#define EMAC_UNICAST_ENABLE             ( 1U )
#define EMAC_CHANNELNUMBER              ( 0U )
#define EMAC_PHYADDRESS                 ( 1U )

/*
 * Macros to indicate EMAC Channel Numbers
 */
#define EMAC_CHANNEL_0                  ( 0x00000000U )
#define EMAC_CHANNEL_1                  ( 0x00000001U )
#define EMAC_CHANNEL_2                  ( 0x00000002U )
#define EMAC_CHANNEL_3                  ( 0x00000003U )
#define EMAC_CHANNEL_4                  ( 0x00000004U )
#define EMAC_CHANNEL_5                  ( 0x00000005U )
#define EMAC_CHANNEL_6                  ( 0x00000006U )
#define EMAC_CHANNEL_7                  ( 0x00000007U )
/* Macros which can be used as duplexMode parameter to the API
** EMACDuplexSet
*/
#define EMAC_DUPLEX_FULL                ( 0x00000001U )
#define EMAC_DUPLEX_HALF                ( 0x00000000U )

/*
** Macros which can be used as matchFilt  parameters to the API
** EMACMACAddrSet
*/
/* Address not used to match/filter incoming packets */
#define EMAC_MACADDR_NO_MATCH_NO_FILTER ( 0x00000000U )

/* Address will be used to filter incoming packets */
#define EMAC_MACADDR_FILTER             ( 0x00100000U )

/* Address will be used to match incoming packets */
#define EMAC_MACADDR_MATCH              ( 0x00180000U )

/*
** Macros which can be passed as eoiFlag to EMACRxIntAckToClear API
*/
#define EMAC_INT_CORE0_RX               ( 0x1U )
#define EMAC_INT_CORE1_RX               ( 0x5U )
#define EMAC_INT_CORE2_RX               ( 0x9U )

/*
** Macros which can be passed as eoiFlag to EMACTxIntAckToClear API
*/
#define EMAC_INT_CORE0_TX               ( 0x2U )
#define EMAC_INT_CORE1_TX               ( 0x6U )
#define EMAC_INT_CORE2_TX               ( 0xAU )
/* Base Addresses */
#define EMAC_CTRL_RAM_0_BASE            0xFC520000U
#define EMAC_0_BASE                     0xFCF78000U
#define EMAC_CTRL_0_BASE                0xFCF78800U
#define MDIO_0_BASE                     0xFCF78900U

/*MAC address length*/
#define EMAC_HWADDR_LEN                 6U
#define MAX_EMAC_INSTANCE               1U
#define SIZE_EMAC_CTRL_RAM              0x2000U
#define MAX_TRANSFER_UNIT               1514U
#define MAX_RX_PBUF_ALLOC               ( 10U )
#define MIN_PKT_LEN                     60U
#define MIN_PACKET_SIZE                 ( 46U )

#define EMAC_BUF_DESC_OWNER             0x20000000U
#define EMAC_BUF_DESC_SOP               0x80000000U
#define EMAC_BUF_DESC_EOP               0x40000000U
#define EMAC_BUF_DESC_EOQ               0x10000000U

#define EMAC_NETSTATREGS( n )           ( ( uint32 ) 0x200U + ( uint32 ) ( ( n ) * 4U ) )

/* Error Signalling Macros */
#define EMAC_ERR_CONNECT                0x2U /* Not connected.  */
#define EMAC_ERR_OK                     0x1U /* No error, everything OK. */

/* Macros for Configuration Value Registers */
#define EMAC_TXCONTROL_CONFIGVALUE      0x00000001U
#define EMAC_RXCONTROL_CONFIGVALUE      0x00000001U
#define EMAC_TXINTMASKSET_CONFIGVALUE   0x00000001U
#define EMAC_TXINTMASKCLEAR_CONFIGVALUE 0x00000001U
#define EMAC_RXINTMASKSET_CONFIGVALUE   0x00000001U
#define EMAC_RXINTMASKCLEAR_CONFIGVALUE 0x00000001U
#define EMAC_MACSRCADDRHI_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0xFFU << 24U ) | ( uint32 ) ( ( uint32 ) 0xFFU << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0xFFU << 8U ) | ( uint32 ) ( ( uint32 ) 0xFFU ) )
#define EMAC_MACSRCADDRLO_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) 0xFFU << 8U ) | ( uint32 ) ( ( uint32 ) 0xFFU ) )
#define EMAC_MDIOCONTROL_CONFIGVALUE 0x4114001FU
#define EMAC_C0RXEN_CONFIGVALUE      0x00000001U
#define EMAC_C0TXEN_CONFIGVALUE      0x00000001U

/* Structure to store pending status from the Tx Interrupt Status Registers. */
typedef struct emac_tx_int_status
{
    volatile uint32 intstatmasked; /* Pending interrupt status read from the Transmit
                                      Interrupt Status (Masked) Register (TXINTSTATMASKED)
                                    */
    volatile uint32 intstatraw;    /* Pending interrupt status read from the Transmit
                                      Interrupt Status (Unmasked) Register (TXINTSTATRAW) */
} emac_tx_int_status_t;

/* Structure to store pending status from the Rx Interrupt Status Registers. */
typedef struct emac_rx_int_status
{
    volatile uint32 intstatmasked_pend; /* Reads RXnPEND value from the Receive Interrupt
                                           Status (Unmasked) Register (RXINTSTATRAW) */
    volatile uint32 intstatmasked_threshpend; /* Reads RXnTRHESHPEND value from the
                                                 Receive Interrupt Status (Unmasked)
                                                 Register (RXINTSTATRAW) */

    volatile uint32 intstatraw_pend; /* Reads RXnPEND value from the Receive Interrupt
                                        Status (Unmasked) Register (RXINTSTATRAW) */
    volatile uint32 intstatraw_threshpend; /* Reads RXnTRHESHPEND value from the Receive
                                              Interrupt Status (Unmasked) Register
                                              (RXINTSTATRAW) */

} emac_rx_int_status_t;

/* EMAC TX Buffer descriptor data structure - Refer TRM for details about the buffer
 * descriptor structure.*/
typedef struct emac_tx_bd
{
    volatile struct emac_tx_bd * next;
    volatile uint32 bufptr;       /* Pointer to the actual Buffer storing the data to be
                                     transmitted. */
    volatile uint32 bufoff_len;   /*Buffer Offset and Buffer Length (16 bits each) */
    volatile uint32 flags_pktlen; /*Status flags and Packet Length. (16 bits each)*/
} emac_tx_bd_t;

/* EMAC RX Buffer descriptor data structure - Refer TRM for details about the buffer
 * descriptor structure. */
typedef struct emac_rx_bd
{
    volatile struct emac_rx_bd * next; /*Used as a pointer for next element in the linked
                                          list of descriptors.*/
    volatile uint32 bufptr; /*Pointer to the actual Buffer which will store the received
                               data.*/
    volatile uint32 bufoff_len;   /*Buffer Offset and Buffer Length (16 bits each)*/
    volatile uint32 flags_pktlen; /*Status flags and Packet Length. (16 bits each)*/
} emac_rx_bd_t;

/**
 * Helper struct to hold the data used to operate on a particular
 * receive channel
 */
typedef struct rxch_struct
{
    volatile emac_rx_bd_t * free_head; /*Used to point to the free buffer descriptor which
                                          can receive new data.*/
    volatile emac_rx_bd_t * active_head; /*Used to point to the active descriptor in the
                                            chain which is receiving.*/
    volatile emac_rx_bd_t * active_tail; /*Used to point to the last descriptor in the
                                            chain.*/
} rxch_t;

/**
 * Helper struct to hold the data used to operate on a particular
 * transmit channel
 */
typedef struct txch_struct
{
    volatile emac_tx_bd_t * free_head; /*Used to point to the free buffer descriptor which
                                          can transmit new data.*/
    volatile emac_tx_bd_t * active_tail; /*Used to point to the last descriptor in the
                                            chain.*/
    volatile emac_tx_bd_t * next_bd_to_process; /*Used to point to the next descriptor in
                                                   the chain to be processed.*/
} txch_t;
/**
 * Helper struct to hold private data used to operate the ethernet interface.
 */
typedef struct hdkif_struct
{
    /* MAC Address of the Module. */
    uint8_t mac_addr[ 6 ];

    /* emac base address */
    uint32 emac_base;

    /* emac controller base address */
    volatile uint32 emac_ctrl_base;
    volatile uint32 emac_ctrl_ram;

    /* mdio base address */
    volatile uint32 mdio_base;

    /* phy parameters for this instance - for future use */
    uint32 phy_addr;
    boolean ( *phy_autoneg )( uint32 param1, uint32 param2, uint16 param3 );
    boolean ( *phy_partnerability )( uint32 param4, uint32 param5, uint16 * param6 );

    /* The tx/rx channels for the interface */
    txch_t txchptr;
    rxch_t rxchptr;
} hdkif_t;

/*Ethernet Frame Structure */
typedef struct ethernet_frame
{
    uint8 dest_addr[ 6 ]; /* Destination MAC Address */
    uint8 src_addr[ 6 ];  /*Source MAC Address. */
    uint16 frame_length;  /* Data Frame Length */
    uint8 data[ 1500 ];   /* Data */
} ethernet_frame_t;

/* Struct used to take packet data input from the user for transmit APIs. */
typedef struct pbuf_struct
{
    /** next pbuf in singly linked pbuf chain */
    struct pbuf_struct * next;

    /**
     * Pointer to the actual ethernet packet/packet fragment to be transmitted.
     * The packet needs to be in the following format:
     * |Destination MAC Address (6 bytes)| Source MAC Address (6 bytes)| Length/Type (2
     *bytes)| Data (46- 1500 bytes) The data can be split up over multiple pbufs which are
     *linked as a linked list.
     **/
    uint8 * payload;

    /**
     * total length of this buffer and all next buffers in chain
     * belonging to the same packet.
     *
     * For non-queue packet chains this is the invariant:
     * p->tot_len == p->len + (p->next? p->next->tot_len: 0)
     */
    uint16 tot_len;

    /** length of this buffer */
    uint16 len;

} pbuf_t;

/* Structure to hold the values of the EMAC Configuration Registers. */
typedef struct emac_config_reg_struct
{
    /* EMAC Module Register Values */
    uint32 TXCONTROL;      /* Transmit Control Register. */
    uint32 RXCONTROL;      /* Receive Control Register */
    uint32 TXINTMASKSET;   /* Transmit Interrupt Mask Set Register */
    uint32 TXINTMASKCLEAR; /* Transmit Interrupt Clear Register */
    uint32 RXINTMASKSET;   /* Receive Interrupt Mask Set Register */
    uint32 RXINTMASKCLEAR; /*Receive Interrupt Mask Clear Register*/
    uint32 MACSRCADDRHI;   /*MAC Source Address High Bytes Register*/
    uint32 MACSRCADDRLO;   /*MAC Source Address Low Bytes Register*/

    /*MDIO Module Registers */
    uint32 MDIOCONTROL; /*MDIO Control Register. */

    /* EMAC Control Module Registers */
    uint32 C0RXEN; /*EMAC Control Module Receive Interrupt Enable Register*/
    uint32 C0TXEN; /*EMAC Control Module Transmit Interrupt Enable Register*/
} emac_config_reg_t;
/*****************************************************************************/
/**
 *  @defgroup EMACMDIO EMAC/MDIO
 *  @brief Ethernet Media Access Controller/Management Data Input/Output.
 *
 *  The EMAC controls the flow of packet data from the system to the PHY. The MDIO module
 *controls PHY configuration and status monitoring.
 *
 *  Both the EMAC and the MDIO modules interface to the system core through a custom
 *interface that allows efficient data transmission and reception. This custom interface
 *is referred to as the EMAC control module and is considered integral to the EMAC/MDIO
 *peripheral
 *
 *	Related Files
 *   - emac.h
 *   - emac.c
 *   - hw_emac.h
 *   - hw_emac_ctrl.h
 *   - hw_mdio.h
 *   - hw_reg_access.h
 *   - mdio.h
 *   - mdio.c
 *  @addtogroup EMACMDIO
 *  @{
 */
/*
** Prototypes for the APIs
*/
extern uint32 EMACLinkSetup( hdkif_t * hdkif );
extern void EMACInstConfig( hdkif_t * hdkif );
extern void EMACTxIntPulseEnable( uint32 emacBase,
                                  uint32 emacCtrlBase,
                                  uint32 ctrlCore,
                                  uint32 channel );
extern void EMACTxIntPulseDisable( uint32 emacBase,
                                   uint32 emacCtrlBase,
                                   uint32 ctrlCore,
                                   uint32 channel );
extern void EMACRxIntPulseEnable( uint32 emacBase,
                                  uint32 emacCtrlBase,
                                  uint32 ctrlCore,
                                  uint32 channel );
extern void EMACRxIntPulseDisable( uint32 emacBase,
                                   uint32 emacCtrlBase,
                                   uint32 ctrlCore,
                                   uint32 channel );
extern void EMACRMIISpeedSet( uint32 emacBase, uint32 speed );
extern void EMACDuplexSet( uint32 emacBase, uint32 duplexMode );
extern void EMACTxEnable( uint32 emacBase );
extern void EMACTxDisable( uint32 emacBase );
extern void EMACRxEnable( uint32 emacBase );
extern void EMACRxDisable( uint32 emacBase );
uint32 EMACSwizzleData( uint32 word );
extern void EMACTxHdrDescPtrWrite( uint32 emacBase, uint32 descHdr, uint32 channel );
extern void EMACRxHdrDescPtrWrite( uint32 emacBase, uint32 descHdr, uint32 channel );
extern void EMACInit( uint32 emacCtrlBase, uint32 emacBase );
extern void EMACMACSrcAddrSet( uint32 emacBase, uint8 macAddr[ 6 ] );
extern void EMACMACAddrSet( uint32 emacBase,
                            uint32 channel,
                            uint8 macAddr[ 6 ],
                            uint32 matchFilt );
extern void EMACMIIEnable( uint32 emacBase );
extern void EMACMIIDisable( uint32 emacBase );
extern void EMACRxUnicastSet( uint32 emacBase, uint32 channel );
extern void EMACRxUnicastClear( uint32 emacBase, uint32 channel );
extern void EMACCoreIntAck( uint32 emacBase, uint32 eoiFlag );
extern void EMACTxCPWrite( uint32 emacBase, uint32 channel, uint32 comPtr );
extern void EMACRxCPWrite( uint32 emacBase, uint32 channel, uint32 comPtr );
extern void EMACRxBroadCastEnable( uint32 emacBase, uint32 channel );
extern void EMACRxBroadCastDisable( uint32 emacBase, uint32 channel );
extern void EMACRxMultiCastEnable( uint32 emacBase, uint32 channel );
extern void EMACRxMultiCastDisable( uint32 emacBase, uint32 channel );
extern void EMACNumFreeBufSet( uint32 emacBase, uint32 channel, uint32 nBuf );
extern uint32 EMACIntVectorGet( uint32 emacBase );
uint32 EMACHWInit( uint8_t macaddr[ 6U ] );
void EMACTxTeardown( uint32 emacBase, uint32 channel );
void EMACRxTeardown( uint32 emacBase, uint32 channel );
void EMACFrameSelect( uint32 emacBase, uint64 hashTable );
void EMACTxPrioritySelect( uint32 emacBase, uint32 txPType );
void EMACSoftReset( uint32 emacCtrlBase, uint32 emacBase );
void EMACEnableIdleState( uint32 emacBase );
void EMACDisableIdleState( uint32 emacBase );
void EMACEnableLoopback( uint32 emacBase );
void EMACDisableLoopback( uint32 emacBase );
void EMACTxFlowControlEnable( uint32 emacBase );
void EMACTxFlowControlDisable( uint32 emacBase );
void EMACRxFlowControlEnable( uint32 emacBase );
void EMACRxFlowControlDisable( uint32 emacBase );
void EMACRxSetFlowThreshold( uint32 emacBase, uint32 channel, uint32 threshold );
uint32 EMACReadNetStatRegisters( uint32 emacBase, uint32 statRegNo );
void EMACDMAInit( hdkif_t * hdkif );
boolean EMACTransmit( hdkif_t * hdkif, pbuf_t * pbuf );
void EMACTxIntHandler( hdkif_t * hdkif );
void EMACReceive( hdkif_t * hdkif );
/* Notification Function to which received packets are passed after processing */
void emacTxNotification( hdkif_t * hdkif );
void emacRxNotification( hdkif_t * hdkif );
void EMACTxIntStat( uint32 emacBase, uint32 channel, emac_tx_int_status_t * txintstat );
void EMACRxIntStat( uint32 emacBase, uint32 channel, emac_rx_int_status_t * rxintstat );
void EMACGetConfigValue( emac_config_reg_t * config_reg, config_value_type_t type );

/* USER CODE BEGIN (2) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif

/**@}*/
#endif /* __EMAC_H__ */
