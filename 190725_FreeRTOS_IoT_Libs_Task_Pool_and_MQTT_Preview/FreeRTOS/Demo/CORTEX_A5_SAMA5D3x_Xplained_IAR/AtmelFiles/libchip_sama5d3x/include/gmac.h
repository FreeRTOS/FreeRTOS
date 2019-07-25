/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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

/** \file */

/** \addtogroup gmac_module
 * @{
 * Provides the interface to configure and use the GMAC peripheral.
 *
 * \section gmac_usage Usage
 * - Configure Gmac::GMAC_NCFG with GMAC_Configure(), some of related controls
 *   are also available, such as:
 *   - GMAC_SetSpeed(): Setup GMAC working clock.
 *   - GMAC_FullDuplexEnable(): Working in full duplex or not.
 *   - GMAC_CpyAllEnable(): Copying all valid frames (\ref GMAC_NCFG_CAF).
 *   - ...
 * - Setup Gmac::GMAC_NCR with GMAC_NetworkControl(), more related controls
 *   can modify with:
 *   - GMAC_ReceiveEnable(): Enable/Disable Rx.
 *   - GMAC_TransmitEnable(): Enable/Disable Tx.
 *   - GMAC_BroadcastDisable(): Enable/Disable broadcast receiving.
 *   - ...
 * - Manage GMAC interrupts with GMAC_EnableIt(), GMAC_DisableIt(),
 *   GMAC_GetItMask() and GMAC_GetItStatus().
 * - Manage GMAC Tx/Rx status with GMAC_GetTxStatus(), GMAC_GetRxStatus()
 *   GMAC_ClearTxStatus() and GMAC_ClearRxStatus().
 * - Manage GMAC Queue with GMAC_SetTxQueue(), GMAC_GetTxQueue(),
 *   GMAC_SetRxQueue() and GMAC_GetRxQueue(), the queue descriptor can define
 *   by \ref sGmacRxDescriptor and \ref sGmacTxDescriptor.
 * - Manage PHY through GMAC is performed by
 *   - GMAC_ManagementEnable(): Enable/Disable PHY management.
 *   - GMAC_PHYMaintain(): Execute PHY management commands.
 *   - GMAC_PHYData(): Return PHY management data.
 *   - GMAC_IsIdle(): Check if PHY is idle.
 * - Setup GMAC parameters with following functions:
 *   - GMAC_SetHash(): Set Hash value.
 *   - GMAC_SetAddress(): Set MAC address.
 * - Enable/Disable GMAC transceiver clock via GMAC_TransceiverClockEnable()
 * - Switch GMAC MII/RMII mode through GMAC_RMIIEnable()
 *
 * For more accurate information, please look at the GMAC section of the
 * Datasheet.
 *
 * \sa \ref gmacd_module
 *
 * Related files:\n
 * gmac.c\n
 * gmac.h.\n
 *
 *   \defgroup gmac_defines GMAC Defines
 *   \defgroup gmac_structs GMAC Data Structs
 *   \defgroup gmac_functions GMAC Functions
 */
/**@}*/

#ifndef _GMAC_H
#define _GMAC_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

#include <stdint.h>

#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Defines
 *----------------------------------------------------------------------------*/
/** \addtogroup gmac_defines
        @{*/

/// Board GMAC base address

/// Number of buffer for RX, be carreful: MUST be 2^n
#define GRX_BUFFERS  16
/// Number of buffer for TX, be carreful: MUST be 2^n
#define GTX_BUFFERS   8

/// Buffer Size
#define GMAC_RX_UNITSIZE            128     /// Fixed size for RX buffer
#define GMAC_TX_UNITSIZE            1518    /// Size for ETH frame length

// The MAC can support frame lengths up to 1536 bytes.
#define GMAC_FRAME_LENTGH_MAX       1536

//
#define GMAC_DUPLEX_HALF 0
#define GMAC_DUPLEX_FULL 1

//
#define GMAC_SPEED_10M      0
#define GMAC_SPEED_100M     1
#define GMAC_SPEED_1000M    2
/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/
/** \addtogroup gmac_structs
        @{*/
/** Receive buffer descriptor struct */
typedef struct _GmacRxDescriptor {
    union _GmacRxAddr {
        uint32_t val;
        struct _GmacRxAddrBM {
            uint32_t bOwnership:1,  /**< User clear, GMAC set this to one once
                                         it has successfully written a frame to
                                         memory */
                     bWrap:1,       /**< Marks last descriptor in receive buffer */
                     addrDW:30;     /**< Address in number of DW */
        } bm;
    } addr;                    /**< Address, Wrap & Ownership */
    union _GmacRxStatus {
        uint32_t val;
        struct _GmacRxStatusBM {
            uint32_t len:12,                /** Length of frame including FCS */
                     offset:2,              /** Receive buffer offset,
                                                bits 13:12 of frame length for jumbo
                                                frame */
                     bSof:1,                /** Start of frame */
                     bEof:1,                /** End of frame */
                     bCFI:1,                /** Concatenation Format Indicator */
                     vlanPriority:3,        /** VLAN priority (if VLAN detected) */
                     bPriorityDetected:1,   /** Priority tag detected */
                     bVlanDetected:1,       /**< VLAN tag detected */
                     bTypeIDMatch:1,        /**< Type ID match */
                     bAddr4Match:1,         /**< Address register 4 match */
                     bAddr3Match:1,         /**< Address register 3 match */
                     bAddr2Match:1,         /**< Address register 2 match */
                     bAddr1Match:1,         /**< Address register 1 match */
                     reserved:1,
                     bExtAddrMatch:1,       /**< External address match */
                     bUniHashMatch:1,       /**< Unicast hash match */
                     bMultiHashMatch:1,     /**< Multicast hash match */
                     bBroadcastDetected:1;  /**< Global all ones broadcast
                                                 address detected */
        } bm;
    } status;
} sGmacRxDescriptor;    /* GCC */

/** Transmit buffer descriptor struct */
typedef struct _GmacTxDescriptor {
    uint32_t addr;
    union _GmacTxStatus {
        uint32_t val;
        struct _GmacTxStatusBM {
            uint32_t len:11,        /**< Length of buffer */
                     reserved:4,
                     bLastBuffer:1, /**< Last buffer (in the current frame) */
                     bNoCRC:1,      /**< No CRC */
                     reserved1:10,
                     bExhausted:1,  /**< Buffer exhausted in mid frame */
                     bUnderrun:1,   /**< Transmit underrun */
                     bError:1,      /**< Retry limit exceeded, error detected */
                     bWrap:1,       /**< Marks last descriptor in TD list */
                     bUsed:1;       /**< User clear, GMAC sets this once a frame
                                         has been successfully transmitted */
        } bm;
    } status;
} sGmacTxDescriptor;     /* GCC */

/**     @}*/

//-----------------------------------------------------------------------------
//         PHY Exported functions
//-----------------------------------------------------------------------------
extern uint8_t GMAC_IsIdle(Gmac *pGmac);
extern void GMAC_PHYMaintain(Gmac      *pGmac,
                             uint8_t   bPhyAddr,
                             uint8_t   bRegAddr,
                             uint8_t   bRW,
                             uint16_t  wData);
extern uint16_t GMAC_PHYData(Gmac *pGmac);
extern void GMAC_ClearStatistics(Gmac *pGmac);
extern void GMAC_IncreaseStatistics(Gmac *pGmac);
extern void GMAC_StatisticsWriteEnable(Gmac *pGmac, uint8_t bEnaDis);
extern uint8_t GMAC_SetMdcClock(Gmac *pGmac, uint32_t mck );
extern void GMAC_EnableMdio(Gmac *pGmac );
extern void GMAC_DisableMdio(Gmac *pGmac );
extern void GMAC_EnableMII(Gmac *pGmac );
extern void GMAC_EnableRMII(Gmac *pGmac );
extern void GMAC_EnableGMII( Gmac *pGmac );
extern void GMAC_SetLinkSpeed(Gmac *pGmac, uint8_t speed, uint8_t fullduplex);
extern void GMAC_EnableIt(Gmac *pGmac, uint32_t dwSources);
extern void GMAC_DisableIt(Gmac *pGmac, uint32_t dwSources);
extern uint32_t GMAC_GetItStatus(Gmac *pGmac);
extern uint32_t GMAC_GetItMask(Gmac *pGmac);
extern uint32_t GMAC_GetTxStatus(Gmac *pGmac);
extern void GMAC_ClearTxStatus(Gmac *pGmac, uint32_t dwStatus);
extern uint32_t GMAC_GetRxStatus(Gmac *pGmac);
extern void GMAC_ClearRxStatus(Gmac *pGmac, uint32_t dwStatus);
extern void GMAC_ReceiveEnable(Gmac* pGmac, uint8_t bEnaDis);
extern void GMAC_TransmitEnable(Gmac *pGmac, uint8_t bEnaDis);
extern void GMAC_SetRxQueue(Gmac *pGmac, uint32_t dwAddr);
extern uint32_t GMAC_SetLocalLoopBack(Gmac *pGmac);
extern uint32_t GMAC_GetRxQueue(Gmac *pGmac);
extern void GMAC_SetTxQueue(Gmac *pGmac, uint32_t dwAddr);
extern uint32_t GMAC_GetTxQueue(Gmac *pGmac);
extern void GMAC_NetworkControl(Gmac *pGmac, uint32_t bmNCR);
extern uint32_t GMAC_GetNetworkControl(Gmac *pGmac);
extern void GMAC_SetAddress(Gmac *pGmac, uint8_t bIndex, uint8_t *pMacAddr);
extern void GMAC_SetAddress32(Gmac *pGmac, uint8_t bIndex, uint32_t dwMacT, uint32_t dwMacB);
extern void GMAC_SetAddress64(Gmac *pGmac, uint8_t bIndex, uint64_t ddwMac);
extern void GMAC_Configure(Gmac *pGmac, uint32_t dwCfg);
extern uint32_t GMAC_GetConfigure(Gmac *pGmac);
extern void GMAC_TransmissionStart(Gmac *pGmac);
extern void GMAC_TransmissionHalt(Gmac *pGmac);
extern void GMAC_EnableRGMII(Gmac *pGmac, uint32_t duplex, uint32_t speed);
#endif // #ifndef GMAC_H

