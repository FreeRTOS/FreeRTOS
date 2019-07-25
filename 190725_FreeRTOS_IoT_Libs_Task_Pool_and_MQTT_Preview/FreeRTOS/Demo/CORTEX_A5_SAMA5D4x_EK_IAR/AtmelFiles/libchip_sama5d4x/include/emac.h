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

/** \file */

/** \addtogroup emac_module
 * @{
 * Provides the interface to configure and use the EMAC peripheral.
 *
 * \section emac_usage Usage
 * - Configure Emac::EMAC_NCFG with EMAC_Configure(), some of related controls
 *   are also available, such as:
 *   - EMAC_SetSpeed(): Setup EMAC working clock.
 *   - EMAC_FullDuplexEnable(): Working in full duplex or not.
 *   - EMAC_CpyAllEnable(): Copying all valid frames (\ref EMAC_NCFG_CAF).
 *   - ...
 * - Setup Emac::EMAC_NCR with EMAC_NetworkControl(), more related controls
 *   can modify with:
 *   - EMAC_ReceiveEnable(): Enable/Disable Rx.
 *   - EMAC_TransmitEnable(): Enable/Disable Tx.
 *   - EMAC_BroadcastDisable(): Enable/Disable broadcast receiving.
 *   - ...
 * - Manage EMAC interrupts with EMAC_EnableIt(), EMAC_DisableIt(),
 *   EMAC_GetItMask() and EMAC_GetItStatus().
 * - Manage EMAC Tx/Rx status with EMAC_GetTxStatus(), EMAC_GetRxStatus()
 *   EMAC_ClearTxStatus() and EMAC_ClearRxStatus().
 * - Manage EMAC Queue with EMAC_SetTxQueue(), EMAC_GetTxQueue(),
 *   EMAC_SetRxQueue() and EMAC_GetRxQueue(), the queue descriptor can define
 *   by \ref sEmacRxDescriptor and \ref sEmacTxDescriptor.
 * - Manage PHY through EMAC is performed by
 *   - EMAC_ManagementEnable(): Enable/Disable PHY management.
 *   - EMAC_PHYMaintain(): Execute PHY management commands.
 *   - EMAC_PHYData(): Return PHY management data.
 *   - EMAC_IsIdle(): Check if PHY is idle.
 * - Setup EMAC parameters with following functions:
 *   - EMAC_SetHash(): Set Hash value.
 *   - EMAC_SetAddress(): Set MAC address.
 * - Enable/Disable EMAC transceiver clock via EMAC_TransceiverClockEnable()
 * - Switch EMAC MII/RMII mode through EMAC_RMIIEnable()
 *
 * For more accurate information, please look at the EMAC section of the
 * Datasheet.
 *
 * \sa \ref emacd_module
 *
 * Related files:\n
 * emac.c\n
 * emac.h.\n
 *
 *   \defgroup emac_defines EMAC Defines
 *   \defgroup emac_structs EMAC Data Structs
 *   \defgroup emac_functions EMAC Functions
 */
/**@}*/

#ifndef _EMAC_H
#define _EMAC_H

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
/** \addtogroup emac_defines
        @{*/

/** The buffer addresses written into the descriptors must be aligned so the
    last few bits are zero.  These bits have special meaning for the EMAC
    peripheral and cannot be used as part of the address. */
#define EMAC_RXD_ADDR_MASK      0xFFFFFFFC
#define EMAC_RXD_bmWRAP         (1ul << 1)  /**< Wrap bit */
#define EMAC_RXD_bmOWNERSHIP    (1ul << 0)  /**< Ownership bit */

#define EMAC_RXD_bmBROADCAST    (1ul << 31) /**< Broadcast detected */
#define EMAC_RXD_bmMULTIHASH    (1ul << 30) /**< Multicast hash match */
#define EMAC_RXD_bmUNIHASH      (1ul << 29) /**< Unicast hash match */
#define EMAC_RXD_bmEXTADDR      (1ul << 28) /**< External address match */
#define EMAC_RXD_bmADDR1        (1ul << 26) /**< Address 1 match */
#define EMAC_RXD_bmADDR2        (1ul << 25) /**< Address 2 match */
#define EMAC_RXD_bmADDR3        (1ul << 24) /**< Address 3 match */
#define EMAC_RXD_bmADDR4        (1ul << 23) /**< Address 4 match */
#define EMAC_RXD_bmTYPE         (1ul << 22) /**< Type ID match */
#define EMAC_RXD_bmVLAN         (1ul << 21) /**< VLAN tag detected */
#define EMAC_RXD_bmPRIORITY     (1ul << 20) /**< Prority tag detected */
#define EMAC_RXD_PRIORITY_MASK  (3ul << 17) /**< VLAN prority */
#define EMAC_RXD_bmCFI          (1ul << 16) /**< Concatenation Format Indicator
                                                 only if bit 21 is set */
#define EMAC_RXD_bmEOF          (1ul << 15) /**< End of frame */
#define EMAC_RXD_bmSOF          (1ul << 14) /**< Start of frame */
#define EMAC_RXD_OFFSET_MASK                /**< Receive buffer offset */
#define EMAC_RXD_LEN_MASK       (0xFFF)     /**< Length of frame including FCS
                                                 (if selected) */
#define EMAC_RXD_LENJUMBO_MASK  (0x3FFF)    /**< Jumbo frame length */

#define EMAC_TXD_bmUSED         (1ul << 31) /**< Frame is transmitted */
#define EMAC_TXD_bmWRAP         (1ul << 30) /**< Last descriptor */
#define EMAC_TXD_bmERROR        (1ul << 29) /**< Retry limit exceed, error */
#define EMAC_TXD_bmUNDERRUN     (1ul << 28) /**< Transmit underrun */
#define EMAC_TXD_bmEXHAUSTED    (1ul << 27) /**< Buffer exhausted */
#define EMAC_TXD_bmNOCRC        (1ul << 16) /**< No CRC */
#define EMAC_TXD_bmLAST         (1ul << 15) /**< Last buffer in frame */
#define EMAC_TXD_LEN_MASK       (0x7FF)     /**< Length of buffer */


/** The MAC can support frame lengths up to 1536 bytes. */
#define EMAC_FRAME_LENTGH_MAX       1536

/**     @}*/
/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/
/** \addtogroup emac_structs
        @{*/
#ifdef __ICCARM__          // IAR
#define PACKED_ATTR 
#elif defined (  __GNUC__  ) /* GCC CS3 */
#define PACKED_ATTR     __attribute__((packed, aligned(8))) 
#endif                     

/** Receive buffer descriptor struct */
typedef struct _EmacRxDescriptor {
    union _EmacRxAddr {
        uint32_t val;
        struct _EmacRxAddrBM {
            uint32_t bOwnership:1,  /**< User clear, EMAC set this to one once
                                         it has successfully written a frame to
                                         memory */
                     bWrap:1,       /**< Marks last descriptor in receive buffer */
                     addrDW:30;     /**< Address in number of DW */
        } bm;
    } addr;                    /**< Address, Wrap & Ownership */
    union _EmacRxStatus {
        uint32_t val;
        struct _EmacRxStatusBM {
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
}PACKED_ATTR sEmacRxDescriptor;    /* GCC */

/** Transmit buffer descriptor struct */
typedef struct _EmacTxDescriptor {
    uint32_t addr;
    union _EmacTxStatus {
        uint32_t val;
        struct _EmacTxStatusBM {
            uint32_t len:11,        /**< Length of buffer */
                     reserved:4,
                     bLastBuffer:1, /**< Last buffer (in the current frame) */
                     bNoCRC:1,      /**< No CRC */
                     reserved1:10,
                     bExhausted:1,  /**< Buffer exhausted in mid frame */
                     bUnderrun:1,   /**< Transmit underrun */
                     bError:1,      /**< Retry limit exceeded, error detected */
                     bWrap:1,       /**< Marks last descriptor in TD list */
                     bUsed:1;       /**< User clear, EMAC sets this once a frame
                                         has been successfully transmitted */
        } bm;
    } status;
} PACKED_ATTR sEmacTxDescriptor;     /* GCC */

/**     @}*/
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/** \addtogroup emac_functions
        @{*/
extern void EMAC_NetworkControl(Emac *pEmac, uint32_t bmNCR);
extern uint32_t EMAC_GetNetworkControl(Emac * pEmac);
extern void EMAC_ReceiveEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_TransmitEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_ManagementEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_ClearStatistics(Emac * pEmac);
extern void EMAC_IncreaseStatistics(Emac * pEmac);
extern void EMAC_StatisticsWriteEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_BackPressureEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_TransmissionStart(Emac * pEmac);
extern void EMAC_TransmissionHalt(Emac * pEmac);

extern void EMAC_Configure(Emac * pEmac,uint32_t dwCfg);
extern uint32_t EMAC_GetConfigure(Emac * pEmac);
extern void EMAC_SetSpeed(Emac * pEmac,uint8_t bSpeed);
extern void EMAC_FullDuplexEnable(Emac * pEmac,uint8_t bFD);
extern void EMAC_CpyAllEnable(Emac * pEmac,uint8_t bCAF);
extern void EMAC_JumboFrameEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_BroadcastDisable(Emac * pEmac,uint8_t bDisEna);
extern void EMAC_MulticastHashEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_BigFrameEnable(Emac * pEmac,uint8_t bEnaDis);
extern uint8_t EMAC_SetClock(Emac * pEmac,uint32_t dwMck);
extern void EMAC_RetryTestEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_PauseFrameEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_SetRxBufferOffset(Emac * pEmac,uint8_t bOffset);
extern void EMAC_RxLenthCheckEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_DiscardFCSEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_EFRHD(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_IRXFCS(Emac * pEmac,uint8_t bEnaDis);

extern uint32_t EMAC_GetStatus(Emac * pEmac);
extern uint8_t EMAC_GetMDIO(Emac * pEmac);
extern uint8_t EMAC_IsIdle(Emac * pEmac);

extern uint32_t EMAC_GetTxStatus(Emac * pEmac);
extern void EMAC_ClearTxStatus(Emac * pEmac,uint32_t dwStatus);

extern uint32_t EMAC_GetRxStatus(Emac * pEmac);
extern void EMAC_ClearRxStatus(Emac * pEmac,uint32_t dwStatus);

extern void EMAC_SetTxQueue(Emac * pEmac,uint32_t dwAddr);
extern uint32_t EMAC_GetTxQueue(Emac * pEmac);

extern void EMAC_SetRxQueue(Emac * pEmac,uint32_t dwAddr);
extern uint32_t EMAC_GetRxQueue(Emac * pEmac);

extern void EMAC_EnableIt(Emac * pEmac,uint32_t dwSources);
extern void EMAC_DisableIt(Emac * pEmac,uint32_t dwSources);
extern uint32_t EMAC_GetItMask(Emac * pEmac);
extern uint32_t EMAC_GetItStatus(Emac * pEmac);

extern void EMAC_PHYMaintain(Emac * pEmac,
                             uint8_t bPhyAddr, uint8_t bRegAddr,
                             uint8_t bRW,
                             uint16_t wData);
extern uint16_t EMAC_PHYData(Emac * pEmac);

extern void EMAC_SetPauseTime(Emac * pEmac,uint16_t wPTime);

extern void EMAC_SetHash(Emac * pEmac,uint32_t dwHashTop,uint32_t dwHashBottom);
extern void EMAC_SetHash64(Emac * pEmac,uint64_t ddwHash);

extern void EMAC_SetAddress(Emac * pEmac,uint8_t bIndex,uint8_t * pMacAddr);
extern void EMAC_SetAddress32(Emac * pEmac,uint8_t bIndex,
                              uint32_t dwMacT,uint32_t dwMacB);
extern void EMAC_SetAddress64(Emac * pEmac,uint8_t bIndex,uint64_t ddwMac);

extern void EMAC_SetTypeID(Emac * pEmac,uint16_t wTID);
extern uint16_t EMAC_GetTypeID(Emac * pEmac);

extern void EMAC_RMIIEnable(Emac * pEmac,uint8_t bEnaDis);
extern void EMAC_TransceiverClockEnable(Emac * pEmac,uint8_t bEnaDis);
/**     @}*/

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _EMAC_H */

