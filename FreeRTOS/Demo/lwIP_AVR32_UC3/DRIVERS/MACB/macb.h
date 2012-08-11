/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief MACB example driver for EVK1100 board.
 *
 * This file defines a useful set of functions for the MACB interface on
 * AVR32 devices.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a MACB module can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


#ifndef AVR32_MACB_H
#define AVR32_MACB_H

#include <avr32/io.h>

#ifdef FREERTOS_USED
#include <arch/sys_arch.h>
#endif

#include "conf_eth.h"

/*! \name Rx Ring descriptor flags
 */
//! @{
#define AVR32_MACB_RX_USED_OFFSET       0
#define AVR32_MACB_RX_USED_SIZE         1
#define AVR32_MACB_RX_WRAP_OFFSET       1
#define AVR32_MACB_RX_WRAP_SIZE         1
#define AVR32_MACB_RX_LEN_OFFSET        0
#define AVR32_MACB_RX_LEN_SIZE         12
#define AVR32_MACB_RX_OFFSET_OFFSET    12
#define AVR32_MACB_RX_OFFSET_SIZE       2
#define AVR32_MACB_RX_SOF_OFFSET       14
#define AVR32_MACB_RX_SOF_SIZE          1
#define AVR32_MACB_RX_EOF_OFFSET       15
#define AVR32_MACB_RX_EOF_SIZE          1
#define AVR32_MACB_RX_CFI_OFFSET       16
#define AVR32_MACB_RX_CFI_SIZE          1
//! @}

/*! \name Tx Ring descriptor flags
 */
//! @{
#define AVR32_MACB_TX_LEN_OFFSET        0
#define AVR32_MACB_TX_LEN_SIZE         11
#define AVR32_MACB_TX_EOF_OFFSET       15
#define AVR32_MACB_TX_EOF_SIZE          1
#define AVR32_MACB_TX_NOCRC_OFFSET     16
#define AVR32_MACB_TX_NOCRC_SIZE        1
#define AVR32_MACB_TX_EMF_OFFSET       27
#define AVR32_MACB_TX_EMF_SIZE          1
#define AVR32_MACB_TX_UNR_OFFSET       28
#define AVR32_MACB_TX_UNR_SIZE          1
#define AVR32_MACB_TX_MAXRETRY_OFFSET  29
#define AVR32_MACB_TX_MAXRETRY_SIZE     1
#define AVR32_MACB_TX_WRAP_OFFSET      30
#define AVR32_MACB_TX_WRAP_SIZE         1
#define AVR32_MACB_TX_USED_OFFSET      31
#define AVR32_MACB_TX_USED_SIZE         1
//! @}

/*! \name Generic MII registers.
 */
//! @{
#define PHY_BMCR            0x00        //!< Basic mode control register
#define PHY_BMSR            0x01        //!< Basic mode status register
#define PHY_PHYSID1         0x02        //!< PHYS ID 1
#define PHY_PHYSID2         0x03        //!< PHYS ID 2
#define PHY_ADVERTISE       0x04        //!< Advertisement control reg
#define PHY_LPA             0x05        //!< Link partner ability reg
//! @}

#if BOARD == EVK1100
/*! \name Extended registers for DP83848
 */
//! @{
#define PHY_RBR             0x17        //!< RMII Bypass reg
#define PHY_MICR            0x11        //!< Interrupt Control reg
#define PHY_MISR            0x12        //!< Interrupt Status reg
#define PHY_PHYCR           0x19        //!< Phy CTRL reg
//! @}
#endif


/*! \name Basic mode control register.
 */
//! @{
#define BMCR_RESV               0x007f  //!< Unused...
#define BMCR_CTST               0x0080  //!< Collision test
#define BMCR_FULLDPLX           0x0100  //!< Full duplex
#define BMCR_ANRESTART          0x0200  //!< Auto negotiation restart
#define BMCR_ISOLATE            0x0400  //!< Disconnect PHY from MII
#define BMCR_PDOWN              0x0800  //!< Powerdown the PHY
#define BMCR_ANENABLE           0x1000  //!< Enable auto negotiation
#define BMCR_SPEED100           0x2000  //!< Select 100Mbps
#define BMCR_LOOPBACK           0x4000  //!< TXD loopback bits
#define BMCR_RESET              0x8000  //!< Reset the PHY
//! @}

/*! \name Basic mode status register.
 */
//! @{
#define BMSR_ERCAP              0x0001  //!< Ext-reg capability
#define BMSR_JCD                0x0002  //!< Jabber detected
#define BMSR_LSTATUS            0x0004  //!< Link status
#define BMSR_ANEGCAPABLE        0x0008  //!< Able to do auto-negotiation
#define BMSR_RFAULT             0x0010  //!< Remote fault detected
#define BMSR_ANEGCOMPLETE       0x0020  //!< Auto-negotiation complete
#define BMSR_RESV               0x00c0  //!< Unused...
#define BMSR_ESTATEN            0x0100  //!< Extended Status in R15
#define BMSR_100FULL2           0x0200  //!< Can do 100BASE-T2 HDX
#define BMSR_100HALF2           0x0400  //!< Can do 100BASE-T2 FDX
#define BMSR_10HALF             0x0800  //!< Can do 10mbps, half-duplex
#define BMSR_10FULL             0x1000  //!< Can do 10mbps, full-duplex
#define BMSR_100HALF            0x2000  //!< Can do 100mbps, half-duplex
#define BMSR_100FULL            0x4000  //!< Can do 100mbps, full-duplex
#define BMSR_100BASE4           0x8000  //!< Can do 100mbps, 4k packets
//! @}

/*! \name Advertisement control register.
 */
//! @{
#define ADVERTISE_SLCT          0x001f  //!< Selector bits
#define ADVERTISE_CSMA          0x0001  //!< Only selector supported
#define ADVERTISE_10HALF        0x0020  //!< Try for 10mbps half-duplex
#define ADVERTISE_1000XFULL     0x0020  //!< Try for 1000BASE-X full-duplex
#define ADVERTISE_10FULL        0x0040  //!< Try for 10mbps full-duplex
#define ADVERTISE_1000XHALF     0x0040  //!< Try for 1000BASE-X half-duplex
#define ADVERTISE_100HALF       0x0080  //!< Try for 100mbps half-duplex
#define ADVERTISE_1000XPAUSE    0x0080  //!< Try for 1000BASE-X pause
#define ADVERTISE_100FULL       0x0100  //!< Try for 100mbps full-duplex
#define ADVERTISE_1000XPSE_ASYM 0x0100  //!< Try for 1000BASE-X asym pause
#define ADVERTISE_100BASE4      0x0200  //!< Try for 100mbps 4k packets
#define ADVERTISE_PAUSE_CAP     0x0400  //!< Try for pause
#define ADVERTISE_PAUSE_ASYM    0x0800  //!< Try for asymetric pause
#define ADVERTISE_RESV          0x1000  //!< Unused...
#define ADVERTISE_RFAULT        0x2000  //!< Say we can detect faults
#define ADVERTISE_LPACK         0x4000  //!< Ack link partners response
#define ADVERTISE_NPAGE         0x8000  //!< Next page bit
//! @}

#define ADVERTISE_FULL (ADVERTISE_100FULL | ADVERTISE_10FULL | ADVERTISE_CSMA)
#define ADVERTISE_ALL (ADVERTISE_10HALF | ADVERTISE_10FULL | \
                       ADVERTISE_100HALF | ADVERTISE_100FULL)

/*! \name Link partner ability register.
 */
//! @{
#define LPA_SLCT                0x001f  //!< Same as advertise selector
#define LPA_10HALF              0x0020  //!< Can do 10mbps half-duplex
#define LPA_1000XFULL           0x0020  //!< Can do 1000BASE-X full-duplex
#define LPA_10FULL              0x0040  //!< Can do 10mbps full-duplex
#define LPA_1000XHALF           0x0040  //!< Can do 1000BASE-X half-duplex
#define LPA_100HALF             0x0080  //!< Can do 100mbps half-duplex
#define LPA_1000XPAUSE          0x0080  //!< Can do 1000BASE-X pause
#define LPA_100FULL             0x0100  //!< Can do 100mbps full-duplex
#define LPA_1000XPAUSE_ASYM     0x0100  //!< Can do 1000BASE-X pause asym
#define LPA_100BASE4            0x0200  //!< Can do 100mbps 4k packets
#define LPA_PAUSE_CAP           0x0400  //!< Can pause
#define LPA_PAUSE_ASYM          0x0800  //!< Can pause asymetrically
#define LPA_RESV                0x1000  //!< Unused...
#define LPA_RFAULT              0x2000  //!< Link partner faulted
#define LPA_LPACK               0x4000  //!< Link partner acked us
#define LPA_NPAGE               0x8000  //!< Next page bit

#define LPA_DUPLEX    (LPA_10FULL | LPA_100FULL)
#define LPA_100       (LPA_100FULL | LPA_100HALF | LPA_100BASE4)
//! @}

#if BOARD == EVK1100
/*! RMII Bypass Register */
#define RBR_RMII                 0x0020  //!< RMII Mode
/*! \name Interrupt Ctrl Register.
 */
//! @{
#define MICR_INTEN               0x0002  //!< Enable interrupts
#define MICR_INTOE               0x0001  //!< Enable INT output
//! @}

/*! \name Interrupt Status Register.
 */
//! @{
#define MISR_ED_INT_EN           0x0040  //!< Energy Detect enabled
#define MISR_LINK_INT_EN         0x0020  //!< Link status change enabled
#define MISR_SPD_INT_EN          0x0010  //!< Speed change enabled
#define MISR_DP_INT_EN           0x0008  //!< Duplex mode change enabled
#define MISR_ANC_INT_EN          0x0004  //!< Auto-Neg complete enabled
#define MISR_FHF_INT_EN          0x0002  //!< False Carrier enabled
#define MISR_RHF_INT_EN          0x0001  //!< Receive Error enabled
#define MISR_ED_INT              0x4000  //!< Energy Detect
#define MISR_LINK_INT            0x2000  //!< Link status change
#define MISR_SPD_INT             0x1000  //!< Speed change
#define MISR_DP_INT              0x0800  //!< Duplex mode change
#define MISR_ANC_INT             0x0400  //!< Auto-Neg complete
#define MISR_FHF_INT             0x0200  //!< False Carrier
#define MISR_RHF_INT             0x0100  //!< Receive Error
//! @}

/*! \name Phy Ctrl Register.
 */
//! @{
#define PHYCR_MDIX_EN            0x8000  //!< Enable Auto MDIX
#define PHYCR_MDIX_FORCE         0x4000  //!< Force MDIX crossed
//! @}
#endif

/*! Packet structure.
 */
//! @{
typedef struct
{
  char *data;        
  unsigned int len;  
} macb_packet_t;
//! @}

/*! Receive Transfer descriptor structure.
 */
//! @{
typedef struct  _AVR32_RxTdDescriptor {
  unsigned int addr;
  union
  {
    unsigned int status;
    struct {
      unsigned int BroadCast:1;
      unsigned int MultiCast:1;
      unsigned int UniCast:1;
      unsigned int ExternalAdd:1;
      unsigned int Res1:1;
      unsigned int Sa1Match:1;
      unsigned int Sa2Match:1;
      unsigned int Sa3Match:1;
      unsigned int Sa4Match:1;
      unsigned int TypeID:1;
      unsigned int VlanTag:1;
      unsigned int PriorityTag:1;
      unsigned int VlanPriority:3;
      unsigned int Cfi:1;
      unsigned int EndOfFrame:1;
      unsigned int StartOfFrame:1;
      unsigned int Rxbuf_off:2;
      unsigned int Res0:1;
      unsigned int Length:11;
    }S_Status;
  }U_Status;
}AVR32_RxTdDescriptor, *AVR32P_RxTdDescriptor;
//! @}

/*! Transmit Transfer descriptor structure.
 */
//! @{
typedef struct _AVR32_TxTdDescriptor {
  unsigned int addr;
  union
  {
    unsigned int status;
    struct {
      unsigned int BuffUsed:1;
      unsigned int Wrap:1;
      unsigned int TransmitError:1;
      unsigned int TransmitUnderrun:1;
      unsigned int BufExhausted:1;
      unsigned int Res1:10;
      unsigned int NoCrc:1;
      unsigned int LastBuff:1;
      unsigned int Res0:4;
      unsigned int Length:11;
    }S_Status;
  }U_Status;
}AVR32_TxTdDescriptor, *AVR32P_TxTdDescriptor;
//! @}

/*! Mask for frame used. */
#define AVR32_OWNERSHIP_BIT   0x00000001

/*! Receive status defintion.
 */
//! @{
#define AVR32_BROADCAST_ADDR  ((unsigned int) (1 << 31))  //* Broadcat address detected
#define AVR32_MULTICAST_HASH  ((unsigned int) (1 << 30))  //* MultiCast hash match
#define AVR32_UNICAST_HASH    ((unsigned int) (1 << 29))  //* UniCast hash match
#define AVR32_EXTERNAL_ADDR   ((unsigned int) (1 << 28))  //* External Address match
#define AVR32_SA1_ADDR        ((unsigned int) (1 << 26))  //* Specific address 1 match
#define AVR32_SA2_ADDR        ((unsigned int) (1 << 25))  //* Specific address 2 match
#define AVR32_SA3_ADDR        ((unsigned int) (1 << 24))  //* Specific address 3 match
#define AVR32_SA4_ADDR        ((unsigned int) (1 << 23))  //* Specific address 4 match
#define AVR32_TYPE_ID         ((unsigned int) (1 << 22))  //* Type ID match
#define AVR32_VLAN_TAG        ((unsigned int) (1 << 21))  //* VLAN tag detected
#define AVR32_PRIORITY_TAG    ((unsigned int) (1 << 20))  //* PRIORITY tag detected
#define AVR32_VLAN_PRIORITY   ((unsigned int) (7 << 17))  //* PRIORITY Mask
#define AVR32_CFI_IND         ((unsigned int) (1 << 16))  //* CFI indicator
#define AVR32_EOF             ((unsigned int) (1 << 15))  //* EOF
#define AVR32_SOF             ((unsigned int) (1 << 14))  //* SOF
#define AVR32_RBF_OFFSET      ((unsigned int) (3 << 12))  //* Receive Buffer Offset Mask
#define AVR32_LENGTH_FRAME    ((unsigned int) 0x0FFF)     //* Length of frame
//! @}

/* Transmit Status definition */
//! @{
#define AVR32_TRANSMIT_OK     ((unsigned int) (1 << 31))  //*
#define AVR32_TRANSMIT_WRAP   ((unsigned int) (1 << 30))  //* Wrap bit: mark the last descriptor
#define AVR32_TRANSMIT_ERR    ((unsigned int) (1 << 29))  //* RLE:transmit error
#define AVR32_TRANSMIT_UND    ((unsigned int) (1 << 28))  //* Transmit Underrun
#define AVR32_BUF_EX          ((unsigned int) (1 << 27))  //* Buffers exhausted in mid frame
#define AVR32_TRANSMIT_NO_CRC ((unsigned int) (1 << 16))  //* No CRC will be appended to the current frame
#define AVR32_LAST_BUFFER     ((unsigned int) (1 << 15))  //*
//! @}

/**
 * \brief Initialise the MACB driver. 
 *  
 * \param *macb Base address of the MACB
 *  
 * \return TRUE if success, FALSE otherwise.
 */
Bool xMACBInit( volatile avr32_macb_t * macb );

/**
 * \brief Send ulLength bytes from pcFrom. This copies the buffer to one of the
 * MACB Tx buffers, then indicates to the MACB that the buffer is ready.
 * If lEndOfFrame is true then the data being copied is the end of the frame
 * and the frame can be transmitted.
 *  
 * \param *macb        Base address of the MACB
 * \param *pcFrom      Address of the data buffer
 * \param ulLength     Length of the frame
 * \param lEndOfFrame  Flag for End Of Frame
 *  
 * \return length sent.
 */
long lMACBSend(volatile avr32_macb_t * macb, char *pcFrom, unsigned long ulLength, long lEndOfFrame );


/**
 * \brief Frames can be read from the MACB in multiple sections.
 * Read ulSectionLength bytes from the MACB receive buffers to pcTo.
 * ulTotalFrameLength is the size of the entire frame.  Generally vMACBRead
 * will be repetedly called until the sum of all the ulSectionLenths totals
 * the value of ulTotalFrameLength.
 *  
 * \param *pcTo               Address of the buffer
 * \param ulSectionLength     Length of the buffer
 * \param ulTotalFrameLength  Length of the frame
 */ 
void vMACBRead( char *pcTo, unsigned long ulSectionLength, unsigned long ulTotalFrameLength );

/**
 * \brief Called by the Tx interrupt, this function traverses the buffers used to
 * hold the frame that has just completed transmission and marks each as
 * free again.
 */ 
void vClearMACBTxBuffer( void );

/**
 * \brief Suspend on a semaphore waiting either for the semaphore to be obtained
 * or a timeout.  The semaphore is used by the MACB ISR to indicate that
 * data has been received and is ready for processing.
 * 
 * \param ulTimeOut    time to wait for an input
 * 
 */
void vMACBWaitForInput( unsigned long ulTimeOut );

/**
 * \brief Function to get length of the next frame in the receive buffers 
 * 
 * \return the length of the next frame in the receive buffers.
 */
unsigned long ulMACBInputLength( void );

/**
 * \brief Set the MACB Physical address (SA1B & SA1T registers).
 * 
 * \param *MACAddress the MAC address to set.
 */ 
void vMACBSetMACAddress(const char * MACAddress);

/**
 * \brief Disable MACB operations (Tx and Rx).
 * 
 * \param *macb        Base address of the MACB
 */ 
void vDisableMACBOperations(volatile avr32_macb_t * macb);

#endif

