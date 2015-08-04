/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xemaclite_l.h
*
* This header file contains identifiers and basic driver functions and macros
* that can be used to access the Xilinx Ethernet Lite 10/100 MAC (EmacLite).
*
* Refer to xemaclite.h for more details.
*
* @note
*
* The functions and macros in this file assume that the proper device address is
* provided in the argument. If the ping buffer is the source or destination,
* the argument should be DeviceAddress + XEL_(T/R)XBUFF_OFFSET. If the pong
* buffer is the source or destination, the argument should be
* DeviceAddress + XEL_(T/R)XBUFF_OFFSET + XEL_BUFFER_OFFSET. The driver does
* not take the different buffers into consideration.
* For more details on the ping/pong buffer configuration please refer to the
* Ethernet Lite 10/100 Media Access Controller hardware specification.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  06/01/02 First release
* 1.01a ecm  03/31/04 Additional functionality and the _AlignedRead and
*                     AlignedWrite functions.
*                     Moved the bulk of description to xemaclite.h
* 1.11a mta  03/21/07 Updated to new coding style
* 2.00a ktn  02/16/09 Added support for MDIO and internal loop back
* 3.00a ktn  10/22/09 The macros have been renamed to remove _m from the name.
*		      The macros changed in this file are
*		      XEmacLite_mReadReg changed to XEmacLite_mReadReg,
*		      XEmacLite_mWriteReg changed to XEmacLite_mWriteReg,
*		      XEmacLite_mGetTxStatus changed to XEmacLite_GetTxStatus,
*		      XEmacLite_mSetTxStatus changed to XEmacLite_SetTxStatus,
*		      XEmacLite_mGetRxStatus changed to XEmacLite_GetRxStatus,
*		      XEmacLite_mSetRxStatus changed to XEmacLite_SetRxStatus,
*		      XEmacLite_mIsTxDone changed to XEmacLite_IsTxDone and
*		      XEmacLite_mIsRxEmpty changed to XEmacLite_IsRxEmpty.
* </pre>
*
******************************************************************************/

#ifndef XEMAC_LITE_L_H		/* prevent circular inclusions */
#define XEMAC_LITE_L_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/
/**
 * Register offsets for the Ethernet MAC.
 */
#define XEL_TXBUFF_OFFSET (0x00000000)			/**< Transmit Buffer */
#define XEL_MDIOADDR_OFFSET (XEL_TXBUFF_OFFSET + 0x07E4)/**< MDIO Address offset
							     register */
#define XEL_MDIOWR_OFFSET  (XEL_TXBUFF_OFFSET + 0x07E8)	/**< MDIO write data
							     register offset */
#define XEL_MDIORD_OFFSET (XEL_TXBUFF_OFFSET + 0x07EC)	/**< MDIO read data
							     register offset*/
#define XEL_MDIOCNTR_OFFSET (XEL_TXBUFF_OFFSET + 0x07F0)/**< MDIO Control
							     Register offset */
#define XEL_GIER_OFFSET   (XEL_TXBUFF_OFFSET + 0x07F8)	/**< Offset for the GIE
							     Register */
#define XEL_TSR_OFFSET	  (XEL_TXBUFF_OFFSET + 0x07FC)	/**< Tx status */
#define XEL_TPLR_OFFSET   (XEL_TXBUFF_OFFSET + 0x07F4)	/**< Tx packet length */

#define XEL_RXBUFF_OFFSET (0x00001000)			/**< Receive Buffer */
#define XEL_RSR_OFFSET	  (XEL_RXBUFF_OFFSET + 0x07FC)	/**< Rx status */
#define XEL_RPLR_OFFSET   (XEL_RXBUFF_OFFSET + 0x0C)	/**< Rx packet length */

#define XEL_MAC_HI_OFFSET (XEL_TXBUFF_OFFSET + 0x14)	/**< MAC address hi
							     offset */
#define XEL_MAC_LO_OFFSET (XEL_TXBUFF_OFFSET)		/**< MAC address lo
							     offset */

#define XEL_BUFFER_OFFSET (0x00000800)			/**< Next buffer's
							     offset  same for
							     both TX and RX */
/**
 * MDIO Address/Write Data/Read Data Register Bit Masks
 */
#define XEL_MDIO_ADDRESS_MASK		0x00003E0	/**< PHY Address mask */
#define XEL_MDIO_ADDRESS_SHIFT		0x5		/**< PHY Address shift*/
#define XEL_MDIO_OP_MASK		0x00000400	/**< PHY read access */

/**
 * MDIO Control Register Bit Masks
 */
#define XEL_MDIOCNTR_STATUS_MASK	0x00000001	/**< MDIO transfer in
							     Progress */
#define XEL_MDIOCNTR_ENABLE_MASK	0x00000008	/**<  MDIO Enable */

/**
 * Global Interrupt Enable Register (GIER) Bit Masks
 */
#define XEL_GIER_GIE_MASK		0x80000000	/**< Global Enable */

/**
 * Transmit Status Register (TSR) Bit Masks
 */
#define XEL_TSR_XMIT_BUSY_MASK		0x00000001	/**< Xmit complete */
#define XEL_TSR_PROGRAM_MASK		0x00000002	/**< Program the MAC
							     address */
#define XEL_TSR_XMIT_IE_MASK		0x00000008	/**< Xmit interrupt
							     enable bit */
#define XEL_TSR_LOOPBACK_MASK		0x00000010	/**< Loop back enable
							     bit */
#define XEL_TSR_XMIT_ACTIVE_MASK	0x80000000	/**< Buffer is active,
							     SW bit only. This
							     is not documented
							     in the HW spec */

/**
 * define for programming the MAC address into the EmacLite
 */
#define XEL_TSR_PROG_MAC_ADDR   (XEL_TSR_XMIT_BUSY_MASK | XEL_TSR_PROGRAM_MASK)

/**
 * Receive Status Register (RSR)
 */
#define XEL_RSR_RECV_DONE_MASK		0x00000001	/**< Recv complete */
#define XEL_RSR_RECV_IE_MASK		0x00000008	/**< Recv interrupt
							     enable bit */

/**
 * Transmit Packet Length Register (TPLR)
 */
#define XEL_TPLR_LENGTH_MASK_HI		0x0000FF00 /**< Transmit packet length
							  upper byte */
#define XEL_TPLR_LENGTH_MASK_LO		0x000000FF /**< Transmit packet length
							  lower byte */

/**
 * Receive Packet Length Register (RPLR)
 */
#define XEL_RPLR_LENGTH_MASK_HI		0x0000FF00 /**< Receive packet length
							  upper byte */
#define XEL_RPLR_LENGTH_MASK_LO		0x000000FF /**< Receive packet length
							  lower byte */

#define XEL_HEADER_SIZE			14  /**< Size of header in bytes */
#define XEL_MTU_SIZE			1500 /**< Max size of data in frame */
#define XEL_FCS_SIZE			4    /**< Size of CRC */

#define XEL_HEADER_OFFSET		12   /**< Offset to length field */
#define XEL_HEADER_SHIFT		16   /**< Right shift value to align
						  length */


#define XEL_MAX_FRAME_SIZE (XEL_HEADER_SIZE+XEL_MTU_SIZE+ XEL_FCS_SIZE)	/**< Max
						length of Rx frame  used if
						length/type field
						contains the type (> 1500) */

#define XEL_MAX_TX_FRAME_SIZE (XEL_HEADER_SIZE + XEL_MTU_SIZE)	/**< Max
						length of Tx frame */


#define XEL_MAC_ADDR_SIZE		6	/**< length of MAC address */


/*
 * General Ethernet Definitions
 */
#define XEL_ETHER_PROTO_TYPE_IP		0x0800  /**< IP Protocol */
#define XEL_ETHER_PROTO_TYPE_ARP	0x0806  /**< ARP Protocol */
#define XEL_ETHER_PROTO_TYPE_VLAN	0x8100  /**< VLAN Tagged */
#define XEL_ARP_PACKET_SIZE		28  	/**< Max ARP packet size */
#define XEL_HEADER_IP_LENGTH_OFFSET	16  	/**< IP Length Offset */
#define XEL_VLAN_TAG_SIZE		4  	/**< VLAN Tag Size */

/***************** Macros (Inline Functions) Definitions *********************/

#define XEmacLite_In32 Xil_In32
#define XEmacLite_Out32 Xil_Out32

/****************************************************************************/
/**
*
* Read from the specified EmacLite device register.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset contains the offset from the 1st register of the
*		device to select the specific register.
*
* @return	The value read from the register.
*
* @note		C-Style signature:
*		u32 XEmacLite_ReadReg(u32 BaseAddress, u32 RegOffset);
*
******************************************************************************/
#define XEmacLite_ReadReg(BaseAddress, RegOffset) \
	XEmacLite_In32((BaseAddress) + (RegOffset))

/***************************************************************************/
/**
*
* Write to the specified EmacLite device register.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset contains the offset from the 1st register of the
*		device to select the specific register.
* @param	RegisterValue is the value to be written to the register.
*
* @return	None.
*
* @note		C-Style signature:
*		void XEmacLite_WriteReg(u32 BaseAddress, u32 RegOffset,
*					u32 RegisterValue);
******************************************************************************/
#define XEmacLite_WriteReg(BaseAddress, RegOffset, RegisterValue) \
	XEmacLite_Out32((BaseAddress) + (RegOffset), (RegisterValue))


/****************************************************************************/
/**
*
* Get the Tx Status Register Contents.
*
* @param	BaseAddress is the base address of the device
*
* @return	The contents of the Tx Status Register.
*
* @note		C-Style signature:
* 		u32 XEmacLite_GetTxStatus(u32 BaseAddress)
*
*****************************************************************************/
#define XEmacLite_GetTxStatus(BaseAddress)			\
	(XEmacLite_ReadReg((BaseAddress), XEL_TSR_OFFSET))


/****************************************************************************/
/**
*
* Set the Tx Status Register Contents.
*
* @param	BaseAddress is the base address of the device
* @param	Data is the value to be written to the Register.
*
* @return	None.
*
* @note		C-Style signature:
* 		u32 XEmacLite_SetTxStatus(u32 BaseAddress, u32 Data)
*
*****************************************************************************/
#define XEmacLite_SetTxStatus(BaseAddress, Data)			\
	(XEmacLite_WriteReg((BaseAddress), XEL_TSR_OFFSET, (Data)))


/****************************************************************************/
/**
*
* Get the Rx Status Register Contents.
*
* @param	BaseAddress is the base address of the device
*
* @return	The contents of the Rx Status Register.
*
* @note		C-Style signature:
* 		u32 XEmacLite_GetRxStatus(u32 BaseAddress)
*
*****************************************************************************/
#define XEmacLite_GetRxStatus(BaseAddress)			\
	(XEmacLite_ReadReg((BaseAddress), XEL_RSR_OFFSET))


/****************************************************************************/
/**
*
* Set the Rx Status Register Contents.
*
* @param	BaseAddress is the base address of the device
* @param	Data is the value to be written to the Register.
*
* @return	None.
*
* @note		C-Style signature:
* 		u32 XEmacLite_SetRxStatus(u32 BaseAddress, u32 Data)
*
*****************************************************************************/
#define XEmacLite_SetRxStatus(BaseAddress, Data)			\
	(XEmacLite_WriteReg((BaseAddress), XEL_RSR_OFFSET, (Data)))


/****************************************************************************/
/**
*
* Check to see if the transmission is complete.
*
* @param	BaseAddress is the base address of the device
*
* @return	TRUE if it is done, or FALSE if it is not.
*
* @note		C-Style signature:
* 		int XEmacLite_IsTxDone(u32 BaseAddress)
*
*****************************************************************************/
#define XEmacLite_IsTxDone(BaseAddress)			\
		 ((XEmacLite_ReadReg((BaseAddress), XEL_TSR_OFFSET) & 	 \
			 XEL_TSR_XMIT_BUSY_MASK) != XEL_TSR_XMIT_BUSY_MASK)


/****************************************************************************/
/**
*
* Check to see if the receive is empty.
*
* @param	BaseAddress is the base address of the device
*
* @return	TRUE if it is empty, or FALSE if it is not.
*
* @note		C-Style signature:
*		int XEmacLite_IsRxEmpty(u32 BaseAddress)
*
*****************************************************************************/
#define XEmacLite_IsRxEmpty(BaseAddress) \
		  ((XEmacLite_ReadReg((BaseAddress), XEL_RSR_OFFSET) & \
			XEL_RSR_RECV_DONE_MASK) != XEL_RSR_RECV_DONE_MASK)

/************************** Function Prototypes ******************************/

void XEmacLite_SendFrame(u32 BaseAddress, u8 *FramePtr, unsigned ByteCount);
u16 XEmacLite_RecvFrame(u32 BaseAddress, u8 *FramePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
