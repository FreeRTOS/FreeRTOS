/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xcanps.h
* @addtogroup canps_v3_0
* @{
* @details
*
* The Xilinx CAN driver component.  This component supports the Xilinx
* CAN Controller.
*
* The CAN Controller supports the following features:
*	- Confirms to the ISO 11898-1, CAN 2.0A and CAN 2.0B standards.
*	- Supports both Standard (11 bit Identifier) and Extended (29 bit
*	  Identifier) frames.
*	- Supports Bit Rates up to 1 Mbps.
*	- Transmit message object FIFO with a user configurable depth of
*	  up to 64 message objects.
*	- Transmit prioritization through one TX High Priority Buffer.
*	- Receive message object FIFO with a user configurable depth of
*	  up to 64 message objects.
*	- Watermark interrupts for Rx FIFO with configurable Watermark.
*	- Acceptance filtering with 4 acceptance filters.
*	- Sleep mode with automatic wake up.
*	- Loop Back mode for diagnostic applications.
*	- Snoop mode for diagnostic applications.
*	- Maskable Error and Status Interrupts.
*	- Readable Error Counters.
*	- External PHY chip required.
*	- Receive Timestamp.
*
* The device driver supports all the features listed above, if applicable.
*
* <b>Driver Description</b>
*
* The device driver enables higher layer software (e.g., an application) to
* communicate to the CAN. The driver handles transmission and reception of
* CAN frames, as well as configuration of the controller. The driver is simply a
* pass-through mechanism between a protocol stack and the CAN. A single device
* driver can support multiple CANs.
*
* Since the driver is a simple pass-through mechanism between a protocol stack
* and the CAN, no assembly or disassembly of CAN frames is done at the
* driver-level. This assumes that the protocol stack passes a correctly
* formatted CAN frame to the driver for transmission, and that the driver
* does not validate the contents of an incoming frame
*
* <b>Operation Modes</b>
*
* The CAN controller supports the following modes of operation:
*   - <b>Configuration Mode</b>: In this mode the CAN timing parameters and
*	 Baud Rate Pre-scalar parameters can be changed. In this mode the CAN
*	 controller loses synchronization with the CAN bus and drives a
*	 constant recessive bit on the bus line. The Error Counter Register are
*	 reset. The CAN controller does not receive or transmit any messages
*	 even if there are pending transmit requests from the TX FIFO or the TX
*	 High Priority Buffer. The Storage FIFOs and the CAN configuration
*	 registers are still accessible.
*   - <b>Normal Mode</b>:In Normal Mode the CAN controller participates in bus
*	 communication, by transmitting and receiving messages.
*   - <b>Sleep Mode</b>: In Sleep Mode the CAN Controller does not transmit any
*	 messages. However, if any other node transmits a message, then the CAN
*	 Controller receives the transmitted message and exits from Sleep Mode.
*	 If there are new transmission requests from either the TX FIFO or the
*	 TX High Priority Buffer when the CAN Controller is in Sleep Mode, these
*	 requests are not serviced, and the CAN Controller continues to remain
*	 in Sleep Mode. Interrupts are generated when the CAN controller enters
*	Sleep mode or Wakes up from Sleep mode.
*   - <b>Loop Back Mode</b>: In Loop Back mode, the CAN controller transmits a
*	 recessive bit stream on to the CAN Bus. Any message that is transmitted
*	 is looped back to the �Rx� line and acknowledged. The CAN controller
*	 thus receives any message that it transmits. It does not participate in
*	 normal bus communication and does not receive any messages that are
*	 transmitted by other CAN nodes. This mode is used for diagnostic
*	 purposes.
*   - <b>Snoop Mode</b>: In Snoop mode, the CAN controller transmits a
*	 recessive bit stream on to the CAN Bus and does not participate
*	 in normal bus communication but receives messages that are transmitted
*	 by other CAN nodes. This mode is used for diagnostic purposes.
*
*
* <b>Buffer Alignment</b>
*
* It is important to note that frame buffers passed to the driver must be
* 32-bit aligned.
*
* <b>Receive Address Filtering</b>
*
* The device can be set to accept frames whose Identifiers match any of the
* 4 filters set in the Acceptance Filter Mask/ID registers.
*
* The incoming Identifier is masked with the bits in the Acceptance Filter Mask
* Register. This value is compared with the result of masking the bits in the
* Acceptance Filter ID Register with the Acceptance Filter Mask Register. If
* both these values are equal, the message will be stored in the RX FIFO.
*
* Acceptance Filtering is performed by each of the defined acceptance filters.
* If the incoming identifier passes through any acceptance filter then the
* frame is stored in the RX FIFO.
*
* If the Accpetance Filters are not set up then all the received messages are
* stroed in the RX FIFO.
*
* <b>PHY Communication</b>
*
* This driver does not provide any mechanism for directly programming PHY.
*
* <b>Interrupts</b>
*
* The driver has no dependencies on the interrupt controller. The driver
* provides an interrupt handler. User of this driver needs to provide
* callback functions. An interrupt handler example is available with
* the driver.
*
* <b>Threads</b>
*
* This driver is not thread safe.  Any needs for threads or thread mutual
* exclusion must be satisfied by the layer above this driver.
*
* <b>Device Reset</b>
*
* Bus Off interrupt that can occur in the device requires a device reset.
* The user is responsible for resetting the device and re-configuring it
* based on its needs (the driver does not save the current configuration).
* When integrating into an RTOS, these reset and re-configure obligations are
* taken care of by the OS adapter software if it exists for that RTOS.
*
* <b>Device Configuration</b>
*
* The device can be configured in various ways during the FPGA implementation
* process. Configuration parameters are stored in the xcanps_g.c files.
* A table is defined where each entry contains configuration information
* for a CAN device.  This information includes such things as the base address
* of the memory-mapped device.
*
* <b>Asserts</b>
*
* Asserts are used within all Xilinx drivers to enforce constraints on argument
* values. Asserts can be turned off on a system-wide basis by defining, at
* compile time, the NDEBUG identifier. By default, asserts are turned on and it
* is recommended that users leave asserts on during development.
*
* <b>Building the driver</b>
*
* The XCanPs driver is composed of several source files. This allows the user
* to build and link only those parts of the driver that are necessary.
* <br><br>
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00a xd/sv  01/12/10 First release
* 1.01a bss    12/27/11 Added the APIs XCanPs_SetTxIntrWatermark and
* 			XCanPs_GetTxIntrWatermark.
*			Updated the Register/bit definitions
*                       Changed XCANPS_RXFWIR_RXFLL_MASK to XCANPS_WIR_FW_MASK
*                       Changed XCANPS_RXWIR_OFFSET to XCANPS_WIR_OFFSET
*			Added XCANPS_IXR_TXFEMP_MASK for Tx Fifo Empty
*			Changed XCANPS_IXR_RXFLL_MASK to
*			XCANPS_IXR_RXFWMFLL_MASK
* 			Changed
*			XCANPS_TXBUF_ID_OFFSET to XCANPS_TXHPB_ID_OFFSET
* 			XCANPS_TXBUF_DLC_OFFSET to XCANPS_TXHPB_DLC_OFFSET
*			XCANPS_TXBUF_DW1_OFFSET to XCANPS_TXHPB_DW1_OFFSET
*			XCANPS_TXBUF_DW2_OFFSET to XCANPS_TXHPB_DW2_OFFSET
* 2.1 adk 		23/08/14 Fixed CR:798792 Peripheral test for CANPS IP in
*			SDK claims a 40kbps baud rate but it's not.
* 3.0 adk     09/12/14  Added support for Zynq Ultrascale Mp.Also code
*			modified for MISRA-C:2012 compliance.
* 3.1 adk     10/11/15  Fixed CR#911958 Add support for Tx Watermark example.
*			Data mismatch while sending data less than 8 bytes.
* 3.1 nsk     12/21/15  Updated XCanPs_IntrHandler in xcanps_intr.c to handle
*			error interrupts correctly. CR#925615
* </pre>
*
******************************************************************************/
#ifndef XCANPS_H			/* prevent circular inclusions */
#define XCANPS_H			/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xcanps_hw.h"
#include "xil_types.h"

/************************** Constant Definitions *****************************/

/** @name CAN operation modes
 *  @{
 */
#define XCANPS_MODE_CONFIG	0x00000001U /**< Configuration mode */
#define XCANPS_MODE_NORMAL	0x00000002U /**< Normal mode */
#define XCANPS_MODE_LOOPBACK	0x00000004U /**< Loop Back mode */
#define XCANPS_MODE_SLEEP	0x00000008U /**< Sleep mode */
#define XCANPS_MODE_SNOOP	0x00000010U /**< Snoop mode */
/* @} */

/** @name Callback identifiers used as parameters to XCanPs_SetHandler()
 *  @{
 */
#define XCANPS_HANDLER_SEND 1U /**< Handler type for frame sending interrupt */
#define XCANPS_HANDLER_RECV 2U /**< Handler type for frame reception interrupt*/
#define XCANPS_HANDLER_ERROR  3U /**< Handler type for error interrupt */
#define XCANPS_HANDLER_EVENT  4U /**< Handler type for all other interrupts */
/* @} */

/**************************** Type Definitions *******************************/

/**
 * This typedef contains configuration information for a device.
 */
typedef struct {
	u16 DeviceId;		/**< Unique ID of device */
	u32 BaseAddr;		/**< Register base address */
} XCanPs_Config;

/******************************************************************************/
/**
 * Callback type for frame sending and reception interrupts.
 *
 * @param 	CallBackRef is a callback reference passed in by the upper layer
 *		when setting the callback functions, and passed back to the
 *		upper layer when the callback is invoked.
*******************************************************************************/
typedef void (*XCanPs_SendRecvHandler) (void *CallBackRef);

/******************************************************************************/
/**
 * Callback type for error interrupt.
 *
 * @param	CallBackRef is a callback reference passed in by the upper layer
 *		when setting the callback functions, and passed back to the
 *		upper layer when the callback is invoked.
 * @param	ErrorMask is a bit mask indicating the cause of the error. Its
 *		value equals 'OR'ing one or more XCANPS_ESR_* values defined in
 *		xcanps_hw.h
*******************************************************************************/
typedef void (*XCanPs_ErrorHandler) (void *CallBackRef, u32 ErrorMask);

/******************************************************************************/
/**
 * Callback type for all kinds of interrupts except sending frame interrupt,
 * receiving frame interrupt, and error interrupt.
 *
 * @param	CallBackRef is a callback reference passed in by the upper layer
 *		when setting the callback functions, and passed back to the
 *		upper layer when the callback is invoked.
 * @param	Mask is a bit mask indicating the pending interrupts. Its value
 *		equals 'OR'ing one or more XCANPS_IXR_* defined in xcanps_hw.h
*******************************************************************************/
typedef void (*XCanPs_EventHandler) (void *CallBackRef, u32 Mask);

/**
 * The XCanPs driver instance data. The user is required to allocate a
 * variable of this type for every CAN device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XCanPs_Config CanConfig; 	/**< Device configuration */
	u32 IsReady;			/**< Device is initialized and ready */

	/**
	 * Callback and callback reference for TXOK interrupt.
	 */
	XCanPs_SendRecvHandler SendHandler;
	void *SendRef;

	/**
	 * Callback and callback reference for RXOK/RXNEMP/RXFLL interrupts.
	 */
	XCanPs_SendRecvHandler RecvHandler;
	void *RecvRef;

	/**
	 * Callback and callback reference for ERROR interrupt.
	 */
	XCanPs_ErrorHandler ErrorHandler;
	void *ErrorRef;

	/**
	 * Callback  and callback reference for RXOFLW/RXUFLW/TXBFLL/TXFLL/
	 * Wakeup/Sleep/Bus off/ARBLST interrupts.
	 */
	XCanPs_EventHandler EventHandler;
	void *EventRef;

} XCanPs;


/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* This macro checks if the transmission is complete.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return
*		- TRUE if the transmission is done.
*		- FALSE if the transmission is not done.
*
* @note		C-Style signature:
*		int XCanPs_IsTxDone(XCanPs *InstancePtr)
*
*******************************************************************************/
#define XCanPs_IsTxDone(InstancePtr) \
	(((XCanPs_ReadReg(((InstancePtr)->CanConfig.BaseAddr),		\
		XCANPS_ISR_OFFSET) & XCANPS_IXR_TXOK_MASK) != (u32)0) ? TRUE : FALSE)


/****************************************************************************/
/**
*
* This macro checks if the transmission FIFO is full.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return
*		- TRUE if TX FIFO is full.
*		- FALSE if the TX FIFO is NOT full.
*
* @note		C-Style signature:
*		int XCanPs_IsTxFifoFull(XCanPs *InstancePtr)
*
*****************************************************************************/
#define XCanPs_IsTxFifoFull(InstancePtr) \
	(((XCanPs_ReadReg(((InstancePtr)->CanConfig.BaseAddr), 	\
		XCANPS_SR_OFFSET) & XCANPS_SR_TXFLL_MASK) != (u32)0) ? TRUE : FALSE)


/****************************************************************************/
/**
*
* This macro checks if the Transmission High Priority Buffer is full.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return
*		- TRUE if the TX High Priority Buffer is full.
*		- FALSE if the TX High Priority Buffer is NOT full.
*
* @note		C-Style signature:
*		int XCanPs_IsHighPriorityBufFull(XCanPs *InstancePtr)
*
*****************************************************************************/
#define XCanPs_IsHighPriorityBufFull(InstancePtr) \
	(((XCanPs_ReadReg(((InstancePtr)->CanConfig.BaseAddr), 	\
		XCANPS_SR_OFFSET) & XCANPS_SR_TXBFLL_MASK) != (u32)0) ? TRUE : FALSE)


/****************************************************************************/
/**
*
* This macro checks if the receive FIFO is empty.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return
*		- TRUE if RX FIFO is empty.
*		- FALSE if the RX FIFO is NOT empty.
*
* @note		C-Style signature:
*		int XCanPs_IsRxEmpty(XCanPs *InstancePtr)
*
*****************************************************************************/
#define XCanPs_IsRxEmpty(InstancePtr) \
	(((XCanPs_ReadReg(((InstancePtr)->CanConfig.BaseAddr), 	\
		XCANPS_ISR_OFFSET) & XCANPS_IXR_RXNEMP_MASK) != (u32)0) ? FALSE : TRUE)


/****************************************************************************/
/**
*
* This macro checks if the CAN device is ready for the driver to change
* Acceptance Filter Identifier Registers (AFIR) and Acceptance Filter Mask
* Registers (AFMR).
*
* AFIR and AFMR for a filter are changeable only after the filter is disabled
* and this routine returns FALSE. The filter can be disabled using the
* XCanPs_AcceptFilterDisable function.
*
* Use the XCanPs_Accept_* functions for configuring the acceptance filters.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return
*		- TRUE if the device is busy and NOT ready to accept writes to
*		AFIR and AFMR.
*		- FALSE if the device is ready to accept writes to AFIR and
*		AFMR.
*
* @note		C-Style signature:
*		int XCanPs_IsAcceptFilterBusy(XCanPs *InstancePtr)
*
*****************************************************************************/
#define XCanPs_IsAcceptFilterBusy(InstancePtr) 		\
	(((XCanPs_ReadReg(((InstancePtr)->CanConfig.BaseAddr), 	\
		XCANPS_SR_OFFSET) & XCANPS_SR_ACFBSY_MASK) != (u32)0) ? TRUE : FALSE)


/****************************************************************************/
/**
*
* This macro calculates CAN message identifier value given identifier field
* values.
*
* @param	StandardId contains Standard Message ID value.
* @param	SubRemoteTransReq contains Substitute Remote Transmission
*		Request value.
* @param	IdExtension contains Identifier Extension value.
* @param	ExtendedId contains Extended Message ID value.
* @param	RemoteTransReq contains Remote Transmission Request value.
*
* @return	Message Identifier value.
*
* @note		C-Style signature:
*		u32 XCanPs_CreateIdValue(u32 StandardId,
*					u32 SubRemoteTransReq,
*					u32 IdExtension, u32 ExtendedId,
*					u32 RemoteTransReq)
*
*		Read the CAN specification for meaning of each parameter.
*
*****************************************************************************/
#define XCanPs_CreateIdValue(StandardId, SubRemoteTransReq, IdExtension, \
		ExtendedId, RemoteTransReq) 				\
 ((((StandardId) << XCANPS_IDR_ID1_SHIFT) & XCANPS_IDR_ID1_MASK) |	\
 (((SubRemoteTransReq) << XCANPS_IDR_SRR_SHIFT) & XCANPS_IDR_SRR_MASK)|\
 (((IdExtension) << XCANPS_IDR_IDE_SHIFT) & XCANPS_IDR_IDE_MASK) |	\
 (((ExtendedId) << XCANPS_IDR_ID2_SHIFT) & XCANPS_IDR_ID2_MASK) |	\
 ((RemoteTransReq) & XCANPS_IDR_RTR_MASK))


/****************************************************************************/
/**
*
* This macro calculates value for Data Length Code register given Data
* Length Code value.
*
* @param	DataLengCode indicates Data Length Code value.
*
* @return	Value that can be assigned to Data Length Code register.
*
* @note		C-Style signature:
*		u32 XCanPs_CreateDlcValue(u32 DataLengCode)
*
*		Read the CAN specification for meaning of Data Length Code.
*
*****************************************************************************/
#define XCanPs_CreateDlcValue(DataLengCode) \
	(((DataLengCode) << XCANPS_DLCR_DLC_SHIFT) & XCANPS_DLCR_DLC_MASK)


/****************************************************************************/
/**
*
* This macro clears the timestamp in the Timestamp Control Register.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XCanPs_ClearTimestamp(XCanPs *InstancePtr)
*
*****************************************************************************/
#define XCanPs_ClearTimestamp(InstancePtr) 			\
	XCanPs_WriteReg((InstancePtr)->CanConfig.BaseAddr, 		\
				XCANPS_TCR_OFFSET, XCANPS_TCR_CTS_MASK)

/************************** Function Prototypes ******************************/

/*
 * Functions in xcanps.c
 */
s32 XCanPs_CfgInitialize(XCanPs *InstancePtr, XCanPs_Config *ConfigPtr,
				u32 EffectiveAddr);

void XCanPs_Reset(XCanPs *InstancePtr);
u8 XCanPs_GetMode(XCanPs *InstancePtr);
void XCanPs_EnterMode(XCanPs *InstancePtr, u8 OperationMode);
u32 XCanPs_GetStatus(XCanPs *InstancePtr);
void XCanPs_GetBusErrorCounter(XCanPs *InstancePtr, u8 *RxErrorCount,
				 u8 *TxErrorCount);
u32 XCanPs_GetBusErrorStatus(XCanPs *InstancePtr);
void XCanPs_ClearBusErrorStatus(XCanPs *InstancePtr, u32 Mask);
s32 XCanPs_Send(XCanPs *InstancePtr, u32 *FramePtr);
s32 XCanPs_Recv(XCanPs *InstancePtr, u32 *FramePtr);
s32 XCanPs_SendHighPriority(XCanPs *InstancePtr, u32 *FramePtr);
void XCanPs_AcceptFilterEnable(XCanPs *InstancePtr, u32 FilterIndexes);
void XCanPs_AcceptFilterDisable(XCanPs *InstancePtr, u32 FilterIndexes);
u32 XCanPs_AcceptFilterGetEnabled(XCanPs *InstancePtr);
s32 XCanPs_AcceptFilterSet(XCanPs *InstancePtr, u32 FilterIndex,
			 u32 MaskValue, u32 IdValue);
void XCanPs_AcceptFilterGet(XCanPs *InstancePtr, u32 FilterIndex,
			  u32 *MaskValue, u32 *IdValue);

s32 XCanPs_SetBaudRatePrescaler(XCanPs *InstancePtr, u8 Prescaler);
u8 XCanPs_GetBaudRatePrescaler(XCanPs *InstancePtr);
s32 XCanPs_SetBitTiming(XCanPs *InstancePtr, u8 SyncJumpWidth,
			  u8 TimeSegment2, u8 TimeSegment1);
void XCanPs_GetBitTiming(XCanPs *InstancePtr, u8 *SyncJumpWidth,
			   u8 *TimeSegment2, u8 *TimeSegment1);

s32 XCanPs_SetRxIntrWatermark(XCanPs *InstancePtr, u8 Threshold);
u8 XCanPs_GetRxIntrWatermark(XCanPs *InstancePtr);
s32 XCanPs_SetTxIntrWatermark(XCanPs *InstancePtr, u8 Threshold);
u8 XCanPs_GetTxIntrWatermark(XCanPs *InstancePtr);

/*
 * Diagnostic functions in xcanps_selftest.c
 */
s32 XCanPs_SelfTest(XCanPs *InstancePtr);

/*
 * Functions in xcanps_intr.c
 */
void XCanPs_IntrEnable(XCanPs *InstancePtr, u32 Mask);
void XCanPs_IntrDisable(XCanPs *InstancePtr, u32 Mask);
u32 XCanPs_IntrGetEnabled(XCanPs *InstancePtr);
u32 XCanPs_IntrGetStatus(XCanPs *InstancePtr);
void XCanPs_IntrClear(XCanPs *InstancePtr, u32 Mask);
void XCanPs_IntrHandler(void *InstancePtr);
s32 XCanPs_SetHandler(XCanPs *InstancePtr, u32 HandlerType,
			void *CallBackFunc, void *CallBackRef);

/*
 * Functions in xcanps_sinit.c
 */
XCanPs_Config *XCanPs_LookupConfig(u16 DeviceId);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
