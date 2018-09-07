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
* @file xemaclite.h
* @addtogroup emaclite_v4_1
* @{
* @details
*
* The Xilinx Ethernet Lite (EmacLite) driver. This driver supports the Xilinx
* Ethernet Lite 10/100 MAC (EmacLite).
*
* The Xilinx Ethernet Lite 10/100 MAC supports the following features:
*   - Media Independent Interface (MII) for connection to external
*     10/100 Mbps PHY transceivers
*   - Independent internal transmit and receive buffers
*   - CSMA/CD compliant operations for half-duplex modes
*   - Unicast and broadcast
*   - Automatic FCS insertion
*   - Automatic pad insertion on transmit
*   - Configurable ping/pong buffers for either/both transmit and receive
*     buffer areas
*   - Interrupt driven mode
*   - Internal loop back
*   - MDIO Support to access PHY Registers
*
* The Xilinx Ethernet Lite 10/100 MAC does not support the following features:
*   - multi-frame buffering
*     only 1 transmit frame is allowed into each transmit buffer,
*     only 1 receive frame is allowed into each receive buffer.
*     the hardware blocks reception until buffer is emptied
*   - Pause frame (flow control) detection in full-duplex mode
*   - Programmable inter frame gap
*   - Multicast and promiscuous address filtering
*   - Automatic source address insertion or overwrite
*
* <b>Driver Description</b>
*
* The device driver enables higher layer software (e.g., an application) to
* communicate to the EmacLite. The driver handles transmission and reception
* of Ethernet frames, as well as configuration of the controller. It does not
* handle protocol stack functionality such as Link Layer Control (LLC) or the
* Address Resolution Protocol (ARP). The protocol stack that makes use of the
* driver handles this functionality. This implies that the driver is simply a
* pass-through mechanism between a protocol stack and the EmacLite.
*
* Since the driver is a simple pass-through mechanism between a protocol stack
* and the EmacLite, no assembly or disassembly of Ethernet frames is done at
* the driver-level. This assumes that the protocol stack passes a correctly
* formatted Ethernet frame to the driver for transmission, and that the driver
* does not validate the contents of an incoming frame. A single device driver
* can support multiple EmacLite devices.
*
* The driver supports interrupt driven mode and the default mode of operation
* is polled mode. If interrupts are desired, XEmacLite_InterruptEnable() must
* be called.
*
* <b>Device Configuration</b>
*
* The device can be configured in various ways during the FPGA implementation
* process.  Configuration parameters are stored in the xemaclite_g.c file.
* A table is defined where each entry contains configuration information for an
* EmacLite device. This information includes such things as the base address
* of the memory-mapped device and the number of buffers.
*
* <b>Interrupt Processing</b>
*
* After _Initialize is called, _InterruptEnable can be called to enable the
* interrupt driven functionality. If polled operation is desired, just call
* _Send and check the return code. If XST_FAILURE is returned, call _Send with
* the same data until XST_SUCCESS is returned. The same idea applies to _Recv.
* Call _Recv until the returned length is non-zero at which point the received
* data is in the buffer provided in the function call.
*
* The Transmit and Receive interrupts are enabled within the _InterruptEnable
* function and disabled in the _InterruptDisable function. The _Send and _Recv
* functions acknowledge the EmacLite generated interrupts associated with each
* function.
* It is the application's responsibility to acknowledge any associated Interrupt
* Controller interrupts if it is used in the system.
*
* <b>Memory Buffer Alignment</b>
*
* The alignment of the input/output buffers for the _Send and _Recv routine is
* not required to be 32 bits. If the buffer is not aligned on a 32-bit boundary
* there will be a performance impact while the driver aligns the data for
* transmission or upon reception.
*
* For optimum performance, the user should provide a 32-bit aligned buffer
* to the _Send and _Recv routines.
*
* <b>Asserts</b>
*
* Asserts are used within all Xilinx drivers to enforce constraints on argument
* values. Asserts can be turned off on a system-wide basis by defining, at
* compile time, the NDEBUG identifier.  By default, asserts are turned on and it
* is recommended that application developers leave asserts on during
* development.
*
* @note
*
* This driver requires EmacLite hardware version 1.01a and higher. It is not
* compatible with earlier versions of the EmacLite hardware. Use version 1.00a
* software driver for hardware version 1.00a/b.
*
* The RX hardware is enabled from powerup and there is no disable. It is
* possible that frames have been received prior to the initialization
* of the driver. If this situation is possible, call XEmacLite_FlushReceive()
* to empty the receive buffers after initialization.
*
* This driver is intended to be RTOS and processor independent.  It works
* with physical addresses only.  Any needs for dynamic memory management,
* threads or thread mutual exclusion, virtual memory, or cache control must
* be satisfied by the layer above this driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.01a ecm  01/30/04 First release
* 1.11a mta  03/21/07 Updated to new coding style
* 1.12a mta  11/28/07 Added the function XEmacLite_CfgInitialize,
*		      moved the functions XEmacLite_LookupConfig and
*		      XEmacLite_Initialize to xemaclite_sinit.c for removing
*		      the dependency on the static config table and
*		      xparameters.h from the driver initialization
* 1.13a sv   02/1/08  Updated the TxBufferAvailable routine to return
*		      busy status properly and added macros for Tx/Rx status
* 1.14a sdm  08/22/08 Removed support for static interrupt handlers from the MDD
*		      file
* 2.00a ktn  02/16/09 Added support for MDIO and internal loop back
* 2.01a ktn  07/20/09 Updated the XEmacLite_AlignedWrite and
*                     XEmacLite_AlignedRead functions to use volatile
*                     variables so that they are not optimized.
*                     Modified the XEmacLite_EnableInterrupts and
*                     XEmacLite_DisableInterrupts functions to enable/disable
*                     the interrupt in the Ping buffer as this is used to enable
*                     the interrupts for both Ping and Pong Buffers.
*                     The interrupt enable bit in the Pong buffer is not used by
*                     the HW.
*                     Modified XEmacLite_Send function to use Ping buffers
*                     Interrupt enable bit since this alone is used to enable
*                     the interrupts for both Ping and Pong Buffers.
* 3.00a ktn  10/22/09 Updated driver to use the HAL Processor APIs/macros.
*		      The macros have been renamed to remove _m from the name in
*		      all the driver files.
*		      The macros changed in this file are
*		      XEmacLite_mNextTransmitAddr is XEmacLite_NextTransmitAddr,
*		      XEmacLite_mNextReceiveAddr is XEmacLite_NextReceiveAddr,
*		      XEmacLite_mIsMdioConfigured is XEmacLite_IsMdioConfigured,
*		      XEmacLite_mIsLoopbackConfigured is
*		      XEmacLite_IsLoopbackConfigured.
*		      See xemaclite_i.h for the macros which have changed.
* 3.01a ktn  07/08/10 The macro XEmacLite_GetReceiveDataLength in the
*		      xemaclite.c file is changed to a static function.
*		      XEmacLite_GetReceiveDataLength and XEmacLite_Recv
*		      functions  are updated to support little endian
*		      MicroBlaze.
* 3.02a sdm  07/22/11 Removed redundant code in XEmacLite_Recv functions for
*		      CR617290
* 3.03a asa  04/05/12 Defined the flag __LITTLE_ENDIAN__ for cases where the
*		      driver is compiled with ARM toolchain.
* 3.04a srt  04/13/13 Removed warnings (CR 705000).
* 4.0   adk  19/12/13 Updated as per the New Tcl API's
* 4.1	nsk  07/13/15 Added Length check in XEmacLite_AlignedWrite function
*		      in xemaclite_l.c file to avoid extra write operation
*		      (CR 843707).
* 4.2   sk   11/10/15 Used UINTPTR instead of u32 for Baseaddress CR# 867425.
*                     Changed the prototype of XEmacLite_CfgInitialize API.
* 4.2   adk  11/18/15 Fix compilation errors due to conflicting data types
*		      CR#917930
* 4.2	adk  29/02/16 Updated interrupt example to support Zynq and ZynqMP
*		      CR#938244.
*
* </pre>
*
*
******************************************************************************/
#ifndef XEMACLITE_H		/* prevent circular inclusions */
#define XEMACLITE_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xenv.h"
#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xemaclite_l.h"

#ifdef __ARMEL__
#ifndef __LITTLE_ENDIAN__
#define __LITTLE_ENDIAN__
#endif
#endif
/************************** Constant Definitions *****************************/
/*
 * Device information
 */
#define XEL_DEVICE_NAME	 "xemaclite"
#define XEL_DEVICE_DESC	 "Xilinx Ethernet Lite 10/100 MAC"

/**************************** Type Definitions *******************************/

/**
 * This typedef contains configuration information for a device.
 */
typedef struct {
	u16 DeviceId;	 /**< Unique ID  of device */
	UINTPTR BaseAddress; /**< Device base address */
	u8 TxPingPong;	 /**< 1 if TX Pong buffer configured, 0 otherwise */
	u8 RxPingPong;	 /**< 1 if RX Pong buffer configured, 0 otherwise */
	u8 MdioInclude;  /**< 1 if MDIO is enabled, 0 otherwise */
	u8 Loopback;     /**< 1 if internal loopback is enabled, 0 otherwise */
} XEmacLite_Config;


/*
 * Callback when data is sent or received .
 * @param 	CallBackRef is a callback reference passed in by the upper layer
 *		when setting the callback functions, and passed back to the
 *		upper layer when the callback is invoked.
 */
typedef void (*XEmacLite_Handler) (void *CallBackRef);

/**
 * The XEmacLite driver instance data. The user is required to allocate a
 * variable of this type for every EmacLite device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XEmacLite_Config EmacLiteConfig; /* Device configuration */
	u32 IsReady;			 /* Device is initialized and ready */

	u32 NextTxBufferToUse;		 /* Next TX buffer to write to */
	u32 NextRxBufferToUse;		 /* Next RX buffer to read from */

	/*
	 * Callbacks
	 */
	XEmacLite_Handler RecvHandler;
	void *RecvRef;
	XEmacLite_Handler SendHandler;
	void *SendRef;

} XEmacLite;

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Return the next expected Transmit Buffer's address.
*
* @param	InstancePtr is the pointer to the instance of the driver to
*		be worked on
*
* @note		C-Style signature:
*		u32 XEmacLite_NextTransmitAddr(XEmacLite *InstancePtr);
*
* This macro returns the address of the next transmit buffer to put data into.
* This is used to determine the destination of the next transmit data frame.
*
*****************************************************************************/
#define XEmacLite_NextTransmitAddr(InstancePtr) 			\
	((InstancePtr)->EmacLiteConfig.BaseAddress + 			\
		(InstancePtr)->NextTxBufferToUse) + XEL_TXBUFF_OFFSET

/****************************************************************************/
/**
*
* Return the next expected Receive Buffer's address.
*
* @param	InstancePtr is the pointer to the instance of the driver to
*		be worked on
*
* @note		C-Style signature:
*		u32 XEmacLite_NextReceiveAddr(XEmacLite *InstancePtr);
*
* This macro returns the address of the next receive buffer to read data from.
* This is the expected receive buffer address if the driver is in sync.
*
*****************************************************************************/
#define XEmacLite_NextReceiveAddr(InstancePtr)				\
	((InstancePtr)->EmacLiteConfig.BaseAddress + 			\
	(InstancePtr)->NextRxBufferToUse)

/*****************************************************************************/
/**
*
* This macro determines if the device is currently configured for MDIO.
*
* @param	InstancePtr is the pointer to the instance of the
*		EmacLite driver.
*
* @return
* 		- TRUE if the device is configured for MDIO.
*		- FALSE if the device is NOT configured for MDIO.
*
* @note		C-Style signature:
*		int XEmacLite_IsMdioConfigured(XEmacLite *InstancePtr)
*
******************************************************************************/
#define XEmacLite_IsMdioConfigured(InstancePtr) 			\
	((InstancePtr)->EmacLiteConfig.MdioInclude == 1)

/*****************************************************************************/
/**
*
* This macro determines if the device is currently configured for internal
* loopback.
*
* @param	InstancePtr is the pointer to the instance of the
*		EmacLite driver.
*
* @return
* 		- TRUE if the device is configured for internal loopback.
*		- FALSE if the device is NOT configured for internal loopback.
*
* @note		C-Style signature:
*		int XEmacLite_IsLoopbackConfigured(XEmacLite *InstancePtr)
*
******************************************************************************/
#define XEmacLite_IsLoopbackConfigured(InstancePtr) 			\
            ((InstancePtr)->EmacLiteConfig.Loopback == 1)

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/*
 * Functions in xemaclite.c
 */
int XEmacLite_CfgInitialize(XEmacLite *InstancePtr,
				XEmacLite_Config *EmacLiteConfigPtr,
				UINTPTR EffectiveAddr);
void XEmacLite_SetMacAddress(XEmacLite *InstancePtr, u8 *AddressPtr);
int XEmacLite_TxBufferAvailable(XEmacLite *InstancePtr);
void XEmacLite_FlushReceive(XEmacLite *InstancePtr);

int XEmacLite_Send(XEmacLite *InstancePtr, u8 *FramePtr, unsigned ByteCount);
u16 XEmacLite_Recv(XEmacLite *InstancePtr, u8 *FramePtr);

int XEmacLite_PhyRead(XEmacLite *InstancePtr, u32 PhyAddress, u32 RegNum,
			u16 *PhyDataPtr);
int XEmacLite_PhyWrite(XEmacLite *InstancePtr, u32 PhyAddress, u32 RegNum,
			u16 PhyData);

void XEmacLite_EnableLoopBack(XEmacLite *InstancePtr);
void XEmacLite_DisableLoopBack(XEmacLite *InstancePtr);

/*
 * Initialization functions in xemaclite_sinit.c
 */
XEmacLite_Config *XEmacLite_LookupConfig(u16 DeviceId);
int XEmacLite_Initialize(XEmacLite *InstancePtr, u16 DeviceId);

/*
 * Interrupt driven functions in xemaclite_intr.c
 */
int XEmacLite_EnableInterrupts(XEmacLite *InstancePtr);
void XEmacLite_DisableInterrupts(XEmacLite *InstancePtr);

void XEmacLite_InterruptHandler(void *InstancePtr);

void XEmacLite_SetRecvHandler(XEmacLite *InstancePtr, void *CallBackRef,
			      XEmacLite_Handler FuncPtr);
void XEmacLite_SetSendHandler(XEmacLite *InstancePtr, void *CallBackRef,
			      XEmacLite_Handler FuncPtr);

/*
 * Selftest function in xemaclite_selftest.c
 */
int XEmacLite_SelfTest(XEmacLite *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */


/** @} */
