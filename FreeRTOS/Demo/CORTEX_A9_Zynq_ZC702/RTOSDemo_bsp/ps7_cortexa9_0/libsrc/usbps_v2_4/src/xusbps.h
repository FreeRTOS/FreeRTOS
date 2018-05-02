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
 * @file xusbps.h
* @addtogroup usbps_v2_4
* @{
* @details
 *
 * This file contains the implementation of the XUsbPs driver. It is the
 * driver for an USB controller in DEVICE or HOST mode.
 *
 * <h2>Introduction</h2>
 *
 * The Spartan-3AF Embedded Peripheral Block contains a USB controller for
 * communication with serial peripherals or hosts. The USB controller supports
 * Host, Device and On the Go (OTG) applications.
 *
 * <h2>USB Controller Features</h2>
 *
 * - Supports Low Speed USB 1.1 (1.5Mbps), Full Speed USB 1.1 (12Mbps), and
 *   High Speed USB 2.0 (480Mbps) data speeds
 * - Supports Device, Host and OTG operational modes
 * - ULPI transceiver interface for USB 2.0 operation
 * - Integrated USB Full and Low speed serial transceiver interfaces for lowest
 *   cost connections
 *
 * <h2>Initialization & Configuration</h2>
 *
 * The configuration of the USB driver happens in multiple stages:
 *
 * - (a) Configuration of the basic parameters:
 *   In this stage the basic parameters for the driver are configured,
 *   including the base address and the controller ID.
 *
 * - (b) Configuration of the DEVICE endpoints (if applicable):
 *   If DEVICE mode is desired, the endpoints of the controller need to be
 *   configured using the XUsbPs_DeviceConfig data structure. Once the
 *   endpoint configuration is set up in the data structure, The user then
 *   needs to allocate the required amount of DMAable memory and
 *   finalize the configuration of the XUsbPs_DeviceConfig data structure,
 *   e.g. setting the DMAMemVirt and DMAMemPhys members.
 *
 * - (c) Configuration of the DEVICE modes:
 *   In the second stage the parameters for DEVICE are configured.
 *   The caller only needs to configure the modes that are
 *   actually used. Configuration is done with the:
 *   	XUsbPs_ConfigureDevice()
 * Configuration parameters are defined and passed
 *   into these functions using the:
 *      XUsbPs_DeviceConfig data structures.
 *
 *
 * <h2>USB Device Endpoints</h2>
 *
 * The USB core supports up to 4 endpoints. Each endpoint has two directions,
 * an OUT (RX) and an IN (TX) direction. Note that the direction is viewed from
 * the host's perspective. Endpoint 0 defaults to be the control endpoint and
 * does not need to be set up. Other endpoints need to be configured and set up
 * depending on the application. Only endpoints that are actuelly used by the
 * application need to be initialized.
 * See the example code (xusbps_intr_example.c) for more information.
 *
 *
 * <h2>Interrupt Handling</h2>
 *
 * The USB core uses one interrupt line to report interrupts to the CPU.
 * Interrupts are handled by the driver's interrupt handler function
 * XUsbPs_IntrHandler().
 * It has to be registered with the OS's interrupt subsystem. The driver's
 * interrupt handler divides incoming interrupts into two categories:
 *
 *  - General device interrupts
 *  - Endopint related interrupts
 *
 * The user (typically the adapter layer) can register general interrupt
 * handler fucntions and endpoint specific interrupt handler functions with the
 * driver to receive those interrupts by calling the
 *    XUsbPs_IntrSetHandler()
 * and
 *    XUsbPs_EpSetHandler()
 * functions respectively. Calling these functions with a NULL pointer as the
 * argument for the function pointer will "clear" the handler function.
 *
 * The user can register one handler function for the generic interrupts and
 * two handler functions for each endpoint, one for the RX (OUT) and one for
 * the TX (IN) direction. For some applications it may be useful to register a
 * single endpoint handler function for muliple endpoints/directions.
 *
 * When a callback function is called by the driver, parameters identifying the
 * type of the interrupt will be passed into the handler functions. For general
 * interrupts the interrupt mask will be passed into the handler function. For
 * endpoint interrupts the parameters include the number of the endpoint, the
 * direction (OUT/IN) and the type of the interrupt.
 *
 *
 * <h2>Data buffer handling</h2>
 *
 * Data buffers are sent to and received from endpoint using the
 *    XUsbPs_EpBufferSend(), XUsbPs_EpBufferSendWithZLT()
 * and
 *    XUsbPs_EpBufferReceive()
 * functions.
 *
 * User data buffer size is limited to 16 Kbytes. If the user wants to send a
 * data buffer that is bigger than this limit it needs to break down the data
 * buffer into multiple fragments and send the fragments individually.
 *
 * From the controller perspective Data buffers can be aligned at any boundary.
 * if the buffers are from cache region then the buffer and buffer size should
 * be aligned to cache line aligned
 *
 *
 * <h3>Zero copy</h3>
 *
 * The driver uses a zero copy mechanism which imposes certain restrictions to
 * the way the user can handle the data buffers.
 *
 * One restriction is that the user needs to release a buffer after it is done
 * processing the data in the buffer.
 *
 * Similarly, when the user sends a data buffer it MUST not re-use the buffer
 * until it is notified by the driver that the buffer has been transmitted. The
 * driver will notify the user via the registered endpoint interrupt handling
 * function by sending a XUSBPS_EP_EVENT_DATA_TX event.
 *
 *
 * <h2>DMA</h2>
 *
 * The driver uses DMA internally to move data from/to memory. This behaviour
 * is transparent to the user. Keeping the DMA handling hidden from the user
 * has the advantage that the same API can be used with USB cores that do not
 * support DMA.
 *
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- ----------------------------------------------------------
 * 1.00a wgr  10/10/10 First release
 * 1.02a wgr  05/16/12 Removed comments as they are showing up in SDK
 *		       Tabs for CR 657898
 * 1.03a nm   09/21/12 Fixed CR#678977. Added proper sequence for setup packet
 *                    handling.
 * 1.04a nm   10/23/12 Fixed CR# 679106.
 *	      11/02/12 Fixed CR# 683931. Mult bits are set properly in dQH.
 * 2.00a kpc 04/03/14 Fixed CR#777763. Corrected the setup tripwire macro val.
 * 2.1   kpc 04/28/14 Removed unused function prototypes
 * 2.2   kpc 08/23/14 Exported XUsbPs_DeviceReset API as global for calling in
 *                    code coverage tests.
 * 2.3   kpc 02/19/14 Fixed CR#873972, CR#873974. Corrected the logic for proper
 *                    moving of dTD Head/Tail Pointers. Invalidate the cache
 *                    after buffer receive in Endpoint Buffer Handler.
 * 2.4   sg  04/26/16 Fixed CR#949693, Corrected the logic for EP flush
 *       ms  03/17/17 Added readme.txt file in examples folder for doxygen
 *                    generation.
 *       ms  04/10/17 Modified filename tag to include the file in doxygen
 *                    examples.
 * </pre>
 *
 ******************************************************************************/

#ifndef XUSBPS_H
#define XUSBPS_H

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xusbps_hw.h"
#include "xil_types.h"
#include "xstatus.h"

/************************** Constant Definitions *****************************/

/**
 * @name System hang prevention Timeout counter value.
 *
 * This value is used throughout the code to initialize a Timeout counter that
 * is used when hard polling a register. The ides is to initialize the Timeout
 * counter to a value that is longer than any expected Timeout but short enough
 * so the system will continue to work and report an error while the user is
 * still paying attention. A reasonable Timeout time would be about 10 seconds.
 * The XUSBPS_TIMEOUT_COUNTER value should be chosen so a polling loop would
 * run about 10 seconds before a Timeout is detected. For example:
 *
 * 	int Timeout = XUSBPS_TIMEOUT_COUNTER;
 *	while ((XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
 *				XUSBPS_CMD_OFFSET) &
 *				XUSBPS_CMD_RST_MASK) && --Timeout) {
 *		;
 *	}
 *	if (0 == Timeout) {
 *		return XST_FAILURE;
 *	}
 *
 */
#define XUSBPS_TIMEOUT_COUNTER		1000000


/**
 * @name Endpoint Direction (bitmask)
 * Definitions to be used with Endpoint related function that require a
 * 'Direction' parameter.
 *
 * NOTE:
 *   The direction is always defined from the perspective of the HOST! This
 *   means that an IN endpoint on the controller is used for sending data while
 *   the OUT endpoint on the controller is used for receiving data.
 * @{
 */
#define XUSBPS_EP_DIRECTION_IN		0x01 /**< Endpoint direction IN. */
#define XUSBPS_EP_DIRECTION_OUT		0x02 /**< Endpoint direction OUT. */
/* @} */


/**
 * @name Endpoint Type
 * Definitions to be used with Endpoint related functions that require a 'Type'
 * parameter.
 * @{
 */
#define XUSBPS_EP_TYPE_NONE		0 /**< Endpoint is not used. */
#define XUSBPS_EP_TYPE_CONTROL		1 /**< Endpoint for Control Transfers */
#define XUSBPS_EP_TYPE_ISOCHRONOUS 	2 /**< Endpoint for isochronous data */
#define XUSBPS_EP_TYPE_BULK		3 /**< Endpoint for BULK Transfers. */
#define XUSBPS_EP_TYPE_INTERRUPT	4 /**< Endpoint for interrupt Transfers */
/* @} */

/**
 * Endpoint Max Packet Length in DeviceConfig is a coded value, ch9.6.6.
 *
 * @{
 */
#define ENDPOINT_MAXP_LENGTH		0x400
#define ENDPOINT_MAXP_MULT_MASK		0xC00
#define ENDPOINT_MAXP_MULT_SHIFT	10
/* @} */

/**
 * @name Field names for status retrieval
 * Definitions for the XUsbPs_GetStatus() function call 'StatusType'
 * parameter.
 * @{
 */
#define XUSBPS_EP_STS_ADDRESS		1 /**< Address of controller. */
#define XUSBPS_EP_STS_CONTROLLER_STATE	2 /**< Current controller state. */
/* @} */



/**
 * @name USB Default alternate setting
 *
 * @{
 */
#define XUSBPS_DEFAULT_ALT_SETTING	0 /**< The default alternate setting is 0 */
/* @} */

/**
 * @name Endpoint event types
 * Definitions that are used to identify events that occur on endpoints. Passed
 * to the endpoint event handler functions registered with
 * XUsbPs_EpSetHandler().
 * @{
 */
#define XUSBPS_EP_EVENT_SETUP_DATA_RECEIVED	0x01
			/**< Setup data has been received on the enpoint. */
#define XUSBPS_EP_EVENT_DATA_RX		0x02
			/**< Data frame has been received on the endpoint. */
#define XUSBPS_EP_EVENT_DATA_TX		0x03
			/**< Data frame has been sent on the endpoint. */
/* @} */


/*
 * Maximum packet size for endpoint, 1024
 * @{
 */
#define XUSBPS_MAX_PACKET_SIZE		1024
				/**< Maximum value can be put into the queue head */
/* @} */
/**************************** Type Definitions *******************************/

/******************************************************************************
 * This data type defines the callback function to be used for Endpoint
 * handlers.
 *
 * @param	CallBackRef is the Callback reference passed in by the upper
 *		layer when setting the handler, and is passed back to the upper
 *		layer when the handler is called.
 * @param	EpNum is the Number of the endpoint that caused the event.
 * @param	EventType is the type of the event that occured on the endpoint.
 * @param	Data is a pointer to user data pointer specified when callback
 *		was registered.
 */
typedef void (*XUsbPs_EpHandlerFunc)(void *CallBackRef,
				      u8 EpNum, u8 EventType, void *Data);


/******************************************************************************
 * This data type defines the callback function to be used for the general
 * interrupt handler.
 *
 * @param	CallBackRef is the Callback reference passed in by the upper
 *		layer when setting the handler, and is passed back to the upper
 *		layer when the handler is called.
 * @param	IrqMask is the Content of the interrupt status register. This
 *		value can be used by the callback function to distinguish the
 *		individual interrupt types.
 */
typedef void (*XUsbPs_IntrHandlerFunc)(void *CallBackRef, u32 IrqMask);


/******************************************************************************/

/* The following type definitions are used for referencing Queue Heads and
 * Transfer Descriptors. The structures themselves are not used, however, the
 * types are used in the API to avoid using (void *) pointers.
 */
typedef u8	XUsbPs_dQH[XUSBPS_dQH_ALIGN];
typedef u8	XUsbPs_dTD[XUSBPS_dTD_ALIGN];


/**
 * The following data structures are used internally by the L0/L1 driver.
 * Their contents MUST NOT be changed by the upper layers.
 */

/**
 * The following data structure represents OUT endpoint.
 */
typedef struct {
	XUsbPs_dQH	*dQH;
		/**< Pointer to the Queue Head structure of the endpoint. */

	XUsbPs_dTD	*dTDs;
		/**< Pointer to the first dTD of the dTD list for this
		 * endpoint. */

	XUsbPs_dTD	*dTDCurr;
		/**< Buffer to the currently processed descriptor. */

	u8	*dTDBufs;
		/**< Pointer to the first buffer of the buffer list for this
		 * endpoint. */

	XUsbPs_EpHandlerFunc	HandlerFunc;
		/**< Handler function for this endpoint. */
	void			*HandlerRef;
		/**< User data reference for the handler. */
} XUsbPs_EpOut;


/**
 * The following data structure represents IN endpoint.
 */
typedef struct {
	XUsbPs_dQH	*dQH;
		/**< Pointer to the Queue Head structure of the endpoint. */

	XUsbPs_dTD	*dTDs;
		/**< List of pointers to the Transfer Descriptors of the
		 * endpoint. */

	XUsbPs_dTD	*dTDHead;
		/**< Buffer to the next available descriptor in the list. */

	XUsbPs_dTD	*dTDTail;
		/**< Buffer to the last unsent descriptor in the list*/

	XUsbPs_EpHandlerFunc	HandlerFunc;
		/**< Handler function for this endpoint. */
	void			*HandlerRef;
		/**< User data reference for the handler. */
} XUsbPs_EpIn;


/**
 * The following data structure represents an endpoint used internally
 * by the L0/L1 driver.
 */
typedef struct {
	/* Each endpoint has an OUT and an IN component.
	 */
	XUsbPs_EpOut	Out;	/**< OUT endpoint structure */
	XUsbPs_EpIn	In;	/**< IN endpoint structure */
} XUsbPs_Endpoint;



/**
 * The following structure is used by the user to receive Setup Data from an
 * endpoint. Using this structure simplifies the process of interpreting the
 * setup data in the core's data fields.
 *
 * The naming scheme for the members of this structure is different from the
 * naming scheme found elsewhere in the code. The members of this structure are
 * defined in the Chapter 9 USB reference guide. Using this naming scheme makes
 * it easier for people familiar with the standard to read the code.
 */
typedef struct {
	u8  bmRequestType;	/**< bmRequestType in setup data */
	u8  bRequest;		/**< bRequest in setup data */
	u16 wValue;		/**< wValue in setup data */
	u16 wIndex;		/**< wIndex in setup data */
	u16 wLength;		/**< wLength in setup data */
}
XUsbPs_SetupData;


/**
 * Data structures used to configure endpoints.
 */
typedef struct {
	u32	Type;
		/**< Endpoint type:
			- XUSBPS_EP_TYPE_CONTROL
			- XUSBPS_EP_TYPE_ISOCHRONOUS
			- XUSBPS_EP_TYPE_BULK
			- XUSBPS_EP_TYPE_INTERRUPT */

	u32	NumBufs;
		/**< Number of buffers to be handled by this endpoint. */
	u32	BufSize;
		/**< Buffer size. Only relevant for OUT (receive) Endpoints. */

	u16	MaxPacketSize;
		/**< Maximum packet size for this endpoint. This number will
		 * define the maximum number of bytes sent on the wire per
		 * transaction. Range: 0..1024 */
} XUsbPs_EpSetup;


/**
 * Endpoint configuration structure.
 */
typedef struct {
	XUsbPs_EpSetup		Out; /**< OUT component of endpoint. */
	XUsbPs_EpSetup		In;  /**< IN component of endpoint. */
} XUsbPs_EpConfig;


/**
 * The XUsbPs_DeviceConfig structure contains the configuration information to
 * configure the USB controller for DEVICE mode. This data structure is used
 * with the XUsbPs_ConfigureDevice() function call.
 */
typedef struct {
	u8  NumEndpoints;	/**< Number of Endpoints for the controller.
				  This number depends on the runtime
				  configuration of driver. The driver may
				  configure fewer endpoints than are available
				  in the core. */

	XUsbPs_EpConfig	EpCfg[XUSBPS_MAX_ENDPOINTS];
				/**< List of endpoint configurations. */


	u32 DMAMemPhys;		/**< Physical base address of DMAable memory
				  allocated for the driver. */

	/* The following members are used internally by the L0/L1 driver.  They
	 * MUST NOT be accesses and/or modified in any way by the upper layers.
	 *
	 * The reason for having these members is that we generally try to
	 * avoid allocating memory in the L0/L1 driver as we want to be OS
	 * independent. In order to avoid allocating memory for this data
	 * structure wihin L0/L1 we put it into the XUsbPs_DeviceConfig
	 * structure which is allocated by the caller.
	 */
	XUsbPs_Endpoint	Ep[XUSBPS_MAX_ENDPOINTS];
				/**< List of endpoint metadata structures. */

	u32 PhysAligned;	/**< 64 byte aligned base address of the DMA
				   memory block. Will be computed and set by
				   the L0/L1 driver. */
} XUsbPs_DeviceConfig;


/**
 * The XUsbPs_Config structure contains configuration information for the USB
 * controller.
 *
 * This structure only contains the basic configuration for the controller. The
 * caller also needs to initialize the controller for the DEVICE mode
 * using the XUsbPs_DeviceConfig data structures with the
 * XUsbPs_ConfigureDevice() function call
 */
typedef struct {
	u16 DeviceID;		/**< Unique ID of controller. */
	u32 BaseAddress;	/**< Core register base address. */
} XUsbPs_Config;


/**
 * The XUsbPs driver instance data. The user is required to allocate a
 * variable of this type for every USB controller in the system. A pointer to a
 * variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XUsbPs_Config Config;	/**< Configuration structure */

	int CurrentAltSetting;	/**< Current alternative setting of interface */

	void *UserDataPtr;	/**< Data pointer to be used by upper layers to
				  store application dependent data structures.
				  The upper layers are responsible to allocated
				  and free the memory. The driver will not
				  mofidy this data pointer. */

	/**
	 * The following structures hold the configuration for DEVICE mode
	 * of the controller. They are initialized using the
	 * XUsbPs_ConfigureDevice() function call.
	 */
	XUsbPs_DeviceConfig	DeviceConfig;
				/**< Configuration for the DEVICE mode. */

	XUsbPs_IntrHandlerFunc	HandlerFunc;
		/**< Handler function for the controller. */
	void			*HandlerRef;
		/**< User data reference for the handler. */
	u32			HandlerMask;
		/**< User interrupt mask. Defines which interrupts will cause
		 * the callback to be called. */
} XUsbPs;


/***************** Macros (Inline Functions) Definitions *********************/

/******************************************************************************
 *
 * USB CONTROLLER RELATED MACROS
 *
 ******************************************************************************/
/*****************************************************************************/
/**
 * This macro returns the current frame number.
 *
 * @param	InstancePtr is a pointer to the XUsbPs instance of the
 *		controller.
 *
 * @return	The current frame number.
 *
 * @note	C-style signature:
 *		u32 XUsbPs_GetFrameNum(const XUsbPs *InstancePtr)
 *
 ******************************************************************************/
#define XUsbPs_GetFrameNum(InstancePtr) \
	XUsbPs_ReadReg((InstancePtr)->Config.BaseAddress, XUSBPS_FRAME_OFFSET)


/*****************************************************************************/
/**
 * This macro starts the USB engine.
 *
 * @param	InstancePtr is a pointer to the XUsbPs instance of the
 *		controller.
 *
 * @note	C-style signature:
 * 		void XUsbPs_Start(XUsbPs *InstancePtr)
 *
 ******************************************************************************/
#define XUsbPs_Start(InstancePtr) \
	XUsbPs_SetBits(InstancePtr, XUSBPS_CMD_OFFSET, XUSBPS_CMD_RS_MASK)


/*****************************************************************************/
/**
 * This macro stops the USB engine.
 *
 * @param	InstancePtr is a pointer to the XUsbPs instance of the
 *		controller.
 *
 * @note	C-style signature:
 * 		void XUsbPs_Stop(XUsbPs *InstancePtr)
 *
 ******************************************************************************/
#define XUsbPs_Stop(InstancePtr) \
	XUsbPs_ClrBits(InstancePtr, XUSBPS_CMD_OFFSET, XUSBPS_CMD_RS_MASK)


/*****************************************************************************/
/**
 * This macro forces the USB engine to be in Full Speed (FS) mode.
 *
 * @param	InstancePtr is a pointer to the XUsbPs instance of the
 *		controller.
 *
 * @note	C-style signature:
 * 		void XUsbPs_ForceFS(XUsbPs *InstancePtr)
 *
 ******************************************************************************/
#define XUsbPs_ForceFS(InstancePtr)					\
	XUsbPs_SetBits(InstancePtr, XUSBPS_PORTSCR1_OFFSET,		\
 		XUSBPS_PORTSCR_PFSC_MASK)


/*****************************************************************************/
/**
 * This macro starts the USB Timer 0, with repeat option for period of
 * one second.
 *
 * @param	InstancePtr is a pointer to XUsbPs instance of the controller.
 * @param	Interval is the interval for Timer0 to generate an interrupt
 *
 * @note	C-style signature:
 *		void XUsbPs_StartTimer0(XUsbPs *InstancePtr, u32 Interval)
 *
 ******************************************************************************/
#define XUsbPs_StartTimer0(InstancePtr, Interval) 			\
{									\
	XUsbPs_WriteReg((InstancePtr)->Config.BaseAddress, 		\
			XUSBPS_TIMER0_LD_OFFSET, (Interval));		\
	XUsbPs_SetBits(InstancePtr, XUSBPS_TIMER0_CTL_OFFSET,		\
			XUSBPS_TIMER_RUN_MASK |			\
			XUSBPS_TIMER_RESET_MASK |			\
			XUSBPS_TIMER_REPEAT_MASK);			\
}									\


/*****************************************************************************/
/**
* This macro stops Timer 0.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @note		C-style signature:
*		void XUsbPs_StopTimer0(XUsbPs *InstancePtr)
*
******************************************************************************/
#define XUsbPs_StopTimer0(InstancePtr) \
	XUsbPs_ClrBits(InstancePtr, XUSBPS_TIMER0_CTL_OFFSET,		\
		XUSBPS_TIMER_RUN_MASK)


/*****************************************************************************/
/**
* This macro reads Timer 0.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @note		C-style signature:
*		void XUsbPs_ReadTimer0(XUsbPs *InstancePtr)
*
******************************************************************************/
#define XUsbPs_ReadTimer0(InstancePtr) 				\
	XUsbPs_ReadReg((InstancePtr)->Config.BaseAddress,		\
			XUSBPS_TIMER0_CTL_OFFSET) & 			\
					XUSBPS_TIMER_COUNTER_MASK


/*****************************************************************************/
/**
* This macro force remote wakeup on host
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @note		C-style signature:
*  		void XUsbPs_RemoteWakeup(XUsbPs *InstancePtr)
*
******************************************************************************/
#define XUsbPs_RemoteWakeup(InstancePtr) \
	XUsbPs_SetBits(InstancePtr, XUSBPS_PORTSCR1_OFFSET,		 \
			XUSBPS_PORTSCR_FPR_MASK)


/******************************************************************************
 *
 * ENDPOINT RELATED MACROS
 *
 ******************************************************************************/
/*****************************************************************************/
/**
* This macro enables the given endpoint for the given direction.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	EpNum is number of the endpoint to enable.
* @param	Dir is direction of the endpoint (bitfield):
* 			- XUSBPS_EP_DIRECTION_OUT
* 			- XUSBPS_EP_DIRECTION_IN
*
* @note		C-style signature:
* 		void XUsbPs_EpEnable(XUsbPs *InstancePtr, u8 EpNum, u8 Dir)
*
******************************************************************************/
#define XUsbPs_EpEnable(InstancePtr, EpNum, Dir) \
	XUsbPs_SetBits(InstancePtr, XUSBPS_EPCRn_OFFSET(EpNum),	 \
	((Dir) & XUSBPS_EP_DIRECTION_OUT ? XUSBPS_EPCR_RXE_MASK : 0) | \
	((Dir) & XUSBPS_EP_DIRECTION_IN  ? XUSBPS_EPCR_TXE_MASK : 0))


/*****************************************************************************/
/**
* This macro disables the given endpoint for the given direction.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	EpNum is the number of the endpoint to disable.
* @param	Dir is the direction of the endpoint (bitfield):
* 		- XUSBPS_EP_DIRECTION_OUT
* 		- XUSBPS_EP_DIRECTION_IN
*
* @note		C-style signature:
* 		void XUsbPs_EpDisable(XUsbPs *InstancePtr, u8 EpNum, u8 Dir)
*
******************************************************************************/
#define XUsbPs_EpDisable(InstancePtr, EpNum, Dir) \
	XUsbPs_ClrBits(InstancePtr, XUSBPS_EPCRn_OFFSET(EpNum),		 \
		((Dir) & XUSBPS_EP_DIRECTION_OUT ? XUSBPS_EPCR_RXE_MASK : 0) | \
		((Dir) & XUSBPS_EP_DIRECTION_IN  ? XUSBPS_EPCR_TXE_MASK : 0))


/*****************************************************************************/
/**
* This macro stalls the given endpoint for the given direction, and flush
* the buffers.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	EpNum is number of the endpoint to stall.
* @param	Dir is the direction of the endpoint (bitfield):
* 			- XUSBPS_EP_DIRECTION_OUT
* 			- XUSBPS_EP_DIRECTION_IN
*
* @note		C-style signature:
*		void XUsbPs_EpStall(XUsbPs *InstancePtr, u8 EpNum, u8 Dir)
*
******************************************************************************/
#define XUsbPs_EpStall(InstancePtr, EpNum, Dir) \
	XUsbPs_SetBits(InstancePtr, XUSBPS_EPCRn_OFFSET(EpNum),	 \
	((Dir) & XUSBPS_EP_DIRECTION_OUT ? XUSBPS_EPCR_RXS_MASK : 0) | \
	((Dir) & XUSBPS_EP_DIRECTION_IN  ? XUSBPS_EPCR_TXS_MASK : 0))


/*****************************************************************************/
/**
* This macro unstalls the given endpoint for the given direction.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	EpNum is the Number of the endpoint to unstall.
* @param	Dir is the Direction of the endpoint (bitfield):
* 		- XUSBPS_EP_DIRECTION_OUT
* 		- XUSBPS_EP_DIRECTION_IN
*
* @note		C-style signature:
* 		void XUsbPs_EpUnStall(XUsbPs *InstancePtr, u8 EpNum, u8 Dir)
*
******************************************************************************/
#define XUsbPs_EpUnStall(InstancePtr, EpNum, Dir) \
	XUsbPs_ClrBits(InstancePtr, XUSBPS_EPCRn_OFFSET(EpNum),	 \
	((Dir) & XUSBPS_EP_DIRECTION_OUT ? XUSBPS_EPCR_RXS_MASK : 0) | \
	((Dir) & XUSBPS_EP_DIRECTION_IN  ? XUSBPS_EPCR_TXS_MASK : 0))


/*****************************************************************************/
/**
* This macro flush an endpoint upon interface disable
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	EpNum is the number of the endpoint to flush.
* @param	Dir is the direction of the endpoint (bitfield):
* 			- XUSBPS_EP_DIRECTION_OUT
* 			- XUSBPS_EP_DIRECTION_IN
*
* @note		C-style signature:
*		void XUsbPs_EpFlush(XUsbPs *InstancePtr, u8 EpNum, u8 Dir)
*
******************************************************************************/
#define XUsbPs_EpFlush(InstancePtr, EpNum, Dir) \
	XUsbPs_SetBits(InstancePtr, XUSBPS_EPFLUSH_OFFSET,	\
		1 << (EpNum + ((Dir) & XUSBPS_EP_DIRECTION_OUT ?		\
			XUSBPS_EPFLUSH_RX_SHIFT:XUSBPS_EPFLUSH_TX_SHIFT))) \

/*****************************************************************************/
/**
* This macro enables the interrupts defined by the bit mask.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	IntrMask is the Bit mask of interrupts to be enabled.
*
* @note		C-style signature:
*		void XUsbPs_IntrEnable(XUsbPs *InstancePtr, u32 IntrMask)
*
******************************************************************************/
#define XUsbPs_IntrEnable(InstancePtr, IntrMask)	\
		XUsbPs_SetBits(InstancePtr, XUSBPS_IER_OFFSET, IntrMask)


/*****************************************************************************/
/**
* This function disables the interrupts defined by the bit mask.
*
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	IntrMask is a Bit mask of interrupts to be disabled.
*
* @note		C-style signature:
* 		void XUsbPs_IntrDisable(XUsbPs *InstancePtr, u32 IntrMask)
*
******************************************************************************/
#define XUsbPs_IntrDisable(InstancePtr, IntrMask)	\
		XUsbPs_ClrBits(InstancePtr, XUSBPS_IER_OFFSET, IntrMask)


/*****************************************************************************/
/**
* This macro enables the endpoint NAK interrupts defined by the bit mask.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	NakIntrMask is the Bit mask of endpoint NAK interrupts to be
*		enabled.
* @note		C-style signature:
* 		void XUsbPs_NakIntrEnable(XUsbPs *InstancePtr, u32 NakIntrMask)
*
******************************************************************************/
#define XUsbPs_NakIntrEnable(InstancePtr, NakIntrMask)	\
	XUsbPs_SetBits(InstancePtr, XUSBPS_EPNAKIER_OFFSET, NakIntrMask)


/*****************************************************************************/
/**
* This macro disables the endpoint NAK interrupts defined by the bit mask.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	NakIntrMask is a Bit mask of endpoint NAK interrupts to be
*		disabled.
*
* @note
* 	C-style signature:
* 	void XUsbPs_NakIntrDisable(XUsbPs *InstancePtr, u32 NakIntrMask)
*
******************************************************************************/
#define XUsbPs_NakIntrDisable(InstancePtr, NakIntrMask)	\
	XUsbPs_ClrBits(InstancePtr, XUSBPS_EPNAKIER_OFFSET, NakIntrMask)


/*****************************************************************************/
/**
* This function clears the endpoint NAK interrupts status defined by the
* bit mask.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	NakIntrMask is the Bit mask of endpoint NAK interrupts to be cleared.
*
* @note		C-style signature:
* 		void XUsbPs_NakIntrClear(XUsbPs *InstancePtr, u32 NakIntrMask)
*
******************************************************************************/
#define XUsbPs_NakIntrClear(InstancePtr, NakIntrMask)			\
	XUsbPs_WriteReg((InstancePtr)->Config.BaseAddress,		\
				XUSBPS_EPNAKISR_OFFSET, NakIntrMask)



/*****************************************************************************/
/**
* This macro sets the Interrupt Threshold value in the control register
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	Threshold is the Interrupt threshold to be set.
* 		Allowed values:
*			- XUSBPS_CMD_ITHRESHOLD_0 - Immediate interrupt
*			- XUSBPS_CMD_ITHRESHOLD_1 - 1 Frame
*			- XUSBPS_CMD_ITHRESHOLD_2 - 2 Frames
*			- XUSBPS_CMD_ITHRESHOLD_4 - 4 Frames
*			- XUSBPS_CMD_ITHRESHOLD_8 - 8 Frames
*			- XUSBPS_CMD_ITHRESHOLD_16 - 16 Frames
*			- XUSBPS_CMD_ITHRESHOLD_32 - 32 Frames
*			- XUSBPS_CMD_ITHRESHOLD_64 - 64 Frames
*
* @note
* 	C-style signature:
*	void XUsbPs_SetIntrThreshold(XUsbPs *InstancePtr, u8 Threshold)
*
******************************************************************************/
#define XUsbPs_SetIntrThreshold(InstancePtr, Threshold)		\
		XUsbPs_WriteReg((InstancePtr)->Config.BaseAddress,	\
					XUSBPS_CMD_OFFSET, (Threshold))\


/*****************************************************************************/
/**
* This macro sets the Tripwire bit in the USB command register.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @note		C-style signature:
*		void XUsbPs_SetTripwire(XUsbPs *InstancePtr)
*
******************************************************************************/
#define XUsbPs_SetSetupTripwire(InstancePtr)				\
		XUsbPs_SetBits(InstancePtr, XUSBPS_CMD_OFFSET,	\
				XUSBPS_CMD_SUTW_MASK)


/*****************************************************************************/
/**
* This macro clears the Tripwire bit in the USB command register.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @note		C-style signature:
*		void XUsbPs_ClrTripwire(XUsbPs *InstancePtr)
*
******************************************************************************/
#define XUsbPs_ClrSetupTripwire(InstancePtr)				\
		XUsbPs_ClrBits(InstancePtr, XUSBPS_CMD_OFFSET,	\
				XUSBPS_CMD_SUTW_MASK)


/*****************************************************************************/
/**
* This macro checks if the Tripwire bit in the USB command register is set.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @return
* 		- TRUE: The tripwire bit is still set.
* 		- FALSE: The tripwire bit has been cleared.
*
* @note		C-style signature:
*		int XUsbPs_TripwireIsSet(XUsbPs *InstancePtr)
*
******************************************************************************/
#define XUsbPs_SetupTripwireIsSet(InstancePtr)				\
		(XUsbPs_ReadReg((InstancePtr)->Config.BaseAddress, 	\
				XUSBPS_CMD_OFFSET) &			\
				XUSBPS_CMD_SUTW_MASK ? TRUE : FALSE)


/******************************************************************************
*
* GENERAL REGISTER / BIT MANIPULATION MACROS
*
******************************************************************************/
/****************************************************************************/
/**
* This macro sets the given bit mask in the register.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	RegOffset is the register offset to be written.
* @param	Bits is the Bits to be set in the register
*
* @return	None.
*
* @note		C-style signature:
*		void XUsbPs_SetBits(u32 BaseAddress, u32 RegOffset, u32 Bits)
*
*****************************************************************************/
#define XUsbPs_SetBits(InstancePtr, RegOffset, Bits) \
	XUsbPs_WriteReg((InstancePtr)->Config.BaseAddress, RegOffset,	\
		XUsbPs_ReadReg((InstancePtr)->Config.BaseAddress, 	\
					RegOffset) | (Bits));


/****************************************************************************/
/**
*
* This macro clears the given bits in the register.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	RegOffset is the register offset to be written.
* @param	Bits are the bits to be cleared in the register
*
* @return	None.
*
* @note
* 	C-style signature:
*	void XUsbPs_ClrBits(u32 BaseAddress, u32 RegOffset, u32 Bits)
*
*****************************************************************************/
#define XUsbPs_ClrBits(InstancePtr, RegOffset, Bits) \
	XUsbPs_WriteReg((InstancePtr)->Config.BaseAddress, RegOffset,	\
		XUsbPs_ReadReg((InstancePtr)->Config.BaseAddress, 	\
				RegOffset) & ~(Bits));


/************************** Function Prototypes ******************************/

/**
 * Setup / Initialize functions.
 *
 * Implemented in file xusbps.c
 */
int XUsbPs_CfgInitialize(XUsbPs *InstancePtr,
			  const XUsbPs_Config *ConfigPtr, u32 BaseAddress);

int XUsbPs_ConfigureDevice(XUsbPs *InstancePtr,
				const XUsbPs_DeviceConfig *CfgPtr);

/**
 * Common functions used for DEVICE/HOST mode.
 */
int XUsbPs_Reset(XUsbPs *InstancePtr);

void XUsbPs_DeviceReset(XUsbPs *InstancePtr);

/**
 * DEVICE mode specific functions.
 */
int XUsbPs_BusReset(XUsbPs *InstancePtr);
int XUsbPs_SetDeviceAddress(XUsbPs *InstancePtr, u8 Address);


/**
 * Handling Suspend and Resume.
 *
 * Implemented in xusbps.c
 */
int XUsbPs_Suspend(const XUsbPs *InstancePtr);
int XUsbPs_Resume(const XUsbPs *InstancePtr);
int XUsbPs_RequestHostResume(const XUsbPs *InstancePtr);


/*
 * Functions for managing Endpoints / Transfers
 *
 * Implemented in file xusbps_endpoint.c
 */
int XUsbPs_EpBufferSend(XUsbPs *InstancePtr, u8 EpNum,
			const u8 *BufferPtr, u32 BufferLen);
int XUsbPs_EpBufferSendWithZLT(XUsbPs *InstancePtr, u8 EpNum,
			const u8 *BufferPtr, u32 BufferLen);
int XUsbPs_EpBufferReceive(XUsbPs *InstancePtr, u8 EpNum,
			u8 **BufferPtr, u32 *BufferLenPtr, u32 *Handle);
void XUsbPs_EpBufferRelease(u32 Handle);

int XUsbPs_EpSetHandler(XUsbPs *InstancePtr, u8 EpNum, u8 Direction,
			XUsbPs_EpHandlerFunc CallBackFunc,
			void *CallBackRef);
int XUsbPs_EpGetSetupData(XUsbPs *InstancePtr, int EpNum,
			XUsbPs_SetupData *SetupDataPtr);

int XUsbPs_EpPrime(XUsbPs *InstancePtr, u8 EpNum, u8 Direction);

int XUsbPs_ReconfigureEp(XUsbPs *InstancePtr, XUsbPs_DeviceConfig *CfgPtr,
			int EpNum, unsigned short NewDirection, int DirectionChanged);

/*
 * Interrupt handling functions
 *
 * Implemented in file xusbps_intr.c
 */
void XUsbPs_IntrHandler(void *InstancePtr);

int XUsbPs_IntrSetHandler(XUsbPs *InstancePtr,
			   XUsbPs_IntrHandlerFunc CallBackFunc,
			   void *CallBackRef, u32 Mask);
/*
 * Helper functions for static configuration.
 * Implemented in xusbps_sinit.c
 */
XUsbPs_Config *XUsbPs_LookupConfig(u16 DeviceId);

#ifdef __cplusplus
}
#endif

#endif /* XUSBPS_H */
/** @} */
