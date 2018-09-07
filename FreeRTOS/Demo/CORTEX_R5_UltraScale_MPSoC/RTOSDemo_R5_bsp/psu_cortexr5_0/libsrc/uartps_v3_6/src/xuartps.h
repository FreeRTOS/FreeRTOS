/******************************************************************************
*
* Copyright (C) 2010 - 2017 Xilinx, Inc.  All rights reserved.
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
/****************************************************************************/
/**
*
* @file xuartps.h
* @addtogroup uartps_v3_5
* @{
* @details
*
* This driver supports the following features:
*
* - Dynamic data format (baud rate, data bits, stop bits, parity)
* - Polled mode
* - Interrupt driven mode
* - Transmit and receive FIFOs (32 byte FIFO depth)
* - Access to the external modem control lines
*
* <b>Initialization & Configuration</b>
*
* The XUartPs_Config structure is used by the driver to configure itself.
* Fields inside this structure are properties of XUartPs based on its hardware
* build.
*
* To support multiple runtime loading and initialization strategies employed
* by various operating systems, the driver instance can be initialized in the
* following way:
*
*   - XUartPs_CfgInitialize(InstancePtr, CfgPtr, EffectiveAddr) - Uses a
*	 configuration structure provided by the caller. If running in a system
*	 with address translation, the parameter EffectiveAddr should be the
* 	  virtual address.
*
* <b>Baud Rate</b>
*
* The UART has an internal baud rate generator, which furnishes the baud rate
* clock for both the receiver and the transmitter. Ther input clock frequency
* can be either the master clock or the master clock divided by 8, configured
* through the mode register.
*
* Accompanied with the baud rate divider register, the baud rate is determined
* by:
* <pre>
*	baud_rate = input_clock / (bgen * (bdiv + 1)
* </pre>
* where bgen is the value of the baud rate generator, and bdiv is the value of
* baud rate divider.
*
* <b>Interrupts</b>
*
* The FIFOs are not flushed when the driver is initialized, but a function is
* provided to allow the user to reset the FIFOs if desired.
*
* The driver defaults to no interrupts at initialization such that interrupts
* must be enabled if desired. An interrupt is generated for one of the
* following conditions.
*
* - A change in the modem signals
* - Data in the receive FIFO for a configuable time without receiver activity
* - A parity error
* - A framing error
* - An overrun error
* - Transmit FIFO is full
* - Transmit FIFO is empty
* - Receive FIFO is full
* - Receive FIFO is empty
* - Data in the receive FIFO equal to the receive threshold
*
* The application can control which interrupts are enabled using the
* XUartPs_SetInterruptMask() function.
*
* In order to use interrupts, it is necessary for the user to connect the
* driver interrupt handler, XUartPs_InterruptHandler(), to the interrupt
* system of the application. A separate handler should be provided by the
* application to communicate with the interrupt system, and conduct
* application specific interrupt handling. An application registers its own
* handler through the XUartPs_SetHandler() function.
*
* <b>Data Transfer</b>
*
* The functions, XUartPs_Send() and XUartPs_Recv(), are provided in the
* driver to allow data to be sent and received. They can be used in either
* polled or interrupt mode.
*
* @note
*
* The default configuration for the UART after initialization is:
*
* - 9,600 bps or XPAR_DFT_BAUDRATE if defined
* - 8 data bits
* - 1 stop bit
* - no parity
* - FIFO's are enabled with a receive threshold of 8 bytes
* - The RX timeout is enabled with a timeout of 1 (4 char times)
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- ----------------------------------------------
* 1.00a	drg/jz 01/12/10 First Release
* 1.00a sdm    09/27/11 Fixed compiler warnings and also a bug
*		        in XUartPs_SetFlowDelay where the value was not
*			being written to the register.
* 1.01a sdm    12/20/11 Removed the InputClockHz parameter from the XUartPs
*			instance structure and the driver is updated to use
*			InputClockHz parameter from the XUartPs_Config config
*			structure.
*			Added a parameter to XUartPs_Config structure which
*			specifies whether the user has selected Modem pins
*			to be connected to MIO or FMIO.
*			Added the tcl file to generate the xparameters.h
* 1.02a sg     05/16/12	Changed XUARTPS_RXWM_MASK to 0x3F for CR 652540 fix.
* 1.03a sg     07/16/12 Updated XUARTPS_FORMAT_7_BITS and XUARTPS_FORMAT_6_BITS
*			with the correct values for CR 666724
* 			Added defines for XUARTPS_IXR_TOVR,  XUARTPS_IXR_TNFUL
*			and XUARTPS_IXR_TTRIG.
*			Modified the name of these defines
*			XUARTPS_MEDEMSR_DCDX to XUARTPS_MODEMSR_DDCD
*			XUARTPS_MEDEMSR_RIX to XUARTPS_MODEMSR_TERI
*			XUARTPS_MEDEMSR_DSRX to XUARTPS_MODEMSR_DDSR
*			XUARTPS_MEDEMSR_CTSX to XUARTPS_MODEMSR_DCTS
* 1.05a hk     08/22/13 Added API for uart reset and related
*			constant definitions.
* 2.0   hk      03/07/14 Version number revised.
* 2.1   hk     04/16/14 Change XUARTPS_MAX_RATE to 921600. CR# 780625.
* 2.2   hk     06/23/14 SW reset of RX and TX should be done when changing
*                       baud rate. CR# 804281.
* 3.0   vm     12/09/14 Modified source code according to misrac guideline.
*			Support for Zynq Ultrascale Mp added.
* 3.1	kvn    04/10/15 Modified code for latest RTL changes. Also added
*						platform variable in driver instance structure.
* 3.1   adk   14/03/16  Include interrupt examples in the peripheral test when
*			uart is connected to a valid interrupt controller CR#946803.
* 3.2   rk     07/20/16 Modified the logic for transmission break bit set
* 3.4   ms     01/23/17 Added xil_printf statement in main function for all
*                       examples to ensure that "Successfully ran" and "Failed"
*                       strings are available in all examples. This is a fix
*                       for CR-965028.
*       ms     03/17/17 Added readme.txt file in examples folder for doxygen
*                       generation.
* 3.6   ms     02/16/18 Updates the flow control mode offset value in modem
*                       control register.
*
* </pre>
*
*****************************************************************************/

#ifndef XUARTPS_H		/* prevent circular inclusions */
#define XUARTPS_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xuartps_hw.h"
#include "xplatform_info.h"

/************************** Constant Definitions ****************************/

/*
 * The following constants indicate the max and min baud rates and these
 * numbers are based only on the testing that has been done. The hardware
 * is capable of other baud rates.
 */
#define XUARTPS_MAX_RATE	 921600U
#define XUARTPS_MIN_RATE	 110U

#define XUARTPS_DFT_BAUDRATE  115200U   /* Default baud rate */

/** @name Configuration options
 * @{
 */
/**
 * These constants specify the options that may be set or retrieved
 * with the driver, each is a unique bit mask such that multiple options
 * may be specified.  These constants indicate the available options
 * in active state.
 *
 */

#define XUARTPS_OPTION_SET_BREAK	0x0080U /**< Starts break transmission */
#define XUARTPS_OPTION_STOP_BREAK	0x0040U /**< Stops break transmission */
#define XUARTPS_OPTION_RESET_TMOUT	0x0020U /**< Reset the receive timeout */
#define XUARTPS_OPTION_RESET_TX		0x0010U /**< Reset the transmitter */
#define XUARTPS_OPTION_RESET_RX		0x0008U /**< Reset the receiver */
#define XUARTPS_OPTION_ASSERT_RTS	0x0004U /**< Assert the RTS bit */
#define XUARTPS_OPTION_ASSERT_DTR	0x0002U /**< Assert the DTR bit */
#define XUARTPS_OPTION_SET_FCM		0x0001U /**< Turn on flow control mode */
/*@}*/


/** @name Channel Operational Mode
 *
 * The UART can operate in one of four modes: Normal, Local Loopback, Remote
 * Loopback, or automatic echo.
 *
 * @{
 */

#define XUARTPS_OPER_MODE_NORMAL		(u8)0x00U	/**< Normal Mode */
#define XUARTPS_OPER_MODE_AUTO_ECHO		(u8)0x01U	/**< Auto Echo Mode */
#define XUARTPS_OPER_MODE_LOCAL_LOOP	(u8)0x02U	/**< Local Loopback Mode */
#define XUARTPS_OPER_MODE_REMOTE_LOOP	(u8)0x03U	/**< Remote Loopback Mode */

/* @} */

/** @name Data format values
 *
 * These constants specify the data format that the driver supports.
 * The data format includes the number of data bits, the number of stop
 * bits and parity.
 *
 * @{
 */
#define XUARTPS_FORMAT_8_BITS		0U /**< 8 data bits */
#define XUARTPS_FORMAT_7_BITS		2U /**< 7 data bits */
#define XUARTPS_FORMAT_6_BITS		3U /**< 6 data bits */

#define XUARTPS_FORMAT_NO_PARITY	4U /**< No parity */
#define XUARTPS_FORMAT_MARK_PARITY	3U /**< Mark parity */
#define XUARTPS_FORMAT_SPACE_PARITY	2U /**< parity */
#define XUARTPS_FORMAT_ODD_PARITY	1U /**< Odd parity */
#define XUARTPS_FORMAT_EVEN_PARITY	0U /**< Even parity */

#define XUARTPS_FORMAT_2_STOP_BIT	2U /**< 2 stop bits */
#define XUARTPS_FORMAT_1_5_STOP_BIT	1U /**< 1.5 stop bits */
#define XUARTPS_FORMAT_1_STOP_BIT	0U /**< 1 stop bit */
/*@}*/

/** @name Callback events
 *
 * These constants specify the handler events that an application can handle
 * using its specific handler function. Note that these constants are not bit
 * mask, so only one event can be passed to an application at a time.
 *
 * @{
 */
#define XUARTPS_EVENT_RECV_DATA			1U /**< Data receiving done */
#define XUARTPS_EVENT_RECV_TOUT			2U /**< A receive timeout occurred */
#define XUARTPS_EVENT_SENT_DATA			3U /**< Data transmission done */
#define XUARTPS_EVENT_RECV_ERROR		4U /**< A receive error detected */
#define XUARTPS_EVENT_MODEM				5U /**< Modem status changed */
#define XUARTPS_EVENT_PARE_FRAME_BRKE	6U /**< A receive parity, frame, break
											 *	error detected */
#define XUARTPS_EVENT_RECV_ORERR		7U /**< A receive overrun error detected */
/*@}*/


/**************************** Type Definitions ******************************/

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;	 /**< Unique ID  of device */
	u32 BaseAddress; /**< Base address of device (IPIF) */
	u32 InputClockHz;/**< Input clock frequency */
	s32 ModemPinsConnected; /** Specifies whether modem pins are connected
				 *  to MIO or FMIO */
} XUartPs_Config;

/* Keep track of state information about a data buffer in the interrupt mode. */
typedef struct {
	u8 *NextBytePtr;
	u32 RequestedBytes;
	u32 RemainingBytes;
} XUartPsBuffer;

/**
 * Keep track of data format setting of a device.
 */
typedef struct {
	u32 BaudRate;	/**< In bps, ie 1200 */
	u32 DataBits;	/**< Number of data bits */
	u32 Parity;		/**< Parity */
	u8 StopBits;	/**< Number of stop bits */
} XUartPsFormat;

/******************************************************************************/
/**
 * This data type defines a handler that an application defines to communicate
 * with interrupt system to retrieve state information about an application.
 *
 * @param	CallBackRef is a callback reference passed in by the upper layer
 *		when setting the handler, and is passed back to the upper layer
 *		when the handler is called. It is used to find the device driver
 *		instance.
 * @param	Event contains one of the event constants indicating events that
 *		have occurred.
 * @param	EventData contains the number of bytes sent or received at the
 *		time of the call for send and receive events and contains the
 *		modem status for modem events.
 *
 ******************************************************************************/
typedef void (*XUartPs_Handler) (void *CallBackRef, u32 Event,
				  u32 EventData);

/**
 * The XUartPs driver instance data structure. A pointer to an instance data
 * structure is passed around by functions to refer to a specific driver
 * instance.
 */
typedef struct {
	XUartPs_Config Config;	/* Configuration data structure */
	u32 InputClockHz;	/* Input clock frequency */
	u32 IsReady;		/* Device is initialized and ready */
	u32 BaudRate;		/* Current baud rate */

	XUartPsBuffer SendBuffer;
	XUartPsBuffer ReceiveBuffer;

	XUartPs_Handler Handler;
	void *CallBackRef;	/* Callback reference for event handler */
	u32 Platform;
	u8 is_rxbs_error;
} XUartPs;


/***************** Macros (Inline Functions) Definitions ********************/

/****************************************************************************/
/**
* Get the UART Channel Status Register.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return	The value read from the register.
*
* @note		C-Style signature:
*		u16 XUartPs_GetChannelStatus(XUartPs *InstancePtr)
*
******************************************************************************/
#define XUartPs_GetChannelStatus(InstancePtr)   \
	Xil_In32(((InstancePtr)->Config.BaseAddress) + (u32)XUARTPS_SR_OFFSET)

/****************************************************************************/
/**
* Get the UART Mode Control Register.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return	The value read from the register.
*
* @note		C-Style signature:
*		u32 XUartPs_GetControl(XUartPs *InstancePtr)
*
******************************************************************************/
#define XUartPs_GetModeControl(InstancePtr)  \
	Xil_In32(((InstancePtr)->Config.BaseAddress) + (u32)XUARTPS_CR_OFFSET)

/****************************************************************************/
/**
* Set the UART Mode Control Register.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	RegisterValue is the value to be written to the register.
*
* @return	None.
*
* @note		C-Style signature:
*	void XUartPs_SetModeControl(XUartPs *InstancePtr, u16 RegisterValue)
*
******************************************************************************/
#define XUartPs_SetModeControl(InstancePtr, RegisterValue) \
   Xil_Out32(((InstancePtr)->Config.BaseAddress) + (u32)XUARTPS_CR_OFFSET, \
			(u32)(RegisterValue))

/****************************************************************************/
/**
* Enable the transmitter and receiver of the UART.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XUartPs_EnableUart(XUartPs *InstancePtr)
*
******************************************************************************/
#define XUartPs_EnableUart(InstancePtr) \
   Xil_Out32(((InstancePtr)->Config.BaseAddress + (u32)XUARTPS_CR_OFFSET), \
	  ((Xil_In32((InstancePtr)->Config.BaseAddress + (u32)XUARTPS_CR_OFFSET) & \
	  (u32)(~XUARTPS_CR_EN_DIS_MASK)) | ((u32)XUARTPS_CR_RX_EN | (u32)XUARTPS_CR_TX_EN)))

/****************************************************************************/
/**
* Disable the transmitter and receiver of the UART.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XUartPs_DisableUart(XUartPs *InstancePtr)
*
******************************************************************************/
#define XUartPs_DisableUart(InstancePtr) \
   Xil_Out32(((InstancePtr)->Config.BaseAddress + (u32)XUARTPS_CR_OFFSET), \
	  (((Xil_In32((InstancePtr)->Config.BaseAddress + (u32)XUARTPS_CR_OFFSET)) & \
	  (u32)(~XUARTPS_CR_EN_DIS_MASK)) | ((u32)XUARTPS_CR_RX_DIS | (u32)XUARTPS_CR_TX_DIS)))

/****************************************************************************/
/**
* Determine if the transmitter FIFO is empty.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return
*		- TRUE if a byte can be sent
*		- FALSE if the Transmitter Fifo is not empty
*
* @note		C-Style signature:
*		u32 XUartPs_IsTransmitEmpty(XUartPs InstancePtr)
*
******************************************************************************/
#define XUartPs_IsTransmitEmpty(InstancePtr)				\
	((Xil_In32(((InstancePtr)->Config.BaseAddress) + (u32)XUARTPS_SR_OFFSET) & \
	 (u32)XUARTPS_SR_TXEMPTY) == (u32)XUARTPS_SR_TXEMPTY)


/************************** Function Prototypes *****************************/

/* Static lookup function implemented in xuartps_sinit.c */
XUartPs_Config *XUartPs_LookupConfig(u16 DeviceId);

/* Interface functions implemented in xuartps.c */
s32 XUartPs_CfgInitialize(XUartPs *InstancePtr,
				  XUartPs_Config * Config, u32 EffectiveAddr);

u32 XUartPs_Send(XUartPs *InstancePtr,u8 *BufferPtr,
			   u32 NumBytes);

u32 XUartPs_Recv(XUartPs *InstancePtr,u8 *BufferPtr,
			   u32 NumBytes);

s32 XUartPs_SetBaudRate(XUartPs *InstancePtr, u32 BaudRate);

/* Options functions in xuartps_options.c */
void XUartPs_SetOptions(XUartPs *InstancePtr, u16 Options);

u16 XUartPs_GetOptions(XUartPs *InstancePtr);

void XUartPs_SetFifoThreshold(XUartPs *InstancePtr, u8 TriggerLevel);

u8 XUartPs_GetFifoThreshold(XUartPs *InstancePtr);

u16 XUartPs_GetModemStatus(XUartPs *InstancePtr);

u32 XUartPs_IsSending(XUartPs *InstancePtr);

u8 XUartPs_GetOperMode(XUartPs *InstancePtr);

void XUartPs_SetOperMode(XUartPs *InstancePtr, u8 OperationMode);

u8 XUartPs_GetFlowDelay(XUartPs *InstancePtr);

void XUartPs_SetFlowDelay(XUartPs *InstancePtr, u8 FlowDelayValue);

u8 XUartPs_GetRecvTimeout(XUartPs *InstancePtr);

void XUartPs_SetRecvTimeout(XUartPs *InstancePtr, u8 RecvTimeout);

s32 XUartPs_SetDataFormat(XUartPs *InstancePtr, XUartPsFormat * FormatPtr);

void XUartPs_GetDataFormat(XUartPs *InstancePtr, XUartPsFormat * FormatPtr);

/* interrupt functions in xuartps_intr.c */
u32 XUartPs_GetInterruptMask(XUartPs *InstancePtr);

void XUartPs_SetInterruptMask(XUartPs *InstancePtr, u32 Mask);

void XUartPs_InterruptHandler(XUartPs *InstancePtr);

void XUartPs_SetHandler(XUartPs *InstancePtr, XUartPs_Handler FuncPtr,
			 void *CallBackRef);

/* self-test functions in xuartps_selftest.c */
s32 XUartPs_SelfTest(XUartPs *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
