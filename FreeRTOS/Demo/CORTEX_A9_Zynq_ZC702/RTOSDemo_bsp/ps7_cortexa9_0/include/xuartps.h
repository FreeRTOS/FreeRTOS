/*****************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
*****************************************************************************/
/****************************************************************************/
/**
*
* @file xuartps.h
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

/************************** Constant Definitions ****************************/

/*
 * The following constants indicate the max and min baud rates and these
 * numbers are based only on the testing that has been done. The hardware
 * is capable of other baud rates.
 */
#define XUARTPS_MAX_RATE	 921600
#define XUARTPS_MIN_RATE	 110

#define XUARTPS_DFT_BAUDRATE  115200   /* Default baud rate */

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

#define XUARTPS_OPTION_SET_BREAK	0x0080 /**< Starts break transmission */
#define XUARTPS_OPTION_STOP_BREAK	0x0040 /**< Stops break transmission */
#define XUARTPS_OPTION_RESET_TMOUT	0x0020 /**< Reset the receive timeout */
#define XUARTPS_OPTION_RESET_TX		0x0010 /**< Reset the transmitter */
#define XUARTPS_OPTION_RESET_RX		0x0008 /**< Reset the receiver */
#define XUARTPS_OPTION_ASSERT_RTS	0x0004 /**< Assert the RTS bit */
#define XUARTPS_OPTION_ASSERT_DTR	0x0002 /**< Assert the DTR bit */
#define XUARTPS_OPTION_SET_FCM		0x0001 /**< Turn on flow control mode */
/*@}*/


/** @name Channel Operational Mode
 *
 * The UART can operate in one of four modes: Normal, Local Loopback, Remote
 * Loopback, or automatic echo.
 *
 * @{
 */

#define XUARTPS_OPER_MODE_NORMAL	0x00	/**< Normal Mode */
#define XUARTPS_OPER_MODE_AUTO_ECHO	0x01	/**< Auto Echo Mode */
#define XUARTPS_OPER_MODE_LOCAL_LOOP	0x02	/**< Local Loopback Mode */
#define XUARTPS_OPER_MODE_REMOTE_LOOP	0x03	/**< Remote Loopback Mode */

/* @} */

/** @name Data format values
 *
 * These constants specify the data format that the driver supports.
 * The data format includes the number of data bits, the number of stop
 * bits and parity.
 *
 * @{
 */
#define XUARTPS_FORMAT_8_BITS		0 /**< 8 data bits */
#define XUARTPS_FORMAT_7_BITS		2 /**< 7 data bits */
#define XUARTPS_FORMAT_6_BITS		3 /**< 6 data bits */

#define XUARTPS_FORMAT_NO_PARITY	4 /**< No parity */
#define XUARTPS_FORMAT_MARK_PARITY	3 /**< Mark parity */
#define XUARTPS_FORMAT_SPACE_PARITY	2 /**< parity */
#define XUARTPS_FORMAT_ODD_PARITY	1 /**< Odd parity */
#define XUARTPS_FORMAT_EVEN_PARITY	0 /**< Even parity */

#define XUARTPS_FORMAT_2_STOP_BIT	2 /**< 2 stop bits */
#define XUARTPS_FORMAT_1_5_STOP_BIT	1 /**< 1.5 stop bits */
#define XUARTPS_FORMAT_1_STOP_BIT	0 /**< 1 stop bit */
/*@}*/

/** @name Callback events
 *
 * These constants specify the handler events that an application can handle
 * using its specific handler function. Note that these constants are not bit
 * mask, so only one event can be passed to an application at a time.
 *
 * @{
 */
#define XUARTPS_EVENT_RECV_DATA		1 /**< Data receiving done */
#define XUARTPS_EVENT_RECV_TOUT		2 /**< A receive timeout occurred */
#define XUARTPS_EVENT_SENT_DATA		3 /**< Data transmission done */
#define XUARTPS_EVENT_RECV_ERROR	4 /**< A receive error detected */
#define XUARTPS_EVENT_MODEM		5 /**< Modem status changed */
/*@}*/


/**************************** Type Definitions ******************************/

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;	 /**< Unique ID  of device */
	u32 BaseAddress; /**< Base address of device (IPIF) */
	u32 InputClockHz;/**< Input clock frequency */
	int ModemPinsConnected; /** Specifies whether modem pins are connected
				 *  to MIO or FMIO */
} XUartPs_Config;

/*
 * Keep track of state information about a data buffer in the interrupt mode.
 */
typedef struct {
	u8 *NextBytePtr;
	unsigned int RequestedBytes;
	unsigned int RemainingBytes;
} XUartPsBuffer;

/**
 * Keep track of data format setting of a device.
 */
typedef struct {
	u32 BaudRate;	/**< In bps, ie 1200 */
	u32 DataBits;	/**< Number of data bits */
	u32 Parity;	/**< Parity */
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
				  unsigned int EventData);

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
	Xil_In32(((InstancePtr)->Config.BaseAddress) + XUARTPS_SR_OFFSET)

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
	Xil_In32(((InstancePtr)->Config.BaseAddress) + XUARTPS_CR_OFFSET)

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
   Xil_Out32(((InstancePtr)->Config.BaseAddress) + XUARTPS_CR_OFFSET, \
			(RegisterValue))

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
   Xil_Out32(((InstancePtr)->Config.BaseAddress + XUARTPS_CR_OFFSET), \
	  ((Xil_In32((InstancePtr)->Config.BaseAddress + XUARTPS_CR_OFFSET) & \
	  ~XUARTPS_CR_EN_DIS_MASK) | (XUARTPS_CR_RX_EN | XUARTPS_CR_TX_EN)))

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
   Xil_Out32(((InstancePtr)->Config.BaseAddress + XUARTPS_CR_OFFSET), \
	  (((Xil_In32((InstancePtr)->Config.BaseAddress + XUARTPS_CR_OFFSET)) & \
	  ~XUARTPS_CR_EN_DIS_MASK) | (XUARTPS_CR_RX_DIS | XUARTPS_CR_TX_DIS)))

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
	((Xil_In32(((InstancePtr)->Config.BaseAddress) + XUARTPS_SR_OFFSET) & \
	 XUARTPS_SR_TXEMPTY) == XUARTPS_SR_TXEMPTY)


/************************** Function Prototypes *****************************/

/*
 * Static lookup function implemented in xuartps_sinit.c
 */
XUartPs_Config *XUartPs_LookupConfig(u16 DeviceId);

/*
 * Interface functions implemented in xuartps.c
 */
int XUartPs_CfgInitialize(XUartPs *InstancePtr,
				   XUartPs_Config * Config, u32 EffectiveAddr);

unsigned int XUartPs_Send(XUartPs *InstancePtr, u8 *BufferPtr,
			   unsigned int NumBytes);

unsigned int XUartPs_Recv(XUartPs *InstancePtr, u8 *BufferPtr,
			   unsigned int NumBytes);

int XUartPs_SetBaudRate(XUartPs *InstancePtr, u32 BaudRate);

/*
 * Options functions in xuartps_options.c
 */
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

int XUartPs_SetDataFormat(XUartPs *InstancePtr, XUartPsFormat * Format);
void XUartPs_GetDataFormat(XUartPs *InstancePtr, XUartPsFormat * Format);

/*
 * interrupt functions in xuartps_intr.c
 */
u32 XUartPs_GetInterruptMask(XUartPs *InstancePtr);

void XUartPs_SetInterruptMask(XUartPs *InstancePtr, u32 Mask);

void XUartPs_InterruptHandler(XUartPs *InstancePtr);

void XUartPs_SetHandler(XUartPs *InstancePtr, XUartPs_Handler FuncPtr,
			 void *CallBackRef);

/*
 * self-test functions in xuartps_selftest.c
 */
int XUartPs_SelfTest(XUartPs *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
