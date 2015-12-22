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
* @file xspips.h
*
* This file contains the implementation of the XSpiPs driver. It works for
* both the master and slave mode. User documentation for the driver functions
* is contained in this file in the form of comment blocks at the front of each
* function.
*
* An SPI device connects to an SPI bus through a 4-wire serial interface.
* The SPI bus is a full-duplex, synchronous bus that facilitates communication
* between one master and one slave. The device is always full-duplex,
* which means that for every byte sent, one is received, and vice-versa.
* The master controls the clock, so it can regulate when it wants to
* send or receive data. The slave is under control of the master, it must
* respond quickly since it has no control of the clock and must send/receive
* data as fast or as slow as the master does.
*
* <b>Initialization & Configuration</b>
*
* The XSpiPs_Config structure is used by the driver to configure itself. This
* configuration structure is typically created by the tool-chain based on HW
* build properties.
*
* To support multiple runtime loading and initialization strategies employed by
* various operating systems, the driver instance can be initialized in the
* following way:
*	- XSpiPs_LookupConfig(DeviceId) - Use the devide identifier to find the
*	static configuration structure defined in xspips_g.c. This is setup by
*	the tools. For some operating systems the config structure will be
*	initialized by the software and this call is not needed.
*	- XSpiPs_CfgInitialize(InstancePtr, CfgPtr, EffectiveAddr) - Uses a
*	configuration structure provided by the caller. If running in a system
*	with address translation, the provided virtual memory base address
*	replaces the physical address present in the configuration structure.
*
* <b>Multiple Masters</b>
*
* More than one master can exist, but arbitration is the responsibility of
* the higher layer software. The device driver does not perform any type of
* arbitration.
*
* <b>Multiple Slaves</b>
*
* Contention between multiple masters is detected by the hardware, in which
* case a mode fault occurs on the device. The device is disabled immediately
* by hardware, and the current word transfer is stopped. The Aborted word
* transfer due to the mode fault is resumed once the devie is enabled again.
*
* <b>Modes of Operation</b>
*
* There are four modes to perform a data transfer and the selection of a mode
* is based on Chip Select(CS) and Start. These two options individually, can
* be controlled either by software(Manual) or hardware(Auto).
* - Auto CS: Chip select is automatically asserted as soon as the first word
*	     is written into the TXFIFO and deasserted when the TXFIFO becomes
*	     empty
* - Manual CS: Software must assert and deassert CS.
* - Auto Start: Data transmission starts as soon as there is data in the
*		TXFIFO and stalls when the TXFIFO is empty
* - Manual Start: Software must start data transmission at the beginning of
*		  the transaction or whenever the TXFIFO has become empty
*
* The preferred combination is Manual CS and Auto Start.
* In this combination, the software asserts CS before loading any data into
* TXFIFO. In Auto Start mode, whenever data is in TXFIFO, controller sends it
* out until TXFIFO becomes empty. The software reads the RXFIFO whenever the
* data is available. If no further data, software disables CS.
*
* Risks/challenges of other combinations:
* - Manual CS and Manual Start: Manual Start bit should be set after each
*   TXFIFO write otherwise there could be a race condition where the TXFIFO
*   becomes empty before the new word is written. In that case the
*   transmission stops.
* - Auto CS with Manual or Auto Start: It is very difficult for software to
*   keep the TXFIFO filled. Whenever the TXFIFO runs empty, CS is deasserted.
*   This results in a single transaction to be split into multiple pieces each
*   with its own chip select. This will result in garbage data to be sent.
*
* <b>Interrupts</b>
*
* The user must connect the interrupt handler of the driver,
* XSpiPs_InterruptHandler, to an interrupt system such that it will be
* called when an interrupt occurs. This function does not save and restore
* the processor context such that the user must provide this processing.
*
* The driver handles the following interrupts:
* - Data Transmit Register/FIFO Underflow
* - Data Receive Register/FIFO Full
* - Data Receive Register/FIFO Not Empty
* - Data Transmit Register/FIFO Full
* - Data Transmit Register/FIFO Overwater
* - Mode Fault Error
* - Data Receive Register/FIFO Overrun
*
* The Data Transmit Register/FIFO Overwater interrupt -- indicates that the
* SPI device has transmitted the data available to transmit, and now its data
* register and FIFO is ready to accept more data. The driver uses this
* interrupt to indicate progress while sending data.  The driver may have
* more data to send, in which case the data transmit register and FIFO is
* filled for subsequent transmission. When this interrupt arrives and all
* the data has been sent, the driver invokes the status callback with a
* value of XST_SPI_TRANSFER_DONE to inform the upper layer software that
* all data has been sent.
*
* The Data Transmit Register/FIFO Underflow interrupt -- indicates that,
* as slave, the SPI device was required to transmit but there was no data
* available to transmit in the transmit register (or FIFO). This may not
* be an error if the master is not expecting data. But in the case where
* the master is expecting data, this serves as a notification of such a
* condition. The driver reports this condition to the upper layer
* software through the status handler.
*
* The Data Receive Register/FIFO Overrun interrupt -- indicates that the SPI
* device received data and subsequently dropped the data because the data
* receive register and FIFO was full. The interrupt applies to both master
* and slave operation. The driver reports this condition to the upper layer
* software through the status handler. This likely indicates a problem with
* the higher layer protocol, or a problem with the slave performance.
*
* The Mode Fault Error interrupt -- indicates that while configured as a
* master, the device was selected as a slave by another master. This can be
* used by the application for arbitration in a multimaster environment or to
* indicate a problem with arbitration. When this interrupt occurs, the
* driver invokes the status callback with a status value of
* XST_SPI_MODE_FAULT. It is up to the application to resolve the conflict.
* When configured as a slave, Mode Fault Error interrupt indicates that a slave
* device was selected as a slave by a master, but the slave device was
* disabled. When configured as a master, Mode Fault Error interrupt indicates
* that another SPI device is acting as a master on the bus.
*
*
* <b>Polled Operation</b>
*
* Transfer in polled mode is supported through a separate interface function
* XSpiPs_PolledTransfer(). Unlike the transfer function in the interrupt mode,
* this function blocks until all data has been sent/received.
*
* <b>Device Busy</b>
*
* Some operations are disallowed when the device is busy. The driver tracks
* whether a device is busy. The device is considered busy when a data transfer
* request is outstanding, and is considered not busy only when that transfer
* completes (or is aborted with a mode fault error). This applies to both
* master and slave devices.
*
* <b>Device Configuration</b>
*
* The device can be configured in various ways during the FPGA implementation
* process. Configuration parameters are stored in the xspips_g.c file or
* passed in via XSpiPs_CfgInitialize(). A table is defined where each entry
* contains configuration information for an SPI device, including the base
* address for the device.
*
* <b>RTOS Independence</b>
*
* This driver is intended to be RTOS and processor independent.  It works with
* physical addresses only.  Any needs for dynamic memory management, threads or
* thread mutual exclusion, virtual memory, or cache control must be satisfied
* by the layer above this driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -----------------------------------------------
* 1.00	drg/jz 01/25/10 First release
* 1.00	sdm    10/25/11 Removed the Divide by 2 in the SPI Clock Prescaler
*			options as this is not supported in the device.
* 1.01	sg     03/07/12 Updated the code to always clear the relevant bits
*			before writing to config register.
*			Always clear the slave select bits before write and
*			clear the bits to no slave at the end of transfer
*			Modified the Polled transfer transmit/receive logic.
*			Tx should wait on TXOW Interrupt and Rx on RXNEMTY.
* 1.02	sg     05/31/12 Updated XSPIPS_FIFO_DEPTH to 128 from 32 to match HW
*			for CR 658289
* 1.03	sg     09/21/12 Added memory barrier dmb in polled transfer and
*			interrupt handler to overcome the clock domain
*			crossing issue in the controller. For CR #679252.
* 1.04a	sg     01/30/13 Created XSPIPS_MANUAL_START_OPTION. Created macros
*			XSpiPs_IsMaster, XSpiPs_IsManualStart and
*			XSpiPs_IsManualChipSelect. Changed SPI
*			Enable/Disable macro argument from BaseAddress to
*			Instance Pointer. Added DelayNss argument to SetDelays
*			and GetDelays API's. Added macros to set/get the
*			RX Watermark value.Created macros XSpiPs_IsMaster,
*			XSpiPs_IsManualStart and XSpiPs_IsManualChipSelect.
*			Changed SPI transfer logic for polled and interrupt
*			modes to be based on filled tx fifo count and receive
*			based on it. RXNEMPTY interrupt is not used.
*			SetSlaveSelect API logic is modified to drive the bit
*			position low based on the slave select value
*			requested. GetSlaveSelect API will return the value
*			based on bit position that is low.
*			Created XSPIPS_CR_MODF_GEN_EN_MASK macro and added it
*			to XSPIPS_CR_RESET_STATE. Created
* 			XSPIPS_IXR_WR_TO_CLR_MASK for interrupts which need
*			write-to-clear. Added shift and mask macros for d_nss
*			parameter. Added Rx Watermark mask.
* 1.05a hk 	   26/04/13 Added disable and enable in XSpiPs_SetOptions when
*				CPOL/CPHA bits are set/reset. Fix for CR#707669.
* 1.06a hk     08/22/13 Changed GetSlaveSelect function. CR# 727866.
*                       Added masking ConfigReg before writing in SetSlaveSel
*                       Added extended slave select support - CR#722569.
*                       Added prototypes of reset API and related constant
*                       definitions.
*                       Added check for MODF in polled transfer function.
* 3.0   vm    12/09/14	Modified driver source code for MISRA-C:2012 compliance.
*			Support for Zynq Ultrascale Mp added.
*
* </pre>
*
******************************************************************************/
#ifndef XSPIPS_H		/* prevent circular inclusions */
#define XSPIPS_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xspips_hw.h"

/************************** Constant Definitions *****************************/

/** @name Configuration options
 *
 * The following options are supported to enable/disable certain features of
 * an SPI device.  Each of the options is a bit mask, so more than one may be
 * specified.
 *
 * <b>The Master option</b> configures the SPI device as a master.
 * By default, the device is a slave.
 *
 * The <b>Active Low Clock option</b> configures the device's clock polarity.
 * Setting this option means the clock is active low and the SCK signal idles
 * high. By default, the clock is active high and SCK idles low.
 *
 * The <b>Clock Phase option</b> configures the SPI device for one of two
 * transfer formats.  A clock phase of 0, the default, means data is valid on
 * the first SCK edge (rising or falling) after the slave select (SS) signal
 * has been asserted. A clock phase of 1 means data is valid on the second SCK
 * edge (rising or falling) after SS has been asserted.
 *
 * The <b>Slave Select Decode Enable option</b> selects how the SPI_SS_outN are
 * controlled by the SPI Slave Select Decode bits.
 * 0: Use this setting for the standard configuration of up to three slave
 * select outputs. Only one of the three slave select outputs will be low.
 * (Default)
 * 1: Use this setting for the optional configuration of an additional decoder
 * to support 8 slave select outputs. SPI_SS_outN reflects the value in the
 * register.
 *
 * The <b>SPI Force Slave Select option</b> is used to enable manual control of
 * the signals SPI_SS_outN.
 * 0: The SPI_SS_outN signals are controlled by the SPI controller during
 * transfers. (Default)
 * 1: The SPI_SS_outN signal indicated by the Slave Select Control bit is
 * forced active (driven low) regardless of any transfers in progress.
 *
 * NOTE: The driver will handle setting and clearing the Slave Select when
 * the user sets the "FORCE_SSELECT_OPTION". Using this option will allow the
 * SPI clock to be set to a faster speed. If the SPI clock is too fast, the
 * processor cannot empty and refill the FIFOs before the TX FIFO is empty
 * When the SPI hardware is controlling the Slave Select signals, this
 * will cause slave to be de-selected and terminate the transfer.
 *
 * The <b>Manual Start option</b> is used to enable manual control of
 * the Start command to perform data transfer.
 * 0: The Start command is controlled by the SPI controller during
 * transfers(Default). Data transmission starts as soon as there is data in
 * the TXFIFO and stalls when the TXFIFO is empty
 * 1: The Start command must be issued by software to perform data transfer.
 * Bit 15 of Configuration register is used to issue Start command. This bit
 * must be set whenever TXFIFO is filled with new data.
 *
 * NOTE: The driver will set the Manual Start Enable bit in Configuration
 * Register, if Manual Start option is selected. Software will issue
 * Manual Start command whenever TXFIFO is filled with data. When there is
 * no further data, driver will clear the Manual Start Enable bit.
 *
 * @{
 */
#define XSPIPS_MASTER_OPTION				0x00000001U  /**< Master mode option */
#define XSPIPS_CLK_ACTIVE_LOW_OPTION		0x00000002U  /**< Active Low Clock option */
#define XSPIPS_CLK_PHASE_1_OPTION			0x00000004U  /**< Clock Phase one option */
#define XSPIPS_DECODE_SSELECT_OPTION		0x00000008U  /**< Select 16 slaves Option */
#define XSPIPS_FORCE_SSELECT_OPTION			0x00000010U /**< Force Slave Select */
#define XSPIPS_MANUAL_START_OPTION			0x00000020U /**< Manual Start mode option */
/*@}*/


/** @name SPI Clock Prescaler options
 * The SPI Clock Prescaler Configuration bits are used to program master mode
 * bit rate. The bit rate can be programmed in divide-by-two decrements from
 * pclk/4 to pclk/256.
 *
 * @{
 */

#define XSPIPS_CLK_PRESCALE_4		0x01U  /**< PCLK/4 Prescaler */
#define XSPIPS_CLK_PRESCALE_8		0x02U  /**< PCLK/8 Prescaler */
#define XSPIPS_CLK_PRESCALE_16		0x03U  /**< PCLK/16 Prescaler */
#define XSPIPS_CLK_PRESCALE_32		0x04U  /**< PCLK/32 Prescaler */
#define XSPIPS_CLK_PRESCALE_64		0x05U  /**< PCLK/64 Prescaler */
#define XSPIPS_CLK_PRESCALE_128		0x06U  /**< PCLK/128 Prescaler */
#define XSPIPS_CLK_PRESCALE_256		0x07U  /**< PCLK/256 Prescaler */
/*@}*/


/** @name Callback events
 *
 * These constants specify the handler events that are passed to
 * a handler from the driver.  These constants are not bit masks such that
 * only one will be passed at a time to the handler.
 *
 * @{
 */
#define XSPIPS_EVENT_MODE_FAULT		1U  /**< Mode fault error */
#define XSPIPS_EVENT_TRANSFER_DONE	2U  /**< Transfer done */
#define XSPIPS_EVENT_TRANSMIT_UNDERRUN	3U  /**< TX FIFO empty */
#define XSPIPS_EVENT_RECEIVE_OVERRUN	4U /**< Receive data loss because
						RX FIFO full */
/*@}*/


/**************************** Type Definitions *******************************/
/**
 * The handler data type allows the user to define a callback function to
 * handle the asynchronous processing for the SPI device.  The application
 * using this driver is expected to define a handler of this type to support
 * interrupt driven mode.  The handler executes in an interrupt context, so
 * only minimal processing should be performed.
 *
 * @param	CallBackRef is the callback reference passed in by the upper
 *		layer when setting the callback functions, and passed back to
 *		the upper layer when the callback is invoked. Its type is
 *		not important to the driver, so it is a void pointer.
 * @param 	StatusEvent holds one or more status events that have occurred.
 *		See the XSpiPs_SetStatusHandler() for details on the status
 *		events that can be passed in the callback.
 * @param	ByteCount indicates how many bytes of data were successfully
 *		transferred.  This may be less than the number of bytes
 *		requested if the status event indicates an error.
 */
typedef void (*XSpiPs_StatusHandler) (void *CallBackRef, u32 StatusEvent,
					u32 ByteCount);

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;		/**< Unique ID  of device */
	u32 BaseAddress;	/**< Base address of the device */
	u32 InputClockHz;	/**< Input clock frequency */
} XSpiPs_Config;

/**
 * The XSpiPs driver instance data. The user is required to allocate a
 * variable of this type for every SPI device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XSpiPs_Config Config;	 /**< Configuration structure */
	u32 IsReady;		 /**< Device is initialized and ready */

	u8 *SendBufferPtr;	 /**< Buffer to send (state) */
	u8 *RecvBufferPtr;	 /**< Buffer to receive (state) */
	u32 RequestedBytes; /**< Number of bytes to transfer (state) */
	u32 RemainingBytes; /**< Number of bytes left to transfer(state) */
	u32 IsBusy;		 /**< A transfer is in progress (state) */
	u32 SlaveSelect;     /**< The slave select value when
					 XSPIPS_FORCE_SSELECT_OPTION is set */

	XSpiPs_StatusHandler StatusHandler;
	void *StatusRef;  	 /**< Callback reference for status handler */

} XSpiPs;

/***************** Macros (Inline Functions) Definitions *********************/
/****************************************************************************/
/*
*
* Check in OptionsTable if Manual Start Option is enabled or disabled.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return
*		- TRUE if option is set
*		- FALSE if option is not set
*
* @note		C-Style signature:
*		u8 XSpiPs_IsManualStart(XSpiPs *InstancePtr);
*
*****************************************************************************/
#define XSpiPs_IsManualStart(InstancePtr) \
		(((XSpiPs_GetOptions(InstancePtr) & \
		  XSPIPS_MANUAL_START_OPTION) != (u32)0U) ? TRUE : FALSE)

/****************************************************************************/
/*
*
* Check in OptionsTable if Manual Chip Select Option is enabled or disabled.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return
*		- TRUE if option is set
*		- FALSE if option is not set
*
* @note		C-Style signature:
*		u8 XSpiPs_IsManualChipSelect(XSpiPs *InstancePtr);
*
*****************************************************************************/
#define XSpiPs_IsManualChipSelect(InstancePtr) \
		(((XSpiPs_GetOptions(InstancePtr) & \
		  XSPIPS_FORCE_SSELECT_OPTION) != (u32)0U) ? TRUE : FALSE)

/****************************************************************************/
/*
*
* Check in OptionsTable if Decode Slave Select option is enabled or disabled.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return
*		- TRUE if option is set
*		- FALSE if option is not set
*
* @note		C-Style signature:
*		u8 XSpiPs_IsDecodeSSelect(XSpiPs *InstancePtr);
*
*****************************************************************************/
#define XSpiPs_IsDecodeSSelect(InstancePtr) \
		(((XSpiPs_GetOptions(InstancePtr) & \
		  XSPIPS_DECODE_SSELECT_OPTION) != (u32)0U) ? TRUE : FALSE)

/****************************************************************************/
/*
*
* Check in OptionsTable if Master Option is enabled or disabled.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return
*		- TRUE if option is set
*		- FALSE if option is not set
*
* @note		C-Style signature:
*		u8 XSpiPs_IsMaster(XSpiPs *InstancePtr);
*
*****************************************************************************/
#define XSpiPs_IsMaster(InstancePtr) \
		(((XSpiPs_GetOptions(InstancePtr) & \
		  XSPIPS_MASTER_OPTION) != (u32)0U) ? TRUE : FALSE)

/****************************************************************************/
/**
*
* Set the contents of the slave idle count register.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	RegisterValue is the value to be writen, valid values are
*		0-255.
*
* @return	None
*
* @note
* C-Style signature:
*	void XSpiPs_SetSlaveIdle(XSpiPs *InstancePtr, u32 RegisterValue)
*
*****************************************************************************/
#define XSpiPs_SetSlaveIdle(InstancePtr, RegisterValue)	\
	XSpiPs_Out32(((InstancePtr)->Config.BaseAddress) + 	\
		XSPIPS_SICR_OFFSET, (RegisterValue))

/****************************************************************************/
/**
*
* Get the contents of the slave idle count register. Use the XSPIPS_SICR_*
* constants defined in xspips_hw.h to interpret the bit-mask returned.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	8-bit value representing the contents of the SIC register.
*
* @note		C-Style signature:
*		u32 XSpiPs_GetSlaveIdle(XSpiPs *InstancePtr)
*
*****************************************************************************/
#define XSpiPs_GetSlaveIdle(InstancePtr)				\
	XSpiPs_In32(((InstancePtr)->Config.BaseAddress) + 		\
	XSPIPS_SICR_OFFSET)

/****************************************************************************/
/**
*
* Set the contents of the transmit FIFO watermark register.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	RegisterValue is the value to be written, valid values
*		are 1-128.
*
* @return	None.
*
* @note
* C-Style signature:
*	void XSpiPs_SetTXWatermark(XSpiPs *InstancePtr, u32 RegisterValue)
*
*****************************************************************************/
#define XSpiPs_SetTXWatermark(InstancePtr, RegisterValue)		\
	XSpiPs_Out32(((InstancePtr)->Config.BaseAddress) + 		\
		XSPIPS_TXWR_OFFSET, (RegisterValue))

/****************************************************************************/
/**
*
* Get the contents of the transmit FIFO watermark register.
* Use the XSPIPS_TXWR_* constants defined xspips_hw.h to interpret
* the bit-mask returned.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	8-bit value representing the contents of the TXWR register.
*
* @note		C-Style signature:
*		u32 XSpiPs_GetTXWatermark(u32 *InstancePtr)
*
*****************************************************************************/
#define XSpiPs_GetTXWatermark(InstancePtr)				\
	XSpiPs_In32(((InstancePtr)->Config.BaseAddress) + XSPIPS_TXWR_OFFSET)

/****************************************************************************/
/**
*
* Set the contents of the receive FIFO watermark register.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	RegisterValue is the value to be written, valid values
*		are 1-128.
*
* @return	None.
*
* @note
* C-Style signature:
*	void XSpiPs_SetRXWatermark(XSpiPs *InstancePtr, u32 RegisterValue)
*
*****************************************************************************/
#define XSpiPs_SetRXWatermark(InstancePtr, RegisterValue)		\
	XSpiPs_Out32(((InstancePtr)->Config.BaseAddress) + 		\
		XSPIPS_RXWR_OFFSET, (RegisterValue))

/****************************************************************************/
/**
*
* Get the contents of the receive FIFO watermark register.
* Use the XSPIPS_RXWR_* constants defined xspips_hw.h to interpret
* the bit-mask returned.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	A 8-bit value representing the contents of the RXWR register.
*
* @note		C-Style signature:
*		u32 XSpiPs_GetRXWatermark(u32 *InstancePtr)
*
*****************************************************************************/
#define XSpiPs_GetRXWatermark(InstancePtr)				\
	XSpiPs_In32(((InstancePtr)->Config.BaseAddress) + XSPIPS_RXWR_OFFSET)

/****************************************************************************/
/**
*
* Enable the device and uninhibit master transactions.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XSpiPs_Enable(u32 *InstancePtr)
*
*****************************************************************************/
#define XSpiPs_Enable(InstancePtr)					\
	XSpiPs_Out32(((InstancePtr)->Config.BaseAddress) + XSPIPS_ER_OFFSET, \
		XSPIPS_ER_ENABLE_MASK)

/****************************************************************************/
/**
*
* Disable the device.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XSpiPs_Disable(u32 *InstancePtr)
*
*****************************************************************************/
#define XSpiPs_Disable(InstancePtr)					\
	XSpiPs_Out32(((InstancePtr)->Config.BaseAddress) + XSPIPS_ER_OFFSET, 0U)

/************************** Function Prototypes ******************************/

/*
 * Initialization function, implemented in xspips_sinit.c
 */
XSpiPs_Config *XSpiPs_LookupConfig(u16 DeviceId);

/*
 * Functions implemented in xspips.c
 */
s32 XSpiPs_CfgInitialize(XSpiPs *InstancePtr, XSpiPs_Config * ConfigPtr,
				u32 EffectiveAddr);

void XSpiPs_Reset(XSpiPs *InstancePtr);

s32 XSpiPs_Transfer(XSpiPs *InstancePtr, u8 *SendBufPtr, u8 *RecvBufPtr,
			u32 ByteCount);

s32 XSpiPs_PolledTransfer(XSpiPs *InstancePtr, u8 *SendBufPtr,
				u8 *RecvBufPtr, u32 ByteCount);

void XSpiPs_SetStatusHandler(XSpiPs *InstancePtr, void *CallBackRef,
				XSpiPs_StatusHandler FunctionPtr);
void XSpiPs_InterruptHandler(XSpiPs *InstancePtr);

void XSpiPs_Abort(XSpiPs *InstancePtr);

s32 XSpiPs_SetSlaveSelect(XSpiPs *InstancePtr, u8 SlaveSel);
u8 XSpiPs_GetSlaveSelect(XSpiPs *InstancePtr);

/*
 * Functions for selftest, in xspips_selftest.c
 */
s32 XSpiPs_SelfTest(XSpiPs *InstancePtr);

/*
 * Functions for options, in xspips_options.c
 */
s32 XSpiPs_SetOptions(XSpiPs *InstancePtr, u32 Options);
u32 XSpiPs_GetOptions(XSpiPs *InstancePtr);

s32 XSpiPs_SetClkPrescaler(XSpiPs *InstancePtr, u8 Prescaler);
u8 XSpiPs_GetClkPrescaler(XSpiPs *InstancePtr);

s32 XSpiPs_SetDelays(XSpiPs *InstancePtr, u8 DelayNss, u8 DelayBtwn,
			u8 DelayAfter, u8 DelayInit);
void XSpiPs_GetDelays(XSpiPs *InstancePtr, u8 *DelayNss, u8 *DelayBtwn,
			u8 *DelayAfter, u8 *DelayInit);
#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
