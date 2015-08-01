/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xqspips.h
*
* This file contains the implementation of the XQspiPs driver. It supports only
* master mode. User documentation for the driver functions is contained in this
* file in the form of comment blocks at the front of each function.
*
* A QSPI device connects to an QSPI bus through a 4-wire serial interface.
* The QSPI bus is a full-duplex, synchronous bus that facilitates communication
* between one master and one slave. The device is always full-duplex,
* which means that for every byte sent, one is received, and vice-versa.
* The master controls the clock, so it can regulate when it wants to
* send or receive data. The slave is under control of the master, it must
* respond quickly since it has no control of the clock and must send/receive
* data as fast or as slow as the master does.
*
* <b> Linear Mode </b>
* The Linear Quad-SPI Controller extends the existing Quad-SPI Controller’s
* functionality by adding a linear addressing scheme that allows the SPI flash
* memory subsystem to behave like a typical ROM device.  The new feature hides
* the normal SPI protocol from a master reading from the SPI flash memory. The
* feature improves both the user friendliness and the overall read memory
* throughput over that of the current Quad-SPI Controller by lessening the
* amount of software overheads required and by the use of the faster AXI
* interface.
*
* <b>Initialization & Configuration</b>
*
* The XQspiPs_Config structure is used by the driver to configure itself. This
* configuration structure is typically created by the tool-chain based on HW
* build properties.
*
* To support multiple runtime loading and initialization strategies employed by
* various operating systems, the driver instance can be initialized in the
* following way:
*	- XQspiPs_LookupConfig(DeviceId) - Use the device identifier to find
*	  static configuration structure defined in xqspips_g.c. This is setup
*	  by the tools. For some operating systems the config structure will be
*	  initialized by the software and this call is not needed.
*	- XQspiPs_CfgInitialize(InstancePtr, CfgPtr, EffectiveAddr) - Uses a
*	  configuration structure provided by the caller. If running in a system
*	  with address translation, the provided virtual memory base address
*	  replaces the physical address present in the configuration structure.
*
* <b>Multiple Masters</b>
*
* More than one master can exist, but arbitration is the responsibility of
* the higher layer software. The device driver does not perform any type of
* arbitration.
*
* <b>Modes of Operation</b>
*
* There are four modes to perform a data transfer and the selection of a mode
* is based on Chip Select(CS) and Start. These two options individually, can
* be controlled either by software(Manual) or hardware(Auto).
* - Auto CS: Chip select is automatically asserted as soon as the first word
*	     is written into the TXFIFO and de asserted when the TXFIFO becomes
*	     empty
* - Manual CS: Software must assert and de assert CS.
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
*   keep the TXFIFO filled. Whenever the TXFIFO runs empty, CS is de asserted.
*   This results in a single transaction to be split into multiple pieces each
*   with its own chip select. This will result in garbage data to be sent.
*
* <b>Interrupts</b>
*
* The user must connect the interrupt handler of the driver,
* XQspiPs_InterruptHandler, to an interrupt system such that it will be
* called when an interrupt occurs. This function does not save and restore
* the processor context such that the user must provide this processing.
*
* The driver handles the following interrupts:
* - Data Transmit Register/FIFO Underflow
* - Data Receive Register/FIFO Not Empty
* - Data Transmit Register/FIFO Overwater
* - Data Receive Register/FIFO Overrun
*
* The Data Transmit Register/FIFO Overwater interrupt -- indicates that the
* QSPI device has transmitted the data available to transmit, and now its data
* register and FIFO is ready to accept more data. The driver uses this
* interrupt to indicate progress while sending data.  The driver may have
* more data to send, in which case the data transmit register and FIFO is
* filled for subsequent transmission. When this interrupt arrives and all
* the data has been sent, the driver invokes the status callback with a
* value of XST_SPI_TRANSFER_DONE to inform the upper layer software that
* all data has been sent.
*
* The Data Transmit Register/FIFO Underflow interrupt -- indicates that,
* as slave, the QSPI device was required to transmit but there was no data
* available to transmit in the transmit register (or FIFO). This may not
* be an error if the master is not expecting data. But in the case where
* the master is expecting data, this serves as a notification of such a
* condition. The driver reports this condition to the upper layer
* software through the status handler.
*
* The Data Receive Register/FIFO Overrun interrupt -- indicates that the QSPI
* device received data and subsequently dropped the data because the data
* receive register and FIFO was full. The driver reports this condition to the
* upper layer software through the status handler. This likely indicates a
* problem with the higher layer protocol, or a problem with the slave
* performance.
*
*
* <b>Polled Operation</b>
*
* Transfer in polled mode is supported through a separate interface function
* XQspiPs_PolledTransfer(). Unlike the transfer function in the interrupt mode,
* this function blocks until all data has been sent/received.
*
* <b>Device Busy</b>
*
* Some operations are disallowed when the device is busy. The driver tracks
* whether a device is busy. The device is considered busy when a data transfer
* request is outstanding, and is considered not busy only when that transfer
* completes (or is aborted with a mode fault error).
*
* <b>Device Configuration</b>
*
* The device can be configured in various ways during the FPGA implementation
* process. Configuration parameters are stored in the xqspips_g.c file or
* passed in via XQspiPs_CfgInitialize(). A table is defined where each entry
* contains configuration information for an QSPI device, including the base
* address for the device.
*
* <b>RTOS Independence</b>
*
* This driver is intended to be RTOS and processor independent.  It works with
* physical addresses only.  Any needs for dynamic memory management, threads or
* thread mutual exclusion, virtual memory, or cache control must be satisfied
* by the layer above this driver.
*
* NOTE: This driver was always tested with endianess set to little-endian.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 1.00a sdm 11/25/10 First release, based on the PS SPI driver...
* 1.01a sdm 11/22/11 Added TCL file for generating QSPI parameters
*		     in xparameters.h
* 2.00a kka 07/25/12 Added a few register defines for CR 670297
* 		     Removed code related to mode fault for CR 671468
*		     The XQspiPs_SetSlaveSelect has been modified to remove
*		     the argument of the slave select as the QSPI controller
*		     only supports one slave.
* 		     XQspiPs_GetSlaveSelect API has been removed
* 		     Added a flag ShiftReadData to the instance structure
*.		     and is used in the XQspiPs_GetReadData API.
*		     The ShiftReadData Flag indicates whether the data
*		     read from the Rx FIFO needs to be shifted
*		     in cases where the data is less than 4  bytes
* 		     Removed the selection for the following options:
*		     Master mode (XQSPIPS_MASTER_OPTION) and
*		     Flash interface mode (XQSPIPS_FLASH_MODE_OPTION) option
*		     as the QSPI driver supports the Master mode
*		     and Flash Interface mode and doesnot support
*		     Slave mode or the legacy mode.
*		     Modified the XQspiPs_PolledTransfer and XQspiPs_Transfer
*		     APIs so that the last argument (IsInst) specifying whether
*		     it is instruction or data has been removed. The first byte
*		     in the SendBufPtr argument of these APIs specify the
*		     instruction to be sent to the Flash Device.
*		     This version of the driver fixes CRs 670197/663787/
*		     670297/671468.
* 		     Added the option for setting the Holdb_dr bit in the
*		     configuration options, XQSPIPS_HOLD_B_DRIVE_OPTION
*		     is the option to be used for setting this bit in the
*		     configuration register.
*		     The XQspiPs_PolledTransfer function has been updated
*		     to fill the data to fifo depth.
* 2.01a sg  02/03/13 Added flash opcodes for DUAL_IO_READ,QUAD_IO_READ.
*		     Added macros for Set/Get Rx Watermark. Changed QSPI
*		     Enable/Disable macro argument from BaseAddress to
*		     Instance Pointer. Added DelayNss argument to SetDelays
*		     and GetDelays API's.
*		     Created macros XQspiPs_IsManualStart and
*		     XQspiPs_IsManualChipSelect.
*		     Changed QSPI transfer logic for polled and interrupt
*		     modes to be based on filled tx fifo count and receive
*		     based on it. RXNEMPTY interrupt is not used.
*		     Added assertions to XQspiPs_LqspiRead function.
*		     SetDelays and GetDelays API's include DelayNss parameter.
*		     Added defines for DelayNss,Rx Watermark,Interrupts
*		     which need write to clear. Removed Read zeros mask from
*		     LQSPI Config register. Renamed Fixed burst error to
*		     data FSM error in  LQSPI Status register.
*
* 2.02a hk  05/07/13 Added ConnectionMode to config structure.
*			 Corresponds to C_QSPI_MODE - 0:Single, 1:Stacked, 2:Parallel
*			 Added enable and disable to the XQspiPs_LqspiRead() function
*			 Removed XQspi_Reset() in Set_Options() function when
*			 LQSPI_MODE_OPTION is set.
*            Added instructions for bank selection, die erase and
*            flag status register to the flash instruction table
*            Handling for instructions not in flash instruction
*			 table added. Checking for Tx FIFO empty when switching from
*			 TXD1/2/3 to TXD0 added. If WRSR instruction is sent with
*            byte count 3 (spansion), instruction size and TXD register
*			 changed accordingly. CR# 712502 and 703869.
*            Added prefix to constant definitions for ConnectionMode
*            Added (#ifdef linear base address) in the Linear read function.
*            Changed  XPAR_XQSPIPS_0_LINEAR_BASEADDR to
*            XPAR_PS7_QSPI_LINEAR_0_S_AXI_BASEADDR in
*            XQspiPs_LqspiRead function. Fix for CR#718141.
*
* 2.03a hk  09/17/13 Modified polled and interrupt transfers to make use of
*                    thresholds. This is to improve performance.
*                    Added API's for QSPI reset and
*                    linear mode initialization for boot.
*                    Added RX and TX threshold reset to one in XQspiPs_Abort.
*                    Added RX threshold reset(1) after transfer in polled and
*                    interrupt transfers. Made changes to make sure threshold
*                    change is done only when no transfer is in progress.
*                    Updated linear init API for parallel and stacked modes.
*                    CR#737760.
*
* </pre>
*
******************************************************************************/
#ifndef XQSPIPS_H		/* prevent circular inclusions */
#define XQSPIPS_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xqspips_hw.h"
#include <string.h>

/************************** Constant Definitions *****************************/

/** @name Configuration options
 *
 * The following options are supported to enable/disable certain features of
 * an QSPI device.  Each of the options is a bit mask, so more than one may be
 * specified.
 *
 *
 * The <b>Active Low Clock option</b> configures the device's clock polarity.
 * Setting this option means the clock is active low and the SCK signal idles
 * high. By default, the clock is active high and SCK idles low.
 *
 * The <b>Clock Phase option</b> configures the QSPI device for one of two
 * transfer formats.  A clock phase of 0, the default, means data is valid on
 * the first SCK edge (rising or falling) after the slave select (SS) signal
 * has been asserted. A clock phase of 1 means data is valid on the second SCK
 * edge (rising or falling) after SS has been asserted.
 *
 *
 * The <b>QSPI Force Slave Select option</b> is used to enable manual control of
 * the slave select signal.
 * 0: The SPI_SS signal is controlled by the QSPI controller during
 * transfers. (Default)
 * 1: The SPI_SS signal is forced active (driven low) regardless of any
 * transfers in progress.
 *
 * NOTE: The driver will handle setting and clearing the Slave Select when
 * the user sets the "FORCE_SSELECT_OPTION". Using this option will allow the
 * QSPI clock to be set to a faster speed. If the QSPI clock is too fast, the
 * processor cannot empty and refill the FIFOs before the TX FIFO is empty
 * When the QSPI hardware is controlling the Slave Select signals, this
 * will cause slave to be de-selected and terminate the transfer.
 *
 * The <b>Manual Start option</b> is used to enable manual control of
 * the Start command to perform data transfer.
 * 0: The Start command is controlled by the QSPI controller during
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
#define XQSPIPS_CLK_ACTIVE_LOW_OPTION	0x2  /**< Active Low Clock option */
#define XQSPIPS_CLK_PHASE_1_OPTION	0x4  /**< Clock Phase one option */
#define XQSPIPS_FORCE_SSELECT_OPTION	0x10 /**< Force Slave Select */
#define XQSPIPS_MANUAL_START_OPTION	0x20 /**< Manual Start enable */
#define XQSPIPS_LQSPI_MODE_OPTION	0x80 /**< Linear QPSI mode */
#define XQSPIPS_HOLD_B_DRIVE_OPTION	0x100 /**< Drive HOLD_B Pin */
/*@}*/


/** @name QSPI Clock Prescaler options
 * The QSPI Clock Prescaler Configuration bits are used to program master mode
 * bit rate. The bit rate can be programmed in divide-by-two decrements from
 * pclk/2 to pclk/256.
 *
 * @{
 */
#define XQSPIPS_CLK_PRESCALE_2		0x00 /**< PCLK/2 Prescaler */
#define XQSPIPS_CLK_PRESCALE_4		0x01 /**< PCLK/4 Prescaler */
#define XQSPIPS_CLK_PRESCALE_8		0x02 /**< PCLK/8 Prescaler */
#define XQSPIPS_CLK_PRESCALE_16		0x03 /**< PCLK/16 Prescaler */
#define XQSPIPS_CLK_PRESCALE_32		0x04 /**< PCLK/32 Prescaler */
#define XQSPIPS_CLK_PRESCALE_64		0x05 /**< PCLK/64 Prescaler */
#define XQSPIPS_CLK_PRESCALE_128	0x06 /**< PCLK/128 Prescaler */
#define XQSPIPS_CLK_PRESCALE_256	0x07 /**< PCLK/256 Prescaler */

/*@}*/


/** @name Callback events
 *
 * These constants specify the handler events that are passed to
 * a handler from the driver.  These constants are not bit masks such that
 * only one will be passed at a time to the handler.
 *
 * @{
 */
#define XQSPIPS_EVENT_TRANSFER_DONE	2 /**< Transfer done */
#define XQSPIPS_EVENT_TRANSMIT_UNDERRUN 3 /**< TX FIFO empty */
#define XQSPIPS_EVENT_RECEIVE_OVERRUN	4 /**< Receive data loss because
						RX FIFO full */
/*@}*/

/** @name Flash commands
 *
 * The following constants define most of the commands supported by flash
 * devices. Users can add more commands supported by the flash devices
 *
 * @{
 */
#define	XQSPIPS_FLASH_OPCODE_WRSR	0x01 /* Write status register */
#define	XQSPIPS_FLASH_OPCODE_PP		0x02 /* Page program */
#define	XQSPIPS_FLASH_OPCODE_NORM_READ	0x03 /* Normal read data bytes */
#define	XQSPIPS_FLASH_OPCODE_WRDS	0x04 /* Write disable */
#define	XQSPIPS_FLASH_OPCODE_RDSR1	0x05 /* Read status register 1 */
#define	XQSPIPS_FLASH_OPCODE_WREN	0x06 /* Write enable */
#define	XQSPIPS_FLASH_OPCODE_FAST_READ	0x0B /* Fast read data bytes */
#define	XQSPIPS_FLASH_OPCODE_BE_4K	0x20 /* Erase 4KiB block */
#define	XQSPIPS_FLASH_OPCODE_RDSR2	0x35 /* Read status register 2 */
#define	XQSPIPS_FLASH_OPCODE_DUAL_READ	0x3B /* Dual read data bytes */
#define	XQSPIPS_FLASH_OPCODE_BE_32K	0x52 /* Erase 32KiB block */
#define	XQSPIPS_FLASH_OPCODE_QUAD_READ	0x6B /* Quad read data bytes */
#define	XQSPIPS_FLASH_OPCODE_ERASE_SUS	0x75 /* Erase suspend */
#define	XQSPIPS_FLASH_OPCODE_ERASE_RES	0x7A /* Erase resume */
#define	XQSPIPS_FLASH_OPCODE_RDID	0x9F /* Read JEDEC ID */
#define	XQSPIPS_FLASH_OPCODE_BE		0xC7 /* Erase whole flash block */
#define	XQSPIPS_FLASH_OPCODE_SE		0xD8 /* Sector erase (usually 64KB)*/
#define XQSPIPS_FLASH_OPCODE_DUAL_IO_READ 0xBB /* Read data using Dual I/O */
#define XQSPIPS_FLASH_OPCODE_QUAD_IO_READ 0xEB /* Read data using Quad I/O */
#define XQSPIPS_FLASH_OPCODE_BRWR	0x17 /* Bank Register Write */
#define XQSPIPS_FLASH_OPCODE_BRRD	0x16 /* Bank Register Read */
/* Extende Address Register Write - Micron's equivalent of Bank Register */
#define XQSPIPS_FLASH_OPCODE_EARWR	0xC5
/* Extende Address Register Read - Micron's equivalent of Bank Register */
#define XQSPIPS_FLASH_OPCODE_EARRD	0xC8
#define XQSPIPS_FLASH_OPCODE_DIE_ERASE	0xC4
#define XQSPIPS_FLASH_OPCODE_READ_FLAG_SR	0x70
#define XQSPIPS_FLASH_OPCODE_CLEAR_FLAG_SR	0x50
#define XQSPIPS_FLASH_OPCODE_READ_LOCK_REG	0xE8	/* Lock register Read */
#define XQSPIPS_FLASH_OPCODE_WRITE_LOCK_REG	0xE5	/* Lock Register Write */

/*@}*/

/** @name Instruction size
 *
 * The following constants define numbers 1 to 4.
 * Used to identify whether TXD0,1,2 or 3 is to be used.
 *
 * @{
 */
#define XQSPIPS_SIZE_ONE 	1
#define XQSPIPS_SIZE_TWO 	2
#define XQSPIPS_SIZE_THREE 	3
#define XQSPIPS_SIZE_FOUR 	4

/*@}*/

/** @name ConnectionMode
 *
 * The following constants are the possible values of ConnectionMode in
 * Config structure.
 *
 * @{
 */
#define XQSPIPS_CONNECTION_MODE_SINGLE		0
#define XQSPIPS_CONNECTION_MODE_STACKED		1
#define XQSPIPS_CONNECTION_MODE_PARALLEL	2

/*@}*/

/** @name FIFO threshold value
 *
 * This is the Rx FIFO threshold (in words) that was found to be most
 * optimal in terms of performance
 *
 * @{
 */
#define XQSPIPS_RXFIFO_THRESHOLD_OPT		32

/*@}*/

/**************************** Type Definitions *******************************/
/**
 * The handler data type allows the user to define a callback function to
 * handle the asynchronous processing for the QSPI device.  The application
 * using this driver is expected to define a handler of this type to support
 * interrupt driven mode.  The handler executes in an interrupt context, so
 * only minimal processing should be performed.
 *
 * @param	CallBackRef is the callback reference passed in by the upper
 *		layer when setting the callback functions, and passed back to
 *		the upper layer when the callback is invoked. Its type is
 *		not important to the driver, so it is a void pointer.
 * @param 	StatusEvent holds one or more status events that have occurred.
 *		See the XQspiPs_SetStatusHandler() for details on the status
 *		events that can be passed in the callback.
 * @param	ByteCount indicates how many bytes of data were successfully
 *		transferred.  This may be less than the number of bytes
 *		requested if the status event indicates an error.
 */
typedef void (*XQspiPs_StatusHandler) (void *CallBackRef, u32 StatusEvent,
					unsigned ByteCount);

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;		/**< Unique ID  of device */
	u32 BaseAddress;	/**< Base address of the device */
	u32 InputClockHz;	/**< Input clock frequency */
	u8  ConnectionMode; /**< Single, Stacked and Parallel mode */
} XQspiPs_Config;

/**
 * The XQspiPs driver instance data. The user is required to allocate a
 * variable of this type for every QSPI device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XQspiPs_Config Config;	 /**< Configuration structure */
	u32 IsReady;		 /**< Device is initialized and ready */

	u8 *SendBufferPtr;	 /**< Buffer to send (state) */
	u8 *RecvBufferPtr;	 /**< Buffer to receive (state) */
	int RequestedBytes;	 /**< Number of bytes to transfer (state) */
	int RemainingBytes;	 /**< Number of bytes left to transfer(state) */
	u32 IsBusy;		 /**< A transfer is in progress (state) */
	XQspiPs_StatusHandler StatusHandler;
	void *StatusRef;  	 /**< Callback reference for status handler */
	u32 ShiftReadData;	 /**<  Flag to indicate whether the data
				   *   read from the Rx FIFO needs to be shifted
				   *   in cases where the data is less than 4
				   *   bytes
				   */
} XQspiPs;

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/*
*
* Check in OptionsTable if Manual Start Option is enabled or disabled.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return
*		- TRUE if option is set
*		- FALSE if option is not set
*
* @note		C-Style signature:
*		u8 XQspiPs_IsManualStart(XQspiPs *InstancePtr);
*
*****************************************************************************/
#define XQspiPs_IsManualStart(InstancePtr) \
	((XQspiPs_GetOptions(InstancePtr) & \
	  XQSPIPS_MANUAL_START_OPTION) ? TRUE : FALSE)

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
*		u8 XQspiPs_IsManualChipSelect(XQspiPs *InstancePtr);
*
*****************************************************************************/
#define XQspiPs_IsManualChipSelect(InstancePtr) \
	((XQspiPs_GetOptions(InstancePtr) & \
	  XQSPIPS_FORCE_SSELECT_OPTION) ? TRUE : FALSE)

/****************************************************************************/
/**
*
* Set the contents of the slave idle count register.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	RegisterValue is the value to be written, valid values are
*		0-255.
*
* @return	None
*
* @note
* C-Style signature:
*	void XQspiPs_SetSlaveIdle(XQspiPs *InstancePtr, u32 RegisterValue)
*
*****************************************************************************/
#define XQspiPs_SetSlaveIdle(InstancePtr, RegisterValue)	\
	XQspiPs_Out32(((InstancePtr)->Config.BaseAddress) + 	\
			XQSPIPS_SICR_OFFSET, (RegisterValue))

/****************************************************************************/
/**
*
* Get the contents of the slave idle count register. Use the XQSPIPS_SICR_*
* constants defined in xqspips_hw.h to interpret the bit-mask returned.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	An 8-bit value representing Slave Idle Count.
*
* @note		C-Style signature:
*		u32 XQspiPs_GetSlaveIdle(XQspiPs *InstancePtr)
*
*****************************************************************************/
#define XQspiPs_GetSlaveIdle(InstancePtr)				\
	XQspiPs_In32(((InstancePtr)->Config.BaseAddress) + 		\
	XQSPIPS_SICR_OFFSET)

/****************************************************************************/
/**
*
* Set the contents of the transmit FIFO watermark register.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	RegisterValue is the value to be written, valid values are 1-63.
*
* @return	None.
*
* @note
* C-Style signature:
*	void XQspiPs_SetTXWatermark(XQspiPs *InstancePtr, u32 RegisterValue)
*
*****************************************************************************/
#define XQspiPs_SetTXWatermark(InstancePtr, RegisterValue)		\
	XQspiPs_Out32(((InstancePtr)->Config.BaseAddress) + 		\
			XQSPIPS_TXWR_OFFSET, (RegisterValue))

/****************************************************************************/
/**
*
* Get the contents of the transmit FIFO watermark register.
* Valid values are in the range 1-63.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	A 6-bit value representing Tx Watermark level.
*
* @note		C-Style signature:
*		u32 XQspiPs_GetTXWatermark(XQspiPs *InstancePtr)
*
*****************************************************************************/
#define XQspiPs_GetTXWatermark(InstancePtr)				\
	XQspiPs_In32((InstancePtr->Config.BaseAddress) + XQSPIPS_TXWR_OFFSET)

/****************************************************************************/
/**
*
* Set the contents of the receive FIFO watermark register.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	RegisterValue is the value to be written, valid values are 1-63.
*
* @return	None.
*
* @note
* C-Style signature:
*	void XQspiPs_SetRXWatermark(XQspiPs *InstancePtr, u32 RegisterValue)
*
*****************************************************************************/
#define XQspiPs_SetRXWatermark(InstancePtr, RegisterValue)		\
	XQspiPs_Out32(((InstancePtr)->Config.BaseAddress) + 		\
			XQSPIPS_RXWR_OFFSET, (RegisterValue))

/****************************************************************************/
/**
*
* Get the contents of the receive FIFO watermark register.
* Valid values are in the range 1-63.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	A 6-bit value representing Rx Watermark level.
*
* @note		C-Style signature:
*		u32 XQspiPs_GetRXWatermark(XQspiPs *InstancePtr)
*
*****************************************************************************/
#define XQspiPs_GetRXWatermark(InstancePtr)				\
	XQspiPs_In32((InstancePtr->Config.BaseAddress) + XQSPIPS_RXWR_OFFSET)

/****************************************************************************/
/**
*
* Enable the device and uninhibit master transactions.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XQspiPs_Enable(XQspiPs *InstancePtr)
*
*****************************************************************************/
#define XQspiPs_Enable(InstancePtr)					\
	XQspiPs_Out32((InstancePtr->Config.BaseAddress) + XQSPIPS_ER_OFFSET, \
			XQSPIPS_ER_ENABLE_MASK)

/****************************************************************************/
/**
*
* Disable the device.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XQspiPs_Disable(XQspiPs *InstancePtr)
*
*****************************************************************************/
#define XQspiPs_Disable(InstancePtr)					\
	XQspiPs_Out32((InstancePtr->Config.BaseAddress) + XQSPIPS_ER_OFFSET, 0)

/****************************************************************************/
/**
*
* Set the contents of the Linear QSPI Configuration register.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	RegisterValue is the value to be written to the Linear QSPI
*		configuration register.
*
* @return	None.
*
* @note
* C-Style signature:
*	void XQspiPs_SetLqspiConfigReg(XQspiPs *InstancePtr,
*					u32 RegisterValue)
*
*****************************************************************************/
#define XQspiPs_SetLqspiConfigReg(InstancePtr, RegisterValue)		\
	XQspiPs_Out32(((InstancePtr)->Config.BaseAddress) +		\
			XQSPIPS_LQSPI_CR_OFFSET, (RegisterValue))

/****************************************************************************/
/**
*
* Get the contents of the Linear QSPI Configuration register.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	A 32-bit value representing the contents of the LQSPI Config
*		register.
*
* @note		C-Style signature:
*		u32 XQspiPs_GetLqspiConfigReg(u32 *InstancePtr)
*
*****************************************************************************/
#define XQspiPs_GetLqspiConfigReg(InstancePtr)				\
	XQspiPs_In32((InstancePtr->Config.BaseAddress) +		\
			XQSPIPS_LQSPI_CR_OFFSET)

/************************** Function Prototypes ******************************/

/*
 * Initialization function, implemented in xqspips_sinit.c
 */
XQspiPs_Config *XQspiPs_LookupConfig(u16 DeviceId);

/*
 * Functions implemented in xqspips.c
 */
int XQspiPs_CfgInitialize(XQspiPs *InstancePtr, XQspiPs_Config * Config,
			   u32 EffectiveAddr);
void XQspiPs_Reset(XQspiPs *InstancePtr);
void XQspiPs_Abort(XQspiPs *InstancePtr);

int XQspiPs_Transfer(XQspiPs *InstancePtr, u8 *SendBufPtr, u8 *RecvBufPtr,
		      unsigned ByteCount);
int XQspiPs_PolledTransfer(XQspiPs *InstancePtr, u8 *SendBufPtr,
			    u8 *RecvBufPtr, unsigned ByteCount);
int XQspiPs_LqspiRead(XQspiPs *InstancePtr, u8 *RecvBufPtr,
			u32 Address, unsigned ByteCount);

int XQspiPs_SetSlaveSelect(XQspiPs *InstancePtr);

void XQspiPs_SetStatusHandler(XQspiPs *InstancePtr, void *CallBackRef,
				XQspiPs_StatusHandler FuncPtr);
void XQspiPs_InterruptHandler(void *InstancePtr);

/*
 * Functions for selftest, in xqspips_selftest.c
 */
int XQspiPs_SelfTest(XQspiPs *InstancePtr);

/*
 * Functions for options, in xqspips_options.c
 */
int XQspiPs_SetOptions(XQspiPs *InstancePtr, u32 Options);
u32 XQspiPs_GetOptions(XQspiPs *InstancePtr);

int XQspiPs_SetClkPrescaler(XQspiPs *InstancePtr, u8 Prescaler);
u8 XQspiPs_GetClkPrescaler(XQspiPs *InstancePtr);

int XQspiPs_SetDelays(XQspiPs *InstancePtr, u8 DelayNss, u8 DelayBtwn,
			 u8 DelayAfter, u8 DelayInit);
void XQspiPs_GetDelays(XQspiPs *InstancePtr, u8 *DelayNss, u8 *DelayBtwn,
			 u8 *DelayAfter, u8 *DelayInit);
#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */

