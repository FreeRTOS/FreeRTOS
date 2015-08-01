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
* @file xiicps.h
*
* This is an implementation of IIC driver in the PS block. The device can
* be either a master or a slave on the IIC bus. This implementation supports
* both interrupt mode transfer and polled mode transfer. Only 7-bit address
* is used in the driver, although the hardware also supports 10-bit address.
*
* IIC is a 2-wire serial interface.  The master controls the clock, so it can
* regulate when it wants to send or receive data. The slave is under control of
* the master, it must respond quickly since it has no control of the clock and
* must send/receive data as fast or as slow as the master does.
*
* The higher level software must implement a higher layer protocol to inform
* the slave what to send to the master.
*
* <b>Initialization & Configuration</b>
*
* The XIicPs_Config structure is used by the driver to configure itself. This
* configuration structure is typically created by the tool-chain based on HW
* build properties.
*
* To support multiple runtime loading and initialization strategies employed by
* various operating systems, the driver instance can be initialized in the
* following way:
*
*    - XIicPs_LookupConfig(DeviceId) - Use the device identifier to find
*      the static configuration structure defined in xiicps_g.c. This is
*      setup by the tools. For some operating systems the config structure
*      will be initialized by the software and this call is not needed.
*
*   - XIicPs_CfgInitialize(InstancePtr, CfgPtr, EffectiveAddr) - Uses a
*     configuration structure provided by the caller. If running in a
*     system with address translation, the provided virtual memory base
*     address replaces the physical address in the configuration
*     structure.
*
* <b>Multiple Masters</b>
*
* More than one master can exist, bus arbitration is defined in the IIC
* standard. Lost of arbitration causes arbitration loss interrupt on the device.
*
* <b>Multiple Slaves</b>
*
* Multiple slaves are supported by selecting them with unique addresses. It is
* up to the system designer to be sure all devices on the IIC bus have
* unique addresses.
*
* <b>Addressing</b>
*
* The IIC hardware can use 7 or 10 bit addresses.  The driver provides the
* ability to control which address size is sent in messages as a master to a
* slave device.
*
* <b>FIFO Size </b>
* The hardware FIFO is 32 bytes deep. The user must know the limitations of
* other IIC devices on the bus. Some are only able to receive a limited number
* of bytes in a single transfer.
*
* <b>Data Rates</b>
*
* The data rate is set by values in the control register. The formula for
* determining the correct register values is:
* Fscl = Fpclk/(22 x (divisor_a+1) x (divisor_b+1))
*
* When the device is configured as a slave, the slck setting controls the
* sample rate and so must be set to be at least as fast as the fastest scl
* expected to be seen in the system.
*
* <b>Polled Mode Operation</b>
*
* This driver supports polled mode transfers.
*
* <b>Interrupts</b>
*
* The user must connect the interrupt handler of the driver,
* XIicPs_InterruptHandler to an interrupt system such that it will be called
* when an interrupt occurs. This function does not save and restore the
* processor context such that the user must provide this processing.
*
* The driver handles the following interrupts:
* - Transfer complete
* - More Data
* - Transfer not Acknowledged
* - Transfer Time out
* - Monitored slave ready - master mode only
* - Receive Overflow
* - Transmit FIFO overflow
* - Receive FIFO underflow
* - Arbitration lost
*
* <b>Bus Busy</b>
*
* Bus busy is checked before the setup of a master mode device, to avoid
* unnecessary arbitration loss interrupt.
*
* <b>RTOS Independence</b>
*
* This driver is intended to be RTOS and processor independent.  It works with
* physical addresses only.  Any needs for dynamic memory management, threads or
* thread mutual exclusion, virtual memory, or cache control must be satisfied by
* the layer above this driver.
*
* @note
* . Less than FIFO size transfers work for both 100 KHz and 400 KHz.
* . Larger than FIFO size interrupt-driven transfers are not reliable on
*    busy systems where interrupt latency is high.
* . Larger than FIFO size interrupt-driven transfers are not reliable for
*    data rate of 400 KHz.
* . Larger than FIFO size polled mode transfers work reliably.
*
* <pre> MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- -----------------------------------------------
* 1.00a drg/jz  01/30/08 First release
* 1.00a sdm     09/21/11 Fixed an issue in the XIicPs_SetOptions and
*			 XIicPs_ClearOptions where the InstancePtr->Options
*			 was not updated correctly.
* 			 Updated the InstancePtr->Options in the
*			 XIicPs_CfgInitialize by calling XIicPs_GetOptions.
*			 Updated the XIicPs_SetupMaster to not check for
*			 Bus Busy condition when the Hold Bit is set.
*			 Removed some unused variables.
* 1.01a sg      03/30/12 Fixed an issue in XIicPs_MasterSendPolled where a
*			 check for transfer completion is added, which indicates
*			 the completion of current transfer.
* 1.02a sg	08/29/12 Updated the logic to arrive at the best divisors
*			 to achieve I2C clock with minimum error for
*			 CR #674195
* 1.03a hk  05/04/13 Initialized BestDivA and BestDivB to 0.
*			 This is fix for CR#704398 to remove warning.
* 2.0   hk  03/07/14 Added check for error status in the while loop that
*                    checks for completion.
*                    (XIicPs_MasterSendPolled function). CR# 762244, 764875.
*                    Limited frequency set when 100KHz or 400KHz is
*                    selected. This is a hardware limitation. CR#779290.
* 2.1   hk  04/24/14 Fix for CR# 789821 to handle >14 byte transfers.
*                    Explicitly reset CR and clear FIFO in Abort function
*                    and state the same in the comments. CR# 784254.
*                    Fix for CR# 761060 - provision for repeated start.
*
* </pre>
*
******************************************************************************/

#ifndef XIICPS_H       /* prevent circular inclusions */
#define XIICPS_H       /* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xiicps_hw.h"

/************************** Constant Definitions *****************************/

/** @name Configuration options
 *
 * The following options may be specified or retrieved for the device and
 * enable/disable additional features of the IIC.  Each of the options
 * are bit fields, so more than one may be specified.
 *
 * @{
 */
#define XIICPS_7_BIT_ADDR_OPTION	0x01  /**< 7-bit address mode */
#define XIICPS_10_BIT_ADDR_OPTION	0x02  /**< 10-bit address mode */
#define XIICPS_SLAVE_MON_OPTION		0x04  /**< Slave monitor mode */
#define XIICPS_REP_START_OPTION		0x08  /**< Repeated Start */
/*@}*/

/** @name Callback events
 *
 * These constants specify the handler events that are passed to an application
 * event handler from the driver.  These constants are bit masks such that
 * more than one event can be passed to the handler.
 *
 * @{
 */
#define XIICPS_EVENT_COMPLETE_SEND	0x0001  /**< Transmit Complete Event*/
#define XIICPS_EVENT_COMPLETE_RECV	0x0002  /**< Receive Complete Event*/
#define XIICPS_EVENT_TIME_OUT		0x0004  /**< Transfer timed out */
#define XIICPS_EVENT_ERROR		0x0008  /**< Receive error */
#define XIICPS_EVENT_ARB_LOST		0x0010  /**< Arbitration lost */
#define XIICPS_EVENT_NACK		0x0020  /**< NACK Received */
#define XIICPS_EVENT_SLAVE_RDY		0x0040  /**< Slave ready */
#define XIICPS_EVENT_RX_OVR		0x0080  /**< RX overflow */
#define XIICPS_EVENT_TX_OVR		0x0100  /**< TX overflow */
#define XIICPS_EVENT_RX_UNF		0x0200  /**< RX underflow */
/*@}*/

/** @name Role constants
 *
 * These constants are used to pass into the device setup routines to
 * set up the device according to transfer direction.
 */
#define SENDING_ROLE		1  /**< Transfer direction is sending */
#define RECVING_ROLE		0  /**< Transfer direction is receiving */

/* Maximum transfer size */
#define XIICPS_MAX_TRANSFER_SIZE	(255 - 3)

/**************************** Type Definitions *******************************/

/**
* The handler data type allows the user to define a callback function to
* respond to interrupt events in the system. This function is executed
* in interrupt context, so amount of processing should be minimized.
*
* @param	CallBackRef is the callback reference passed in by the upper
*		layer when setting the callback functions, and passed back to
*		the upper layer when the callback is invoked. Its type is
*		not important to the driver, so it is a void pointer.
* @param	StatusEvent indicates one or more status events that occurred.
*/
typedef void (*XIicPs_IntrHandler) (void *CallBackRef, u32 StatusEvent);

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;     /**< Unique ID  of device */
	u32 BaseAddress;  /**< Base address of the device */
	u32 InputClockHz; /**< Input clock frequency */
} XIicPs_Config;

/**
 * The XIicPs driver instance data. The user is required to allocate a
 * variable of this type for each IIC device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XIicPs_Config Config;	/* Configuration structure */
	u32 IsReady;		/* Device is initialized and ready */
	u32 Options;		/* Options set in the device */

	u8 *SendBufferPtr;	/* Pointer to send buffer */
	u8 *RecvBufferPtr;	/* Pointer to recv buffer */
	int SendByteCount;	/* Number of bytes still expected to send */
	int RecvByteCount;	/* Number of bytes still expected to receive */
	int CurrByteCount;	/* No. of bytes expected in current transfer */

	int UpdateTxSize;	/* If tx size register has to be updated */
	int IsSend;		/* Whether master is sending or receiving */
	int IsRepeatedStart;	/* Indicates if user set repeated start */

	XIicPs_IntrHandler StatusHandler;  /* Event handler function */
	void *CallBackRef;	/* Callback reference for event handler */
} XIicPs;

/***************** Macros (Inline Functions) Definitions *********************/
/****************************************************************************/
/*
*
* Place one byte into the transmit FIFO.
*
* @param	InstancePtr is the instance of IIC
*
* @return	None.
*
* @note		C-Style signature:
*		void XIicPs_SendByte(XIicPs *InstancePtr)
*
*****************************************************************************/
#define XIicPs_SendByte(InstancePtr)					\
{									\
	 XIicPs_Out32((InstancePtr)->Config.BaseAddress			\
			 + XIICPS_DATA_OFFSET, 				\
	*(InstancePtr)->SendBufferPtr ++);				\
	 (InstancePtr)->SendByteCount --;				\
}

/****************************************************************************/
/*
*
* Receive one byte from FIFO.
*
* @param	InstancePtr is the instance of IIC
*
* @return	None.
*
* @note		C-Style signature:
*		u8 XIicPs_RecvByte(XIicPs *InstancePtr)
*
*****************************************************************************/
#define XIicPs_RecvByte(InstancePtr)					\
{									\
	*(InstancePtr)->RecvBufferPtr ++ =				\
	 (u8)XIicPs_In32((InstancePtr)->Config.BaseAddress		\
		  + XIICPS_DATA_OFFSET); 				\
	 (InstancePtr)->RecvByteCount --; 				\
}

/************************** Function Prototypes ******************************/

/*
 * Function for configuration lookup, in xiicps_sinit.c
 */
XIicPs_Config *XIicPs_LookupConfig(u16 DeviceId);

/*
 * Functions for general setup, in xiicps.c
 */
int XIicPs_CfgInitialize(XIicPs *InstancePtr, XIicPs_Config * Config,
				  u32 EffectiveAddr);

void XIicPs_Abort(XIicPs *InstancePtr);
void XIicPs_Reset(XIicPs *InstancePtr);

int XIicPs_BusIsBusy(XIicPs *InstancePtr);

/*
 * Functions for interrupts, in xiicps_intr.c
 */
void XIicPs_SetStatusHandler(XIicPs *InstancePtr, void *CallBackRef,
				  XIicPs_IntrHandler FuncPtr);

/*
 * Functions for device as master, in xiicps_master.c
 */
void XIicPs_MasterSend(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount,
		u16 SlaveAddr);
void XIicPs_MasterRecv(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount,
		u16 SlaveAddr);
int XIicPs_MasterSendPolled(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount,
		u16 SlaveAddr);
int XIicPs_MasterRecvPolled(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount,
		u16 SlaveAddr);
void XIicPs_EnableSlaveMonitor(XIicPs *InstancePtr, u16 SlaveAddr);
void XIicPs_DisableSlaveMonitor(XIicPs *InstancePtr);
void XIicPs_MasterInterruptHandler(XIicPs *InstancePtr);

/*
 * Functions for device as slave, in xiicps_slave.c
 */
void XIicPs_SetupSlave(XIicPs *InstancePtr, u16 SlaveAddr);
void XIicPs_SlaveSend(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount);
void XIicPs_SlaveRecv(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount);
int XIicPs_SlaveSendPolled(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount);
int XIicPs_SlaveRecvPolled(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount);
void XIicPs_SlaveInterruptHandler(XIicPs *InstancePtr);

/*
 * Functions for selftest, in xiicps_selftest.c
 */
int XIicPs_SelfTest(XIicPs *InstancePtr);

/*
 * Functions for setting and getting data rate, in xiicps_options.c
 */
int XIicPs_SetOptions(XIicPs *InstancePtr, u32 Options);
int XIicPs_ClearOptions(XIicPs *InstancePtr, u32 Options);
u32 XIicPs_GetOptions(XIicPs *InstancePtr);

int XIicPs_SetSClk(XIicPs *InstancePtr, u32 FsclHz);
u32 XIicPs_GetSClk(XIicPs *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */

