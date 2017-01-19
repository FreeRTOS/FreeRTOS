/******************************************************************************
*
* Copyright (C) 2015 - 2016 Xilinx, Inc.  All rights reserved.
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
 * @file xipipsu.h
* @addtogroup ipipsu_v1_0
* @{
* @details
 *
 * This is the header file for implementation of IPIPSU driver.
 * Inter Processor Interrupt (IPI) is used for communication between
 * different processors on ZynqMP SoC. Each IPI register set has Trigger, Status
 * and Observation registers for communication between processors. Each IPI path
 * has a 32 byte buffer associated with it and these buffers are located in the
 * XPPU RAM. This driver supports the following operations:
 *
 * - Trigger IPIs to CPUs on the SoC
 * - Write and Read Message buffers
 * - Read the status of Observation Register to get status of Triggered IPI
 * - Enable/Disable IPIs from selected Masters
 * - Read the Status register to get the source of an incoming IPI
 *
 * <b>Initialization</b>
 * The config data for the driver is loaded and is based on the HW build. The
 * XIpiPsu_Config data structure contains all the data related to the
 * IPI driver instance and also teh available Target CPUs.
 *
 * <b>Sending an IPI</b>
 * The following steps can be followed to send an IPI:
 * - Write the Message into Message Buffer using XIpiPsu_WriteMessage()
 * - Trigger IPI using XIpiPsu_TriggerIpi()
 * - Wait for Ack using XIpiPsu_PollForAck()
 * - Read response using XIpiPsu_ReadMessage()
 *
 * @note	XIpiPsu_GetObsStatus() before sending an IPI to ensure that the
 * previous IPI was serviced by the target
 *
 * <b>Receiving an IPI</b>
 * To receive an IPI, the following sequence can be followed:
 * - Register an interrupt handler for the IPIs interrupt ID
 * - Enable the required sources using XIpiPsu_InterruptEnable()
 * - In the interrupt handler, Check for source using XIpiPsu_GetInterruptStatus
 * - Read the message form source using XIpiPsu_ReadMessage()
 * - Write the response using XIpiPsu_WriteMessage()
 * - Ack the IPI using XIpiPsu_ClearInterruptStatus()
 *
 * @note	XIpiPsu_Reset can be used at startup to clear the status and
 * disable all sources
 *
 */
/*****************************************************************************/
#ifndef XIPIPSU_H_
#define XIPIPSU_H_


/***************************** Include Files *********************************/
#include "xil_io.h"
#include "xstatus.h"
#include "xipipsu_hw.h"

/************************** Constant Definitions *****************************/
#define XIPIPSU_BUF_TYPE_MSG	(0x00000001U)
#define XIPIPSU_BUF_TYPE_RESP	(0x00000002U)
#define XIPIPSU_MAX_MSG_LEN		XIPIPSU_MSG_BUF_SIZE
/**************************** Type Definitions *******************************/
/**
 * Data structure used to refer IPI Targets
 */
typedef struct {
	u32 Mask; /**< Bit Mask for the target */
	u32 BufferIndex; /**< Buffer Index used for calculating buffer address */
} XIpiPsu_Target;

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u32 DeviceId; /**< Unique ID  of device */
	u32 BaseAddress; /**< Base address of the device */
	u32 BitMask; /**< BitMask to be used to identify this CPU */
	u32 BufferIndex; /**< Index of the IPI Message Buffer */
	u32 IntId; /**< Interrupt ID on GIC **/
	u32 TargetCount; /**< Number of available IPI Targets */
	XIpiPsu_Target TargetList[XIPIPSU_MAX_TARGETS] ; /** < List of IPI Targets */
} XIpiPsu_Config;

/**
 * The XIpiPsu driver instance data. The user is required to allocate a
 * variable of this type for each IPI device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XIpiPsu_Config Config; /**< Configuration structure */
	u32 IsReady; /**< Device is initialized and ready */
	u32 Options; /**< Options set in the device */
} XIpiPsu;

/***************** Macros (Inline Functions) Definitions *********************/
/**
*
* Read the register specified by the base address and offset
*
* @param	BaseAddress is the base address of the IPI instance
* @param	RegOffset is the offset of the register relative to base
*
* @return	Value of the specified register
* @note
* C-style signature
*	u32 XIpiPsu_ReadReg(u32 BaseAddress, u32 RegOffset)
*
*****************************************************************************/

#define XIpiPsu_ReadReg(BaseAddress, RegOffset) \
		Xil_In32((BaseAddress) + (RegOffset))

/****************************************************************************/
/**
*
* Write a value into a register specified by base address and offset
*
* @param BaseAddress is the base address of the IPI instance
* @param RegOffset is the offset of the register relative to base
* @param Data is a 32-bit value that is to be written into the specified register
*
* @note
* C-style signature
*	void XIpiPsu_WriteReg(u32 BaseAddress, u32 RegOffset, u32 Data)
*
*****************************************************************************/

#define XIpiPsu_WriteReg(BaseAddress, RegOffset, Data) \
		Xil_Out32(((BaseAddress) + (RegOffset)), (Data))

/****************************************************************************/
/**
*
* Enable interrupts specified in <i>Mask</i>. The corresponding interrupt for
* each bit set to 1 in <i>Mask</i>, will be enabled.
*
* @param	InstancePtr is a pointer to the instance to be worked on.
* @param	Mask contains a bit mask of interrupts to enable. The mask can
*			be formed using a set of bitwise or'd values of individual CPU masks
*
* @note
* C-style signature
*	void XIpiPsu_InterruptEnable(XIpiPsu *InstancePtr, u32 Mask)
*
*****************************************************************************/
#define XIpiPsu_InterruptEnable(InstancePtr, Mask) \
	XIpiPsu_WriteReg((InstancePtr)->Config.BaseAddress, \
		XIPIPSU_IER_OFFSET, \
		((Mask) & XIPIPSU_ALL_MASK));

/****************************************************************************/
/**
*
* Disable interrupts specified in <i>Mask</i>. The corresponding interrupt for
* each bit set to 1 in <i>Mask</i>, will be disabled.
*
* @param	InstancePtr is a pointer to the instance to be worked on.
* @param	Mask contains a bit mask of interrupts to disable. The mask can
*			be formed using a set of bitwise or'd values of individual CPU masks
*
* @note
* C-style signature
*	void XIpiPsu_InterruptDisable(XIpiPsu *InstancePtr, u32 Mask)
*
*****************************************************************************/
#define XIpiPsu_InterruptDisable(InstancePtr, Mask)  \
	XIpiPsu_WriteReg((InstancePtr)->Config.BaseAddress, \
		XIPIPSU_IDR_OFFSET, \
		((Mask) & XIPIPSU_ALL_MASK));
/****************************************************************************/
/**
*
* Get the <i>STATUS REGISTER</i> of the current IPI instance.
*
* @param InstancePtr is a pointer to the instance to be worked on.
* @return Returns the Interrupt Status register(ISR) contents
* @note User needs to parse this 32-bit value to check the source CPU
* C-style signature
*	u32 XIpiPsu_GetInterruptStatus(XIpiPsu *InstancePtr)
*
*****************************************************************************/
#define XIpiPsu_GetInterruptStatus(InstancePtr)  \
	XIpiPsu_ReadReg((InstancePtr)->Config.BaseAddress, \
		XIPIPSU_ISR_OFFSET)
/****************************************************************************/
/**
*
* Clear the <i>STATUS REGISTER</i> of the current IPI instance.
* The corresponding interrupt status for
* each bit set to 1 in <i>Mask</i>, will be cleared
*
* @param InstancePtr is a pointer to the instance to be worked on.
* @param Mask corresponding to the source CPU*
*
* @note This function should be used after handling the IPI.
* Clearing the status will automatically clear the corresponding bit in
* OBSERVATION register of Source CPU
* C-style signature
*	void XIpiPsu_ClearInterruptStatus(XIpiPsu *InstancePtr, u32 Mask)
*
*****************************************************************************/

#define XIpiPsu_ClearInterruptStatus(InstancePtr, Mask)  \
	XIpiPsu_WriteReg((InstancePtr)->Config.BaseAddress, \
		XIPIPSU_ISR_OFFSET, \
		((Mask) & XIPIPSU_ALL_MASK));
/****************************************************************************/
/**
*
* Get the <i>OBSERVATION REGISTER</i> of the current IPI instance.
*
* @param	InstancePtr is a pointer to the instance to be worked on.
* @return	Returns the Observation register(OBS) contents
* @note		User needs to parse this 32-bit value to check the status of
*			individual CPUs
* C-style signature
*	u32 XIpiPsu_GetObsStatus(XIpiPsu *InstancePtr)
*
*****************************************************************************/
#define XIpiPsu_GetObsStatus(InstancePtr)  \
	XIpiPsu_ReadReg((InstancePtr)->Config.BaseAddress, \
		XIPIPSU_OBS_OFFSET)
/****************************************************************************/
/************************** Function Prototypes *****************************/

/* Static lookup function implemented in xipipsu_sinit.c */

XIpiPsu_Config *XIpiPsu_LookupConfig(u32 DeviceId);

/* Interface Functions implemented in xipipsu.c */

XStatus XIpiPsu_CfgInitialize(XIpiPsu *InstancePtr, XIpiPsu_Config * CfgPtr,
		UINTPTR EffectiveAddress);

void XIpiPsu_Reset(XIpiPsu *InstancePtr);

XStatus XIpiPsu_TriggerIpi(XIpiPsu *InstancePtr, u32 DestCpuMask);

XStatus XIpiPsu_PollForAck(XIpiPsu *InstancePtr, u32 DestCpuMask,
		u32 TimeOutCount);

XStatus XIpiPsu_ReadMessage(XIpiPsu *InstancePtr, u32 SrcCpuMask, u32 *MsgPtr,
		u32 MsgLength, u8 BufferType);

XStatus XIpiPsu_WriteMessage(XIpiPsu *InstancePtr, u32 DestCpuMask, u32 *MsgPtr,
		u32 MsgLength, u8 BufferType);

#endif /* XIPIPSU_H_ */
/** @} */
