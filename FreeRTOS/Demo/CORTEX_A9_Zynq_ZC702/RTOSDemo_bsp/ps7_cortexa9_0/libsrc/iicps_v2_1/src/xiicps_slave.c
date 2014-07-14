/******************************************************************************
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
******************************************************************************/
/*****************************************************************************/
/**
* @file xiicps_slave.c
*
* Handles slave transfers
*
* <pre> MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --  -------- ---------------------------------------------
* 1.00a jz  01/30/10 First release
* 1.04a kpc 08/30/13 Avoid buffer overwrite in SlaveRecvData function
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/
#include "xiicps.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/
extern int TransmitFifoFill(XIicPs *InstancePtr);

static int SlaveRecvData(XIicPs *InstancePtr);

/************************* Variable Definitions *****************************/

/*****************************************************************************/
/**
* This function sets up the device to be a slave.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	SlaveAddr is the address of the slave we are receiving from.
*
* @return	None.
*
* @note
*	Interrupt is always enabled no matter the tranfer is interrupt-
*	driven or polled mode. Whether device will be interrupted or not
*	depends on whether the device is connected to an interrupt
*	controller and interrupt for the device is enabled.
*
****************************************************************************/
void XIicPs_SetupSlave(XIicPs *InstancePtr, u16 SlaveAddr)
{
	volatile u32 ControlReg;
	u32 BaseAddr;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(XIICPS_ADDR_MASK >= SlaveAddr);

	BaseAddr = InstancePtr->Config.BaseAddress;

	ControlReg = XIicPs_In32(BaseAddr + XIICPS_CR_OFFSET);

	/*
	 * Set up master, AckEn, nea and also clear fifo.
	 */
	ControlReg |= XIICPS_CR_ACKEN_MASK | XIICPS_CR_CLR_FIFO_MASK;
	ControlReg |= XIICPS_CR_NEA_MASK;
	ControlReg &= ~XIICPS_CR_MS_MASK;

	XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
			  ControlReg);

	XIicPs_DisableAllInterrupts(BaseAddr);

	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_ADDR_OFFSET, SlaveAddr);

	return;
}

/*****************************************************************************/
/**
* This function setup a slave interrupt-driven send. It set the repeated
* start for the device is the tranfer size is larger than FIFO depth.
* Data processing for the send is initiated by the interrupt handler.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the send buffer.
* @param	ByteCount is the number of bytes to be sent.
*
* @return	None.
*
* @note		This send routine is for interrupt-driven transfer only.
*
****************************************************************************/
void XIicPs_SlaveSend(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount)
{
	u32 BaseAddr;

	/*
	 * Assert validates the input arguments
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(MsgPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	BaseAddr = InstancePtr->Config.BaseAddress;
	InstancePtr->SendBufferPtr = MsgPtr;
	InstancePtr->SendByteCount = ByteCount;
	InstancePtr->RecvBufferPtr = NULL;

	XIicPs_EnableInterrupts(BaseAddr,
			XIICPS_IXR_DATA_MASK | XIICPS_IXR_COMP_MASK |
			XIICPS_IXR_TO_MASK | XIICPS_IXR_NACK_MASK |
			XIICPS_IXR_TX_OVR_MASK);
}

/*****************************************************************************/
/**
* This function setup a slave interrupt-driven receive.
* Data processing for the receive is handled by the interrupt handler.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the receive buffer.
* @param	ByteCount is the number of bytes to be received.
*
* @return	None.
*
* @note		This routine is for interrupt-driven transfer only.
*
****************************************************************************/
void XIicPs_SlaveRecv(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount)
{
	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(MsgPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	InstancePtr->RecvBufferPtr = MsgPtr;
	InstancePtr->RecvByteCount = ByteCount;
	InstancePtr->SendBufferPtr = NULL;

	XIicPs_EnableInterrupts(InstancePtr->Config.BaseAddress,
			XIICPS_IXR_DATA_MASK | XIICPS_IXR_COMP_MASK |
			XIICPS_IXR_NACK_MASK | XIICPS_IXR_TO_MASK |
			XIICPS_IXR_RX_OVR_MASK | XIICPS_IXR_RX_UNF_MASK);

}

/*****************************************************************************/
/**
* This function sends  a buffer in polled mode as a slave.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the send buffer.
* @param	ByteCount is the number of bytes to be sent.
*
* @return
*		- XST_SUCCESS if everything went well.
*		- XST_FAILURE if master sends us data or master terminates the
*		transfer before all data has sent out.
*
* @note		This send routine is for polled mode transfer only.
*
****************************************************************************/
int XIicPs_SlaveSendPolled(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount)
{
	volatile u32 IntrStatusReg;
	volatile u32 StatusReg;
	u32 BaseAddr;
	int Tmp;
	int BytesToSend;
	int Error = 0;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(MsgPtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	BaseAddr = InstancePtr->Config.BaseAddress;
	InstancePtr->SendBufferPtr = MsgPtr;
	InstancePtr->SendByteCount = ByteCount;

	/*
	 * Use RXRW bit in status register to wait master to start a read.
	 */
	StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);
	while (((StatusReg & XIICPS_SR_RXRW_MASK) == 0) && (!Error)) {

		/*
		 * If master tries to send us data, it is an error.
		 */
		if (StatusReg & XIICPS_SR_RXDV_MASK) {
			Error = 1;
		}

		StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);
	}

	if (Error) {
		return XST_FAILURE;
	}

	/*
	 * Clear the interrupt status register.
	 */
	IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);
	XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET, IntrStatusReg);

	/*
	 * Send data as long as there is more data to send and
	 * there are no errors.
	 */
	while ((InstancePtr->SendByteCount > 0) && (!Error)){

		/*
		 * Find out how many can be sent.
		 */
		BytesToSend = InstancePtr->SendByteCount;
		if (BytesToSend > XIICPS_FIFO_DEPTH) {
			BytesToSend = XIICPS_FIFO_DEPTH;
		}

		for(Tmp = 0; Tmp < BytesToSend; Tmp ++) {
			XIicPs_SendByte(InstancePtr);
		}

		StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);

		/*
		 * Wait for master to read the data out of fifo.
		 */
		while (((StatusReg & XIICPS_SR_TXDV_MASK) != 0) && (!Error)) {

			/*
			 * If master terminates the transfer before all data is
			 * sent, it is an error.
			 */
			IntrStatusReg = XIicPs_ReadReg(BaseAddr,
			XIICPS_ISR_OFFSET);
			if (IntrStatusReg & XIICPS_IXR_NACK_MASK) {
				Error = 1;
			}

			/* Clear ISR.
			 */
			XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET,
						IntrStatusReg);

			StatusReg = XIicPs_ReadReg(BaseAddr,
					XIICPS_SR_OFFSET);
		}
	}

	if (Error) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}
/*****************************************************************************/
/**
* This function receives a buffer in polled mode as a slave.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the receive buffer.
* @param	ByteCount is the number of bytes to be received.
*
* @return
*		- XST_SUCCESS if everything went well.
*		- XST_FAILURE if timed out.
*
* @note		This receive routine is for polled mode transfer only.
*
****************************************************************************/
int XIicPs_SlaveRecvPolled(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount)
{
	volatile u32 IntrStatusReg;
	volatile u32 StatusReg;
	u32 BaseAddr;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(MsgPtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	BaseAddr = InstancePtr->Config.BaseAddress;
	InstancePtr->RecvBufferPtr = MsgPtr;
	InstancePtr->RecvByteCount = ByteCount;

	StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);

	/*
	 * Clear the interrupt status register.
	 */
	IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);
	XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET, IntrStatusReg);

	/*
	 * Clear the status register.
	 */
	StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);
	XIicPs_WriteReg(BaseAddr, XIICPS_SR_OFFSET, StatusReg);

	StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);
	while (InstancePtr->RecvByteCount > 0) {

		/* Wait for master to put data */
		while ((StatusReg & XIICPS_SR_RXDV_MASK) == 0) {
		    StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);

			/*
			 * If master terminates the transfer before we get all
			 * the data or the master tries to read from us,
		 	 * it is an error.
		 	 */
			IntrStatusReg = XIicPs_ReadReg(BaseAddr,
						XIICPS_ISR_OFFSET);
			if ((IntrStatusReg & (XIICPS_IXR_DATA_MASK |
					XIICPS_IXR_COMP_MASK)) &&
				((StatusReg & XIICPS_SR_RXDV_MASK) == 0) &&
				(InstancePtr->RecvByteCount > 0)) {

				return XST_FAILURE;
			}

			/*
			 * Clear the interrupt status register.
			 */
			XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET,
			IntrStatusReg);
		}

		/*
		 * Read all data from FIFO.
		 */
		while ((StatusReg & XIICPS_SR_RXDV_MASK) &&
			 (InstancePtr->RecvByteCount > 0)){

			XIicPs_RecvByte(InstancePtr);

			StatusReg = XIicPs_ReadReg(BaseAddr,
				XIICPS_SR_OFFSET);
		}
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* The interrupt handler for slave mode. It does the protocol handling for
* the interrupt-driven transfers.
*
* Completion events and errors are signaled to upper layer for proper
* handling.
*
* <pre>
*
* The interrupts that are handled are:
* - DATA
*	If the instance is sending, it means that the master wants to read more
*	data from us. Send more data, and check whether we are done with this
*	send.
*
*	If the instance is receiving, it means that the master has writen
* 	more data to us. Receive more data, and check whether we are done with
*	with this receive.
*
* - COMP
*	This marks that stop sequence has been sent from the master, transfer
*	is about to terminate. However, for receiving, the master may have
*	written us some data, so receive that first.
*
*	It is an error if the amount of transfered data is less than expected.
*
* - NAK
*	This marks that master does not want our data. It is for send only.
*
* - Other interrupts
*	These interrupts are marked as error.
*
* </pre>
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	None.
*
* @note 	None.
*
****************************************************************************/
void XIicPs_SlaveInterruptHandler(XIicPs *InstancePtr)
{
	volatile u32 IntrStatusReg;
	u32 IsSend = 0;
	u32 StatusEvent = 0;
	int LeftOver;
	u32 BaseAddr;

	/*
 	 * Assert validates the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	BaseAddr = InstancePtr->Config.BaseAddress;

	/*
	 * Read the Interrupt status register.
	 */
	IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);

	/*
	 * Write the status back to clear the interrupts so no events are missed
	 * while processing this interrupt.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET, IntrStatusReg);

	/*
	 * Use the Mask register AND with the Interrupt Status register so
	 * disabled interrupts are not processed.
	 */
	IntrStatusReg &= ~(XIicPs_ReadReg(BaseAddr, XIICPS_IMR_OFFSET));

	/*
	 * Determine whether the device is sending.
	 */
	if (InstancePtr->RecvBufferPtr == NULL) {
		IsSend = 1;
	}

	/* Data interrupt
	 *
	 * This means master wants to do more data transfers.
	 * Also check for completion of transfer, signal upper layer if done.
	 */
	if (0 != (IntrStatusReg & XIICPS_IXR_DATA_MASK)) {
		if (IsSend) {
			LeftOver = TransmitFifoFill(InstancePtr);
				/*
				 * We may finish send here
				 */
				if (LeftOver == 0) {
					StatusEvent |=
						XIICPS_EVENT_COMPLETE_SEND;
				}
		} else {
			LeftOver = SlaveRecvData(InstancePtr);

			/* We may finish the receive here */
			if (LeftOver == 0) {
				StatusEvent |= XIICPS_EVENT_COMPLETE_RECV;
			}
		}
	}

	/*
	 * Complete interrupt.
	 *
	 * In slave mode, it means the master has done with this transfer, so
	 * we signal the application using completion event.
	 */
	if (0 != (IntrStatusReg & XIICPS_IXR_COMP_MASK)) {
		if (IsSend) {
			if (InstancePtr->SendByteCount > 0) {
				StatusEvent |= XIICPS_EVENT_ERROR;
			}else {
				StatusEvent |= XIICPS_EVENT_COMPLETE_SEND;
			}
		} else {
			LeftOver = SlaveRecvData(InstancePtr);
			if (LeftOver > 0) {
				StatusEvent |= XIICPS_EVENT_ERROR;
			} else {
				StatusEvent |= XIICPS_EVENT_COMPLETE_RECV;
			}
		}
	}

	/*
	 * Nack interrupt, pass this information to application.
	 */
	if (0 != (IntrStatusReg & XIICPS_IXR_NACK_MASK)) {
		StatusEvent |= XIICPS_EVENT_NACK;
	}

	/*
	 * All other interrupts are treated as error.
	 */
	if (0 != (IntrStatusReg & (XIICPS_IXR_TO_MASK |
			  	XIICPS_IXR_RX_UNF_MASK |
				XIICPS_IXR_TX_OVR_MASK |
				XIICPS_IXR_RX_OVR_MASK))){

		StatusEvent |= XIICPS_EVENT_ERROR;
	}

	/*
	 * Signal application if there are any events.
	 */
	if (0 != StatusEvent) {
		InstancePtr->StatusHandler(InstancePtr->CallBackRef,
					   StatusEvent);
	}
}

/*****************************************************************************/
/*
*
* This function handles continuation of receiving data. It is invoked
* from interrupt handler.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	Number of bytes still expected by the instance.
*
* @note		None.
*
****************************************************************************/
static int SlaveRecvData(XIicPs *InstancePtr)
{
	volatile u32 StatusReg;
	u32 BaseAddr;

	BaseAddr = InstancePtr->Config.BaseAddress;

	StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);

	while ((StatusReg & XIICPS_SR_RXDV_MASK) && 
			(InstancePtr->RecvByteCount > 0)) {
		XIicPs_RecvByte(InstancePtr);
		StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);
	}

	return InstancePtr->RecvByteCount;
}

