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
* @file xiicps_master.c
*
* Handles master mode transfers.
*
* <pre> MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---  -------- ---------------------------------------------
* 1.00a jz   01/30/10 First release
* 1.00a sdm  09/21/11 Updated the XIicPs_SetupMaster to not check for
*		      Bus Busy condition when the Hold Bit is set.
* 1.01a sg   03/30/12 Fixed an issue in XIicPs_MasterSendPolled where a
*		      check for transfer completion is added, which indicates
*			 the completion of current transfer.
* 2.0   hk   03/07/14 Added check for error status in the while loop that
*                     checks for completion. CR# 762244, 764875.
* 2.1   hk   04/24/14 Fix for CR# 789821 to handle >14 byte transfers.
*                     Fix for CR# 761060 - provision for repeated start.
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
int TransmitFifoFill(XIicPs *InstancePtr);

static int XIicPs_SetupMaster(XIicPs *InstancePtr, int Role);
static void MasterSendData(XIicPs *InstancePtr);

/************************* Variable Definitions *****************************/

/*****************************************************************************/
/**
* This function initiates an interrupt-driven send in master mode.
*
* It tries to send the first FIFO-full of data, then lets the interrupt
* handler to handle the rest of the data if there is any.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the send buffer.
* @param	ByteCount is the number of bytes to be sent.
* @param	SlaveAddr is the address of the slave we are sending to.
*
* @return	None.
*
* @note		This send routine is for interrupt-driven transfer only.
*
 ****************************************************************************/
void XIicPs_MasterSend(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount,
		 u16 SlaveAddr)
{
	u32 BaseAddr;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(MsgPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(XIICPS_ADDR_MASK >= SlaveAddr);


	BaseAddr = InstancePtr->Config.BaseAddress;
	InstancePtr->SendBufferPtr = MsgPtr;
	InstancePtr->SendByteCount = ByteCount;
	InstancePtr->RecvBufferPtr = NULL;
	InstancePtr->IsSend = 1;

	/*
	 * Set repeated start if sending more than FIFO of data.
	 */
	if ((InstancePtr->IsRepeatedStart) ||
		(ByteCount > XIICPS_FIFO_DEPTH)) {
		XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
			XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET) |
				XIICPS_CR_HOLD_MASK);
	}

	/*
	 * Setup as a master sending role.
	 */
	XIicPs_SetupMaster(InstancePtr, SENDING_ROLE);

	/*
	 * Do the address transfer to notify the slave.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_ADDR_OFFSET, SlaveAddr);

	TransmitFifoFill(InstancePtr);

	XIicPs_EnableInterrupts(BaseAddr,
		XIICPS_IXR_NACK_MASK | XIICPS_IXR_COMP_MASK |
		XIICPS_IXR_ARB_LOST_MASK);
}

/*****************************************************************************/
/**
* This function initiates an interrupt-driven receive in master mode.
*
* It sets the transfer size register so the slave can send data to us.
* The rest of the work is managed by interrupt handler.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the receive buffer.
* @param	ByteCount is the number of bytes to be received.
* @param	SlaveAddr is the address of the slave we are receiving from.
*
* @return	None.
*
* @note		This receive routine is for interrupt-driven transfer only.
*
****************************************************************************/
void XIicPs_MasterRecv(XIicPs *InstancePtr, u8 *MsgPtr, int ByteCount,
		 u16 SlaveAddr)
{
	u32 BaseAddr;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(MsgPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(XIICPS_ADDR_MASK >= SlaveAddr);

	BaseAddr = InstancePtr->Config.BaseAddress;
	InstancePtr->RecvBufferPtr = MsgPtr;
	InstancePtr->RecvByteCount = ByteCount;
	InstancePtr->CurrByteCount = ByteCount;
	InstancePtr->SendBufferPtr = NULL;
	InstancePtr->IsSend = 0;
	InstancePtr->UpdateTxSize = 0;

	if ((ByteCount > XIICPS_DATA_INTR_DEPTH) ||
		(InstancePtr->IsRepeatedStart))
	{
		XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
				XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET) |
						XIICPS_CR_HOLD_MASK);
	}

	/*
	 * Initialize for a master receiving role.
	 */
	XIicPs_SetupMaster(InstancePtr, RECVING_ROLE);

	/*
	 * Do the address transfer to signal the slave.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_ADDR_OFFSET, SlaveAddr);

	/*
	 * Setup the transfer size register so the slave knows how much
	 * to send to us.
	 */
	if (ByteCount > XIICPS_MAX_TRANSFER_SIZE) {
		XIicPs_WriteReg(BaseAddr, XIICPS_TRANS_SIZE_OFFSET,
				XIICPS_MAX_TRANSFER_SIZE);
		InstancePtr->CurrByteCount = XIICPS_MAX_TRANSFER_SIZE;
		InstancePtr->UpdateTxSize = 1;
	}else {
		XIicPs_WriteReg(BaseAddr, XIICPS_TRANS_SIZE_OFFSET,
			 ByteCount);
	}

	XIicPs_EnableInterrupts(BaseAddr,
		XIICPS_IXR_NACK_MASK | XIICPS_IXR_DATA_MASK |
		XIICPS_IXR_RX_OVR_MASK | XIICPS_IXR_COMP_MASK |
		XIICPS_IXR_ARB_LOST_MASK);
}

/*****************************************************************************/
/**
* This function initiates a polled mode send in master mode.
*
* It sends data to the FIFO and waits for the slave to pick them up.
* If slave fails to remove data from FIFO, the send fails with
* time out.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the send buffer.
* @param	ByteCount is the number of bytes to be sent.
* @param	SlaveAddr is the address of the slave we are sending to.
*
* @return
*		- XST_SUCCESS if everything went well.
*		- XST_FAILURE if timed out.
*
* @note		This send routine is for polled mode transfer only.
*
****************************************************************************/
int XIicPs_MasterSendPolled(XIicPs *InstancePtr, u8 *MsgPtr,
		 int ByteCount, u16 SlaveAddr)
{
	u32 IntrStatusReg;
	u32 StatusReg;
	u32 BaseAddr;
	u32 Intrs;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(MsgPtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(XIICPS_ADDR_MASK >= SlaveAddr);

	BaseAddr = InstancePtr->Config.BaseAddress;
	InstancePtr->SendBufferPtr = MsgPtr;
	InstancePtr->SendByteCount = ByteCount;

	if ((InstancePtr->IsRepeatedStart) ||
		(ByteCount > XIICPS_FIFO_DEPTH)) {
		XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
				XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET) |
						XIICPS_CR_HOLD_MASK);
	}

	XIicPs_SetupMaster(InstancePtr, SENDING_ROLE);

	XIicPs_WriteReg(BaseAddr, XIICPS_ADDR_OFFSET, SlaveAddr);

	/*
	 * Intrs keeps all the error-related interrupts.
	 */
	Intrs = XIICPS_IXR_ARB_LOST_MASK | XIICPS_IXR_TX_OVR_MASK |
		XIICPS_IXR_NACK_MASK;

	/*
	 * Clear the interrupt status register before use it to monitor.
	 */
	IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);
	XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET, IntrStatusReg);

	/*
	 * Transmit first FIFO full of data.
	 */
	TransmitFifoFill(InstancePtr);

	IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);

	/*
	 * Continue sending as long as there is more data and
	 * there are no errors.
	 */
	while ((InstancePtr->SendByteCount > 0) &&
		((IntrStatusReg & Intrs) == 0)) {
		StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);

		/*
		 * Wait until transmit FIFO is empty.
		 */
		if ((StatusReg & XIICPS_SR_TXDV_MASK) != 0) {
			IntrStatusReg = XIicPs_ReadReg(BaseAddr,
					XIICPS_ISR_OFFSET);
			continue;
		}

		/*
		 * Send more data out through transmit FIFO.
		 */
		TransmitFifoFill(InstancePtr);
	}

	/*
	 * Check for completion of transfer.
	 */
	while ((IntrStatusReg & XIICPS_IXR_COMP_MASK) != XIICPS_IXR_COMP_MASK){

		IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);
		/*
		 * If there is an error, tell the caller.
		 */
		if ((IntrStatusReg & Intrs) != 0) {
			return XST_FAILURE;
		}
	}

	if (!(InstancePtr->IsRepeatedStart)) {
		XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
				XIicPs_ReadReg(BaseAddr,XIICPS_CR_OFFSET) &
						(~XIICPS_CR_HOLD_MASK));
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* This function initiates a polled mode receive in master mode.
*
* It repeatedly sets the transfer size register so the slave can
* send data to us. It polls the data register for data to come in.
* If slave fails to send us data, it fails with time out.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	MsgPtr is the pointer to the receive buffer.
* @param	ByteCount is the number of bytes to be received.
* @param	SlaveAddr is the address of the slave we are receiving from.
*
* @return
*		- XST_SUCCESS if everything went well.
*		- XST_FAILURE if timed out.
*
* @note		This receive routine is for polled mode transfer only.
*
****************************************************************************/
int XIicPs_MasterRecvPolled(XIicPs *InstancePtr, u8 *MsgPtr,
				int ByteCount, u16 SlaveAddr)
{
	u32 IntrStatusReg;
	u32 Intrs;
	u32 StatusReg;
	u32 BaseAddr;
	int IsHold = 0;
	int UpdateTxSize = 0;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(MsgPtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(XIICPS_ADDR_MASK >= SlaveAddr);

	BaseAddr = InstancePtr->Config.BaseAddress;
	InstancePtr->RecvBufferPtr = MsgPtr;
	InstancePtr->RecvByteCount = ByteCount;

	if((ByteCount > XIICPS_DATA_INTR_DEPTH) ||
		(InstancePtr->IsRepeatedStart))
	{
		XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
				XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET) |
						XIICPS_CR_HOLD_MASK);
		IsHold = 1;
	}

	XIicPs_SetupMaster(InstancePtr, RECVING_ROLE);

	/*
	 * Clear the interrupt status register before use it to monitor.
	 */
	IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);
	XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET, IntrStatusReg);

	XIicPs_WriteReg(BaseAddr, XIICPS_ADDR_OFFSET, SlaveAddr);

	/*
	 * Set up the transfer size register so the slave knows how much
	 * to send to us.
	 */
	if (ByteCount > XIICPS_MAX_TRANSFER_SIZE) {
		XIicPs_WriteReg(BaseAddr, XIICPS_TRANS_SIZE_OFFSET,
				XIICPS_MAX_TRANSFER_SIZE);
		ByteCount = XIICPS_MAX_TRANSFER_SIZE;
		UpdateTxSize = 1;
	}else {
		XIicPs_WriteReg(BaseAddr, XIICPS_TRANS_SIZE_OFFSET,
			 ByteCount);
	}

	/*
	 * Intrs keeps all the error-related interrupts.
	 */
	Intrs = XIICPS_IXR_ARB_LOST_MASK | XIICPS_IXR_RX_OVR_MASK |
			XIICPS_IXR_RX_UNF_MASK | XIICPS_IXR_NACK_MASK;

	/*
	 * Poll the interrupt status register to find the errors.
	 */
	IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);
	while ((InstancePtr->RecvByteCount > 0) &&
			((IntrStatusReg & Intrs) == 0)) {
		StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);

		while (StatusReg & XIICPS_SR_RXDV_MASK) {
			if ((InstancePtr->RecvByteCount <
				XIICPS_DATA_INTR_DEPTH) && IsHold &&
				(!(InstancePtr->IsRepeatedStart))) {
				IsHold = 0;
				XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
						XIicPs_ReadReg(BaseAddr,
						XIICPS_CR_OFFSET) &
						(~XIICPS_CR_HOLD_MASK));
			}
			XIicPs_RecvByte(InstancePtr);
			ByteCount --;

			if (UpdateTxSize &&
				(ByteCount == XIICPS_FIFO_DEPTH + 1))
				break;

			StatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET);
		}

		if (UpdateTxSize && (ByteCount == XIICPS_FIFO_DEPTH + 1)) {
			/*
			 * wait while fifo is full
			 */
			while(XIicPs_ReadReg(BaseAddr,
				XIICPS_TRANS_SIZE_OFFSET) !=
				(ByteCount - XIICPS_FIFO_DEPTH));

			if ((InstancePtr->RecvByteCount - XIICPS_FIFO_DEPTH) >
				XIICPS_MAX_TRANSFER_SIZE) {

				XIicPs_WriteReg(BaseAddr,
					XIICPS_TRANS_SIZE_OFFSET,
					XIICPS_MAX_TRANSFER_SIZE);
				ByteCount = XIICPS_MAX_TRANSFER_SIZE +
						XIICPS_FIFO_DEPTH;
			}else {
				XIicPs_WriteReg(BaseAddr,
					XIICPS_TRANS_SIZE_OFFSET,
					InstancePtr->RecvByteCount -
					XIICPS_FIFO_DEPTH);
				UpdateTxSize = 0;
				ByteCount = InstancePtr->RecvByteCount;
			}
		}

		IntrStatusReg = XIicPs_ReadReg(BaseAddr, XIICPS_ISR_OFFSET);
	}

	if (!(InstancePtr->IsRepeatedStart)) {
		XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
				XIicPs_ReadReg(BaseAddr,XIICPS_CR_OFFSET) &
						(~XIICPS_CR_HOLD_MASK));
	}

	if (IntrStatusReg & Intrs) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* This function enables the slave monitor mode.
*
* It enables slave monitor in the control register and enables
* slave ready interrupt. It then does an address transfer to slave.
* Interrupt handler will signal the caller if slave responds to
* the address transfer.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	SlaveAddr is the address of the slave we want to contact.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XIicPs_EnableSlaveMonitor(XIicPs *InstancePtr, u16 SlaveAddr)
{
	u32 BaseAddr;

	Xil_AssertVoid(InstancePtr != NULL);

	BaseAddr = InstancePtr->Config.BaseAddress;

	/*
	 * Enable slave monitor mode in control register.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
	XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET) |
				XIICPS_CR_MS_MASK |
				XIICPS_CR_NEA_MASK |
				XIICPS_CR_SLVMON_MASK );

	/*
	 * Set up interrupt flag for slave monitor interrupt.
	 */
	XIicPs_EnableInterrupts(BaseAddr, XIICPS_IXR_NACK_MASK |
				XIICPS_IXR_SLV_RDY_MASK);

	/*
	 * Initialize the slave monitor register.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_SLV_PAUSE_OFFSET, 0xF);

	/*
	 * Set the slave address to start the slave address transmission.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_ADDR_OFFSET, SlaveAddr);

	return;
}

/*****************************************************************************/
/**
* This function disables slave monitor mode.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XIicPs_DisableSlaveMonitor(XIicPs *InstancePtr)
{
	u32 BaseAddr;

	Xil_AssertVoid(InstancePtr != NULL);

	BaseAddr = InstancePtr->Config.BaseAddress;

	/*
	 * Clear slave monitor control bit.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
		XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET)
			& (~XIICPS_CR_SLVMON_MASK));

	/*
	 * Clear interrupt flag for slave monitor interrupt.
	 */
	XIicPs_DisableInterrupts(BaseAddr, XIICPS_IXR_SLV_RDY_MASK);

	return;
}

/*****************************************************************************/
/**
* The interrupt handler for the master mode. It does the protocol handling for
* the interrupt-driven transfers.
*
* Completion events and errors are signaled to upper layer for proper handling.
*
* <pre>
* The interrupts that are handled are:
* - DATA
*	This case is handled only for master receive data.
*	The master has to request for more data (if there is more data to
*	receive) and read the data from the FIFO .
*
* - COMP
*	If the Master is transmitting data and there is more data to be
*	sent then the data is written to the FIFO. If there is no more data to
*	be transmitted then a completion event is signalled to the upper layer
*	by calling the callback handler.
*
*	If the Master is receiving data then the data is read from the FIFO and
*	the Master has to request for more data (if there is more data to
*	receive). If all the data has been received then a completion event
*	is signalled to the upper layer by calling the callback handler.
*	It is an error if the amount of received data is more than expected.
*
* - NAK and SLAVE_RDY
*	This is signalled to the upper layer by calling the callback handler.
*
* - All Other interrupts
*	These interrupts are marked as error. This is signalled to the upper
*	layer by calling the callback handler.
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
void XIicPs_MasterInterruptHandler(XIicPs *InstancePtr)
{
	u32 IntrStatusReg;
	u32 StatusEvent = 0;
	u32 BaseAddr;
	int ByteCnt;
	int IsHold;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	BaseAddr = InstancePtr->Config.BaseAddress;

	/*
	 * Read the Interrupt status register.
	 */
	IntrStatusReg = XIicPs_ReadReg(BaseAddr,
					 XIICPS_ISR_OFFSET);

	/*
	 * Write the status back to clear the interrupts so no events are
	 * missed while processing this interrupt.
	 */
	XIicPs_WriteReg(BaseAddr, XIICPS_ISR_OFFSET, IntrStatusReg);

	/*
	 * Use the Mask register AND with the Interrupt Status register so
	 * disabled interrupts are not processed.
	 */
	IntrStatusReg &= ~(XIicPs_ReadReg(BaseAddr, XIICPS_IMR_OFFSET));

	ByteCnt = InstancePtr->CurrByteCount;

	IsHold = 0;
	if (XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET) & XIICPS_CR_HOLD_MASK) {
		IsHold = 1;
	}

	/*
	 * Send
	 */
	if ((InstancePtr->IsSend) &&
		(0 != (IntrStatusReg & XIICPS_IXR_COMP_MASK))) {
		if (InstancePtr->SendByteCount > 0) {
			MasterSendData(InstancePtr);
		} else {
			StatusEvent |= XIICPS_EVENT_COMPLETE_SEND;
		}
	}


	/*
	 * Receive
	 */
	if ((!(InstancePtr->IsSend)) &&
		((0 != (IntrStatusReg & XIICPS_IXR_DATA_MASK)) ||
		(0 != (IntrStatusReg & XIICPS_IXR_COMP_MASK)))){

		while (XIicPs_ReadReg(BaseAddr, XIICPS_SR_OFFSET) &
				XIICPS_SR_RXDV_MASK) {
			if ((InstancePtr->RecvByteCount <
				XIICPS_DATA_INTR_DEPTH) && IsHold &&
				(!(InstancePtr->IsRepeatedStart))) {
				IsHold = 0;
				XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
						XIicPs_ReadReg(BaseAddr,
						XIICPS_CR_OFFSET) &
						(~XIICPS_CR_HOLD_MASK));
			}
			XIicPs_RecvByte(InstancePtr);
			ByteCnt--;

			if (InstancePtr->UpdateTxSize &&
				(ByteCnt == XIICPS_FIFO_DEPTH + 1))
				break;
		}

		if (InstancePtr->UpdateTxSize &&
			(ByteCnt == XIICPS_FIFO_DEPTH + 1)) {
			/*
			 * wait while fifo is full
			 */
			while(XIicPs_ReadReg(BaseAddr,
				XIICPS_TRANS_SIZE_OFFSET) !=
				(ByteCnt - XIICPS_FIFO_DEPTH));

			if ((InstancePtr->RecvByteCount - XIICPS_FIFO_DEPTH) >
				XIICPS_MAX_TRANSFER_SIZE) {

				XIicPs_WriteReg(BaseAddr,
					XIICPS_TRANS_SIZE_OFFSET,
					XIICPS_MAX_TRANSFER_SIZE);
				ByteCnt = XIICPS_MAX_TRANSFER_SIZE +
						XIICPS_FIFO_DEPTH;
			}else {
				XIicPs_WriteReg(BaseAddr,
					XIICPS_TRANS_SIZE_OFFSET,
					InstancePtr->RecvByteCount -
					XIICPS_FIFO_DEPTH);
				InstancePtr->UpdateTxSize = 0;
				ByteCnt = InstancePtr->RecvByteCount;
			}
		}
		InstancePtr->CurrByteCount = ByteCnt;
	}

	if ((!(InstancePtr->IsSend)) &&
		(0 != (IntrStatusReg & XIICPS_IXR_COMP_MASK))) {
		/*
		 * If all done, tell the application.
		 */
		if (InstancePtr->RecvByteCount == 0){
			if (!(InstancePtr->IsRepeatedStart)) {
				XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
						XIicPs_ReadReg(BaseAddr,
						XIICPS_CR_OFFSET) &
						(~XIICPS_CR_HOLD_MASK));
			}
			StatusEvent |= XIICPS_EVENT_COMPLETE_RECV;
		}
	}


	/*
	 * Slave ready interrupt, it is only meaningful for master mode.
	 */
	if (0 != (IntrStatusReg & XIICPS_IXR_SLV_RDY_MASK)) {
		StatusEvent |= XIICPS_EVENT_SLAVE_RDY;
	}

	if (0 != (IntrStatusReg & XIICPS_IXR_NACK_MASK)) {
		if (!(InstancePtr->IsRepeatedStart)) {
			XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
					XIicPs_ReadReg(BaseAddr,
					XIICPS_CR_OFFSET) &
					(~XIICPS_CR_HOLD_MASK));
		}
		StatusEvent |= XIICPS_EVENT_NACK;
	}

	/*
	 * All other interrupts are treated as error.
	 */
	if (0 != (IntrStatusReg & (XIICPS_IXR_NACK_MASK |
			XIICPS_IXR_ARB_LOST_MASK | XIICPS_IXR_RX_UNF_MASK |
			XIICPS_IXR_TX_OVR_MASK | XIICPS_IXR_RX_OVR_MASK))) {
		if (!(InstancePtr->IsRepeatedStart)) {
			XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET,
					XIicPs_ReadReg(BaseAddr,
					XIICPS_CR_OFFSET) &
					(~XIICPS_CR_HOLD_MASK));
		}
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
* This function prepares a device to transfers as a master.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @param	Role specifies whether the device is sending or receiving.
*
* @return
*		- XST_SUCCESS if everything went well.
*		- XST_FAILURE if bus is busy.
*
* @note		Interrupts are always disabled, device which needs to use
*		interrupts needs to setup interrupts after this call.
*
****************************************************************************/
static int XIicPs_SetupMaster(XIicPs *InstancePtr, int Role)
{
	u32 ControlReg;
	u32 BaseAddr;
	u32 EnabledIntr = 0x0;

	Xil_AssertNonvoid(InstancePtr != NULL);

	BaseAddr = InstancePtr->Config.BaseAddress;
	ControlReg = XIicPs_ReadReg(BaseAddr, XIICPS_CR_OFFSET);


	/*
	 * Only check if bus is busy when repeated start option is not set.
	 */
	if ((ControlReg & XIICPS_CR_HOLD_MASK) == 0) {
		if (XIicPs_BusIsBusy(InstancePtr)) {
			return XST_FAILURE;
		}
	}

	/*
	 * Set up master, AckEn, nea and also clear fifo.
	 */
	ControlReg |= XIICPS_CR_ACKEN_MASK | XIICPS_CR_CLR_FIFO_MASK |
		 	XIICPS_CR_NEA_MASK | XIICPS_CR_MS_MASK;

	if (Role == RECVING_ROLE) {
		ControlReg |= XIICPS_CR_RD_WR_MASK;
		EnabledIntr = XIICPS_IXR_DATA_MASK |XIICPS_IXR_RX_OVR_MASK;
	}else {
		ControlReg &= ~XIICPS_CR_RD_WR_MASK;
	}
	EnabledIntr |= XIICPS_IXR_COMP_MASK | XIICPS_IXR_ARB_LOST_MASK;

	XIicPs_WriteReg(BaseAddr, XIICPS_CR_OFFSET, ControlReg);

	XIicPs_DisableAllInterrupts(BaseAddr);

	return XST_SUCCESS;
}

/*****************************************************************************/
/*
* This function handles continuation of sending data. It is invoked
* from interrupt handler.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
static void MasterSendData(XIicPs *InstancePtr)
{
	TransmitFifoFill(InstancePtr);

	/*
	 * Clear hold bit if done, so stop can be sent out.
	 */
	if (InstancePtr->SendByteCount == 0) {

		/*
		 * If user has enabled repeated start as an option,
		 * do not disable it.
		 */
		if (!(InstancePtr->IsRepeatedStart)) {

			XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
				XIICPS_CR_OFFSET,
				XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				XIICPS_CR_OFFSET) & ~ XIICPS_CR_HOLD_MASK);
		}
	}

	return;
}



