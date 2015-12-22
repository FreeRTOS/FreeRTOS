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
* @file xspips.c
*
* Contains implements the interface functions of the XSpiPs driver.
* See xspips.h for a detailed description of the device and driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -----------------------------------------------
* 1.00  drg/jz 01/25/10 First release
* 1.01	sg     03/07/12 Updated the code to always clear the relevant bits
*			before writing to config register.
*			Always clear the slave select bits before write and
*			clear the bits to no slave at the end of transfer
*			Modified the Polled transfer transmit/receive logic.
*			Tx should wait on TXOW Interrupt and Rx on RXNEMTY.
* 1.03	sg     09/21/12 Added memory barrier dmb in polled transfer and
*			interrupt handler to overcome the clock domain
*			crossing issue in the controller. For CR #679252.
* 1.04a	sg     01/30/13 Changed SPI transfer logic for polled and interrupt
*			modes to be based on filled tx fifo count and receive
*			based on it. RXNEMPTY interrupt is not used.
*			SetSlaveSelect API logic is modified to drive the bit
*			position low based on the slave select value
*			requested. GetSlaveSelect API will return the value
*			based on bit position that is low.
* 1.06a hk     08/22/13 Changed GetSlaveSelect function. CR# 727866.
*                       Added masking ConfigReg before writing in SetSlaveSel
*                       Added extended slave select support - CR#722569.
*                       Added check for MODF in polled transfer function.
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xspips.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/*
*
* Send one byte to the currently selected slave. A byte of data is written to
* transmit FIFO/register.
*
* @param	BaseAddress is the  base address of the device
*
* @return	None.
*
* @note		C-Style signature:
*		void XSpiPs_SendByte(u32 BaseAddress, u8 Data);
*
*****************************************************************************/
#define XSpiPs_SendByte(BaseAddress, Data) \
        XSpiPs_Out32((BaseAddress) + (u32)XSPIPS_TXD_OFFSET, (u32)(Data))

/****************************************************************************/
/*
*
* Receive one byte from the device's receive FIFO/register. It is assumed
* that the byte is already available.
*
* @param	BaseAddress is the  base address of the device
*
* @return	The byte retrieved from the receive FIFO/register.
*
* @note		C-Style signature:
*		u8 XSpiPs_RecvByte(u32 BaseAddress);
*
*****************************************************************************/
#define XSpiPs_RecvByte(BaseAddress) \
		XSpiPs_In32((u32)((BaseAddress) + (u32)XSPIPS_RXD_OFFSET))

/************************** Function Prototypes ******************************/

static void StubStatusHandler(void *CallBackRef, u32 StatusEvent,
				u32 ByteCount);

/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Initializes a specific XSpiPs instance such that the driver is ready to use.
*
* The state of the device after initialization is:
*   - Device is disabled
*   - Slave mode
*   - Active high clock polarity
*   - Clock phase 0
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	ConfigPtr is a reference to a structure containing information
*		about a specific SPI device. This function initializes an
*		InstancePtr object for a specific device specified by the
*		contents of Config. This function can initialize multiple
*		instance objects with the use of multiple calls giving different
*		Config information on each call.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. The caller is responsible for keeping the address
*		mapping from EffectiveAddr to the device physical base address
*		unchanged once this function is invoked. Unexpected errors may
*		occur if the address mapping changes after this function is
*		called. If address translation is not used, use
*		ConfigPtr->Config.BaseAddress for this device.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_DEVICE_IS_STARTED if the device is already started.
*		It must be stopped to re-initialize.
*
* @note		None.
*
******************************************************************************/
s32 XSpiPs_CfgInitialize(XSpiPs *InstancePtr, XSpiPs_Config *ConfigPtr,
				u32 EffectiveAddr)
{
	s32 Status;
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * If the device is busy, disallow the initialize and return a status
	 * indicating it is already started. This allows the user to stop the
	 * device and re-initialize, but prevents a user from inadvertently
	 * initializing. This assumes the busy flag is cleared at startup.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		Status = (s32)XST_DEVICE_IS_STARTED;
	} else {

		/*
		 * Set some default values.
		 */
		InstancePtr->IsBusy = FALSE;

		InstancePtr->Config.BaseAddress = EffectiveAddr;
		InstancePtr->StatusHandler = StubStatusHandler;

		InstancePtr->SendBufferPtr = NULL;
		InstancePtr->RecvBufferPtr = NULL;
		InstancePtr->RequestedBytes = 0U;
		InstancePtr->RemainingBytes = 0U;
		InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

		/*
		 * Reset the SPI device to get it into its initial state. It is
		 * expected that device configuration will take place after this
		 * initialization is done, but before the device is started.
		 */
		XSpiPs_Reset(InstancePtr);
		Status = (s32)XST_SUCCESS;
	}

	return Status;
}


/*****************************************************************************/
/**
*
* Resets the SPI device. Reset must only be called after the driver has been
* initialized. The configuration of the device after reset is the same as its
* configuration after initialization.  Any data transfer that is in progress
* is aborted.
*
* The upper layer software is responsible for re-configuring (if necessary)
* and restarting the SPI device after the reset.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XSpiPs_Reset(XSpiPs *InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Abort any transfer that is in progress
	 */
	XSpiPs_Abort(InstancePtr);

        /*
         * Reset any values that are not reset by the hardware reset such that
         * the software state matches the hardware device
         */
        XSpiPs_WriteReg(InstancePtr->Config.BaseAddress, XSPIPS_CR_OFFSET,
                        XSPIPS_CR_RESET_STATE);

}

/*****************************************************************************/
/**
*
* Transfers specified data on the SPI bus. If the SPI device is configured as
* a master, this function initiates bus communication and sends/receives the
* data to/from the selected SPI slave. If the SPI device is configured as a
* slave, this function prepares the buffers to be sent/received when selected
* by a master. For every byte sent, a byte is received. This function should
* be used to perform interrupt based transfers.
*
* The caller has the option of providing two different buffers for send and
* receive, or one buffer for both send and receive, or no buffer for receive.
* The receive buffer must be at least as big as the send buffer to prevent
* unwanted memory writes. This implies that the byte count passed in as an
* argument must be the smaller of the two buffers if they differ in size.
* Here are some sample usages:
* <pre>
*   XSpiPs_Transfer(InstancePtr, SendBuf, RecvBuf, ByteCount)
*	The caller wishes to send and receive, and provides two different
*	buffers for send and receive.
*
*   XSpiPs_Transfer(InstancePtr, SendBuf, NULL, ByteCount)
*	The caller wishes only to send and does not care about the received
*	data. The driver ignores the received data in this case.
*
*   XSpiPs_Transfer(InstancePtr, SendBuf, SendBuf, ByteCount)
*	The caller wishes to send and receive, but provides the same buffer
*	for doing both. The driver sends the data and overwrites the send
*	buffer with received data as it transfers the data.
*
*   XSpiPs_Transfer(InstancePtr, RecvBuf, RecvBuf, ByteCount)
*	The caller wishes to only receive and does not care about sending
*	data.  In this case, the caller must still provide a send buffer, but
*	it can be the same as the receive buffer if the caller does not care
*	what it sends.  The device must send N bytes of data if it wishes to
*	receive N bytes of data.
* </pre>
* Although this function takes entire buffers as arguments, the driver can only
* transfer a limited number of bytes at a time, limited by the size of the
* FIFO. A call to this function only starts the transfer, then subsequent
* transfers of the data is performed by the interrupt service routine until
* the entire buffer has been transferred. The status callback function is
* called when the entire buffer has been sent/received.
*
* This function is non-blocking. As a master, the SetSlaveSelect function must
* be called prior to this function.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	SendBufPtr is a pointer to a buffer of data for sending.
*		This buffer must not be NULL.
* @param	RecvBufPtr is a pointer to a buffer for received data.
*		This argument can be NULL if do not care about receiving.
* @param	ByteCount contains the number of bytes to send/receive.
*		The number of bytes received always equals the number of bytes
*		sent.
*
* @return
*		- XST_SUCCESS if the buffers are successfully handed off to the
*		device for transfer.
*		- XST_DEVICE_BUSY indicates that a data transfer is already in
*		progress. This is determined by the driver.
*
* @note
*
* This function is not thread-safe.  The higher layer software must ensure that
* no two threads are transferring data on the SPI bus at the same time.
*
******************************************************************************/
s32 XSpiPs_Transfer(XSpiPs *InstancePtr, u8 *SendBufPtr,
			u8 *RecvBufPtr, u32 ByteCount)
{
	u32 ConfigReg;
	u8 TransCount = 0U;
	s32 StatusTransfer;

	/*
	 * The RecvBufPtr argument can be null
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(SendBufPtr != NULL);
	Xil_AssertNonvoid(ByteCount > 0U);
	Xil_AssertNonvoid(InstancePtr->IsReady == (u32)XIL_COMPONENT_IS_READY);

	/*
	 * Check whether there is another transfer in progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		StatusTransfer = (s32)XST_DEVICE_BUSY;
	} else {

		/*
		 * Set the busy flag, which will be cleared in the ISR when the
		 * transfer is entirely done.
		 */
		InstancePtr->IsBusy = TRUE;

		/*
		 * Set up buffer pointers.
		 */
		InstancePtr->SendBufferPtr = SendBufPtr;
		InstancePtr->RecvBufferPtr = RecvBufPtr;

		InstancePtr->RequestedBytes = ByteCount;
		InstancePtr->RemainingBytes = ByteCount;

	/*
	 * If manual chip select mode, initialize the slave select value.
	 */
	if (XSpiPs_IsManualChipSelect(InstancePtr) != FALSE) {
		ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET);
		/*
		 * Set the slave select value.
		 */
		ConfigReg &= (u32)(~XSPIPS_CR_SSCTRL_MASK);
		ConfigReg |= InstancePtr->SlaveSelect;
		XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET, ConfigReg);
	}

		/*
		 * Enable the device.
		 */
		XSpiPs_Enable(InstancePtr);

		/*
		 * Clear all the interrrupts.
		 */
		XSpiPs_WriteReg(InstancePtr->Config.BaseAddress, XSPIPS_SR_OFFSET,
				XSPIPS_IXR_WR_TO_CLR_MASK);

		/*
		 * Fill the TXFIFO with as many bytes as it will take (or as many as
		 * we have to send).
		 */
		while ((InstancePtr->RemainingBytes > 0U) &&
			(TransCount < XSPIPS_FIFO_DEPTH)) {
			XSpiPs_SendByte(InstancePtr->Config.BaseAddress,
				  *InstancePtr->SendBufferPtr);
                  InstancePtr->SendBufferPtr += 1;
			InstancePtr->RemainingBytes--;
			TransCount++;
		}

		/*
		 * Enable interrupts (connecting to the interrupt controller and
		 * enabling interrupts should have been done by the caller).
		 */
		XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
				XSPIPS_IER_OFFSET, XSPIPS_IXR_DFLT_MASK);

		/*
		 * If master mode and manual start mode, issue manual start command
		 * to start the transfer.
		 */
	     if ((XSpiPs_IsManualStart(InstancePtr) == TRUE)
		&& (XSpiPs_IsMaster(InstancePtr) == TRUE)) {
			ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
						   XSPIPS_CR_OFFSET);
				ConfigReg |= XSPIPS_CR_MANSTRT_MASK;
			XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET, ConfigReg);
		 }
		StatusTransfer = (s32)XST_SUCCESS;
	}
	return StatusTransfer;
}

/*****************************************************************************/
/**
* Transfers specified data on the SPI bus in polled mode.
*
* The caller has the option of providing two different buffers for send and
* receive, or one buffer for both send and receive, or no buffer for receive.
* The receive buffer must be at least as big as the send buffer to prevent
* unwanted memory writes. This implies that the byte count passed in as an
* argument must be the smaller of the two buffers if they differ in size.
* Here are some sample usages:
* <pre>
*   XSpiPs_PolledTransfer(InstancePtr, SendBuf, RecvBuf, ByteCount)
*	The caller wishes to send and receive, and provides two different
*	buffers for send and receive.
*
*   XSpiPs_PolledTransfer(InstancePtr, SendBuf, NULL, ByteCount)
*	The caller wishes only to send and does not care about the received
*	data. The driver ignores the received data in this case.
*
*   XSpiPs_PolledTransfer(InstancePtr, SendBuf, SendBuf, ByteCount)
*	The caller wishes to send and receive, but provides the same buffer
*	for doing both. The driver sends the data and overwrites the send
*	buffer with received data as it transfers the data.
*
*   XSpiPs_PolledTransfer(InstancePtr, RecvBuf, RecvBuf, ByteCount)
*	The caller wishes to only receive and does not care about sending
*	data.  In this case, the caller must still provide a send buffer, but
*	it can be the same as the receive buffer if the caller does not care
*	what it sends.  The device must send N bytes of data if it wishes to
*	receive N bytes of data.
*
* </pre>
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	SendBufPtr is a pointer to a buffer of data for sending.
*		This buffer must not be NULL.
* @param	RecvBufPtr is a pointer to a buffer for received data.
*		This argument can be NULL if do not care about receiving.
* @param	ByteCount contains the number of bytes to send/receive.
*		The number of bytes received always equals the number of bytes
*		sent.

* @return
*		- XST_SUCCESS if the buffers are successfully handed off to the
*		device for transfer.
*		- XST_DEVICE_BUSY indicates that a data transfer is already in
*		progress. This is determined by the driver.
*
* @note
*
* This function is not thread-safe.  The higher layer software must ensure that
* no two threads are transferring data on the SPI bus at the same time.
*
******************************************************************************/
s32 XSpiPs_PolledTransfer(XSpiPs *InstancePtr, u8 *SendBufPtr,
				u8 *RecvBufPtr, u32 ByteCount)
{
	u32 StatusReg;
	u32 ConfigReg;
	u32 TransCount;
	u32 CheckTransfer;
	s32 Status_Polled;
	u8 TempData;

	/*
	 * The RecvBufPtr argument can be NULL.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(SendBufPtr != NULL);
	Xil_AssertNonvoid(ByteCount > 0U);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check whether there is another transfer in progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		Status_Polled = (s32)XST_DEVICE_BUSY;
	} else {

		/*
		 * Set the busy flag, which will be cleared when the transfer is
		 * entirely done.
		 */
		InstancePtr->IsBusy = TRUE;

		/*
		 * Set up buffer pointers.
		 */
		InstancePtr->SendBufferPtr = SendBufPtr;
		InstancePtr->RecvBufferPtr = RecvBufPtr;

		InstancePtr->RequestedBytes = ByteCount;
		InstancePtr->RemainingBytes = ByteCount;

		/*
		 * If manual chip select mode, initialize the slave select value.
		 */
	     if (XSpiPs_IsManualChipSelect(InstancePtr) == TRUE) {
			ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
						 XSPIPS_CR_OFFSET);
			/*
			 * Set the slave select value.
			 */
			ConfigReg &= (u32)(~XSPIPS_CR_SSCTRL_MASK);
			ConfigReg |= InstancePtr->SlaveSelect;
			XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET, ConfigReg);
		}

		/*
		 * Enable the device.
		 */
		XSpiPs_Enable(InstancePtr);

		while((InstancePtr->RemainingBytes > (u32)0U) ||
			(InstancePtr->RequestedBytes > (u32)0U)) {
			TransCount = 0U;
			/*
			 * Fill the TXFIFO with as many bytes as it will take (or as
			 * many as we have to send).
			 */
			while ((InstancePtr->RemainingBytes > (u32)0U) &&
				((u32)TransCount < (u32)XSPIPS_FIFO_DEPTH)) {
				XSpiPs_SendByte(InstancePtr->Config.BaseAddress,
						*InstancePtr->SendBufferPtr);
				InstancePtr->SendBufferPtr += 1;
				InstancePtr->RemainingBytes--;
				++TransCount;
			}

			/*
			 * If master mode and manual start mode, issue manual start
			 * command to start the transfer.
			 */
			if ((XSpiPs_IsManualStart(InstancePtr) == TRUE)
				&& (XSpiPs_IsMaster(InstancePtr) == TRUE)) {
				ConfigReg = XSpiPs_ReadReg(
						InstancePtr->Config.BaseAddress,
						 XSPIPS_CR_OFFSET);
				ConfigReg |= XSPIPS_CR_MANSTRT_MASK;
				XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
						 XSPIPS_CR_OFFSET, ConfigReg);
			}

			/*
			 * Wait for the transfer to finish by polling Tx fifo status.
			 */
	        CheckTransfer = (u32)0U;
	        while (CheckTransfer == 0U){
			StatusReg = XSpiPs_ReadReg(
					        InstancePtr->Config.BaseAddress,
						        XSPIPS_SR_OFFSET);
				if ( (StatusReg & XSPIPS_IXR_MODF_MASK) != 0U) {
					/*
					 * Clear the mode fail bit
					 */
					XSpiPs_WriteReg(
						InstancePtr->Config.BaseAddress,
						XSPIPS_SR_OFFSET,
						XSPIPS_IXR_MODF_MASK);
					return (s32)XST_SEND_ERROR;
				}
		        CheckTransfer = (StatusReg &
							XSPIPS_IXR_TXOW_MASK);
		    }

			/*
			 * A transmit has just completed. Process received data and
			 * check for more data to transmit.
			 * First get the data received as a result of the transmit
			 * that just completed. Receive data based on the
			 * count obtained while filling tx fifo. Always get the
			 * received data, but only fill the receive buffer if it
			 * points to something (the upper layer software may not
			 * care to receive data).
			 */
			while (TransCount != (u32)0U) {
				TempData = (u8)XSpiPs_RecvByte(
					InstancePtr->Config.BaseAddress);
				if (InstancePtr->RecvBufferPtr != NULL) {
					*(InstancePtr->RecvBufferPtr) = TempData;
					InstancePtr->RecvBufferPtr += 1;
				}
				InstancePtr->RequestedBytes--;
				--TransCount;
			}
		}

		/*
		 * Clear the slave selects now, before terminating the transfer.
		 */
		if (XSpiPs_IsManualChipSelect(InstancePtr) == TRUE) {
			ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
						XSPIPS_CR_OFFSET);
			ConfigReg |= XSPIPS_CR_SSCTRL_MASK;
			XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET, ConfigReg);
		}

		/*
		 * Clear the busy flag.
		 */
		InstancePtr->IsBusy = FALSE;

		/*
		 * Disable the device.
		 */
		XSpiPs_Disable(InstancePtr);
		Status_Polled = (s32)XST_SUCCESS;
	}
	return Status_Polled;
}

/*****************************************************************************/
/**
*
* Selects or deselect the slave with which the master communicates. This setting
* affects the SPI_ss_outN signals. The behavior depends on the setting of the
* CR_SSDECEN bit. If CR_SSDECEN is 0, the SPI_ss_outN bits will be output with a
* single signal low. If CR_SSDECEN is 1, the SPI_ss_outN bits will reflect the
* value set.
*
* The user is not allowed to deselect the slave while a transfer is in progress.
* If no transfer is in progress, the user can select a new slave, which
* implicitly deselects the current slave. In order to explicitly deselect the
* current slave, a value of all 1's, 0x0F can be passed in as the argument to
* the function.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	SlaveSel is the slave number to be selected.
* 		Normally, 3 slaves can be selected with values 0-2.
* 		In case, 3-8 decode option is set, then upto 8 slaves
* 		can be selected. Only one slave can be selected at a time.
*
* @return
*		- XST_SUCCESS if the slave is selected or deselected
*		successfully.
*		- XST_DEVICE_BUSY if a transfer is in progress, slave cannot be
*		changed.
*
* @note
*
* This function only sets the slave which will be selected when a transfer
* occurs. The slave is not selected when the SPI is idle. The slave select
* has no affect when the device is configured as a slave.
*
******************************************************************************/
s32 XSpiPs_SetSlaveSelect(XSpiPs *InstancePtr, u8 SlaveSel)
{
	u32 ConfigReg;
	s32 Status_Slave;
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(SlaveSel <= XSPIPS_CR_SSCTRL_MAXIMUM);

	/*
	 * Do not allow the slave select to change while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		Status_Slave = (s32)XST_DEVICE_BUSY;
	} else {
		/*
		 * If decode slave select option is set,
		 * then set slave select value directly.
		 * Update the Instance structure member.
		 */
		if ( XSpiPs_IsDecodeSSelect( InstancePtr ) == TRUE) {
			InstancePtr->SlaveSelect = ((u32)SlaveSel) << XSPIPS_CR_SSCTRL_SHIFT;
		}
		else {
		/*
		 * Set the bit position to low using SlaveSel. Update the Instance
		 * structure member.
		 */
			InstancePtr->SlaveSelect = ((~(1U << SlaveSel)) & \
				XSPIPS_CR_SSCTRL_MAXIMUM) << XSPIPS_CR_SSCTRL_SHIFT;
		}

		/*
		 * Read the config register, update the slave select value and write
		 * back to config register.
		 */
		ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET);
		ConfigReg &= (u32)(~XSPIPS_CR_SSCTRL_MASK);
		ConfigReg |= InstancePtr->SlaveSelect;
		XSpiPs_WriteReg(InstancePtr->Config.BaseAddress, XSPIPS_CR_OFFSET,
				 ConfigReg);
	    Status_Slave = (s32)XST_SUCCESS;
	}
	return Status_Slave;
}

/*****************************************************************************/
/**
*
* Gets the current slave select setting for the SPI device.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	The slave number selected (starting from 0).
*
* @note		None.
*
******************************************************************************/
u8 XSpiPs_GetSlaveSelect(XSpiPs *InstancePtr)
{
	u32 ConfigReg;
	u32 SlaveSel;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	ConfigReg = InstancePtr->SlaveSelect;
	ConfigReg &= XSPIPS_CR_SSCTRL_MASK;
	ConfigReg >>= XSPIPS_CR_SSCTRL_SHIFT;
	ConfigReg &= XSPIPS_CR_SSCTRL_MAXIMUM;

	/*
	 * If decode slave select option is set, then read value directly.
	 */
	if ( XSpiPs_IsDecodeSSelect( InstancePtr ) == TRUE) {
		SlaveSel = ConfigReg;
	}
	else {

		/*
		 * Get the slave select value
		 */
		if(ConfigReg == 0x0FU) {
			/*
			 * No slave selected
			 */
			SlaveSel = 0xFU;
		}else {
			/*
			 * Get selected slave number (0,1 or 2)
			 */
			SlaveSel = ((~ConfigReg) & XSPIPS_CR_SSCTRL_MAXIMUM)/2;
		}
	}
	return (u8)SlaveSel;
}

/*****************************************************************************/
/**
*
* Sets the status callback function, the status handler, which the driver
* calls when it encounters conditions that should be reported to upper
* layer software. The handler executes in an interrupt context, so it must
* minimize the amount of processing performed. One of the following status
* events is passed to the status handler.
*
* <pre>
* XST_SPI_MODE_FAULT		A mode fault error occurred, meaning the device
*				is selected as slave while being a master.
*
* XST_SPI_TRANSFER_DONE		The requested data transfer is done
*
* XST_SPI_TRANSMIT_UNDERRUN	As a slave device, the master clocked data
*				but there were none available in the transmit
*				register/FIFO. This typically means the slave
*				application did not issue a transfer request
*				fast enough, or the processor/driver could not
*				fill the transmit register/FIFO fast enough.
*
* XST_SPI_RECEIVE_OVERRUN	The SPI device lost data. Data was received
*				but the receive data register/FIFO was full.
*
* XST_SPI_SLAVE_MODE_FAULT	A slave SPI device was selected as a slave
*				while it was disabled. This indicates the
*				master is already transferring data (which is
*				being dropped until the slave application
*				issues a transfer).
* </pre>
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
* @param	FunctionPtr is the pointer to the callback function.
*
* @return	None.
*
* @note
*
* The handler is called within interrupt context, so it should do its work
* quickly and queue potentially time-consuming work to a task-level thread.
*
******************************************************************************/
void XSpiPs_SetStatusHandler(XSpiPs *InstancePtr, void *CallBackRef,
				XSpiPs_StatusHandler FunctionPtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FunctionPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->StatusHandler = FunctionPtr;
	InstancePtr->StatusRef = CallBackRef;
}

/*****************************************************************************/
/**
*
* This is a stub for the status callback. The stub is here in case the upper
* layers forget to set the handler.
*
* @param	CallBackRef is a pointer to the upper layer callback reference
* @param	StatusEvent is the event that just occurred.
* @param	ByteCount is the number of bytes transferred up until the event
*		occurred.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void StubStatusHandler(void *CallBackRef, u32 StatusEvent,
				u32 ByteCount)
{
	(void) CallBackRef;
	(void) StatusEvent;
	(void) ByteCount;

	Xil_AssertVoidAlways();
}

/*****************************************************************************/
/**
*
* The interrupt handler for SPI interrupts. This function must be connected
* by the user to an interrupt controller.
*
* The interrupts that are handled are:
*
* - Mode Fault Error. This interrupt is generated if this device is selected
*   as a slave when it is configured as a master. The driver aborts any data
*   transfer that is in progress by resetting FIFOs (if present) and resetting
*   its buffer pointers. The upper layer software is informed of the error.
*
* - Data Transmit Register (FIFO) Empty. This interrupt is generated when the
*   transmit register or FIFO is empty. The driver uses this interrupt during a
*   transmission to continually send/receive data until the transfer is done.
*
* - Data Transmit Register (FIFO) Underflow. This interrupt is generated when
*   the SPI device, when configured as a slave, attempts to read an empty
*   DTR/FIFO.  An empty DTR/FIFO usually means that software is not giving the
*   device data in a timely manner. No action is taken by the driver other than
*   to inform the upper layer software of the error.
*
* - Data Receive Register (FIFO) Overflow. This interrupt is generated when the
*   SPI device attempts to write a received byte to an already full DRR/FIFO.
*   A full DRR/FIFO usually means software is not emptying the data in a timely
*   manner.  No action is taken by the driver other than to inform the upper
*   layer software of the error.
*
* - Slave Mode Fault Error. This interrupt is generated if a slave device is
*   selected as a slave while it is disabled. No action is taken by the driver
*   other than to inform the upper layer software of the error.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	None.
*
* @note
*
* The slave select register is being set to deselect the slave when a transfer
* is complete.  This is being done regardless of whether it is a slave or a
* master since the hardware does not drive the slave select as a slave.
*
******************************************************************************/
void XSpiPs_InterruptHandler(XSpiPs *InstancePtr)
{
	XSpiPs *SpiPtr = InstancePtr;
	u32 IntrStatus;
	u32 ConfigReg;
	u32 BytesDone; /* Number of bytes done so far. */

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(SpiPtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Immediately clear the interrupts in case the ISR causes another
	 * interrupt to be generated. If we clear at the end of the ISR,
	 * we may miss newly generated interrupts.
	 * Disable the TXOW interrupt because we transmit from within the ISR,
	 * which could potentially cause another TX_OW interrupt.
	 */
	IntrStatus =
		XSpiPs_ReadReg(SpiPtr->Config.BaseAddress, XSPIPS_SR_OFFSET);
	XSpiPs_WriteReg(SpiPtr->Config.BaseAddress, XSPIPS_SR_OFFSET,
			(IntrStatus & XSPIPS_IXR_WR_TO_CLR_MASK));
	XSpiPs_WriteReg(SpiPtr->Config.BaseAddress, XSPIPS_IDR_OFFSET,
			XSPIPS_IXR_TXOW_MASK);

	/*
	 * Check for mode fault error. We want to check for this error first,
	 * before checking for progress of a transfer, since this error needs
	 * to abort any operation in progress.
	 */
	if ((u32)XSPIPS_IXR_MODF_MASK == (u32)(IntrStatus & XSPIPS_IXR_MODF_MASK)) {
		BytesDone = SpiPtr->RequestedBytes - SpiPtr->RemainingBytes;

		/*
		 * Abort any operation currently in progress. This includes
		 * clearing the mode fault condition by reading the status
		 * register. Note that the status register should be read after
		 * the abort, since reading the status register clears the mode
		 * fault condition and would cause the device to restart any
		 * transfer that may be in progress.
		 */
		XSpiPs_Abort(SpiPtr);

		SpiPtr->StatusHandler(SpiPtr->StatusRef, XST_SPI_MODE_FAULT,
					BytesDone);

		return; /* Do not continue servicing other interrupts. */
	}


	if ((IntrStatus & XSPIPS_IXR_TXOW_MASK) != 0U) {
		u8 TempData;
		u32 TransCount;
		/*
		 * A transmit has just completed. Process received data and
		 * check for more data to transmit.
		 * First get the data received as a result of the transmit that
		 * just completed.  Always get the received data, but only fill
		 * the receive buffer if it is not null (it can be null when
		 * the device does not care to receive data).
		 * Initialize the TransCount based on the requested bytes.
		 * Loop on receive FIFO based on TransCount.
		 */
		TransCount = SpiPtr->RequestedBytes - SpiPtr->RemainingBytes;

		while (TransCount != 0U) {
			TempData = (u8)XSpiPs_RecvByte(SpiPtr->Config.BaseAddress);
			if (SpiPtr->RecvBufferPtr != NULL) {
				*SpiPtr->RecvBufferPtr = TempData;
				SpiPtr->RecvBufferPtr += 1;
			}
			SpiPtr->RequestedBytes--;
			--TransCount;
		}

		/*
		 * Fill the TXFIFO until data exists, otherwise fill upto
		 * FIFO depth.
		 */
		while ((SpiPtr->RemainingBytes > 0U) &&
			(TransCount < XSPIPS_FIFO_DEPTH)) {
			XSpiPs_SendByte(SpiPtr->Config.BaseAddress,
					 *SpiPtr->SendBufferPtr);
			SpiPtr->SendBufferPtr += 1;
			SpiPtr->RemainingBytes--;
			++TransCount;
		}

		if ((SpiPtr->RemainingBytes == 0U) &&
			(SpiPtr->RequestedBytes == 0U)) {
			/*
			 * No more data to send. Disable the interrupt and
			 * inform the upper layer software that the transfer
			 * is done. The interrupt will be re-enabled when
			 * another transfer is initiated.
			 */
			XSpiPs_WriteReg(SpiPtr->Config.BaseAddress,
				 XSPIPS_IDR_OFFSET, XSPIPS_IXR_DFLT_MASK);

			/*
			 * Disable slave select lines as the transfer
			 * is complete.
			 */
			if (XSpiPs_IsManualChipSelect(InstancePtr) == TRUE) {
				ConfigReg = XSpiPs_ReadReg(
					SpiPtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET);
				ConfigReg |= XSPIPS_CR_SSCTRL_MASK;
				XSpiPs_WriteReg(
					SpiPtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET, ConfigReg);
			}

			/*
			 * Clear the busy flag.
			 */
			SpiPtr->IsBusy = FALSE;

			/*
			 * Disable the device.
			 */
			XSpiPs_Disable(SpiPtr);

			/*
			 * Inform the Transfer done to upper layers.
			 */
			SpiPtr->StatusHandler(SpiPtr->StatusRef,
						XST_SPI_TRANSFER_DONE,
						SpiPtr->RequestedBytes);
		} else {
			/*
			 * Enable the TXOW interrupt.
			 */
			XSpiPs_WriteReg(SpiPtr->Config.BaseAddress,
				 XSPIPS_IER_OFFSET, XSPIPS_IXR_TXOW_MASK);
			/*
			 * Start the transfer by not inhibiting the transmitter
			 * any longer.
			 */
			if ((XSpiPs_IsManualStart(SpiPtr) == TRUE)
				&& (XSpiPs_IsMaster(SpiPtr) == TRUE)) {
				ConfigReg = XSpiPs_ReadReg(
					SpiPtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET);
				ConfigReg |= XSPIPS_CR_MANSTRT_MASK;
				XSpiPs_WriteReg(
					SpiPtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET, ConfigReg);
			}
		}
	}

	/*
	 * Check for overflow and underflow errors.
	 */
	if ((IntrStatus & XSPIPS_IXR_RXOVR_MASK) != 0U) {
		BytesDone = SpiPtr->RequestedBytes - SpiPtr->RemainingBytes;
		SpiPtr->IsBusy = FALSE;

		/*
		 * The Slave select lines are being manually controlled.
		 * Disable them because the transfer is complete.
		 */
		if (XSpiPs_IsManualChipSelect(SpiPtr) == TRUE) {
			ConfigReg = XSpiPs_ReadReg(
				SpiPtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET);
			ConfigReg |= XSPIPS_CR_SSCTRL_MASK;
			XSpiPs_WriteReg(
				SpiPtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET, ConfigReg);
		}

		SpiPtr->StatusHandler(SpiPtr->StatusRef,
			XST_SPI_RECEIVE_OVERRUN, BytesDone);
	}

	if ((IntrStatus & XSPIPS_IXR_TXUF_MASK) != 0U) {
		BytesDone = SpiPtr->RequestedBytes - SpiPtr->RemainingBytes;

		SpiPtr->IsBusy = FALSE;
		/*
		 * The Slave select lines are being manually controlled.
		 * Disable them because the transfer is complete.
		 */
		if (XSpiPs_IsManualChipSelect(SpiPtr) == TRUE) {
			ConfigReg = XSpiPs_ReadReg(
				SpiPtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET);
			ConfigReg |= XSPIPS_CR_SSCTRL_MASK;
			XSpiPs_WriteReg(
				SpiPtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET, ConfigReg);
		}

		SpiPtr->StatusHandler(SpiPtr->StatusRef,
			XST_SPI_TRANSMIT_UNDERRUN, BytesDone);
	}

}

/*****************************************************************************/
/**
*
* Aborts a transfer in progress by disabling the device and resetting the FIFOs
* if present. The byte counts are cleared, the busy flag is cleared, and mode
* fault is cleared.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	None.
*
* @note
*
* This function does a read/modify/write of the Config register. The user of
* this function needs to take care of critical sections.
*
******************************************************************************/
void XSpiPs_Abort(XSpiPs *InstancePtr)
{

	u8 Temp;
	u32 Check;
	XSpiPs_Disable(InstancePtr);

	/*
	 * Clear the RX FIFO and drop any data.
	 */
	Check = (XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
		XSPIPS_SR_OFFSET) & XSPIPS_IXR_RXNEMPTY_MASK);
	while (Check != (u32)0U) {
		Temp = (u8)XSpiPs_RecvByte(InstancePtr->Config.BaseAddress);
		if(Temp != (u8)0U){
		}
		Check = (XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
		XSPIPS_SR_OFFSET) & XSPIPS_IXR_RXNEMPTY_MASK);
	}

	/*
	 * Clear mode fault condition.
	 */
	XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
			XSPIPS_SR_OFFSET,
			XSPIPS_IXR_MODF_MASK);

	InstancePtr->RemainingBytes = 0U;
	InstancePtr->RequestedBytes = 0U;
	InstancePtr->IsBusy = FALSE;
}
