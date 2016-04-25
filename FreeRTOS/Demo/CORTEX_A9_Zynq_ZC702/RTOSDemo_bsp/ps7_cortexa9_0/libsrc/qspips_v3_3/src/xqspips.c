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
* @file xqspips.c
* @addtogroup qspips_v3_2
* @{
*
* Contains implements the interface functions of the XQspiPs driver.
* See xqspips.h for a detailed description of the device and driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 1.00  sdm 11/25/10 First release
* 2.00a kka 07/25/12 Removed XQspiPs_GetWriteData API.
*		     The XQspiPs_SetSlaveSelect has been modified to remove
*		     the argument of the slave select as the QSPI controller
*		     only supports one slave.
* 		     XQspiPs_GetSlaveSelect API has been removed
* 		     Added logic to XQspiPs_GetReadData to handle data
*		     shift for normal data reads and instruction/status
*		     reads differently based on the ShiftReadData flag.
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
*		     The XQspiPs_PolledTransfer function has been updated
*		     to fill the data to fifo depth.
*		     This version of the driver fixes CRs 670197/663787.
* 2.01a sg  02/03/13 Added flash opcodes for DUAL_IO_READ,QUAD_IO_READ.
*		     Created macros XQspiPs_IsManualStart and
*		     XQspiPs_IsManualChipSelect.
*		     Changed QSPI transfer logic for polled and interrupt
*		     modes to be based on filled tx fifo count and receive
*		     based on it. RXNEMPTY interrupt is not used.
*		     Added assertions to XQspiPs_LqspiRead function.
*
* 2.02a hk  05/14/13 Added enable and disable to the XQspiPs_LqspiRead()
*			 function
*            Added instructions for bank selection, die erase and
*            flag status register to the flash instruction table
*            Handling for instructions not in flash instruction
*			 table added. Checking for Tx FIFO empty when switching from
*			 TXD1/2/3 to TXD0 added. If WRSR instruction is sent with
*            byte count 3 (spansion), instruction size and TXD register
*			 changed accordingly. CR# 712502 and 703869.
*            Added (#ifdef linear base address) in the Linear read function.
*            Changed  XPAR_XQSPIPS_0_LINEAR_BASEADDR to
*            XPAR_PS7_QSPI_LINEAR_0_S_AXI_BASEADDR in
*            XQspiPs_LqspiRead function. Fix for CR#718141
*
* 2.03a hk  09/05/13 Modified polled and interrupt transfers to make use of
*                    thresholds. This is to improve performance.
*                    Added RX and TX threshold reset to one in XQspiPs_Abort.
*                    Added RX threshold reset(1) after transfer in polled and
*                    interrupt transfers. Made changes to make sure threshold
*                    change is done only when no transfer is in progress.
* 3.1   hk  08/13/14 When writing to the configuration register, set/reset
*                    required bits leaving reserved bits untouched. CR# 796813.
* 3.2	sk	02/05/15 Add SLCR reset in abort function as a workaround because
* 					 controller does not update FIFO status flags as expected
* 					 when thresholds are used.
* 3.3   sk  11/07/15 Modified the API prototypes according to MISRAC standards
*                    to remove compilation warnings. CR# 868893.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xqspips.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/

/**
 * This typedef defines qspi flash instruction format
 */
typedef struct {
	u8 OpCode;	/**< Operational code of the instruction */
	u8 InstSize;	/**< Size of the instruction including address bytes */
	u8 TxOffset;	/**< Register address where instruction has to be
			     written */
} XQspiPsInstFormat;

/***************** Macros (Inline Functions) Definitions *********************/

#define ARRAY_SIZE(Array)		(sizeof(Array) / sizeof((Array)[0]))

/************************** Function Prototypes ******************************/
static void XQspiPs_GetReadData(XQspiPs *InstancePtr, u32 Data, u8 Size);
static void StubStatusHandler(void *CallBackRef, u32 StatusEvent,
				unsigned ByteCount);

/************************** Variable Definitions *****************************/

/*
 * List of all the QSPI instructions and its format
 */
static XQspiPsInstFormat FlashInst[] = {
	{ XQSPIPS_FLASH_OPCODE_WREN, 1, XQSPIPS_TXD_01_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_WRDS, 1, XQSPIPS_TXD_01_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_RDSR1, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_RDSR2, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_WRSR, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_PP, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_SE, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_BE_32K, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_BE_4K, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_BE, 1, XQSPIPS_TXD_01_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_ERASE_SUS, 1, XQSPIPS_TXD_01_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_ERASE_RES, 1, XQSPIPS_TXD_01_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_RDID, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_NORM_READ, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_FAST_READ, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_DUAL_READ, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_QUAD_READ, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_DUAL_IO_READ, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_QUAD_IO_READ, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_BRWR, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_BRRD, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_EARWR, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_EARRD, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_DIE_ERASE, 4, XQSPIPS_TXD_00_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_READ_FLAG_SR, 2, XQSPIPS_TXD_10_OFFSET },
	{ XQSPIPS_FLASH_OPCODE_CLEAR_FLAG_SR, 1, XQSPIPS_TXD_01_OFFSET },
	/* Add all the instructions supported by the flash device */
};

/*****************************************************************************/
/**
*
* Initializes a specific XQspiPs instance such that the driver is ready to use.
*
* The state of the device after initialization is:
*   - Master mode
*   - Active high clock polarity
*   - Clock phase 0
*   - Baud rate divisor 2
*   - Transfer width 32
*   - Master reference clock = pclk
*   - No chip select active
*   - Manual CS and Manual Start disabled
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	ConfigPtr is a reference to a structure containing information
*		about a specific QSPI device. This function initializes an
*		InstancePtr object for a specific device specified by the
*		contents of Config.
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
int XQspiPs_CfgInitialize(XQspiPs *InstancePtr, XQspiPs_Config *ConfigPtr,
				u32 EffectiveAddr)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * If the device is busy, disallow the initialize and return a status
	 * indicating it is already started. This allows the user to stop the
	 * device and re-initialize, but prevents a user from inadvertently
	 * initializing. This assumes the busy flag is cleared at startup.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		return XST_DEVICE_IS_STARTED;
	}

	/*
	 * Set some default values.
	 */
	InstancePtr->IsBusy = FALSE;

	InstancePtr->Config.BaseAddress = EffectiveAddr;
	InstancePtr->StatusHandler = StubStatusHandler;

	InstancePtr->SendBufferPtr = NULL;
	InstancePtr->RecvBufferPtr = NULL;
	InstancePtr->RequestedBytes = 0;
	InstancePtr->RemainingBytes = 0;
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	InstancePtr->Config.ConnectionMode = ConfigPtr->ConnectionMode;

	/*
	 * Reset the QSPI device to get it into its initial state. It is
	 * expected that device configuration will take place after this
	 * initialization is done, but before the device is started.
	 */
	XQspiPs_Reset(InstancePtr);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* Resets the QSPI device. Reset must only be called after the driver has been
* initialized. Any data transfer that is in progress is aborted.
*
* The upper layer software is responsible for re-configuring (if necessary)
* and restarting the QSPI device after the reset.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XQspiPs_Reset(XQspiPs *InstancePtr)
{
	u32 ConfigReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Abort any transfer that is in progress
	 */
	XQspiPs_Abort(InstancePtr);

	/*
	 * Write default value to configuration register.
	 * Do not modify reserved bits.
	 */
	ConfigReg = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
			 XQSPIPS_CR_OFFSET);
	ConfigReg |= XQSPIPS_CR_RESET_MASK_SET;
	ConfigReg &= ~XQSPIPS_CR_RESET_MASK_CLR;
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress, XQSPIPS_CR_OFFSET,
			  ConfigReg);
}

/*****************************************************************************/
/**
*
* Aborts a transfer in progress by disabling the device and flush the RxFIFO.
* The byte counts are cleared, the busy flag is cleared.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	None.
*
* @note
*
* This function does a read/modify/write of the config register. The user of
* this function needs to take care of critical sections.
*
******************************************************************************/
void XQspiPs_Abort(XQspiPs *InstancePtr)
{
	u32 ConfigReg;
	u32 IsLock;

	XQspiPs_Disable(InstancePtr);

	/*
	 * De-assert slave select lines.
	 */
	ConfigReg = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
			 XQSPIPS_CR_OFFSET);
	ConfigReg |= (XQSPIPS_CR_SSCTRL_MASK | XQSPIPS_CR_SSFORCE_MASK);
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			 XQSPIPS_CR_OFFSET, ConfigReg);

	/*
	 * QSPI Software Reset
	 */
	IsLock = XQspiPs_ReadReg(XPAR_XSLCR_0_BASEADDR, SLCR_LOCKSTA);
	if (IsLock) {
		XQspiPs_WriteReg(XPAR_XSLCR_0_BASEADDR, SLCR_UNLOCK,
				SLCR_UNLOCK_MASK);
	}
	XQspiPs_WriteReg(XPAR_XSLCR_0_BASEADDR, LQSPI_RST_CTRL,
			LQSPI_RST_CTRL_MASK);
	XQspiPs_WriteReg(XPAR_XSLCR_0_BASEADDR, LQSPI_RST_CTRL, 0x0);
	if (IsLock) {
		XQspiPs_WriteReg(XPAR_XSLCR_0_BASEADDR, SLCR_LOCK,
				SLCR_LOCK_MASK);
	}

	/*
	 * Set the RX and TX FIFO threshold to reset value (one)
	 */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPS_RXWR_OFFSET, XQSPIPS_RXWR_RESET_VALUE);

	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPS_TXWR_OFFSET, XQSPIPS_TXWR_RESET_VALUE);

	InstancePtr->RemainingBytes = 0;
	InstancePtr->RequestedBytes = 0;
	InstancePtr->IsBusy = FALSE;
}

/*****************************************************************************/
/**
*
* Transfers specified data on the QSPI bus. Initiates bus communication and
* sends/receives data to/from the selected QSPI slave. For every byte sent,
* a byte is received.
*
* The caller has the option of providing two different buffers for send and
* receive, or one buffer for both send and receive, or no buffer for receive.
* The receive buffer must be at least as big as the send buffer to prevent
* unwanted memory writes. This implies that the byte count passed in as an
* argument must be the smaller of the two buffers if they differ in size.
* Here are some sample usages:
* <pre>
*   XQspiPs_Transfer(InstancePtr, SendBuf, RecvBuf, ByteCount)
*	The caller wishes to send and receive, and provides two different
*	buffers for send and receive.
*
*   XQspiPs_Transfer(InstancePtr, SendBuf, NULL, ByteCount)
*	The caller wishes only to send and does not care about the received
*	data. The driver ignores the received data in this case.
*
*   XQspiPs_Transfer(InstancePtr, SendBuf, SendBuf, ByteCount)
*	The caller wishes to send and receive, but provides the same buffer
*	for doing both. The driver sends the data and overwrites the send
*	buffer with received data as it transfers the data.
*
*   XQspiPs_Transfer(InstancePtr, RecvBuf, RecvBuf, ByteCount)
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
* This function is non-blocking. The SetSlaveSelect function must be called
* prior to this function.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	SendBufPtr is a pointer to a data buffer that needs to be
*		transmitted. This buffer must not be NULL.
* @param	RecvBufPtr is a pointer to a buffer for received data.
*		This argument can be NULL if do not care about receiving.
* @param	ByteCount contains the number of bytes to send/receive.
*		The number of bytes received always equals the number of bytes
*		sent.
*
* @return
*		- XST_SUCCESS if the buffers are successfully handed off to the
*		  device for transfer.
*		- XST_DEVICE_BUSY indicates that a data transfer is already in
*		  progress. This is determined by the driver.
*
* @note
*
* This function is not thread-safe.  The higher layer software must ensure that
* no two threads are transferring data on the QSPI bus at the same time.
*
******************************************************************************/
s32 XQspiPs_Transfer(XQspiPs *InstancePtr, u8 *SendBufPtr, u8 *RecvBufPtr,
			u32 ByteCount)
{
	u32 StatusReg;
	u32 ConfigReg;
	u8 Instruction;
	u32 Data;
	unsigned int Index;
	u8 TransCount = 0;
	XQspiPsInstFormat *CurrInst;
	XQspiPsInstFormat NewInst[2];
	u8 SwitchFlag  = 0;

	CurrInst = &NewInst[0];

	/*
	 * The RecvBufPtr argument can be null
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(SendBufPtr != NULL);
	Xil_AssertNonvoid(ByteCount > 0);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check whether there is another transfer in progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

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
	 * The first byte with every chip-select assertion is always
	 * expected to be an instruction for flash interface mode
	 */
	Instruction = *InstancePtr->SendBufferPtr;

	for (Index = 0 ; Index < ARRAY_SIZE(FlashInst); Index++) {
		if (Instruction == FlashInst[Index].OpCode) {
			break;
		}
	}

	/*
	 * Set the RX FIFO threshold
	 */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPS_RXWR_OFFSET, XQSPIPS_RXFIFO_THRESHOLD_OPT);

	/*
	 * If the slave select is "Forced" or under manual control,
	 * set the slave select now, before beginning the transfer.
	 */
	if (XQspiPs_IsManualChipSelect(InstancePtr)) {
		ConfigReg = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XQSPIPS_CR_OFFSET);
		ConfigReg &= ~XQSPIPS_CR_SSCTRL_MASK;
		XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
				  XQSPIPS_CR_OFFSET,
				  ConfigReg);
	}

	/*
	 * Enable the device.
	 */
	XQspiPs_Enable(InstancePtr);

	/*
	 * Clear all the interrrupts.
	 */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress, XQSPIPS_SR_OFFSET,
			XQSPIPS_IXR_WR_TO_CLR_MASK);

	if (Index < ARRAY_SIZE(FlashInst)) {
		CurrInst = &FlashInst[Index];
		/*
		 * Check for WRSR instruction which has different size for
		 * Spansion (3 bytes) and Micron (2 bytes)
		 */
		if( (CurrInst->OpCode == XQSPIPS_FLASH_OPCODE_WRSR) &&
			(ByteCount == 3) ) {
			CurrInst->InstSize = 3;
			CurrInst->TxOffset = XQSPIPS_TXD_11_OFFSET;
		}
	}

	/*
	 * If instruction not present in table
	 */
	if (Index == ARRAY_SIZE(FlashInst)) {
		/*
		 * Assign current instruction, size and TXD register to be used
		 * The InstSize mentioned in case of instructions greater than
		 * 4 bytes is not the actual size, but is indicative of
		 * the TXD register used.
		 * The remaining bytes of the instruction will be transmitted
		 * through TXD0 below.
		 */
		switch(ByteCount%4)
		{
			case XQSPIPS_SIZE_ONE:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_ONE;
				CurrInst->TxOffset = XQSPIPS_TXD_01_OFFSET;
				if(ByteCount > 4) {
					SwitchFlag = 1;
				}
				break;
			case XQSPIPS_SIZE_TWO:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_TWO;
				CurrInst->TxOffset = XQSPIPS_TXD_10_OFFSET;
				if(ByteCount > 4) {
					SwitchFlag = 1;
				}
				break;
			case XQSPIPS_SIZE_THREE:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_THREE;
				CurrInst->TxOffset = XQSPIPS_TXD_11_OFFSET;
				if(ByteCount > 4) {
					SwitchFlag = 1;
				}
				break;
			default:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_FOUR;
				CurrInst->TxOffset = XQSPIPS_TXD_00_OFFSET;
				break;
		}
	}

	/*
	 * If the instruction size in not 4 bytes then the data received needs
	 * to be shifted
	 */
	if( CurrInst->InstSize != 4 ) {
		InstancePtr->ShiftReadData = 1;
	} else {
		InstancePtr->ShiftReadData = 0;
	}

	/* Get the complete command (flash inst + address/data) */
	Data = *((u32 *)InstancePtr->SendBufferPtr);
	InstancePtr->SendBufferPtr += CurrInst->InstSize;
	InstancePtr->RemainingBytes -= CurrInst->InstSize;
	if (InstancePtr->RemainingBytes < 0) {
		InstancePtr->RemainingBytes = 0;
	}

	/* Write the command to the FIFO */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			 CurrInst->TxOffset, Data);
	TransCount++;

	/*
	 * If switching from TXD1/2/3 to TXD0, then start transfer and
	 * check for FIFO empty
	 */
	if(SwitchFlag == 1) {
		SwitchFlag = 0;
		/*
		 * If, in Manual Start mode, start the transfer.
		 */
		if (XQspiPs_IsManualStart(InstancePtr)) {
			ConfigReg = XQspiPs_ReadReg(
					InstancePtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET);
			ConfigReg |= XQSPIPS_CR_MANSTRT_MASK;
			XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET, ConfigReg);
		}
		/*
		 * Wait for the transfer to finish by polling Tx fifo status.
		 */
		do {
			StatusReg = XQspiPs_ReadReg(
					InstancePtr->Config.BaseAddress,
					XQSPIPS_SR_OFFSET);
		} while ((StatusReg & XQSPIPS_IXR_TXOW_MASK) == 0);

	}

	/*
	 * Fill the Tx FIFO with as many bytes as it takes (or as many as
	 * we have to send).
	 */
	while ((InstancePtr->RemainingBytes > 0) &&
		(TransCount < XQSPIPS_FIFO_DEPTH)) {
		XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
				  XQSPIPS_TXD_00_OFFSET,
				  *((u32 *)InstancePtr->SendBufferPtr));
		InstancePtr->SendBufferPtr += 4;
		InstancePtr->RemainingBytes -= 4;
		if (InstancePtr->RemainingBytes < 0) {
			InstancePtr->RemainingBytes = 0;
		}
		TransCount++;
	}

	/*
	 * Enable QSPI interrupts (connecting to the interrupt controller and
	 * enabling interrupts should have been done by the caller).
	 */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XQSPIPS_IER_OFFSET, XQSPIPS_IXR_RXNEMPTY_MASK |
			  XQSPIPS_IXR_TXOW_MASK | XQSPIPS_IXR_RXOVR_MASK |
			  XQSPIPS_IXR_TXUF_MASK);

	/*
	 * If, in Manual Start mode, Start the transfer.
	 */
	if (XQspiPs_IsManualStart(InstancePtr)) {
		ConfigReg = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
				XQSPIPS_CR_OFFSET);
		ConfigReg |= XQSPIPS_CR_MANSTRT_MASK;
		XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
				  XQSPIPS_CR_OFFSET, ConfigReg);
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* Transfers specified data on the QSPI bus in polled mode.
*
* The caller has the option of providing two different buffers for send and
* receive, or one buffer for both send and receive, or no buffer for receive.
* The receive buffer must be at least as big as the send buffer to prevent
* unwanted memory writes. This implies that the byte count passed in as an
* argument must be the smaller of the two buffers if they differ in size.
* Here are some sample usages:
* <pre>
*   XQspiPs_PolledTransfer(InstancePtr, SendBuf, RecvBuf, ByteCount)
*	The caller wishes to send and receive, and provides two different
*	buffers for send and receive.
*
*   XQspiPs_PolledTransfer(InstancePtr, SendBuf, NULL, ByteCount)
*	The caller wishes only to send and does not care about the received
*	data. The driver ignores the received data in this case.
*
*   XQspiPs_PolledTransfer(InstancePtr, SendBuf, SendBuf, ByteCount)
*	The caller wishes to send and receive, but provides the same buffer
*	for doing both. The driver sends the data and overwrites the send
*	buffer with received data as it transfers the data.
*
*   XQspiPs_PolledTransfer(InstancePtr, RecvBuf, RecvBuf, ByteCount)
*	The caller wishes to only receive and does not care about sending
*	data.  In this case, the caller must still provide a send buffer, but
*	it can be the same as the receive buffer if the caller does not care
*	what it sends.  The device must send N bytes of data if it wishes to
*	receive N bytes of data.
*
* </pre>
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	SendBufPtr is a pointer to a data buffer that needs to be
*		transmitted. This buffer must not be NULL.
* @param	RecvBufPtr is a pointer to a buffer for received data.
*		This argument can be NULL if do not care about receiving.
* @param	ByteCount contains the number of bytes to send/receive.
*		The number of bytes received always equals the number of bytes
*		sent.
* @return
*		- XST_SUCCESS if the buffers are successfully handed off to the
*		  device for transfer.
*		- XST_DEVICE_BUSY indicates that a data transfer is already in
*		  progress. This is determined by the driver.
*
* @note
*
* This function is not thread-safe.  The higher layer software must ensure that
* no two threads are transferring data on the QSPI bus at the same time.
*
******************************************************************************/
s32 XQspiPs_PolledTransfer(XQspiPs *InstancePtr, u8 *SendBufPtr,
			    u8 *RecvBufPtr, u32 ByteCount)
{
	u32 StatusReg;
	u32 ConfigReg;
	u8 Instruction;
	u32 Data;
	u8 TransCount;
	unsigned int Index;
	XQspiPsInstFormat *CurrInst;
	XQspiPsInstFormat NewInst[2];
	u8 SwitchFlag  = 0;
	u8 IsManualStart = FALSE;
	u32 RxCount = 0;

	CurrInst = &NewInst[0];
	/*
	 * The RecvBufPtr argument can be NULL.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(SendBufPtr != NULL);
	Xil_AssertNonvoid(ByteCount > 0);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check whether there is another transfer in progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

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
	 * The first byte with every chip-select assertion is always
	 * expected to be an instruction for flash interface mode
	 */
	Instruction = *InstancePtr->SendBufferPtr;

	for (Index = 0 ; Index < ARRAY_SIZE(FlashInst); Index++) {
		if (Instruction == FlashInst[Index].OpCode) {
			break;
		}
	}

	/*
	 * Set the RX FIFO threshold
	 */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPS_RXWR_OFFSET, XQSPIPS_RXFIFO_THRESHOLD_OPT);

	/*
	 * If the slave select is "Forced" or under manual control,
	 * set the slave select now, before beginning the transfer.
	 */
	if (XQspiPs_IsManualChipSelect(InstancePtr)) {
		ConfigReg = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XQSPIPS_CR_OFFSET);
		ConfigReg &= ~XQSPIPS_CR_SSCTRL_MASK;
		XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
				  XQSPIPS_CR_OFFSET,
				  ConfigReg);
	}

	/*
	 * Enable the device.
	 */
	XQspiPs_Enable(InstancePtr);

	if (Index < ARRAY_SIZE(FlashInst)) {

		CurrInst = &FlashInst[Index];
		/*
		 * Check for WRSR instruction which has different size for
		 * Spansion (3 bytes) and Micron (2 bytes)
		 */
		if( (CurrInst->OpCode == XQSPIPS_FLASH_OPCODE_WRSR) &&
			(ByteCount == 3) ) {
			CurrInst->InstSize = 3;
			CurrInst->TxOffset = XQSPIPS_TXD_11_OFFSET;
		}
	}

	/*
	 * If instruction not present in table
	 */
	if (Index == ARRAY_SIZE(FlashInst)) {
		/*
		 * Assign current instruction, size and TXD register to be used.
		 * The InstSize mentioned in case of instructions greater than 4 bytes
		 * is not the actual size, but is indicative of the TXD register used.
		 * The remaining bytes of the instruction will be transmitted
		 * through TXD0 below.
		 */
		switch(ByteCount%4)
		{
			case XQSPIPS_SIZE_ONE:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_ONE;
				CurrInst->TxOffset = XQSPIPS_TXD_01_OFFSET;
				if(ByteCount > 4) {
					SwitchFlag = 1;
				}
				break;
			case XQSPIPS_SIZE_TWO:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_TWO;
				CurrInst->TxOffset = XQSPIPS_TXD_10_OFFSET;
				if(ByteCount > 4) {
					SwitchFlag = 1;
				}
				break;
			case XQSPIPS_SIZE_THREE:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_THREE;
				CurrInst->TxOffset = XQSPIPS_TXD_11_OFFSET;
				if(ByteCount > 4) {
					SwitchFlag = 1;
				}
				break;
			default:
				CurrInst->OpCode = Instruction;
				CurrInst->InstSize = XQSPIPS_SIZE_FOUR;
				CurrInst->TxOffset = XQSPIPS_TXD_00_OFFSET;
				break;
		}
	}

	/*
	 * If the instruction size in not 4 bytes then the data received needs
	 * to be shifted
	 */
	if( CurrInst->InstSize != 4 ) {
		InstancePtr->ShiftReadData = 1;
	} else {
		InstancePtr->ShiftReadData = 0;
	}
	TransCount = 0;
	/* Get the complete command (flash inst + address/data) */
	Data = *((u32 *)InstancePtr->SendBufferPtr);
	InstancePtr->SendBufferPtr += CurrInst->InstSize;
	InstancePtr->RemainingBytes -= CurrInst->InstSize;
	if (InstancePtr->RemainingBytes < 0) {
		InstancePtr->RemainingBytes = 0;
	}

	/* Write the command to the FIFO */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
					CurrInst->TxOffset, Data);
	++TransCount;

	/*
	 * If switching from TXD1/2/3 to TXD0, then start transfer and
	 * check for FIFO empty
	 */
	if(SwitchFlag == 1) {
		SwitchFlag = 0;
		/*
		 * If, in Manual Start mode, start the transfer.
		 */
		if (XQspiPs_IsManualStart(InstancePtr)) {
			ConfigReg = XQspiPs_ReadReg(
					InstancePtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET);
			ConfigReg |= XQSPIPS_CR_MANSTRT_MASK;
			XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET, ConfigReg);
		}
		/*
		 * Wait for the transfer to finish by polling Tx fifo status.
		 */
		do {
			StatusReg = XQspiPs_ReadReg(
					InstancePtr->Config.BaseAddress,
					XQSPIPS_SR_OFFSET);
		} while ((StatusReg & XQSPIPS_IXR_TXOW_MASK) == 0);

	}

	/*
	 * Check if manual start is selected and store it in a
	 * local varibale for reference. This is to avoid reading
	 * the config register everytime.
	 */
	IsManualStart = XQspiPs_IsManualStart(InstancePtr);

	/*
	 * Fill the DTR/FIFO with as many bytes as it will take (or as
	 * many as we have to send).
	 */
	while ((InstancePtr->RemainingBytes > 0) &&
		(TransCount < XQSPIPS_FIFO_DEPTH)) {
		XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
				 XQSPIPS_TXD_00_OFFSET,
				 *((u32 *)InstancePtr->SendBufferPtr));
		InstancePtr->SendBufferPtr += 4;
		InstancePtr->RemainingBytes -= 4;
		if (InstancePtr->RemainingBytes < 0) {
			InstancePtr->RemainingBytes = 0;
		}
		++TransCount;
	}

	while((InstancePtr->RemainingBytes > 0) ||
	      (InstancePtr->RequestedBytes > 0)) {

		/*
		 * Fill the TX FIFO with RX threshold no. of entries (or as
		 * many as we have to send, in case that's less).
		 */
		while ((InstancePtr->RemainingBytes > 0) &&
			(TransCount < XQSPIPS_RXFIFO_THRESHOLD_OPT)) {
			XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
					 XQSPIPS_TXD_00_OFFSET,
					 *((u32 *)InstancePtr->SendBufferPtr));
			InstancePtr->SendBufferPtr += 4;
			InstancePtr->RemainingBytes -= 4;
			if (InstancePtr->RemainingBytes < 0) {
				InstancePtr->RemainingBytes = 0;
			}
			++TransCount;
		}

		/*
		 * If, in Manual Start mode, start the transfer.
		 */
		if (IsManualStart == TRUE) {
			ConfigReg = XQspiPs_ReadReg(
					InstancePtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET);
			ConfigReg |= XQSPIPS_CR_MANSTRT_MASK;
			XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET, ConfigReg);
		}

		/*
		 * Reset TransCount - this is only used to fill TX FIFO
		 * in the above loop;
		 * RxCount is used to keep track of data received
		 */
		TransCount = 0;

		/*
		 * Wait for RX FIFO to reach threshold (or)
		 * TX FIFO to become empty.
		 * The latter check is required for
		 * small transfers (<32 words) and
		 * when the last chunk in a large data transfer is < 32 words.
		 */

		do {
			StatusReg = XQspiPs_ReadReg(
					InstancePtr->Config.BaseAddress,
					XQSPIPS_SR_OFFSET);
		} while ( ((StatusReg & XQSPIPS_IXR_TXOW_MASK) == 0) &&
			((StatusReg & XQSPIPS_IXR_RXNEMPTY_MASK) == 0) );

		/*
		 * A transmit has just completed. Process received data
		 * and check for more data to transmit.
		 * First get the data received as a result of the
		 * transmit that just completed. Receive data based on the
		 * count obtained while filling tx fifo. Always get
		 * the received data, but only fill the receive
		 * buffer if it points to something (the upper layer
		 * software may not care to receive data).
		 */
		while ((InstancePtr->RequestedBytes > 0) &&
			(RxCount < XQSPIPS_RXFIFO_THRESHOLD_OPT )) {
			u32 Data;

			RxCount++;

			if (InstancePtr->RecvBufferPtr != NULL) {
				if (InstancePtr->RequestedBytes < 4) {
					Data = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
						XQSPIPS_RXD_OFFSET);
					XQspiPs_GetReadData(InstancePtr, Data,
						InstancePtr->RequestedBytes);
				} else {
					(*(u32 *)InstancePtr->RecvBufferPtr) =
						XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
						XQSPIPS_RXD_OFFSET);
					InstancePtr->RecvBufferPtr += 4;
					InstancePtr->RequestedBytes -= 4;
					if (InstancePtr->RequestedBytes < 0) {
						InstancePtr->RequestedBytes = 0;
					}
				}
			} else {
				Data = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
						XQSPIPS_RXD_OFFSET);
				InstancePtr->RequestedBytes -= 4;
			}
		}
		RxCount = 0;
	}

	/*
	 * If the Slave select lines are being manually controlled, disable
	 * them because the transfer is complete.
	 */
	if (XQspiPs_IsManualChipSelect(InstancePtr)) {
		ConfigReg = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XQSPIPS_CR_OFFSET);
		ConfigReg |= XQSPIPS_CR_SSCTRL_MASK;
		XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
				  XQSPIPS_CR_OFFSET, ConfigReg);
	}

	/*
	 * Clear the busy flag.
	 */
	InstancePtr->IsBusy = FALSE;

	/*
	 * Disable the device.
	 */
	XQspiPs_Disable(InstancePtr);

	/*
	 * Reset the RX FIFO threshold to one
	 */
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPS_RXWR_OFFSET, XQSPIPS_RXWR_RESET_VALUE);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* Read the flash in Linear QSPI mode.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	RecvBufPtr is a pointer to a buffer for received data.
* @param	Address is the starting address within the flash from
*		from where data needs to be read.
* @param	ByteCount contains the number of bytes to receive.
*
* @return
*		- XST_SUCCESS if read is performed
*		- XST_FAILURE if Linear mode is not set
*
* @note		None.
*
*
******************************************************************************/
int XQspiPs_LqspiRead(XQspiPs *InstancePtr, u8 *RecvBufPtr,
			u32 Address, unsigned ByteCount)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(RecvBufPtr != NULL);
	Xil_AssertNonvoid(ByteCount > 0);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

#ifndef XPAR_PS7_QSPI_LINEAR_0_S_AXI_BASEADDR
#define	XPAR_PS7_QSPI_LINEAR_0_S_AXI_BASEADDR 0xFC000000
#endif
	/*
	 * Enable the controller
	 */
	XQspiPs_Enable(InstancePtr);

	if (XQspiPs_GetLqspiConfigReg(InstancePtr) &
		XQSPIPS_LQSPI_CR_LINEAR_MASK) {
		memcpy((void*)RecvBufPtr,
		      (const void*)(XPAR_PS7_QSPI_LINEAR_0_S_AXI_BASEADDR +
		       Address),
		      (size_t)ByteCount);
		return XST_SUCCESS;
	} else {
		return XST_FAILURE;
	}

	/*
	 * Disable the controller
	 */
	XQspiPs_Disable(InstancePtr);

}

/*****************************************************************************/
/**
*
* Selects the slave with which the master communicates.
*
* The user is not allowed to select the slave while a transfer is in progress.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return
*		- XST_SUCCESS if the slave is selected or deselected
*		  successfully.
*		- XST_DEVICE_BUSY if a transfer is in progress, slave cannot be
*		  changed.
*
* @note
*
* This function only sets the slave which will be selected when a transfer
* occurs. The slave is not selected when the QSPI is idle.
*
******************************************************************************/
int XQspiPs_SetSlaveSelect(XQspiPs *InstancePtr)
{
	u32 ConfigReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Do not allow the slave select to change while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

	/*
	 * Select the slave
	 */
	ConfigReg = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
				      XQSPIPS_CR_OFFSET);
	ConfigReg &= ~XQSPIPS_CR_SSCTRL_MASK;
	XQspiPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XQSPIPS_CR_OFFSET, ConfigReg);

	return XST_SUCCESS;
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
* XST_SPI_RECEIVE_OVERRUN	The QSPI device lost data. Data was received
*				but the receive data register/FIFO was full.
*
* </pre>
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
* @param	FuncPtr is the pointer to the callback function.
*
* @return	None.
*
* @note
*
* The handler is called within interrupt context, so it should do its work
* quickly and queue potentially time-consuming work to a task-level thread.
*
******************************************************************************/
void XQspiPs_SetStatusHandler(XQspiPs *InstancePtr, void *CallBackRef,
				XQspiPs_StatusHandler FuncPtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FuncPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->StatusHandler = FuncPtr;
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
				unsigned ByteCount)
{
	(void) CallBackRef;
	(void) StatusEvent;
	(void) ByteCount;

	Xil_AssertVoidAlways();
}

/*****************************************************************************/
/**
*
* The interrupt handler for QSPI interrupts. This function must be connected
* by the user to an interrupt controller.
*
* The interrupts that are handled are:
*
*
* - Data Transmit Register (FIFO) Empty. This interrupt is generated when the
*   transmit register or FIFO is empty. The driver uses this interrupt during a
*   transmission to continually send/receive data until the transfer is done.
*
* - Data Transmit Register (FIFO) Underflow. This interrupt is generated when
*   the QSPI device, when configured as a slave, attempts to read an empty
*   DTR/FIFO.  An empty DTR/FIFO usually means that software is not giving the
*   device data in a timely manner. No action is taken by the driver other than
*   to inform the upper layer software of the error.
*
* - Data Receive Register (FIFO) Overflow. This interrupt is generated when the
*   QSPI device attempts to write a received byte to an already full DRR/FIFO.
*   A full DRR/FIFO usually means software is not emptying the data in a timely
*   manner.  No action is taken by the driver other than to inform the upper
*   layer software of the error.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return	None.
*
* @note
*
* The slave select register is being set to deselect the slave when a transfer
* is complete.
*
******************************************************************************/
void XQspiPs_InterruptHandler(void *InstancePtr)
{
	XQspiPs *QspiPtr = (XQspiPs *)InstancePtr;
	u32 IntrStatus;
	u32 ConfigReg;
	u32 Data;
	u32 TransCount;
	u32 Count = 0;
	unsigned BytesDone; /* Number of bytes done so far. */

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(QspiPtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Immediately clear the interrupts in case the ISR causes another
	 * interrupt to be generated. If we clear at the end of the ISR,
	 * we may miss newly generated interrupts. This occurs because we
	 * transmit from within the ISR, which could potentially cause another
	 * TX_EMPTY interrupt.
	 */
	IntrStatus = XQspiPs_ReadReg(QspiPtr->Config.BaseAddress,
				      XQSPIPS_SR_OFFSET);
	XQspiPs_WriteReg(QspiPtr->Config.BaseAddress, XQSPIPS_SR_OFFSET,
			  (IntrStatus & XQSPIPS_IXR_WR_TO_CLR_MASK));
	XQspiPs_WriteReg(QspiPtr->Config.BaseAddress, XQSPIPS_IDR_OFFSET,
			XQSPIPS_IXR_TXOW_MASK | XQSPIPS_IXR_RXNEMPTY_MASK |
			XQSPIPS_IXR_RXOVR_MASK | XQSPIPS_IXR_TXUF_MASK);

	if ((IntrStatus & XQSPIPS_IXR_TXOW_MASK) ||
		(IntrStatus & XQSPIPS_IXR_RXNEMPTY_MASK)) {

		/*
		 * Rx FIFO has just reached threshold no. of entries.
		 * Read threshold no. of entries from RX FIFO
		 * Another possiblity of entering this loop is when
		 * the last byte has been transmitted and TX FIFO is empty,
		 * in which case, read all the data from RX FIFO.
		 * Always get the received data, but only fill the
		 * receive buffer if it is not null (it can be null when
		 * the device does not care to receive data).
		 */
		TransCount = QspiPtr->RequestedBytes - QspiPtr->RemainingBytes;
		if (TransCount % 4) {
			TransCount = TransCount/4 + 1;
		} else {
			TransCount = TransCount/4;
		}

		while ((Count < TransCount) &&
			(Count < XQSPIPS_RXFIFO_THRESHOLD_OPT)) {

			if (QspiPtr->RecvBufferPtr != NULL) {
				if (QspiPtr->RequestedBytes < 4) {
					Data = XQspiPs_ReadReg(QspiPtr->Config.BaseAddress,
						XQSPIPS_RXD_OFFSET);
					XQspiPs_GetReadData(QspiPtr, Data,
						QspiPtr->RequestedBytes);
				} else {
					(*(u32 *)QspiPtr->RecvBufferPtr) =
						XQspiPs_ReadReg(QspiPtr->Config.BaseAddress,
						XQSPIPS_RXD_OFFSET);
					QspiPtr->RecvBufferPtr += 4;
					QspiPtr->RequestedBytes -= 4;
					if (QspiPtr->RequestedBytes < 0) {
						QspiPtr->RequestedBytes = 0;
					}
				}
			} else {
				XQspiPs_ReadReg(QspiPtr->Config.BaseAddress,
						XQSPIPS_RXD_OFFSET);
				QspiPtr->RequestedBytes -= 4;
				if (QspiPtr->RequestedBytes < 0) {
					QspiPtr->RequestedBytes = 0;
				}

			}
			Count++;
		}
		Count = 0;
		/*
		 * Interrupt asserted as TX_OW got asserted
		 * See if there is more data to send.
		 * Fill TX FIFO with RX threshold no. of entries or
		 * remaining entries (in case that is less than threshold)
		 */
		while ((QspiPtr->RemainingBytes > 0) &&
			(Count < XQSPIPS_RXFIFO_THRESHOLD_OPT)) {
			/*
			 * Send more data.
			 */
			XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
				XQSPIPS_TXD_00_OFFSET,
				*((u32 *)QspiPtr->SendBufferPtr));
			QspiPtr->SendBufferPtr += 4;
			QspiPtr->RemainingBytes -= 4;
			if (QspiPtr->RemainingBytes < 0) {
				QspiPtr->RemainingBytes = 0;
			}

			Count++;
		}

		if ((QspiPtr->RemainingBytes == 0) &&
			(QspiPtr->RequestedBytes == 0)) {
			/*
			 * No more data to send.  Disable the interrupt
			 * and inform the upper layer software that the
			 * transfer is done. The interrupt will be re-enabled
			 * when another transfer is initiated.
			 */
			XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
					  XQSPIPS_IDR_OFFSET,
					  XQSPIPS_IXR_RXNEMPTY_MASK |
					  XQSPIPS_IXR_TXOW_MASK |
					  XQSPIPS_IXR_RXOVR_MASK |
					  XQSPIPS_IXR_TXUF_MASK);

			/*
			 * If the Slave select is being manually controlled,
			 * disable it because the transfer is complete.
			 */
			if (XQspiPs_IsManualChipSelect(InstancePtr)) {
				ConfigReg = XQspiPs_ReadReg(
						QspiPtr->Config.BaseAddress,
						XQSPIPS_CR_OFFSET);
				ConfigReg |= XQSPIPS_CR_SSCTRL_MASK;
				XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
						  XQSPIPS_CR_OFFSET,
						   ConfigReg);
			}

			/*
			 * Clear the busy flag.
			 */
			QspiPtr->IsBusy = FALSE;

			/*
			 * Disable the device.
			 */
			XQspiPs_Disable(QspiPtr);

			/*
			 * Reset the RX FIFO threshold to one
			 */
			XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
				XQSPIPS_RXWR_OFFSET, XQSPIPS_RXWR_RESET_VALUE);

			QspiPtr->StatusHandler(QspiPtr->StatusRef,
						XST_SPI_TRANSFER_DONE,
						QspiPtr->RequestedBytes);
		} else {
			/*
			 * Enable the TXOW interrupt.
			 */
			XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
					 XQSPIPS_IER_OFFSET,
					 XQSPIPS_IXR_RXNEMPTY_MASK |
					 XQSPIPS_IXR_TXOW_MASK |
					 XQSPIPS_IXR_RXOVR_MASK |
					 XQSPIPS_IXR_TXUF_MASK);
			/*
			 * If, in Manual Start mode, start the transfer.
			 */
			if (XQspiPs_IsManualStart(QspiPtr)) {
				ConfigReg = XQspiPs_ReadReg(
					QspiPtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET);
				ConfigReg |= XQSPIPS_CR_MANSTRT_MASK;
				XQspiPs_WriteReg(
					QspiPtr->Config.BaseAddress,
					 XQSPIPS_CR_OFFSET, ConfigReg);
			}
		}
	}

	/*
	 * Check for overflow and underflow errors.
	 */
	if (IntrStatus & XQSPIPS_IXR_RXOVR_MASK) {
		BytesDone = QspiPtr->RequestedBytes - QspiPtr->RemainingBytes;
		QspiPtr->IsBusy = FALSE;

		/*
		 * If the Slave select lines is being manually controlled,
		 * disable it because the transfer is complete.
		 */
		if (XQspiPs_IsManualChipSelect(InstancePtr)) {
			ConfigReg = XQspiPs_ReadReg(
					QspiPtr->Config.BaseAddress,
					XQSPIPS_CR_OFFSET);
			ConfigReg |= XQSPIPS_CR_SSCTRL_MASK;
			XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
				XQSPIPS_CR_OFFSET, ConfigReg);
		}

		/*
		 * Disable the device.
		 */
		XQspiPs_Disable(QspiPtr);

		/*
		 * Reset the RX FIFO threshold to one
		 */
		XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
			XQSPIPS_RXWR_OFFSET, XQSPIPS_RXWR_RESET_VALUE);

		QspiPtr->StatusHandler(QspiPtr->StatusRef,
			XST_SPI_RECEIVE_OVERRUN, BytesDone);
	}

	if (IntrStatus & XQSPIPS_IXR_TXUF_MASK) {
		BytesDone = QspiPtr->RequestedBytes - QspiPtr->RemainingBytes;

		QspiPtr->IsBusy = FALSE;
		/*
		 * If the Slave select lines is being manually controlled,
		 * disable it because the transfer is complete.
		 */
		if (XQspiPs_IsManualChipSelect(InstancePtr)) {
			ConfigReg = XQspiPs_ReadReg(
					QspiPtr->Config.BaseAddress,
					XQSPIPS_CR_OFFSET);
			ConfigReg |= XQSPIPS_CR_SSCTRL_MASK;
			XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
					  XQSPIPS_CR_OFFSET, ConfigReg);
		}

		/*
		 * Disable the device.
		 */
		XQspiPs_Disable(QspiPtr);

		/*
		 * Reset the RX FIFO threshold to one
		 */
		XQspiPs_WriteReg(QspiPtr->Config.BaseAddress,
			XQSPIPS_RXWR_OFFSET, XQSPIPS_RXWR_RESET_VALUE);

		QspiPtr->StatusHandler(QspiPtr->StatusRef,
				      XST_SPI_TRANSMIT_UNDERRUN, BytesDone);
	}
}


/*****************************************************************************/
/**
*
* Copies data from Data to the Receive buffer.
*
* @param	InstancePtr is a pointer to the XQspiPs instance.
* @param	Data is the data which needs to be copied to the Rx buffer.
* @param	Size is the number of bytes to be copied to the Receive buffer.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XQspiPs_GetReadData(XQspiPs *InstancePtr, u32 Data, u8 Size)
{
	u8 DataByte3;

	if (InstancePtr->RecvBufferPtr) {
		switch (Size) {
		case 1:
			if (InstancePtr->ShiftReadData == 1) {
				*((u8 *)InstancePtr->RecvBufferPtr) =
					((Data & 0xFF000000) >> 24);
			} else {
				*((u8 *)InstancePtr->RecvBufferPtr) =
					(Data & 0xFF);
			}
			InstancePtr->RecvBufferPtr += 1;
			break;
		case 2:
			if (InstancePtr->ShiftReadData == 1) {
				*((u16 *)InstancePtr->RecvBufferPtr) =
					((Data & 0xFFFF0000) >> 16);
			} else 	{
				*((u16 *)InstancePtr->RecvBufferPtr) =
					(Data & 0xFFFF);
			}
			InstancePtr->RecvBufferPtr += 2;
			break;
		case 3:
			if (InstancePtr->ShiftReadData == 1) {
				*((u16 *)InstancePtr->RecvBufferPtr) =
					((Data & 0x00FFFF00) >> 8);
				InstancePtr->RecvBufferPtr += 2;
				DataByte3 = ((Data & 0xFF000000) >> 24);
				*((u8 *)InstancePtr->RecvBufferPtr) = DataByte3;
			} else {
				*((u16 *)InstancePtr->RecvBufferPtr) =
					(Data & 0xFFFF);
				InstancePtr->RecvBufferPtr += 2;
				DataByte3 = ((Data & 0x00FF0000) >> 16);
				*((u8 *)InstancePtr->RecvBufferPtr) = DataByte3;
			}
			InstancePtr->RecvBufferPtr += 1;
			break;
		default:
			/* This will never execute */
			break;
		}
	}
	InstancePtr->ShiftReadData  = 0;
	InstancePtr->RequestedBytes -= Size;
	if (InstancePtr->RequestedBytes < 0) {
		InstancePtr->RequestedBytes = 0;
	}
}
/** @} */
