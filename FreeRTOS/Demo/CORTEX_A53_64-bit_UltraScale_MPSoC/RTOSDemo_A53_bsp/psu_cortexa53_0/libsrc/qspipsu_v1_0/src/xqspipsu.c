/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xqspipsu.c
*
* This file implements the functions required to use the QSPIPSU hardware to
* perform a transfer. These are accessible to the user via xqspipsu.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 1.0   hk  08/21/14 First release
*       sk  03/13/15 Added IO mode support.
*       hk  03/18/15 Switch to I/O mode before clearing RX FIFO.
*                    Clear and disbale DMA interrupts/status in abort.
*                    Use DMA DONE bit instead of BUSY as recommended.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xqspipsu.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/
static void StubStatusHandler(void *CallBackRef, u32 StatusEvent,
			unsigned ByteCount);
static inline u32 XQspiPsu_SelectSpiMode(u8 SpiMode);
static inline void XQspiPsu_TXRXSetup(XQspiPsu *InstancePtr, XQspiPsu_Msg *Msg,
			u32 *GenFifoEntry);
static inline void XQspiPsu_FillTxFifo(XQspiPsu *InstancePtr,
			XQspiPsu_Msg *Msg, int Size);
static inline void XQspiPsu_SetupRxDma(XQspiPsu *InstancePtr,
			XQspiPsu_Msg *Msg);
static inline void XQspiPsu_GenFifoEntryCSAssert(XQspiPsu *InstancePtr);
static inline int XQspiPsu_GenFifoEntryData(XQspiPsu *InstancePtr,
			XQspiPsu_Msg *Msg, int Index);
static inline void XQspiPsu_GenFifoEntryCSDeAssert(XQspiPsu *InstancePtr);
static inline void XQspiPsu_ReadRxFifo(XQspiPsu *InstancePtr,
			XQspiPsu_Msg *Msg, int Size);

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
*
* Initializes a specific XQspiPsu instance such that the driver is ready to use.
*
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	ConfigPtr is a reference to a structure containing information
*		about a specific QSPIPSU device. This function initializes an
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
int XQspiPsu_CfgInitialize(XQspiPsu *InstancePtr, XQspiPsu_Config *ConfigPtr,
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

	/* Set some default values. */
	InstancePtr->IsBusy = FALSE;

	InstancePtr->Config.BaseAddress = EffectiveAddr + XQSPIPSU_OFFSET;
	InstancePtr->Config.ConnectionMode = ConfigPtr->ConnectionMode;
	InstancePtr->StatusHandler = StubStatusHandler;

	/* Other instance variable initializations */
	InstancePtr->SendBufferPtr = NULL;
	InstancePtr->RecvBufferPtr = NULL;
	InstancePtr->GenFifoBufferPtr = NULL;
	InstancePtr->TxBytes = 0;
	InstancePtr->RxBytes = 0;
	InstancePtr->GenFifoEntries = 0;
	InstancePtr->ReadMode = XQSPIPSU_READMODE_DMA;
	InstancePtr->GenFifoCS = XQSPIPSU_GENFIFO_CS_LOWER;
	InstancePtr->GenFifoBus = XQSPIPSU_GENFIFO_BUS_LOWER;
	InstancePtr->IsUnaligned = 0;

	/* Select QSPIPSU */
	XQspiPsu_Select(InstancePtr);

	/*
	 * Reset the QSPIPSU device to get it into its initial state. It is
	 * expected that device configuration will take place after this
	 * initialization is done, but before the device is started.
	 */
	XQspiPsu_Reset(InstancePtr);

	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* Resets the QSPIPSU device. Reset must only be called after the driver has
* been initialized. Any data transfer that is in progress is aborted.
*
* The upper layer software is responsible for re-configuring (if necessary)
* and restarting the QSPIPSU device after the reset.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XQspiPsu_Reset(XQspiPsu *InstancePtr)
{
	u32 ConfigReg;

	Xil_AssertVoid(InstancePtr != NULL);

	/* Abort any transfer that is in progress */
	XQspiPsu_Abort(InstancePtr);

	/* Default value to config register */
	ConfigReg = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_CFG_OFFSET);

	/* DMA mode */
	ConfigReg &= ~XQSPIPSU_CFG_MODE_EN_MASK;
	ConfigReg |= XQSPIPSU_CFG_MODE_EN_DMA_MASK;
	/* Manual start */
	ConfigReg |= XQSPIPSU_CFG_GEN_FIFO_START_MODE_MASK;
	/* Little endain by default */
	ConfigReg &= ~XQSPIPSU_CFG_ENDIAN_MASK;
	/* Disable poll timeout */
	ConfigReg &= ~XQSPIPSU_CFG_EN_POLL_TO_MASK;
	/* Set hold bit */
	ConfigReg |= XQSPIPSU_CFG_WP_HOLD_MASK;
	/* Clear prescalar by default */
	ConfigReg &= ~XQSPIPSU_CFG_BAUD_RATE_DIV_MASK;
	/* CPOL CPHA 00 */
	ConfigReg &= ~XQSPIPSU_CFG_CLK_PHA_MASK;
	ConfigReg &= ~XQSPIPSU_CFG_CLK_POL_MASK;

	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_CFG_OFFSET, ConfigReg);

	/* Set by default to allow for high frequencies */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_LPBK_DLY_ADJ_OFFSET,
		XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_LPBK_DLY_ADJ_OFFSET) |
			XQSPIPSU_LPBK_DLY_ADJ_USE_LPBK_MASK);

	/* Reset thresholds */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_TX_THRESHOLD_OFFSET,
		XQSPIPSU_TX_FIFO_THRESHOLD_RESET_VAL);
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_RX_THRESHOLD_OFFSET,
		XQSPIPSU_RX_FIFO_THRESHOLD_RESET_VAL);
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_GF_THRESHOLD_OFFSET,
		XQSPIPSU_GEN_FIFO_THRESHOLD_RESET_VAL);

	/* DMA init */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_QSPIDMA_DST_CTRL_OFFSET,
			XQSPIPSU_QSPIDMA_DST_CTRL_RESET_VAL);

}

/*****************************************************************************/
/**
*
* Aborts a transfer in progress by
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
*
* @return	None.
*
* @note
*
******************************************************************************/
void XQspiPsu_Abort(XQspiPsu *InstancePtr)
{

	u32 IntrStatus, ConfigReg;

	IntrStatus = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
					XQSPIPSU_ISR_OFFSET);

	/* Clear and disable interrupts */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_ISR_OFFSET, IntrStatus | XQSPIPSU_ISR_WR_TO_CLR_MASK);
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_QSPIDMA_DST_I_STS_OFFSET,
		XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				XQSPIPSU_QSPIDMA_DST_I_STS_OFFSET));
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_QSPIDMA_DST_STS_OFFSET,
			XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				XQSPIPSU_QSPIDMA_DST_STS_OFFSET) |
				XQSPIPSU_QSPIDMA_DST_STS_WTC);
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_IDR_OFFSET, XQSPIPSU_IDR_ALL_MASK);
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_QSPIDMA_DST_I_DIS_OFFSET,
			XQSPIPSU_QSPIDMA_DST_INTR_ALL_MASK);

	/* Clear FIFO */
	if((XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_ISR_OFFSET) & XQSPIPSU_ISR_RXEMPTY_MASK)) {
		XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_FIFO_CTRL_OFFSET,
			XQSPIPSU_FIFO_CTRL_RST_TX_FIFO_MASK |
			XQSPIPSU_FIFO_CTRL_RST_GEN_FIFO_MASK);
	}

	/*
	 * Switch to IO mode to Clear RX FIFO. This is becuase of DMA behaviour
	 * where it waits on RX empty and goes busy assuming there is data
	 * to be transfered even if there is no request.
	 */
	if ((IntrStatus & XQSPIPSU_ISR_RXEMPTY_MASK) != 0) {
		ConfigReg = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
					XQSPIPSU_CFG_OFFSET);
		ConfigReg &= ~XQSPIPSU_CFG_MODE_EN_MASK;
		XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XQSPIPSU_CFG_OFFSET, ConfigReg);

		XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XQSPIPSU_FIFO_CTRL_OFFSET,
				XQSPIPSU_FIFO_CTRL_RST_RX_FIFO_MASK);

		if (InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA) {
			ConfigReg |= XQSPIPSU_CFG_MODE_EN_DMA_MASK;
			XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
					XQSPIPSU_CFG_OFFSET, ConfigReg);
		}
	}

	/* Disable QSPIPSU */
	XQspiPsu_Disable(InstancePtr);

	InstancePtr->TxBytes = 0;
	InstancePtr->RxBytes = 0;
	InstancePtr->GenFifoEntries = 0;
	InstancePtr->IsBusy = FALSE;
}

/*****************************************************************************/
/**
*
* This function performs a transfer on the bus in polled mode. The messages
* passed are all transferred on the bus between one CS assert and de-assert.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Msg is a pointer to the structure containing transfer data.
* @param	NumMsg is the number of messages to be transferred.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if transfer fails.
*		- XST_DEVICE_BUSY if a transfer is already in progress.
*
* @note		None.
*
******************************************************************************/
int XQspiPsu_PolledTransfer(XQspiPsu *InstancePtr, XQspiPsu_Msg *Msg,
				unsigned NumMsg)
{
	u32 StatusReg;
	u32 ConfigReg;
	int Index;
	u8 IsManualStart = FALSE;
	u32 QspiPsuStatusReg, DmaStatusReg;
	u32 BaseAddress;
	int Status;
	u32 RxThr;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	for (Index = 0; Index < NumMsg; Index++) {
		Xil_AssertNonvoid(Msg[Index].ByteCount > 0);
	}

	/* Check whether there is another transfer in progress. Not thread-safe */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

	/*
	 * Set the busy flag, which will be cleared when the transfer is
	 * entirely done.
	 */
	InstancePtr->IsBusy = TRUE;

	BaseAddress = InstancePtr->Config.BaseAddress;

	/* Start if manual start */
	IsManualStart = XQspiPsu_IsManualStart(InstancePtr);

	/* Enable */
	XQspiPsu_Enable(InstancePtr);

	/* Select slave */
	XQspiPsu_GenFifoEntryCSAssert(InstancePtr);

	/* list */
	for (Index = 0; Index < NumMsg; Index++) {

GENFIFO:
		Status = XQspiPsu_GenFifoEntryData(InstancePtr, Msg, Index);
		if (Status != XST_SUCCESS) {
			return Status;
		}

		if (IsManualStart) {
			XQspiPsu_WriteReg(BaseAddress, XQSPIPSU_CFG_OFFSET,
				XQspiPsu_ReadReg(BaseAddress,
					XQSPIPSU_CFG_OFFSET) |
					XQSPIPSU_CFG_START_GEN_FIFO_MASK);
		}

		/* Use thresholds here */
		/* If there is more data to be transmitted */
		do {
			QspiPsuStatusReg = XQspiPsu_ReadReg(BaseAddress,
						XQSPIPSU_ISR_OFFSET);

			/* Transmit more data if left */
			if ((QspiPsuStatusReg & XQSPIPSU_ISR_TXNOT_FULL_MASK) &&
				(Msg[Index].TxBfrPtr != NULL) &&
				(InstancePtr->TxBytes > 0)) {
				XQspiPsu_FillTxFifo(InstancePtr, &Msg[Index],
						XQSPIPSU_TXD_DEPTH);
			}

			/* Check if DMA RX is complete and update RxBytes */
			if ((InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA) &&
				(Msg[Index].RxBfrPtr != NULL)) {
				u32 DmaIntrSts;
				DmaIntrSts = XQspiPsu_ReadReg(BaseAddress,
								XQSPIPSU_QSPIDMA_DST_I_STS_OFFSET);
				if (DmaIntrSts & XQSPIPSU_QSPIDMA_DST_I_STS_DONE_MASK) {
					XQspiPsu_WriteReg(BaseAddress,
						XQSPIPSU_QSPIDMA_DST_I_STS_OFFSET,
						DmaIntrSts);
					/* Read remaining bytes using IO mode */
					if(InstancePtr->RxBytes % 4 != 0 ) {
						XQspiPsu_WriteReg(BaseAddress,
							XQSPIPSU_CFG_OFFSET,
							(XQspiPsu_ReadReg(BaseAddress,
							XQSPIPSU_CFG_OFFSET) &
							~XQSPIPSU_CFG_MODE_EN_MASK));
						InstancePtr->ReadMode = XQSPIPSU_READMODE_IO;
						Msg[Index].ByteCount =
							(InstancePtr->RxBytes % 4);
						Msg[Index].RxBfrPtr += (InstancePtr->RxBytes -
								(InstancePtr->RxBytes % 4));
						InstancePtr->IsUnaligned = 1;
						goto GENFIFO;
					}
					InstancePtr->RxBytes = 0;
				}
			} else if (Msg[Index].RxBfrPtr != NULL) {
				/* Check if PIO RX is complete and update RxBytes */
				RxThr = XQspiPsu_ReadReg(BaseAddress,
						XQSPIPSU_RX_THRESHOLD_OFFSET);
				if ((QspiPsuStatusReg & XQSPIPSU_ISR_RXNEMPTY_MASK)
								!= 0U) {
					XQspiPsu_ReadRxFifo(InstancePtr,
							&Msg[Index], RxThr);

				} else if ((QspiPsuStatusReg &
					XQSPIPSU_ISR_GENFIFOEMPTY_MASK) != 0U) {
					    XQspiPsu_ReadRxFifo(InstancePtr,
						    &Msg[Index], InstancePtr->RxBytes);
				}
			}
		} while (!(QspiPsuStatusReg & XQSPIPSU_ISR_GENFIFOEMPTY_MASK) ||
			(InstancePtr->TxBytes != 0) ||
			!(QspiPsuStatusReg & XQSPIPSU_ISR_TXEMPTY_MASK) ||
			(InstancePtr->RxBytes != 0));

		if(InstancePtr->IsUnaligned) {
			InstancePtr->IsUnaligned = 0;
			XQspiPsu_WriteReg(BaseAddress,
				XQSPIPSU_CFG_OFFSET, (XQspiPsu_ReadReg(
				BaseAddress,
				XQSPIPSU_CFG_OFFSET) |
				XQSPIPSU_CFG_MODE_EN_DMA_MASK));
			InstancePtr->ReadMode = XQSPIPSU_READMODE_DMA;
		}
	}

	/* De-select slave */
	XQspiPsu_GenFifoEntryCSDeAssert(InstancePtr);

	if (IsManualStart) {
		XQspiPsu_WriteReg(BaseAddress, XQSPIPSU_CFG_OFFSET,
			XQspiPsu_ReadReg(BaseAddress, XQSPIPSU_CFG_OFFSET) |
				XQSPIPSU_CFG_START_GEN_FIFO_MASK);
	}

	QspiPsuStatusReg = XQspiPsu_ReadReg(BaseAddress, XQSPIPSU_ISR_OFFSET);
	while (!(QspiPsuStatusReg & XQSPIPSU_ISR_GENFIFOEMPTY_MASK)) {
		QspiPsuStatusReg = XQspiPsu_ReadReg(BaseAddress,
						XQSPIPSU_ISR_OFFSET);
	}

	/* Clear the busy flag. */
	InstancePtr->IsBusy = FALSE;

	/* Disable the device. */
	XQspiPsu_Disable(InstancePtr);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function initiates a transfer on the bus and enables interrupts.
* The transfer is completed by the interrupt handler. The messages passed are
* all transferred on the bus between one CS assert and de-assert.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Msg is a pointer to the structure containing transfer data.
* @param	NumMsg is the number of messages to be transferred.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if transfer fails.
*		- XST_DEVICE_BUSY if a transfer is already in progress.
*
* @note		None.
*
******************************************************************************/
int XQspiPsu_InterruptTransfer(XQspiPsu *InstancePtr, XQspiPsu_Msg *Msg,
				unsigned NumMsg)
{
	u32 StatusReg;
	u32 ConfigReg;
	int Index;
	u8 IsManualStart = FALSE;
	u32 BaseAddress;
	int Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	for (Index = 0; Index < NumMsg; Index++) {
		Xil_AssertNonvoid(Msg[Index].ByteCount > 0);
	}

	/* Check whether there is another transfer in progress. Not thread-safe */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

	/*
	 * Set the busy flag, which will be cleared when the transfer is
	 * entirely done.
	 */
	InstancePtr->IsBusy = TRUE;

	BaseAddress = InstancePtr->Config.BaseAddress;

	/* Start if manual start */
	IsManualStart = XQspiPsu_IsManualStart(InstancePtr);

	InstancePtr->Msg = Msg;
	InstancePtr->NumMsg = NumMsg;
	InstancePtr->MsgCnt = 0;

	/* Enable */
	XQspiPsu_Enable(InstancePtr);

	/* Select slave */
	XQspiPsu_GenFifoEntryCSAssert(InstancePtr);

	/* This might not work if not manual start */
	/* Put first message in FIFO along with the above slave select */
	Status = XQspiPsu_GenFifoEntryData(InstancePtr, Msg, 0);
	if (Status != XST_SUCCESS) {
		return Status;
	}

	if (IsManualStart) {
		XQspiPsu_WriteReg(BaseAddress, XQSPIPSU_CFG_OFFSET,
			XQspiPsu_ReadReg(BaseAddress, XQSPIPSU_CFG_OFFSET) |
				XQSPIPSU_CFG_START_GEN_FIFO_MASK);
	}

	/* Enable interrupts */
	XQspiPsu_WriteReg(BaseAddress, XQSPIPSU_IER_OFFSET,
		XQSPIPSU_IER_TXNOT_FULL_MASK | XQSPIPSU_IER_TXEMPTY_MASK |
		XQSPIPSU_IER_RXNEMPTY_MASK | XQSPIPSU_IER_GENFIFOEMPTY_MASK);

	if (InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA) {
		XQspiPsu_WriteReg(BaseAddress, XQSPIPSU_QSPIDMA_DST_I_EN_OFFSET,
				XQSPIPSU_QSPIDMA_DST_I_EN_DONE_MASK);
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* Handles interrupt based transfers by acting on GENFIFO and DMA interurpts.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if transfer fails.
*
* @note		None.
*
******************************************************************************/
int XQspiPsu_InterruptHandler(XQspiPsu *InstancePtr)
{
	u8 IsManualStart = FALSE;
	u32 QspiPsuStatusReg, DmaIntrStatusReg;
	u32 BaseAddress;
	XQspiPsu_Msg *Msg;
	int NumMsg;
	int MsgCnt;
	u8 DeltaMsgCnt = 0;
	u32 RxThr;

	Xil_AssertNonvoid(InstancePtr != NULL);

	BaseAddress = InstancePtr->Config.BaseAddress;
	Msg = InstancePtr->Msg;
	NumMsg = InstancePtr->NumMsg;
	MsgCnt = InstancePtr->MsgCnt;

	/* Start if manual start */
	IsManualStart = XQspiPsu_IsManualStart(InstancePtr);

	/* QSPIPSU Intr cleared on read */
	QspiPsuStatusReg = XQspiPsu_ReadReg(BaseAddress, XQSPIPSU_ISR_OFFSET);
	if (InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA) {
		/* DMA Intr write to clear */
		DmaIntrStatusReg = XQspiPsu_ReadReg(BaseAddress,
					XQSPIPSU_QSPIDMA_DST_I_STS_OFFSET);

		XQspiPsu_WriteReg(BaseAddress,
			XQSPIPSU_QSPIDMA_DST_I_STS_OFFSET, DmaIntrStatusReg);
	}
	if ((QspiPsuStatusReg & XQSPIPSU_ISR_POLL_TIME_EXPIRE_MASK) ||
		(DmaIntrStatusReg & XQSPIPSU_QSPIDMA_DST_INTR_ERR_MASK)) {
		/* Call status handler to indicate error */
		InstancePtr->StatusHandler(InstancePtr->StatusRef,
					XST_SPI_COMMAND_ERROR, 0);
	}

	/* Fill more data to be txed if required */
	if ((MsgCnt < NumMsg) && (Msg[MsgCnt].TxBfrPtr != NULL) &&
		(QspiPsuStatusReg & XQSPIPSU_ISR_TXNOT_FULL_MASK) &&
		(InstancePtr->TxBytes > 0)) {
		XQspiPsu_FillTxFifo(InstancePtr, &Msg[MsgCnt],
				XQSPIPSU_TXD_DEPTH);
	}

	/*
	 * Check if the entry is ONLY TX and increase MsgCnt.
	 * This is to allow TX and RX together in one entry - corner case.
	 */
	if ((MsgCnt < NumMsg) && (Msg[MsgCnt].TxBfrPtr != NULL) &&
		(QspiPsuStatusReg & XQSPIPSU_ISR_TXEMPTY_MASK) &&
		(QspiPsuStatusReg & XQSPIPSU_ISR_GENFIFOEMPTY_MASK) &&
		(InstancePtr->TxBytes == 0) &&
		(Msg[MsgCnt].RxBfrPtr == NULL)) {
		MsgCnt += 1;
		DeltaMsgCnt = 1;
	}

	if (InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA &&
		(MsgCnt < NumMsg) && (Msg[MsgCnt].RxBfrPtr != NULL)) {
		if ((DmaIntrStatusReg & XQSPIPSU_QSPIDMA_DST_I_STS_DONE_MASK)) {
				/* Read remaining bytes using IO mode */
			if(InstancePtr->RxBytes % 4 != 0 ) {
				XQspiPsu_WriteReg(BaseAddress,
					XQSPIPSU_CFG_OFFSET, (XQspiPsu_ReadReg(
					BaseAddress, XQSPIPSU_CFG_OFFSET) &
					~XQSPIPSU_CFG_MODE_EN_MASK));
				InstancePtr->ReadMode = XQSPIPSU_READMODE_IO;
				Msg[MsgCnt].ByteCount = (InstancePtr->RxBytes % 4);
				Msg[MsgCnt].RxBfrPtr += (InstancePtr->RxBytes -
						(InstancePtr->RxBytes % 4));
				InstancePtr->IsUnaligned = 1;
				XQspiPsu_GenFifoEntryData(InstancePtr, Msg,
						MsgCnt);
				if(IsManualStart) {
					XQspiPsu_WriteReg(BaseAddress,
						XQSPIPSU_CFG_OFFSET,
						XQspiPsu_ReadReg(BaseAddress,
						XQSPIPSU_CFG_OFFSET) |
						XQSPIPSU_CFG_START_GEN_FIFO_MASK);
				}
			}
			else {
				InstancePtr->RxBytes = 0;
				MsgCnt += 1;
				DeltaMsgCnt = 1;
			}
		}
	} else if ((MsgCnt < NumMsg) && (Msg[MsgCnt].RxBfrPtr != NULL)) {
		RxThr = XQspiPsu_ReadReg(BaseAddress,
					XQSPIPSU_RX_THRESHOLD_OFFSET);
		if (InstancePtr->RxBytes != 0) {
			if ((QspiPsuStatusReg & XQSPIPSU_ISR_RXNEMPTY_MASK)
							!= 0) {
				XQspiPsu_ReadRxFifo(InstancePtr, &Msg[MsgCnt],
					RxThr);
			} else if ((QspiPsuStatusReg &
				XQSPIPSU_ISR_GENFIFOEMPTY_MASK) != 0) {
				XQspiPsu_ReadRxFifo(InstancePtr, &Msg[MsgCnt],
					InstancePtr->RxBytes);
			}
			if (InstancePtr->RxBytes == 0) {
				MsgCnt += 1;
				DeltaMsgCnt = 1;
			}
		}
	}

	/*
	 * Dummy byte transfer
	 * MsgCnt < NumMsg check is to ensure is it a valid dummy cycle message
	 * If one of the above conditions increased MsgCnt, then
	 * the new message is yet to be placed in the FIFO; hence !DeltaMsgCnt.
	 */
	if ((MsgCnt < NumMsg) && !DeltaMsgCnt &&
		(Msg[MsgCnt].RxBfrPtr == NULL) &&
		(Msg[MsgCnt].TxBfrPtr == NULL) &&
		(QspiPsuStatusReg & XQSPIPSU_ISR_GENFIFOEMPTY_MASK)) {
		MsgCnt += 1;
		DeltaMsgCnt = 1;
	}
	InstancePtr->MsgCnt = MsgCnt;

	/*
	 * DeltaMsgCnt is to handle conditions where genfifo empty can be set
	 * while tx is still not empty or rx dma is not yet done.
	 * MsgCnt > NumMsg indicates CS de-assert entry was also executed.
	 */
	if ((QspiPsuStatusReg & XQSPIPSU_ISR_GENFIFOEMPTY_MASK) &&
		(DeltaMsgCnt || (MsgCnt > NumMsg))) {
		if (MsgCnt < NumMsg) {
			if(InstancePtr->IsUnaligned) {
				InstancePtr->IsUnaligned = 0;
				XQspiPsu_WriteReg(InstancePtr->Config.
					BaseAddress, XQSPIPSU_CFG_OFFSET,
					(XQspiPsu_ReadReg(InstancePtr->Config.
					BaseAddress, XQSPIPSU_CFG_OFFSET) |
					XQSPIPSU_CFG_MODE_EN_DMA_MASK));
				InstancePtr->ReadMode = XQSPIPSU_READMODE_DMA;
			}
			/* This might not work if not manual start */
			XQspiPsu_GenFifoEntryData(InstancePtr, Msg, MsgCnt);

			if (IsManualStart) {
				XQspiPsu_WriteReg(BaseAddress,
					XQSPIPSU_CFG_OFFSET,
					XQspiPsu_ReadReg(BaseAddress,
						XQSPIPSU_CFG_OFFSET) |
						XQSPIPSU_CFG_START_GEN_FIFO_MASK);
			}
		} else if (MsgCnt == NumMsg) {
			/* This is just to keep track of the de-assert entry */
			MsgCnt += 1;
			InstancePtr->MsgCnt = MsgCnt;

			/* De-select slave */
			XQspiPsu_GenFifoEntryCSDeAssert(InstancePtr);

			if (IsManualStart) {
				XQspiPsu_WriteReg(BaseAddress,
					XQSPIPSU_CFG_OFFSET,
					XQspiPsu_ReadReg(BaseAddress,
						XQSPIPSU_CFG_OFFSET) |
						XQSPIPSU_CFG_START_GEN_FIFO_MASK);
			}
		} else {
			/* Disable interrupts */
			XQspiPsu_WriteReg(BaseAddress, XQSPIPSU_IDR_OFFSET,
					XQSPIPSU_IER_TXNOT_FULL_MASK |
					XQSPIPSU_IER_TXEMPTY_MASK |
					XQSPIPSU_IER_RXNEMPTY_MASK |
					XQSPIPSU_IER_GENFIFOEMPTY_MASK);
			if (InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA) {
				XQspiPsu_WriteReg(BaseAddress,
					XQSPIPSU_QSPIDMA_DST_I_DIS_OFFSET,
					XQSPIPSU_QSPIDMA_DST_I_EN_DONE_MASK);
			}

			/* Clear the busy flag. */
			InstancePtr->IsBusy = FALSE;

			/* Disable the device. */
			XQspiPsu_Disable(InstancePtr);

			/* Call status handler to indicate completion */
			InstancePtr->StatusHandler(InstancePtr->StatusRef,
						XST_SPI_TRANSFER_DONE, 0);
		}
	}

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
* XST_SPI_RECEIVE_OVERRUN	The QSPIPSU device lost data. Data was received
*				but the receive data register/FIFO was full.
*
* </pre>
* @param	InstancePtr is a pointer to the XQspiPsu instance.
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
void XQspiPsu_SetStatusHandler(XQspiPsu *InstancePtr, void *CallBackRef,
				XQspiPsu_StatusHandler FuncPtr)
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
* Selects SPI mode - x1 or x2 or x4.
*
* @param	SpiMode - spi or dual or quad.
* @return	Mask to set desired SPI mode in GENFIFO entry.
*
* @note		None.
*
******************************************************************************/
static inline u32 XQspiPsu_SelectSpiMode(u8 SpiMode)
{
	u32 Mask;
	switch (SpiMode) {
		case XQSPIPSU_SELECT_MODE_DUALSPI:
			Mask = XQSPIPSU_GENFIFO_MODE_DUALSPI;
			break;
		case XQSPIPSU_SELECT_MODE_QUADSPI:
			Mask = XQSPIPSU_GENFIFO_MODE_QUADSPI;
			break;
		case XQSPIPSU_SELECT_MODE_SPI:
		default:
			Mask = XQSPIPSU_GENFIFO_MODE_SPI;
	}

	return Mask;
}

/*****************************************************************************/
/**
*
* This function checks the TX/RX buffers in the message and setups up the
* GENFIFO entries, TX FIFO or RX DMA as required.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Msg is a pointer to the structure containing transfer data.
* @param	GenFifoEntry is pointer to the variable in which GENFIFO mask
*		is returned to calling function
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void XQspiPsu_TXRXSetup(XQspiPsu *InstancePtr, XQspiPsu_Msg *Msg,
					u32 *GenFifoEntry)
{
	Xil_AssertVoid(InstancePtr != NULL);

	/* Transmit */
	if ((Msg->TxBfrPtr != NULL) && (Msg->RxBfrPtr == NULL)) {
		/* Setup data to be TXed */
		*GenFifoEntry |= XQSPIPSU_GENFIFO_DATA_XFER;
		*GenFifoEntry |= XQSPIPSU_GENFIFO_TX;
		InstancePtr->TxBytes = Msg->ByteCount;
		XQspiPsu_FillTxFifo(InstancePtr, Msg, XQSPIPSU_TXD_DEPTH);
		/* Discard RX data */
		*GenFifoEntry &= ~XQSPIPSU_GENFIFO_RX;
		InstancePtr->RxBytes = 0;
	}

	/* Receive */
	if ((Msg->TxBfrPtr == NULL) && (Msg->RxBfrPtr != NULL)) {
		/* TX auto fill */
		*GenFifoEntry &= ~XQSPIPSU_GENFIFO_TX;
		InstancePtr->TxBytes = 0;
		/* Setup RX */
		*GenFifoEntry |= XQSPIPSU_GENFIFO_DATA_XFER;
		*GenFifoEntry |= XQSPIPSU_GENFIFO_RX;
		InstancePtr->RxBytes = Msg->ByteCount;
		if (InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA) {
			XQspiPsu_SetupRxDma(InstancePtr, Msg);
		}
	}

	/* If only dummy is requested as a separate entry */
	if ((Msg->TxBfrPtr == NULL) && (Msg->RxBfrPtr == NULL)) {
		*GenFifoEntry |= XQSPIPSU_GENFIFO_DATA_XFER;
		*GenFifoEntry &= ~(XQSPIPSU_GENFIFO_TX | XQSPIPSU_GENFIFO_RX);
		InstancePtr->TxBytes = 0;
		InstancePtr->RxBytes = 0;
	}

	/* Dummy and cmd sent by upper layer to received data */
	if ((Msg->TxBfrPtr != NULL) && (Msg->RxBfrPtr != NULL)) {
		*GenFifoEntry |= XQSPIPSU_GENFIFO_DATA_XFER;
		*GenFifoEntry |= (XQSPIPSU_GENFIFO_TX | XQSPIPSU_GENFIFO_RX);
		InstancePtr->TxBytes = Msg->ByteCount;
		InstancePtr->RxBytes = Msg->ByteCount;
		XQspiPsu_FillTxFifo(InstancePtr, Msg, XQSPIPSU_TXD_DEPTH);
		/* Add check for DMA or PIO here */
		if (InstancePtr->ReadMode == XQSPIPSU_READMODE_DMA) {
			XQspiPsu_SetupRxDma(InstancePtr, Msg);
		}
	}
}

/*****************************************************************************/
/**
*
* Fills the TX FIFO as long as there is room in the FIFO or the bytes required
* to be transmitted.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Msg is a pointer to the structure containing transfer data.
* @param	Size is the number of bytes to be transmitted.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void XQspiPsu_FillTxFifo(XQspiPsu *InstancePtr,
					XQspiPsu_Msg *Msg, int Size)
{
	int Count = 0;
	u32 Data;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Msg->TxBfrPtr != NULL);

	while ((InstancePtr->TxBytes > 0) && (Count < Size)) {
		Data = *((u32*)Msg->TxBfrPtr);
		XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XQSPIPSU_TXD_OFFSET, Data);
		Msg->TxBfrPtr += 4;
		InstancePtr->TxBytes -= 4;
		Count++;
	}
	if (InstancePtr->TxBytes < 0)
		InstancePtr->TxBytes = 0;
}

/*****************************************************************************/
/**
*
* This function sets up the RX DMA operation.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Msg is a pointer to the structure containing transfer data.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void XQspiPsu_SetupRxDma(XQspiPsu *InstancePtr,
					XQspiPsu_Msg *Msg)
{
	int Remainder;
	int DmaRxBytes;
	u64 AddrTemp;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Msg->RxBfrPtr != NULL);

	AddrTemp = (u64)(INTPTR)(Msg->RxBfrPtr) &
				XQSPIPSU_QSPIDMA_DST_ADDR_MASK;
	/* Check for RXBfrPtr to be word aligned */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_QSPIDMA_DST_ADDR_OFFSET,
			(u32)AddrTemp);

	AddrTemp = AddrTemp >> 32;
	if (AddrTemp & 0xFFF) {
		XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XQSPIPSU_QSPIDMA_DST_ADDR_MSB_OFFSET,
				(u32)AddrTemp &
				XQSPIPSU_QSPIDMA_DST_ADDR_MSB_MASK);
	}

	Remainder = InstancePtr->RxBytes % 4;
	DmaRxBytes = InstancePtr->RxBytes;
	if (Remainder != 0) {
		/* This is done to make Dma bytes aligned */
		DmaRxBytes = InstancePtr->RxBytes - Remainder;
		Msg->ByteCount = DmaRxBytes;
	}

	/* Write no. of words to DMA DST SIZE */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XQSPIPSU_QSPIDMA_DST_SIZE_OFFSET, DmaRxBytes);

}

/*****************************************************************************/
/**
*
* This function writes the GENFIFO entry to assert CS.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void XQspiPsu_GenFifoEntryCSAssert(XQspiPsu *InstancePtr)
{
	u32 GenFifoEntry;

	GenFifoEntry = 0x0;
	GenFifoEntry &= ~(XQSPIPSU_GENFIFO_DATA_XFER | XQSPIPSU_GENFIFO_EXP);
	GenFifoEntry &= ~XQSPIPSU_GENFIFO_MODE_MASK;
	GenFifoEntry |= XQSPIPSU_GENFIFO_MODE_SPI;
	GenFifoEntry |= InstancePtr->GenFifoCS;
	GenFifoEntry &= ~XQSPIPSU_GENFIFO_BUS_MASK;
	GenFifoEntry |= InstancePtr->GenFifoBus;
	GenFifoEntry &= ~(XQSPIPSU_GENFIFO_TX | XQSPIPSU_GENFIFO_RX |
			XQSPIPSU_GENFIFO_STRIPE | XQSPIPSU_GENFIFO_POLL);
	GenFifoEntry |= XQSPIPSU_GENFIFO_CS_SETUP;

	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_GEN_FIFO_OFFSET, GenFifoEntry);
}

/*****************************************************************************/
/**
*
* This function writes the GENFIFO entries to transmit the messages requested.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Msg is a pointer to the structure containing transfer data.
* @param	Index of the current message to be handled.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if transfer fails.
*		- XST_DEVICE_BUSY if a transfer is already in progress.
*
* @note		None.
*
******************************************************************************/
static inline int XQspiPsu_GenFifoEntryData(XQspiPsu *InstancePtr,
						XQspiPsu_Msg *Msg, int Index)
{
	u32 GenFifoEntry;
	u32 BaseAddress;
	int TempCount;
	int ImmData;

	BaseAddress = InstancePtr->Config.BaseAddress;

	GenFifoEntry = 0x0;
	/* Bus width */
	GenFifoEntry &= ~XQSPIPSU_GENFIFO_MODE_MASK;
	GenFifoEntry |= XQspiPsu_SelectSpiMode(Msg[Index].BusWidth);

	GenFifoEntry |= InstancePtr->GenFifoCS;
	GenFifoEntry &= ~XQSPIPSU_GENFIFO_BUS_MASK;
	GenFifoEntry |= InstancePtr->GenFifoBus;

	/* Data */
	if (Msg[Index].Flags & XQSPIPSU_MSG_FLAG_STRIPE)
		GenFifoEntry |= XQSPIPSU_GENFIFO_STRIPE;
	else
		GenFifoEntry &= ~XQSPIPSU_GENFIFO_STRIPE;

	XQspiPsu_TXRXSetup(InstancePtr, &Msg[Index], &GenFifoEntry);

	if (Msg[Index].ByteCount < XQSPIPSU_GENFIFO_IMM_DATA_MASK) {
		GenFifoEntry &= ~XQSPIPSU_GENFIFO_IMM_DATA_MASK;
		GenFifoEntry |= Msg[Index].ByteCount;
		XQspiPsu_WriteReg(BaseAddress, XQSPIPSU_GEN_FIFO_OFFSET,
				GenFifoEntry);
	} else {
		TempCount = Msg[Index].ByteCount;
		u32 Exponent = 8;	/* 2^8 = 256 */

		/* Check for ByteCount upper limit - 2^28 for DMA */
		if (TempCount > XQSPIPSU_DMA_BYTES_MAX) {
			return XST_FAILURE;
		}

		ImmData = TempCount & 0xFF;
		/* Exponent entries */
		GenFifoEntry |= XQSPIPSU_GENFIFO_EXP;
		while (TempCount != 0) {
			if (TempCount & XQSPIPSU_GENFIFO_EXP_START) {
				GenFifoEntry &= ~XQSPIPSU_GENFIFO_IMM_DATA_MASK;
				GenFifoEntry |= Exponent;
				XQspiPsu_WriteReg(BaseAddress,
					XQSPIPSU_GEN_FIFO_OFFSET,
					GenFifoEntry);
			}
			TempCount = TempCount >> 1;
			Exponent++;
		}

		/* Immediate entry */
		GenFifoEntry &= ~XQSPIPSU_GENFIFO_EXP;
		if (ImmData & 0xFF) {
			GenFifoEntry &= ~XQSPIPSU_GENFIFO_IMM_DATA_MASK;
			GenFifoEntry |= ImmData & 0xFF;
			XQspiPsu_WriteReg(BaseAddress,
				XQSPIPSU_GEN_FIFO_OFFSET, GenFifoEntry);
		}
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function writes the GENFIFO entry to de-assert CS.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void XQspiPsu_GenFifoEntryCSDeAssert(XQspiPsu *InstancePtr)
{
	u32 GenFifoEntry;

	GenFifoEntry = 0x0;
	GenFifoEntry &= ~(XQSPIPSU_GENFIFO_DATA_XFER | XQSPIPSU_GENFIFO_EXP);
	GenFifoEntry &= ~XQSPIPSU_GENFIFO_MODE_MASK;
	GenFifoEntry |= XQSPIPSU_GENFIFO_MODE_SPI;
	GenFifoEntry &= ~XQSPIPSU_GENFIFO_BUS_MASK;
	GenFifoEntry |= InstancePtr->GenFifoBus;
	GenFifoEntry &= ~(XQSPIPSU_GENFIFO_TX | XQSPIPSU_GENFIFO_RX |
			XQSPIPSU_GENFIFO_STRIPE | XQSPIPSU_GENFIFO_POLL);
	GenFifoEntry |= XQSPIPSU_GENFIFO_CS_HOLD;

	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
		XQSPIPSU_GEN_FIFO_OFFSET, GenFifoEntry);
}

/*****************************************************************************/
/**
*
* Read the specified number of bytes from RX FIFO
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Msg is a pointer to the structure containing transfer data.
* @param	Size is the number of bytes to be read.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void XQspiPsu_ReadRxFifo(XQspiPsu *InstancePtr,
					XQspiPsu_Msg *Msg, int Size)
{
	int Count = 0;
	u32 Data;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Msg != NULL);

	while (InstancePtr->RxBytes != 0 && Count < Size) {
		Data = XQspiPsu_ReadReg(InstancePtr->
				Config.BaseAddress, XQSPIPSU_RXD_OFFSET);
		if (InstancePtr->RxBytes >= 4) {
			*(u32 *)Msg->RxBfrPtr = Data;
			InstancePtr->RxBytes -= 4;
			Msg->RxBfrPtr += 4;
			Count += 4;
		} else {
			/* Read unaligned bytes (< 4 bytes) */
			while (InstancePtr->RxBytes != 0) {
				*Msg->RxBfrPtr = Data;
				InstancePtr->RxBytes--;
				Msg->RxBfrPtr++;
				Count++;
				Data >>= 8;
			}
		}
	}
}
