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
/****************************************************************************/
/**
*
* @file xuartps_options.c
* @addtogroup uartps_v3_5
* @{
*
* The implementation of the options functions for the XUartPs driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- -----------------------------------------------
* 1.00  drg/jz 01/13/10 First Release
* 1.00  sdm    09/27/11 Fixed a bug in XUartPs_SetFlowDelay where the input
*			value was not being written to the register.
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
* 3.2   rk     07/20/16 Modified the logic for transmission break bit set
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xuartps.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/
/*
 * The following data type is a map from an option to the offset in the
 * register to which it belongs as well as its bit mask in that register.
 */
typedef struct {
	u16 Option;
	u16 RegisterOffset;
	u32 Mask;
} Mapping;

/*
 * Create the table which contains options which are to be processed to get/set
 * the options. These options are table driven to allow easy maintenance and
 * expansion of the options.
 */

static Mapping OptionsTable[] = {
	{XUARTPS_OPTION_SET_BREAK, XUARTPS_CR_OFFSET, XUARTPS_CR_STARTBRK},
	{XUARTPS_OPTION_STOP_BREAK, XUARTPS_CR_OFFSET, XUARTPS_CR_STOPBRK},
	{XUARTPS_OPTION_RESET_TMOUT, XUARTPS_CR_OFFSET, XUARTPS_CR_TORST},
	{XUARTPS_OPTION_RESET_TX, XUARTPS_CR_OFFSET, XUARTPS_CR_TXRST},
	{XUARTPS_OPTION_RESET_RX, XUARTPS_CR_OFFSET, XUARTPS_CR_RXRST},
	{XUARTPS_OPTION_ASSERT_RTS, XUARTPS_MODEMCR_OFFSET,
	 XUARTPS_MODEMCR_RTS},
	{XUARTPS_OPTION_ASSERT_DTR, XUARTPS_MODEMCR_OFFSET,
	 XUARTPS_MODEMCR_DTR},
	{XUARTPS_OPTION_SET_FCM, XUARTPS_MODEMCR_OFFSET, XUARTPS_MODEMCR_FCM}
};

/* Create a constant for the number of entries in the table */

#define XUARTPS_NUM_OPTIONS	  (sizeof(OptionsTable) / sizeof(Mapping))

/************************** Function Prototypes *****************************/

/****************************************************************************/
/**
*
* Gets the options for the specified driver instance. The options are
* implemented as bit masks such that multiple options may be enabled or
* disabled simulataneously.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return
*
* The current options for the UART. The optionss are bit masks that are
* contained in the file xuartps.h and named XUARTPS_OPTION_*.
*
* @note		None.
*
*****************************************************************************/
u16 XUartPs_GetOptions(XUartPs *InstancePtr)
{
	u16 Options = 0U;
	u32 Register;
	u32 Index;

	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Loop thru the options table to map the physical options in the
	 * registers of the UART to the logical options to be returned
	 */
	for (Index = 0U; Index < XUARTPS_NUM_OPTIONS; Index++) {
		Register = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
						 OptionsTable[Index].
						 RegisterOffset);

		/*
		 * If the bit in the register which correlates to the option
		 * is set, then set the corresponding bit in the options,
		 * ignoring any bits which are zero since the options variable
		 * is initialized to zero
		 */
		if ((Register & OptionsTable[Index].Mask) != (u32)0) {
			Options |= OptionsTable[Index].Option;
		}
	}

	return Options;
}

/****************************************************************************/
/**
*
* Sets the options for the specified driver instance. The options are
* implemented as bit masks such that multiple options may be enabled or
* disabled simultaneously.
*
* The GetOptions function may be called to retrieve the currently enabled
* options. The result is ORed in the desired new settings to be enabled and
* ANDed with the inverse to clear the settings to be disabled. The resulting
* value is then used as the options for the SetOption function call.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	Options contains the options to be set which are bit masks
*		contained in the file xuartps.h and named XUARTPS_OPTION_*.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SetOptions(XUartPs *InstancePtr, u16 Options)
{
	u32 Index;
	u32 Register;

	/* Assert validates the input arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Loop thru the options table to map the logical options to the
	 * physical options in the registers of the UART.
	 */
	for (Index = 0U; Index < XUARTPS_NUM_OPTIONS; Index++) {

		/*
		 * Read the register which contains option so that the register
		 * can be changed without destoying any other bits of the
		 * register.
		 */
		Register = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
						 OptionsTable[Index].
						 RegisterOffset);

		/*
		 * If the option is set in the input, then set the corresponding
		 * bit in the specified register, otherwise clear the bit in
		 * the register.
		 */
		if ((Options & OptionsTable[Index].Option) != (u16)0) {
			if(OptionsTable[Index].Option == XUARTPS_OPTION_SET_BREAK)
				Register &= ~XUARTPS_CR_STOPBRK;
			Register |= OptionsTable[Index].Mask;
		}
		else {
			Register &= ~OptionsTable[Index].Mask;
		}

		/* Write the new value to the register to set the option */
		XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
				   OptionsTable[Index].RegisterOffset,
				   Register);
	}

}

/****************************************************************************/
/**
*
* This function gets the receive FIFO trigger level. The receive trigger
* level indicates the number of bytes in the receive FIFO that cause a receive
* data event (interrupt) to be generated.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return	The current receive FIFO trigger level. This is a value
*		from 0-31.
*
* @note		None.
*
*****************************************************************************/
u8 XUartPs_GetFifoThreshold(XUartPs *InstancePtr)
{
	u8 RtrigRegister;

	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the value of the FIFO control register so that the threshold
	 * can be retrieved, this read takes special register processing
	 */
	RtrigRegister = (u8) XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
						   XUARTPS_RXWM_OFFSET);

	/* Return only the trigger level from the register value */

	RtrigRegister &= (u8)XUARTPS_RXWM_MASK;
	return RtrigRegister;
}

/****************************************************************************/
/**
*
* This functions sets the receive FIFO trigger level. The receive trigger
* level specifies the number of bytes in the receive FIFO that cause a receive
* data event (interrupt) to be generated.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	TriggerLevel contains the trigger level to set.
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SetFifoThreshold(XUartPs *InstancePtr, u8 TriggerLevel)
{
	u32 RtrigRegister;

	/* Assert validates the input arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(TriggerLevel <= (u8)XUARTPS_RXWM_MASK);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RtrigRegister = ((u32)TriggerLevel) & (u32)XUARTPS_RXWM_MASK;

	/*
	 * Write the new value for the FIFO control register to it such that the
	 * threshold is changed
	 */
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XUARTPS_RXWM_OFFSET, RtrigRegister);

}

/****************************************************************************/
/**
*
* This function gets the modem status from the specified UART. The modem
* status indicates any changes of the modem signals. This function allows
* the modem status to be read in a polled mode. The modem status is updated
* whenever it is read such that reading it twice may not yield the same
* results.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return
*
* The modem status which are bit masks that are contained in the file
* xuartps.h and named XUARTPS_MODEM_*.
*
* @note
*
* The bit masks used for the modem status are the exact bits of the modem
* status register with no abstraction.
*
*****************************************************************************/
u16 XUartPs_GetModemStatus(XUartPs *InstancePtr)
{
	u32 ModemStatusRegister;
	u16 TmpRegister;
	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Read the modem status register to return
	 */
	ModemStatusRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
						XUARTPS_MODEMSR_OFFSET);
	TmpRegister = (u16)ModemStatusRegister;
	return TmpRegister;
}

/****************************************************************************/
/**
*
* This function determines if the specified UART is sending data.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return
*		- TRUE if the UART is sending data
*		- FALSE if UART is not sending data
*
* @note		None.
*
*****************************************************************************/
u32 XUartPs_IsSending(XUartPs *InstancePtr)
{
	u32 ChanStatRegister;
	u32 ChanTmpSRegister;
	u32 ActiveResult;
	u32 EmptyResult;

	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the channel status register to determine if the transmitter is
	 * active
	 */
	ChanStatRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
						 XUARTPS_SR_OFFSET);

	/*
	 * If the transmitter is active, or the TX FIFO is not empty, then indicate
	 * that the UART is still sending some data
	 */
	ActiveResult = ChanStatRegister & ((u32)XUARTPS_SR_TACTIVE);
	EmptyResult = ChanStatRegister & ((u32)XUARTPS_SR_TXEMPTY);
	ChanTmpSRegister = (((u32)XUARTPS_SR_TACTIVE) == ActiveResult) ||
		(((u32)XUARTPS_SR_TXEMPTY) != EmptyResult);

	return ChanTmpSRegister;
}

/****************************************************************************/
/**
*
* This function gets the operational mode of the UART. The UART can operate
* in one of four modes: Normal, Local Loopback, Remote Loopback, or automatic
* echo.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return
*
* The operational mode is specified by constants defined in xuartps.h. The
* constants are named XUARTPS_OPER_MODE_*
*
* @note		None.
*
*****************************************************************************/
u8 XUartPs_GetOperMode(XUartPs *InstancePtr)
{
	u32 ModeRegister;
	u8 OperMode;

	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Read the Mode register. */
	ModeRegister =
		XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XUARTPS_MR_OFFSET);

	ModeRegister &= (u32)XUARTPS_MR_CHMODE_MASK;
	/* Return the constant */
	switch (ModeRegister) {
	case XUARTPS_MR_CHMODE_NORM:
		OperMode = XUARTPS_OPER_MODE_NORMAL;
		break;
	case XUARTPS_MR_CHMODE_ECHO:
		OperMode = XUARTPS_OPER_MODE_AUTO_ECHO;
		break;
	case XUARTPS_MR_CHMODE_L_LOOP:
		OperMode = XUARTPS_OPER_MODE_LOCAL_LOOP;
		break;
	case XUARTPS_MR_CHMODE_R_LOOP:
		OperMode = XUARTPS_OPER_MODE_REMOTE_LOOP;
		break;
	default:
		OperMode = (u8) ((ModeRegister & (u32)XUARTPS_MR_CHMODE_MASK) >>
			XUARTPS_MR_CHMODE_SHIFT);
		break;
	}

	return OperMode;
}

/****************************************************************************/
/**
*
* This function sets the operational mode of the UART. The UART can operate
* in one of four modes: Normal, Local Loopback, Remote Loopback, or automatic
* echo.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	OperationMode is the mode of the UART.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SetOperMode(XUartPs *InstancePtr, u8 OperationMode)
{
	u32 ModeRegister;

	/* Assert validates the input arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(OperationMode <= XUARTPS_OPER_MODE_REMOTE_LOOP);

	/* Read the Mode register. */
	ModeRegister =
		XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XUARTPS_MR_OFFSET);

	/* Set the correct value by masking the bits, then ORing the const. */
	ModeRegister &= (u32)(~XUARTPS_MR_CHMODE_MASK);

	switch (OperationMode) {
		case XUARTPS_OPER_MODE_NORMAL:
			ModeRegister |= (u32)XUARTPS_MR_CHMODE_NORM;
			break;
		case XUARTPS_OPER_MODE_AUTO_ECHO:
			ModeRegister |= (u32)XUARTPS_MR_CHMODE_ECHO;
			break;
		case XUARTPS_OPER_MODE_LOCAL_LOOP:
			ModeRegister |= (u32)XUARTPS_MR_CHMODE_L_LOOP;
			break;
		case XUARTPS_OPER_MODE_REMOTE_LOOP:
			ModeRegister |= (u32)XUARTPS_MR_CHMODE_R_LOOP;
			break;
		default:
			/* Default case made for MISRA-C Compliance. */
			break;
	}

	XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_MR_OFFSET,
			   ModeRegister);

}

/****************************************************************************/
/**
*
* This function sets the Flow Delay.
* 0 - 3: Flow delay inactive
* 4 - 32: If Flow Control mode is enabled, UART_rtsN is deactivated when the
* receive FIFO fills to this level.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return
*
* The Flow Delay is specified by constants defined in xuartps_hw.h. The
* constants are named XUARTPS_FLOWDEL*
*
* @note		None.
*
*****************************************************************************/
u8 XUartPs_GetFlowDelay(XUartPs *InstancePtr)
{
	u32 FdelTmpRegister;

	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Read the Mode register. */
	FdelTmpRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
					 XUARTPS_FLOWDEL_OFFSET);

	/* Return the contents of the flow delay register */
	FdelTmpRegister = (u8)(FdelTmpRegister & (u32)XUARTPS_FLOWDEL_MASK);
	return  FdelTmpRegister;
}

/****************************************************************************/
/**
*
* This function sets the Flow Delay.
* 0 - 3: Flow delay inactive
* 4 - 63: If Flow Control mode is enabled, UART_rtsN is deactivated when the
* receive FIFO fills to this level.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	FlowDelayValue is the Setting for the flow delay.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SetFlowDelay(XUartPs *InstancePtr, u8 FlowDelayValue)
{
	u32 FdelRegister;

	/* Assert validates the input arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FlowDelayValue > (u8)XUARTPS_FLOWDEL_MASK);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Set the correct value by shifting the input constant, then masking
	 * the bits
	 */
	FdelRegister = ((u32)FlowDelayValue) & (u32)XUARTPS_FLOWDEL_MASK;

	XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XUARTPS_FLOWDEL_OFFSET, FdelRegister);

}

/****************************************************************************/
/**
*
* This function gets the Receive Timeout of the UART.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return	The current setting for receive time out.
*
* @note		None.
*
*****************************************************************************/
u8 XUartPs_GetRecvTimeout(XUartPs *InstancePtr)
{
	u32 RtoRegister;
	u8 RtoRTmpRegister;

	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Read the Receive Timeout register. */
	RtoRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
					XUARTPS_RXTOUT_OFFSET);

	/* Return the contents of the mode register shifted appropriately */
	RtoRTmpRegister = (u8)(RtoRegister & (u32)XUARTPS_RXTOUT_MASK);
	return RtoRTmpRegister;
}

/****************************************************************************/
/**
*
* This function sets the Receive Timeout of the UART.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	RecvTimeout setting allows the UART to detect an idle connection
*		on the reciever data line.
*		Timeout duration = RecvTimeout x 4 x Bit Period. 0 disables the
*		timeout function.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SetRecvTimeout(XUartPs *InstancePtr, u8 RecvTimeout)
{
	u32 RtoRegister;

	/* Assert validates the input arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Set the correct value by masking the bits */
	RtoRegister = ((u32)RecvTimeout & (u32)XUARTPS_RXTOUT_MASK);

	XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XUARTPS_RXTOUT_OFFSET, RtoRegister);

	/* Configure CR to restart the receiver timeout counter */
	RtoRegister =
		XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XUARTPS_CR_OFFSET);
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_CR_OFFSET,
			   (RtoRegister | XUARTPS_CR_TORST));

}
/****************************************************************************/
/**
*
* Sets the data format for the device. The data format includes the
* baud rate, number of data bits, number of stop bits, and parity. It is the
* caller's responsibility to ensure that the UART is not sending or receiving
* data when this function is called.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	FormatPtr is a pointer to a format structure containing the data
*		format to be set.
*
* @return
*		- XST_SUCCESS if the data format was successfully set.
*		- XST_UART_BAUD_ERROR indicates the baud rate could not be
*		set because of the amount of error with the baud rate and
*		the input clock frequency.
*		- XST_INVALID_PARAM if one of the parameters was not valid.
*
* @note
*
* The data types in the format type, data bits and parity, are 32 bit fields
* to prevent a compiler warning.
* The asserts in this function will cause a warning if these fields are
* bytes.
* <br><br>
*
*****************************************************************************/
s32 XUartPs_SetDataFormat(XUartPs *InstancePtr,
			XUartPsFormat * FormatPtr)
{
	s32 Status;
	u32 ModeRegister;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(FormatPtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Verify the inputs specified are valid */
	if ((FormatPtr->DataBits > ((u32)XUARTPS_FORMAT_6_BITS)) ||
		(FormatPtr->StopBits > ((u8)XUARTPS_FORMAT_2_STOP_BIT)) ||
		(FormatPtr->Parity > ((u32)XUARTPS_FORMAT_NO_PARITY))) {
		Status = XST_INVALID_PARAM;
	} else {

		/*
		 * Try to set the baud rate and if it's not successful then don't
		 * continue altering the data format, this is done first to avoid the
		 * format from being altered when an error occurs
		 */
		Status = XUartPs_SetBaudRate(InstancePtr, FormatPtr->BaudRate);
		if (Status != (s32)XST_SUCCESS) {
			;
		} else {

			ModeRegister =
				XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
						  XUARTPS_MR_OFFSET);

			/*
			 * Set the length of data (8,7,6) by first clearing out the bits
			 * that control it in the register, then set the length in the register
			 */
			ModeRegister &= (u32)(~XUARTPS_MR_CHARLEN_MASK);
			ModeRegister |= (FormatPtr->DataBits << XUARTPS_MR_CHARLEN_SHIFT);

			/*
			 * Set the number of stop bits in the mode register by first clearing
			 * out the bits that control it in the register, then set the number
			 * of stop bits in the register.
			 */
			ModeRegister &= (u32)(~XUARTPS_MR_STOPMODE_MASK);
			ModeRegister |= (((u32)FormatPtr->StopBits) << XUARTPS_MR_STOPMODE_SHIFT);

			/*
			 * Set the parity by first clearing out the bits that control it in the
			 * register, then set the bits in the register, the default is no parity
			 * after clearing the register bits
			 */
			ModeRegister &= (u32)(~XUARTPS_MR_PARITY_MASK);
			ModeRegister |= (FormatPtr->Parity << XUARTPS_MR_PARITY_SHIFT);

			/* Update the mode register */
			XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_MR_OFFSET,
					   ModeRegister);

			Status = XST_SUCCESS;
		}
	}
	return Status;
}

/****************************************************************************/
/**
*
* Gets the data format for the specified UART. The data format includes the
* baud rate, number of data bits, number of stop bits, and parity.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
* @param	FormatPtr is a pointer to a format structure that will contain
*		the data format after this call completes.
*
* @return	None.
*
* @note		None.
*
*
*****************************************************************************/
void XUartPs_GetDataFormat(XUartPs *InstancePtr, XUartPsFormat * FormatPtr)
{
	u32 ModeRegister;


	/* Assert validates the input arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FormatPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Get the baud rate from the instance, this is not retrieved from the
	 * hardware because it is only kept as a divisor such that it is more
	 * difficult to get back to the baud rate
	 */
	FormatPtr->BaudRate = InstancePtr->BaudRate;

	ModeRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XUARTPS_MR_OFFSET);

	/* Get the length of data (8,7,6,5) */
	FormatPtr->DataBits =
		((ModeRegister & (u32)XUARTPS_MR_CHARLEN_MASK) >>
		XUARTPS_MR_CHARLEN_SHIFT);

	/* Get the number of stop bits */
	FormatPtr->StopBits =
		(u8)((ModeRegister & (u32)XUARTPS_MR_STOPMODE_MASK) >>
		XUARTPS_MR_STOPMODE_SHIFT);

	/* Determine what parity is */
	FormatPtr->Parity =
		(u32)((ModeRegister & (u32)XUARTPS_MR_PARITY_MASK) >>
		XUARTPS_MR_PARITY_SHIFT);
}
/** @} */
