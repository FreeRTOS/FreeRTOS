/******************************************************************************
*
* Copyright (C) 2013 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xqspips_hw.c
* @addtogroup qspips_v3_0
* @{
*
* Contains low level functions, primarily reset related.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 2.03a hk  09/17/13 First release
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xqspips_hw.h"
#include "xqspips.h"

/************************** Constant Definitions *****************************/

/** @name Pre-scaler value for divided by 4
 *
 * Pre-scaler value for divided by 4
 *
 * @{
 */
#define XQSPIPS_CR_PRESC_DIV_BY_4	0x01
/* @} */

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Resets QSPI by disabling the device and bringing it to reset state through
* register writes.
*
* @param	None
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XQspiPs_ResetHw(u32 BaseAddress)
{
	u32 ConfigReg;

	/*
	 * Disable interrupts
	 */
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_IDR_OFFSET,
				XQSPIPS_IXR_DISABLE_ALL);

	/*
	 * Disable device
	 */
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_ER_OFFSET,
				0);

	/*
	 * De-assert slave select lines.
	 */
	ConfigReg = XQspiPs_ReadReg(BaseAddress, XQSPIPS_CR_OFFSET);
	ConfigReg |= (XQSPIPS_CR_SSCTRL_MASK | XQSPIPS_CR_SSFORCE_MASK);
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_CR_OFFSET, ConfigReg);

	/*
	 * Write default value to RX and TX threshold registers
	 * RX threshold should be set to 1 here because the corresponding
	 * status bit is used next to clear the RXFIFO
	 */
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_TXWR_OFFSET,
			(XQSPIPS_TXWR_RESET_VALUE & XQSPIPS_TXWR_MASK));
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_RXWR_OFFSET,
			(XQSPIPS_RXWR_RESET_VALUE & XQSPIPS_RXWR_MASK));

	/*
	 * Clear RXFIFO
	 */
	while ((XQspiPs_ReadReg(BaseAddress,XQSPIPS_SR_OFFSET) &
		XQSPIPS_IXR_RXNEMPTY_MASK) != 0) {
		XQspiPs_ReadReg(BaseAddress, XQSPIPS_RXD_OFFSET);
	}

	/*
	 * Clear status register by reading register and
	 * writing 1 to clear the write to clear bits
	 */
	XQspiPs_ReadReg(BaseAddress, XQSPIPS_SR_OFFSET);
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_SR_OFFSET,
				XQSPIPS_IXR_WR_TO_CLR_MASK);

	/*
	 * Write default value to configuration register
	 */
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_CR_OFFSET,
				XQSPIPS_CR_RESET_STATE);


	/*
	 * De-select linear mode
	 */
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_LQSPI_CR_OFFSET,
				0x0);

}

/*****************************************************************************/
/**
*
* Initializes QSPI to Linear mode with default QSPI boot settings.
*
* @param	None
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XQspiPs_LinearInit(u32 BaseAddress)
{
	u32 BaudRateDiv;
	u32 LinearCfg;

	/*
	 * Baud rate divisor for dividing by 4. Value of CR bits [5:3]
	 * should be set to 0x001; hence shift the value and use the mask.
	 */
	BaudRateDiv = ( (XQSPIPS_CR_PRESC_DIV_BY_4) <<
			XQSPIPS_CR_PRESC_SHIFT) & XQSPIPS_CR_PRESC_MASK;
	/*
	 * Write configuration register with default values, slave selected &
	 * pre-scaler value for divide by 4
	 */
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_CR_OFFSET,
				((XQSPIPS_CR_RESET_STATE |
				XQSPIPS_CR_HOLD_B_MASK | BaudRateDiv) &
				(~XQSPIPS_CR_SSCTRL_MASK) ));

	/*
	 * Write linear configuration register with default value -
	 * enable linear mode and use fast read.
	 */

	if(XPAR_PS7_QSPI_0_QSPI_MODE == XQSPIPS_CONNECTION_MODE_SINGLE){

		LinearCfg = XQSPIPS_LQSPI_CR_RST_STATE;

	}else if(XPAR_PS7_QSPI_0_QSPI_MODE ==
			XQSPIPS_CONNECTION_MODE_STACKED){

		LinearCfg = XQSPIPS_LQSPI_CR_RST_STATE |
				XQSPIPS_LQSPI_CR_TWO_MEM_MASK;

	}else if(XPAR_PS7_QSPI_0_QSPI_MODE ==
	 		XQSPIPS_CONNECTION_MODE_PARALLEL){

		LinearCfg = XQSPIPS_LQSPI_CR_RST_STATE |
				XQSPIPS_LQSPI_CR_TWO_MEM_MASK |
		 		XQSPIPS_LQSPI_CR_SEP_BUS_MASK;

	}

	XQspiPs_WriteReg(BaseAddress, XQSPIPS_LQSPI_CR_OFFSET,
				LinearCfg);

	/*
	 * Enable device
	 */
	XQspiPs_WriteReg(BaseAddress, XQSPIPS_ER_OFFSET,
				XQSPIPS_ER_ENABLE_MASK);

}


/** @} */
