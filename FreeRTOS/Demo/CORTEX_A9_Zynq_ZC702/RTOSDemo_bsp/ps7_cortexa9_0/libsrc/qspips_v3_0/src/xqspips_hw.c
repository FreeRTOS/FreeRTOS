/******************************************************************************
*
* (c) Copyright 2013 Xilinx, Inc. All rights reserved.
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
*
* @file xqspips_hw.c
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


