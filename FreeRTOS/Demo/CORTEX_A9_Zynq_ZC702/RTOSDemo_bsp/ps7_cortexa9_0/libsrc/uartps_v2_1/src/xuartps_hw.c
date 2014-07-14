/*****************************************************************************
*
* (c) Copyright 2010-13 Xilinx, Inc. All rights reserved.
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
*****************************************************************************/
/****************************************************************************/
/**
*
* @file xuartps_hw.c
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- ----------------------------------------------
* 1.00	drg/jz 01/12/10 First Release
* 1.05a hk     08/22/13 Added reset function
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xuartps_hw.h"

/************************** Constant Definitions ****************************/


/***************** Macros (Inline Functions) Definitions ********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* This function sends one byte using the device. This function operates in
* polled mode and blocks until the data has been put into the TX FIFO register.
*
* @param	BaseAddress contains the base address of the device.
* @param	Data contains the byte to be sent.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SendByte(u32 BaseAddress, u8 Data)
{
		/*
		 * Wait until there is space in TX FIFO
		 */
		while (XUartPs_IsTransmitFull(BaseAddress));

		/*
		 * Write the byte into the TX FIFO
		 */
		XUartPs_WriteReg(BaseAddress, XUARTPS_FIFO_OFFSET, Data);
}

/****************************************************************************/
/**
*
* This function receives a byte from the device. It operates in polled mode
* and blocks until a byte has received.
*
* @param	BaseAddress contains the base address of the device.
*
* @return	The data byte received.
*
* @note		None.
*
*****************************************************************************/
u8 XUartPs_RecvByte(u32 BaseAddress)
{
		/*
		 * Wait until there is data
		 */
		while (!XUartPs_IsReceiveData(BaseAddress));

		/*
		 * Return the byte received
		 */
		return (XUartPs_ReadReg(BaseAddress, XUARTPS_FIFO_OFFSET));
}

/****************************************************************************/
/**
*
* This function resets UART
*
* @param	BaseAddress contains the base address of the device.
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XUartPs_ResetHw(u32 BaseAddress)
{

	/*
	 * Disable interrupts
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_IDR_OFFSET, XUARTPS_IXR_MASK);

	/*
	 * Disable receive and transmit
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_CR_OFFSET,
				XUARTPS_CR_RX_DIS | XUARTPS_CR_TX_DIS);

	/*
	 * Software reset of receive and transmit
	 * This clears the FIFO.
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_CR_OFFSET,
				XUARTPS_CR_TXRST | XUARTPS_CR_RXRST);

	/*
	 * Clear status flags - SW reset wont clear sticky flags.
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_ISR_OFFSET, XUARTPS_IXR_MASK);

	/*
	 * Mode register reset value : All zeroes
	 * Normal mode, even parity, 1 stop bit
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_MR_OFFSET,
				XUARTPS_MR_CHMODE_NORM);

	/*
	 * Rx and TX trigger register reset values
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_RXWM_OFFSET,
				XUARTPS_RXWM_RESET_VAL);
	XUartPs_WriteReg(BaseAddress, XUARTPS_TXWM_OFFSET,
				XUARTPS_TXWM_RESET_VAL);

	/*
	 * Rx timeout disabled by default
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_RXTOUT_OFFSET,
				XUARTPS_RXTOUT_DISABLE);

	/*
	 * Baud rate generator and dividor reset values
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_BAUDGEN_OFFSET,
				XUARTPS_BAUDGEN_RESET_VAL);
	XUartPs_WriteReg(BaseAddress, XUARTPS_BAUDDIV_OFFSET,
				XUARTPS_BAUDDIV_RESET_VAL);

	/*
	 * Control register reset value -
	 * RX and TX are disable by default
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_CR_OFFSET,
				XUARTPS_CR_RX_DIS | XUARTPS_CR_TX_DIS |
				XUARTPS_CR_STOPBRK);

}

