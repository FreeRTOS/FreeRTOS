/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
* @file uart.c
*
* This file contains APIs for configuring the UART.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 5.00 	pkp  	 05/29/14 First release
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"
#include "xparameters.h"

/* Register offsets */
#define UART_CR_OFFSET		0x00000000U
#define UART_MR_OFFSET		0x00000004U
#define UART_BAUDGEN_OFFSET	0x00000018U
#define UART_BAUDDIV_OFFSET	0x00000034U

#define MAX_BAUD_ERROR_RATE	3U	/* max % error allowed */
#define UART_BAUDRATE	115200U
#define CSU_VERSION_REG     0xFFCA0044U

void Init_Uart(void);

void Init_Uart(void)
{
#ifdef STDOUT_BASEADDRESS
	u8 IterBAUDDIV;		/* Iterator for available baud divisor values */
	u32 BRGR_Value;		/* Calculated value for baud rate generator */
	u32 CalcBaudRate;	/* Calculated baud rate */
	u32 BaudError;		/* Diff between calculated and requested baud
				 * rate */
	u32 Best_BRGR = 0U;	/* Best value for baud rate generator */
	u8 Best_BAUDDIV = 0U;	/* Best value for baud divisor */
	u32 Best_Error = 0xFFFFFFFFU;
	u32 PercentError;
	u32 InputClk;
	u32 BaudRate = UART_BAUDRATE;

	/* set CD and BDIV */

#if (STDOUT_BASEADDRESS == XPAR_XUARTPS_0_BASEADDR)
	InputClk = XPAR_XUARTPS_0_UART_CLK_FREQ_HZ;
#elif (STDOUT_BASEADDRESS == XPAR_XUARTPS_1_BASEADDR)
	InputClk = XPAR_XUARTPS_1_UART_CLK_FREQ_HZ;
#else
	/* STDIO is not set or axi_uart is being used for STDIO */
	return;
#endif
InputClk = 25000000U;
	/*
	 * Determine the Baud divider. It can be 4to 254.
	 * Loop through all possible combinations
	 */
	for (IterBAUDDIV = 4U; IterBAUDDIV < 255U; IterBAUDDIV++) {

		/*
		 * Calculate the value for BRGR register
		 */
		BRGR_Value = InputClk / (BaudRate * ((u32)IterBAUDDIV + 1U));

		/*
		 * Calculate the baud rate from the BRGR value
		 */
		CalcBaudRate = InputClk/ (BRGR_Value * ((u32)IterBAUDDIV + 1U));

		/*
		 * Avoid unsigned integer underflow
		 */
		if (BaudRate > CalcBaudRate) {
			BaudError = BaudRate - CalcBaudRate;
		} else {
			BaudError = CalcBaudRate - BaudRate;
		}

		/*
		 * Find the calculated baud rate closest to requested baud rate.
		 */
		if (Best_Error > BaudError) {

			Best_BRGR = BRGR_Value;
			Best_BAUDDIV = IterBAUDDIV;
			Best_Error = BaudError;
		}
	}

	/*
	 * Make sure the best error is not too large.
	 */
	PercentError = (Best_Error * 100U) / BaudRate;
	if (((u32)MAX_BAUD_ERROR_RATE) < PercentError) {
		return;
	}

	/* set CD and BDIV */
	Xil_Out32(STDOUT_BASEADDRESS + UART_BAUDGEN_OFFSET, Best_BRGR);
	Xil_Out32(STDOUT_BASEADDRESS + UART_BAUDDIV_OFFSET, (u32)Best_BAUDDIV);

    /*
     * Veloce specific code
     */
    if((Xil_In32(CSU_VERSION_REG) & 0x0000F000U) == 0x00002000U ) {
	Xil_Out32(STDOUT_BASEADDRESS + UART_BAUDGEN_OFFSET, 2U);
	    Xil_Out32(STDOUT_BASEADDRESS + UART_BAUDDIV_OFFSET, 4U);
    }

	/*
	 * 8 data, 1 stop, 0 parity bits
	 * sel_clk=uart_clk=APB clock
	 */
	Xil_Out32(STDOUT_BASEADDRESS + UART_MR_OFFSET, 0x00000020U);

	/* enable Tx/Rx and reset Tx/Rx data path */
	Xil_Out32((STDOUT_BASEADDRESS + UART_CR_OFFSET), 0x00000017U);

	return;
#endif
}
