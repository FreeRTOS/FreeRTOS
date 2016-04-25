/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
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
* @file xcoresightpsdcc.c
* @addtogroup coresightps_dcc_v1_1
* @{
*
* Functions in this file are the minimum required functions for the
* XCoreSightPs driver.
*
* @note 	None.
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date		Changes
* ----- -----  -------- -----------------------------------------------
* 1.00  kvn    02/14/15 First release
* 1.1   kvn    06/12/15 Add support for Zynq Ultrascale+ MP.
*       kvn    08/18/15 Modified Makefile according to compiler changes.
* 1.2   kvn    10/09/15 Add support for IAR Compiler.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include <xil_types.h>
#include <xpseudo_asm.h>

#ifdef __ICCARM__
#define INLINE
#else
#define INLINE __inline
#endif

/* DCC Status Bits */
#define XCORESIGHTPS_DCC_STATUS_RX (1 << 30)
#define XCORESIGHTPS_DCC_STATUS_TX (1 << 29)

static INLINE u32 XCoresightPs_DccGetStatus(void);

/****************************************************************************/
/**
*
* This functions sends a single byte using the DCC. It is blocking in that it
* waits for the transmitter to become non-full before it writes the byte to
* the transmit register.
*
* @param	BaseAddress is a dummy parameter to match the function proto
*		of functions for other stdio devices.
* @param	Data is the byte of data to send
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XCoresightPs_DccSendByte(u32 BaseAddress, u8 Data)
{
	(void) BaseAddress;
	while (XCoresightPs_DccGetStatus() & XCORESIGHTPS_DCC_STATUS_TX)
	dsb();
#ifdef __aarch64__
	asm volatile ("msr dbgdtrtx_el0, %0" : : "r" (Data));
#elif defined (__GNUC__) || defined (__ICCARM__)
	asm volatile("mcr p14, 0, %0, c0, c5, 0"
			: : "r" (Data));
#else
	{
		volatile register u32 Reg __asm("cp14:0:c0:c5:0");
		Reg = Data;
	}
#endif
	isb();

}

/****************************************************************************/
/**
*
* This functions receives a single byte using the DCC. It is blocking in that
* it waits for the receiver to become non-empty before it reads from the
* receive register.
*
* @param	BaseAddress is a dummy parameter to match the function proto
*		of functions for other stdio devices.
*
* @return	The byte of data received.
*
* @note		None.
*
******************************************************************************/
u8 XCoresightPs_DccRecvByte(u32 BaseAddress)
{
	u8 Data;
	(void) BaseAddress;

	while (!(XCoresightPs_DccGetStatus() & XCORESIGHTPS_DCC_STATUS_RX))
		dsb();

#ifdef __aarch64__
	asm volatile ("mrs %0, dbgdtrrx_el0" : "=r" (Data));
#elif defined (__GNUC__) || defined (__ICCARM__)
	asm volatile("mrc p14, 0, %0, c0, c5, 0"
			: "=r" (Data));
#else
	{
		volatile register u32 Reg __asm("cp14:0:c0:c5:0");
		Data = Reg;
	}
#endif
	isb();

	return Data;
}


/****************************************************************************/
/**INLINE
*
* This functions read the status register of the DCC.
*
* @param	BaseAddress is the base address of the device
*
* @return	The contents of the Status Register.
*
* @note		None.
*
******************************************************************************/
static INLINE u32 XCoresightPs_DccGetStatus(void)
{
	u32 Status;

#ifdef __aarch64__
	asm volatile ("mrs %0, mdccsr_el0" : "=r" (Status));
#elif defined (__GNUC__) || defined (__ICCARM__)
	asm volatile("mrc p14, 0, %0, c0, c1, 0"
			: "=r" (Status) : : "cc");
#else
	{
		volatile register u32 Reg __asm("cp14:0:c0:c1:0");
		Status = Reg;
	}
#endif
	return Status;
}
/** @} */
