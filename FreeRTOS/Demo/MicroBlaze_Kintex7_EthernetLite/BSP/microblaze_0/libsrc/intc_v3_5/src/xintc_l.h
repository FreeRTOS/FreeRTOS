/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
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
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
* @file xintc_l.h
* @addtogroup intc_v3_4
* @{
*
* This header file contains identifiers and low-level driver functions (or
* macros) that can be used to access the device.  The user should refer to the
* hardware device specification for more details of the device operation.
*
*
* Note that users of the driver interface given in this file can register
* an interrupt handler dynamically (at run-time) using the
* XIntc_RegisterHandler() function.
* User of the driver interface given in xintc.h should still use
* XIntc_Connect(), as always.
* Also see the discussion of the interrupt vector tables in xintc.h.
*
* There are currently two interrupt handlers specified in this interface.
*
* - XIntc_LowLevelInterruptHandler() is a handler without any arguments that
*   is used in cases where there is a single interrupt controller device in
*   the system and the handler cannot be passed an argument. This function is
*   provided mostly for backward compatibility.
*
* - XIntc_DeviceInterruptHandler() is a handler that takes a device ID as an
*   argument, indicating which interrupt controller device in the system is
*   causing the interrupt - thereby supporting multiple interrupt controllers.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------------
* 1.00b jhl  04/24/02 First release
* 1.00c rpm  10/17/03 New release. Support the static vector table created
*                     in the xintc_g.c configuration table.
* 1.10c mta  03/21/07 Updated to new coding style
* 1.11a sv   11/21/07 Updated driver to support access through a DCR bridge
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs. _m is removed from all
*		      the macro definitions.
* 2.04a bss  01/13/12 Updated for adding defines for IMR and IVAR for
*                     the FAST Interrupt
* 2.05a bss  08/18/12 Added XIntc_RegisterFastHandler API to register fast
*		      interrupt handlers using base address.
* 2.07a bss  10/18/13 Added XIN_ILR_OFFSET macro for nested interrupts.
* 3.5   sk   11/10/15 Used UINTPTR instead of u32 for Baseaddress CR# 867425.
*                     Changed the prototypes of XIntc_RegisterFastHandler,
*                     XIntc_SetIntrSvcOption, XIntc_RegisterHandler APIs.
*
* </pre>
*
******************************************************************************/

#ifndef XINTC_L_H		/* prevent circular inclusions */
#define XINTC_L_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xparameters.h"
#include "xil_io.h"

/*
 * XPAR_XINTC_USE_DCR_BRIDGE has to be set to 1 if the Intc device will be
 * accessed through a DCR bus connected to a bridge.
 */
#define XPAR_XINTC_USE_DCR_BRIDGE 0

#if ((XPAR_XINTC_USE_DCR != 0) || (XPAR_XINTC_USE_DCR_BRIDGE != 0))
#include "xio_dcr.h"
#endif

/************************** Constant Definitions *****************************/

/* define the offsets from the base address for all the registers of the
 * interrupt controller, some registers may be optional in the hardware device
 */
#if ((XPAR_XINTC_USE_DCR != 0) || (XPAR_XINTC_USE_DCR_BRIDGE != 0))

#define XIN_ISR_OFFSET      0	/* Interrupt Status Register */
#define XIN_IPR_OFFSET      1	/* Interrupt Pending Register */
#define XIN_IER_OFFSET      2	/* Interrupt Enable Register */
#define XIN_IAR_OFFSET      3	/* Interrupt Acknowledge Register */
#define XIN_SIE_OFFSET      4	/* Set Interrupt Enable Register */
#define XIN_CIE_OFFSET      5	/* Clear Interrupt Enable Register */
#define XIN_IVR_OFFSET      6	/* Interrupt Vector Register */
#define XIN_MER_OFFSET      7	/* Master Enable Register */
#define XIN_IMR_OFFSET      8	/* Interrupt Mode Register , this is present
				 *  only for Fast Interrupt */
#define XIN_IVAR_OFFSET     64  /* Interrupt Vector Address Register
				 * Interrupt 0 Offest, this is present
				 * only for Fast Interrupt */

#else /* ((XPAR_XINTC_USE_DCR != 0) || (XPAR_XINTC_USE_DCR_BRIDGE != 0)) */

#define XIN_ISR_OFFSET      0	/* Interrupt Status Register */
#define XIN_IPR_OFFSET      4	/* Interrupt Pending Register */
#define XIN_IER_OFFSET      8	/* Interrupt Enable Register */
#define XIN_IAR_OFFSET      12	/* Interrupt Acknowledge Register */
#define XIN_SIE_OFFSET      16	/* Set Interrupt Enable Register */
#define XIN_CIE_OFFSET      20	/* Clear Interrupt Enable Register */
#define XIN_IVR_OFFSET      24	/* Interrupt Vector Register */
#define XIN_MER_OFFSET      28	/* Master Enable Register */
#define XIN_IMR_OFFSET      32	/* Interrupt Mode Register , this is present
				 *  only for Fast Interrupt */
#define XIN_ILR_OFFSET      36  /* Interrupt level register */
#define XIN_IVAR_OFFSET     0x100 /* Interrupt Vector Address Register
				   * Interrupt 0 Offest, this is present
				   * only for Fast Interrupt */



#endif /* ((XPAR_XINTC_USE_DCR != 0) || (XPAR_XINTC_USE_DCR_BRIDGE != 0)) */

/* Bit definitions for the bits of the MER register */

#define XIN_INT_MASTER_ENABLE_MASK      0x1UL
#define XIN_INT_HARDWARE_ENABLE_MASK    0x2UL	/* once set cannot be cleared */

/**************************** Type Definitions *******************************/

/* The following data type defines each entry in an interrupt vector table.
 * The callback reference is the base address of the interrupting device
 * for the driver interface given in this file and an instance pointer for the
 * driver interface given in xintc.h file.
 */
typedef struct {
	XInterruptHandler Handler;
	void *CallBackRef;
} XIntc_VectorTableEntry;

typedef void (*XFastInterruptHandler) (void);

/***************** Macros (Inline Functions) Definitions *********************/

/*
 * Define the appropriate I/O access method to memory mapped I/O or DCR.
 */
#if ((XPAR_XINTC_USE_DCR != 0) || (XPAR_XINTC_USE_DCR_BRIDGE != 0))

#define XIntc_In32  XIo_DcrIn
#define XIntc_Out32 XIo_DcrOut

#else

#define XIntc_In32  Xil_In32
#define XIntc_Out32 Xil_Out32

#endif

/****************************************************************************/
/**
*
* Enable all interrupts in the Master Enable register of the interrupt
* controller.  The interrupt controller defaults to all interrupts disabled
* from reset such that this macro must be used to enable interrupts.
*
* @param	BaseAddress is the base address of the device.
*
* @return	None.
*
* @note		C-style signature:
*		void XIntc_MasterEnable(u32 BaseAddress);
*
*****************************************************************************/
#define XIntc_MasterEnable(BaseAddress) \
	XIntc_Out32((BaseAddress) + XIN_MER_OFFSET, \
	XIN_INT_MASTER_ENABLE_MASK | XIN_INT_HARDWARE_ENABLE_MASK)

/****************************************************************************/
/**
*
* Disable all interrupts in the Master Enable register of the interrupt
* controller.
*
* @param	BaseAddress is the base address of the device.
*
* @return	None.
*
* @note		C-style signature:
*		void XIntc_MasterDisable(u32 BaseAddress);
*
*****************************************************************************/
#define XIntc_MasterDisable(BaseAddress) \
	XIntc_Out32((BaseAddress) + XIN_MER_OFFSET, 0)

/****************************************************************************/
/**
*
* Enable specific interrupt(s) in the interrupt controller.
*
* @param	BaseAddress is the base address of the device
* @param	EnableMask is the 32-bit value to write to the enable register.
*		Each bit of the mask corresponds to an interrupt input signal
*		that is connected to the interrupt controller (INT0 = LSB).
*		Only the bits which are set in the mask will enable interrupts.
*
* @return	None.
*
* @note		C-style signature:
*		void XIntc_EnableIntr(u32 BaseAddress, u32 EnableMask);
*
*****************************************************************************/
#define XIntc_EnableIntr(BaseAddress, EnableMask) \
	XIntc_Out32((BaseAddress) + XIN_IER_OFFSET, (EnableMask))

/****************************************************************************/
/**
*
* Disable specific interrupt(s) in the interrupt controller.
*
* @param	BaseAddress is the base address of the device
* @param	DisableMask is the 32-bit value to write to the enable register.
*		Each bit of the mask corresponds to an interrupt input signal
*		that is connected to the interrupt controller (INT0 = LSB).
*		Only the bits which are set in the mask will disable interrupts.
*
* @return	None.
*
* @note		C-style signature:
*		void XIntc_DisableIntr(u32 BaseAddress, u32 DisableMask);
*
*****************************************************************************/
#define XIntc_DisableIntr(BaseAddress, DisableMask) \
	XIntc_Out32((BaseAddress) + XIN_IER_OFFSET, ~(DisableMask))

/****************************************************************************/
/**
*
* Acknowledge specific interrupt(s) in the interrupt controller.
*
* @param	BaseAddress is the base address of the device
* @param	AckMask is the 32-bit value to write to the acknowledge
*		register. Each bit of the mask corresponds to an interrupt input
*		signal that is connected to the interrupt controller (INT0 =
*		LSB).  Only the bits which are set in the mask will acknowledge
*		interrupts.
*
* @return	None.
*
* @note		C-style signature:
*		void XIntc_AckIntr(u32 BaseAddress, u32 AckMask);
*
*****************************************************************************/
#define XIntc_AckIntr(BaseAddress, AckMask) \
	XIntc_Out32((BaseAddress) + XIN_IAR_OFFSET, (AckMask))

/****************************************************************************/
/**
*
* Get the interrupt status from the interrupt controller which indicates
* which interrupts are active and enabled.
*
* @param	BaseAddress is the base address of the device
*
* @return	The 32-bit contents of the interrupt status register. Each bit
*		corresponds to an interrupt input signal that is connected to
*		the interrupt controller (INT0 = LSB). Bits which are set
*		indicate an active interrupt which is also enabled.
*
* @note		C-style signature:
*		u32 XIntc_GetIntrStatus(u32 BaseAddress);
*
*****************************************************************************/
#define XIntc_GetIntrStatus(BaseAddress) \
	(XIntc_In32((BaseAddress) + XIN_ISR_OFFSET) & \
	XIntc_In32((BaseAddress) + XIN_IER_OFFSET))

/************************** Function Prototypes ******************************/

/*
 * Interrupt controller handlers, to be connected to processor exception
 * handling code.
 */
void XIntc_LowLevelInterruptHandler(void);
void XIntc_DeviceInterruptHandler(void *DeviceId);

/* Various configuration functions */
void XIntc_SetIntrSvcOption(UINTPTR BaseAddress, int Option);

void XIntc_RegisterHandler(UINTPTR BaseAddress, int InterruptId,
			   XInterruptHandler Handler, void *CallBackRef);

void XIntc_RegisterFastHandler(UINTPTR BaseAddress, u8 Id,
					XFastInterruptHandler FastHandler);

/************************** Variable Definitions *****************************/


#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
