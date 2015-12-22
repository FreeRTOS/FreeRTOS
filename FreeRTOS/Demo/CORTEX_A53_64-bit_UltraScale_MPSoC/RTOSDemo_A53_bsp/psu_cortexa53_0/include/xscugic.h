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
* @file xscugic.h
*
* The generic interrupt controller driver component.
*
* The interrupt controller driver uses the idea of priority for the various
* handlers. Priority is an integer within the range of 1 and 31 inclusive with
* default of 1 being the highest priority interrupt source. The priorities
* of the various sources can be dynamically altered as needed through
* hardware configuration.
*
* The generic interrupt controller supports the following
* features:
*
*   - specific individual interrupt enabling/disabling
*   - specific individual interrupt acknowledging
*   - attaching specific callback function to handle interrupt source
*   - assigning desired priority to interrupt source if default is not
*     acceptable.
*
* Details about connecting the interrupt handler of the driver are contained
* in the source file specific to interrupt processing, xscugic_intr.c.
*
* This driver is intended to be RTOS and processor independent.  It works with
* physical addresses only.  Any needs for dynamic memory management, threads
* or thread mutual exclusion, virtual memory, or cache control must be
* satisfied by the layer above this driver.
*
* <b>Interrupt Vector Tables</b>
*
* The device ID of the interrupt controller device is used by the driver as a
* direct index into the configuration data table. The user should populate the
* vector table with handlers and callbacks at run-time using the
* XScuGic_Connect() and XScuGic_Disconnect() functions.
*
* Each vector table entry corresponds to a device that can generate an
* interrupt. Each entry contains an interrupt handler function and an
* argument to be passed to the handler when an interrupt occurs.  The
* user must use XScuGic_Connect() when the interrupt handler takes an
* argument other than the base address.
*
* <b>Nested Interrupts Processing</b>
*
* Nested interrupts are not supported by this driver.
*
* NOTE:
* The generic interrupt controller is not a part of the snoop control unit
* as indicated by the prefix "scu" in the name of the driver.
* It is an independent module in APU.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------------
* 1.00a drg  01/19/00 First release
* 1.01a sdm  11/09/11 The XScuGic and XScuGic_Config structures have changed.
*		      The HandlerTable (of type XScuGic_VectorTableEntry) is
*		      moved to XScuGic_Config structure from XScuGic structure.
*
*		      The "Config" entry in XScuGic structure is made as
*		      pointer for better efficiency.
*
*		      A new file named as xscugic_hw.c is now added. It is
*		      to implement low level driver routines without using
*		      any xscugic instance pointer. They are useful when the
*		      user wants to use xscugic through device id or
*		      base address. The driver routines provided are explained
*		      below.
*		      XScuGic_DeviceInitialize that takes device id as
*		      argument and initializes the device (without calling
*		      XScuGic_CfgInitialize).
*		      XScuGic_DeviceInterruptHandler that takes device id
*		      as argument and calls appropriate handlers from the
*		      HandlerTable.
*		      XScuGic_RegisterHandler that registers a new handler
*		      by taking xscugic hardware base address as argument.
*		      LookupConfigByBaseAddress is used to return the
*		      corresponding config structure from XScuGic_ConfigTable
*		      based on the scugic base address passed.
* 1.02a sdm  12/20/11 Removed AckBeforeService from the XScuGic_Config
*		      structure.
* 1.03a srt  02/27/13 Moved Offset calculation macros from *.c and *_hw.c to
*		      *_hw.h
*		      Added APIs
*			- XScuGic_SetPriTrigTypeByDistAddr()
*			- XScuGic_GetPriTrigTypeByDistAddr()
*		      (CR 702687)
*			Added support to direct interrupts to the appropriate CPU. Earlier
*			  interrupts were directed to CPU1 (hard coded). Now depending
*			  upon the CPU selected by the user (xparameters.h), interrupts
*			  will be directed to the relevant CPU. This fixes CR 699688.
* 1.04a hk   05/04/13 Assigned EffectiveAddr to CpuBaseAddress in
*			  XScuGic_CfgInitialize. Fix for CR#704400 to remove warnings.
*			  Moved functions XScuGic_SetPriTrigTypeByDistAddr and
*             XScuGic_GetPriTrigTypeByDistAddr to xscugic_hw.c.
*			  This is fix for CR#705621.
* 1.05a hk   06/26/13 Modified tcl to export external interrupts correctly to
*                     xparameters.h. Fix for CR's 690505, 708928 & 719359.
* 2.0   adk  12/10/13 Updated as per the New Tcl API's
* 2.1   adk  25/04/14 Fixed the CR:789373 changes are made in the driver tcl file.
* 3.00  kvn  02/13/15 Modified code for MISRA-C:2012 compliance.
*
* </pre>
*
******************************************************************************/

#ifndef XSCUGIC_H /* prevent circular inclusions */
#define XSCUGIC_H /* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif


/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xil_io.h"
#include "xscugic_hw.h"
#include "xil_exception.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/

/* The following data type defines each entry in an interrupt vector table.
 * The callback reference is the base address of the interrupting device
 * for the low level driver and an instance pointer for the high level driver.
 */
typedef struct
{
	Xil_InterruptHandler Handler;
	void *CallBackRef;
} XScuGic_VectorTableEntry;

/**
 * This typedef contains configuration information for the device.
 */
typedef struct
{
	u16 DeviceId;		/**< Unique ID  of device */
	u32 CpuBaseAddress;	/**< CPU Interface Register base address */
	u32 DistBaseAddress;	/**< Distributor Register base address */
	XScuGic_VectorTableEntry HandlerTable[XSCUGIC_MAX_NUM_INTR_INPUTS];/**<
				 Vector table of interrupt handlers */
} XScuGic_Config;

/**
 * The XScuGic driver instance data. The user is required to allocate a
 * variable of this type for every intc device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct
{
	XScuGic_Config *Config;  /**< Configuration table entry */
	u32 IsReady;		 /**< Device is initialized and ready */
	u32 UnhandledInterrupts; /**< Intc Statistics */
} XScuGic;

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Write the given CPU Interface register
*
* @param    InstancePtr is a pointer to the instance to be worked on.
* @param    RegOffset is the register offset to be written
* @param    Data is the 32-bit value to write to the register
*
* @return   None.
*
* @note
* C-style signature:
*    void XScuGic_CPUWriteReg(XScuGic *InstancePtr, u32 RegOffset, u32 Data)
*
*****************************************************************************/
#define XScuGic_CPUWriteReg(InstancePtr, RegOffset, Data) \
(XScuGic_WriteReg(((InstancePtr)->Config->CpuBaseAddress), (RegOffset), \
					((u32)(Data))))

/****************************************************************************/
/**
*
* Read the given CPU Interface register
*
* @param    InstancePtr is a pointer to the instance to be worked on.
* @param    RegOffset is the register offset to be read
*
* @return   The 32-bit value of the register
*
* @note
* C-style signature:
*    u32 XScuGic_CPUReadReg(XScuGic *InstancePtr, u32 RegOffset)
*
*****************************************************************************/
#define XScuGic_CPUReadReg(InstancePtr, RegOffset) \
	(XScuGic_ReadReg(((InstancePtr)->Config->CpuBaseAddress), (RegOffset)))

/****************************************************************************/
/**
*
* Write the given Distributor Interface register
*
* @param    InstancePtr is a pointer to the instance to be worked on.
* @param    RegOffset is the register offset to be written
* @param    Data is the 32-bit value to write to the register
*
* @return   None.
*
* @note
* C-style signature:
*    void XScuGic_DistWriteReg(XScuGic *InstancePtr, u32 RegOffset, u32 Data)
*
*****************************************************************************/
#define XScuGic_DistWriteReg(InstancePtr, RegOffset, Data) \
(XScuGic_WriteReg(((InstancePtr)->Config->DistBaseAddress), (RegOffset), \
					((u32)(Data))))

/****************************************************************************/
/**
*
* Read the given Distributor Interface register
*
* @param    InstancePtr is a pointer to the instance to be worked on.
* @param    RegOffset is the register offset to be read
*
* @return   The 32-bit value of the register
*
* @note
* C-style signature:
*    u32 XScuGic_DistReadReg(XScuGic *InstancePtr, u32 RegOffset)
*
*****************************************************************************/
#define XScuGic_DistReadReg(InstancePtr, RegOffset) \
(XScuGic_ReadReg(((InstancePtr)->Config->DistBaseAddress), (RegOffset)))

/************************** Function Prototypes ******************************/

/*
 * Required functions in xscugic.c
 */

s32  XScuGic_Connect(XScuGic *InstancePtr, u32 Int_Id,
			Xil_InterruptHandler Handler, void *CallBackRef);
void XScuGic_Disconnect(XScuGic *InstancePtr, u32 Int_Id);

void XScuGic_Enable(XScuGic *InstancePtr, u32 Int_Id);
void XScuGic_Disable(XScuGic *InstancePtr, u32 Int_Id);

s32  XScuGic_CfgInitialize(XScuGic *InstancePtr, XScuGic_Config *ConfigPtr,
							u32 EffectiveAddr);

s32  XScuGic_SoftwareIntr(XScuGic *InstancePtr, u32 Int_Id, u32 Cpu_Id);

void XScuGic_GetPriorityTriggerType(XScuGic *InstancePtr, u32 Int_Id,
					u8 *Priority, u8 *Trigger);
void XScuGic_SetPriorityTriggerType(XScuGic *InstancePtr, u32 Int_Id,
					u8 Priority, u8 Trigger);

/*
 * Initialization functions in xscugic_sinit.c
 */
XScuGic_Config *XScuGic_LookupConfig(u16 DeviceId);

/*
 * Interrupt functions in xscugic_intr.c
 */
void XScuGic_InterruptHandler(XScuGic *InstancePtr);

/*
 * Self-test functions in xscugic_selftest.c
 */
s32  XScuGic_SelfTest(XScuGic *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif            /* end of protection macro */
