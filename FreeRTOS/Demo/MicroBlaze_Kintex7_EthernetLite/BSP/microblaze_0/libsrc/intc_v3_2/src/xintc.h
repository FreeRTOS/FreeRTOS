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
* @file xintc.h
*
* The Xilinx interrupt controller driver component. This component supports the
* Xilinx interrupt controller.
*
* The interrupt controller driver uses the idea of priority for the various
* handlers. Priority is an integer within the range of 0 and 31 inclusive with
* 0 being the highest priority interrupt source.
*
* The Xilinx interrupt controller supports the following features:
*
*   - specific individual interrupt enabling/disabling
*   - specific individual interrupt acknowledging
*   - attaching specific callback function to handle interrupt source
*   - master enable/disable
*   - single callback per interrupt or all pending interrupts handled for
*     each interrupt of the processor
*
* The acknowledgement of the interrupt within the interrupt controller is
* selectable, either prior to the device's handler being called or after
* the handler is called. This is necessary to support interrupt signal inputs
* which are either edge or level signals.  Edge driven interrupt signals
* require that the interrupt is acknowledged prior to the interrupt being
* serviced in order to prevent the loss of interrupts which are occurring
* extremely close together.  A level driven interrupt input signal requires
* the interrupt to acknowledged after servicing the interrupt to ensure that
* the interrupt only generates a single interrupt condition.
*
* Details about connecting the interrupt handler of the driver are contained
* in the source file specific to interrupt processing, xintc_intr.c.
*
* This driver is intended to be RTOS and processor independent.  It works with
* physical addresses only.  Any needs for dynamic memory management, threads
* or thread mutual exclusion, virtual memory, or cache control must be
* satisfied by the layer above this driver.
*
* <b>Interrupt Vector Tables</b>
*
* The interrupt vector table for each interrupt controller device is declared
* statically in xintc_g.c within the configuration data for each instance.
* The device ID of the interrupt controller device is used by the driver as a
* direct index into the configuration data table - to retrieve the vector table
* for an instance of the interrupt controller. The user should populate the
* vector table with handlers and callbacks at run-time using the XIntc_Connect()
* and XIntc_Disconnect() functions.
*
* Each vector table entry corresponds to a device that can generate an
* interrupt. Each entry contains an interrupt handler function and an argument
* to be passed to the handler when an interrupt occurs.  The tools default this
* argument to the base address of the interrupting device.  Note that the
* device driver interrupt handlers given in this file do not take a base
* address as an argument, but instead take a pointer to the driver instance.
* This means that although the table is created statically, the user must still
* use XIntc_Connect() when the interrupt handler takes an argument other than
* the base address. This is only to say that the existence of the static vector
* tables should not mislead the user into thinking they no longer need to
* register/connect interrupt handlers with this driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a ecm  08/16/01 First release
* 1.00a rpm  01/09/02 Removed the AckLocation argument from XIntc_Connect().
*                     This information is now internal in xintc_g.c.
* 1.00b jhl  02/13/02 Repartitioned the driver for smaller files
* 1.00b jhl  04/24/02 Made LookupConfig function global and relocated config
*                     data type
* 1.00c rpm  10/17/03 New release. Support the static vector table created
*                     in the xintc_g.c configuration table. Moved vector
*                     table and options out of instance structure and into
*                     the configuration table.
* 1.10c mta  03/21/07 Updated to new coding style
* 1.11a sv   11/21/07 Updated driver to support access through a DCR bridge
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs and _m is removed from
*		      all the macro names/definitions.
* 2.01a sdm  04/27/10 Updated the tcl so that the defintions are generated in
*		      the xparameters.h to know whether the optional registers
*		      SIE, CIE and IVR are enabled in the HW - Refer CR 555392.
*		      This driver doesnot make use of these definitions and does
*		      not use the optional registers.
* 2.03a hvm  05/24/11 Updated the tcl to generate vector Ids for external
*		      interrupts. CR565336
* 2.04a bss  01/13/12 Added XIntc_ConnectFastHandler API for Fast Interrupt
*		      and XIntc_SetNormalIntrMode for setting to normal
*		      interrupt mode.
* 2.04a asa  03/19/12 Changed the XIntc_Config struct. The order of entries
*		      declared in the structure now matches with the
*		      XIntc_ConfigTable generated by the driver tcl.
* 2.05a bss  08/16/12 Updated to support relocatable vectors in Microblaze,
*		      added IntVectorAddr to XIntc_Config for this.
*		      Added XIntc_RegisterFastHandler API to register fast
*		      interrupt handlers using base address.
* 2.06a bss  01/28/13 To support Cascade mode:
* 		      Added XIN_INTC_NOCASCADE,XIN_INTC_PRIMARY,
*		      XIN_INTC_SECONDARY,XIN_INTC_LAST and
*		      XIN_CONTROLLER_MAX_INTRS  macros
*		      Added NumberofIntrs and IntcType fields in XIntc_Config
*		      structure.
*		      Modified XIntc_Initialize,XIntc_Start,XIntc_Connect
*		      XIntc_Disconnect,XIntc_Enable,XIntc_Disable,
*		      XIntc_Acknowledge,XIntc_ConnectFastHandler and
*		      XIntc_SetNormalIntrMode APIs.Added XIntc_InitializeSlaves
*		      API in xintc.c
*  		      Modified XIntc_DeviceInterruptHandler,
*  		      XIntc_SetIntrSvcOption,XIntc_RegisterHandler and
*		      XIntc_RegisterFastHandler APIs.Added XIntc_CascadeHandler
*		      API in xintc_l.c.
*		      Modified XIntc_SetOptions API in xintc_options.c.
*		      Modified XIntc_SimulateIntr API in xintc_selftest.c.
*		      Modified driver tcl:
*			to check for Cascade mode and generate XPAR_INTC_TYPE
*			for each controller.
*			Generate XPAR_INTC_MAX_NUM_INTR_INPUTS by adding all
*			interrupt sources of all Controllers in Cascade mode.
* 2.07a bss  10/18/13 To support Nested interrupts:
*		      Modified XIntc_DeviceInterruptHandler API.
*		      Added XIN_ILR_OFFSET macro in xintc_l.h.
*		      Modified driver tcl to generate HAS_ILR parameter in
*		      xparameters.h
* 3.0   bss  01/28/13 Modified xintc.c to initialize IVAR register with
*		      XPAR_MICROBLAZE_BASE_VECTORS + 0x10 to fix
*		      CR#765931.
*		      Modified driver tcl to generate XPAR_AXI_INTC_0_TYPE
*		      correctly(CR#764865).
*
* @note
*		For Cascade mode, Interrupt IDs are generated in xparameters.h
*		as shown below:
*
*	    Master/Primary INTC
*		 ______
*		|      |-0      Secondary INTC
*		|      |-.         ______
*		|      |-.        |      |-32        Last INTC
*		|      |-.        |      |-.          ______
*		|______|<-31------|      |-.         |      |-64
*			          |      |-.         |      |-.
*			          |______|<-63-------|      |-.
*                                                    |      |-.
*                                                    |______|-95
*
*		All driver functions has to be called using DeviceId/
*		InstancePtr/BaseAddress of Primary/Master Controller and
*		Interrupts IDs generated in xparameters.h only.
*		Driver functions takes care of Slave Controllers based on
*		Interrupt ID passed. User must not use Interrupt source/ID
*		31 of Primary and Secondary controllers to call driver
*		functions.
*
*		For nested interrupts, XIntc_DeviceInterruptHandler saves
*		microblaze r14 register on entry and restores on exit. This is
*		required since compiler does not support nesting. It enables
*		Microblaze interrupts after blocking further interrupts from
*		the current interrupt number and interrupts below current
*		interrupt proirity by writing to Interrupt Level Register of
*		INTC on entry. On exit, it disables microblaze interrupts and
*		restores ILR register default value(0xFFFFFFFF)back. It is
*		recommended to increase STACK_SIZE in linker script for nested
*		interrupts.
* 3.0     adk    12/10/13  Updated as per the New Tcl API's
* 3.0 	  adk 	 17/02/14  Fixed the CR:771287 Changes are made in the intc
* 		           driver tcl.
* 3.1     adk    8/4/14    Fixed the CR:783248 Changes are made in
*			   the test-app tcl
* 3.2     bss    4/8/14    Fixed driver tcl to handle external interrupt pins
*			   correctly (CR#799609).
*
* </pre>
*
******************************************************************************/

#ifndef XINTC_H			/* prevent circular inclusions */
#define XINTC_H			/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif


/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xparameters.h"
#include "xstatus.h"
#include "xintc_l.h"

/************************** Constant Definitions *****************************/

/**
 * @name Configuration options
 * These options are used in XIntc_SetOptions() to configure the device.
 * @{
 */
/**
 * <pre>
 * XIN_SVC_SGL_ISR_OPTION	Service the highest priority pending interrupt
 *				and then return.
 * XIN_SVC_ALL_ISRS_OPTION	Service all of the pending interrupts and then
 *				return.
 * </pre>
 */
#define XIN_SVC_SGL_ISR_OPTION  1UL
#define XIN_SVC_ALL_ISRS_OPTION 2UL
/*@}*/

/**
 * @name Start modes
 * One of these values is passed to XIntc_Start() to start the device.
 * @{
 */
/** Simulation only mode, no hardware interrupts recognized */
#define XIN_SIMULATION_MODE     0
/** Real mode, no simulation allowed, hardware interrupts recognized */
#define XIN_REAL_MODE           1
/*@}*/

/**
 * @name Masks to specify Interrupt Controller Mode
 * @{
 */
#define XIN_INTC_NOCASCADE     	0	/* Normal - No Cascade Mode */
#define XIN_INTC_PRIMARY     	1	/* Master/Primary controller */
#define XIN_INTC_SECONDARY     	2	/* Secondary Slave Controllers */
#define XIN_INTC_LAST     	3	/* Last Slave Controller */

/*@}*/

/**
 * @name Mask to specify maximum number of interrupt sources per controller
 * @{
 */
#define XIN_CONTROLLER_MAX_INTRS	32  /* Each Controller has 32
					       interrupt pins */
/*@}*/

/**************************** Type Definitions *******************************/

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;		/**< Unique ID  of device */
	u32 BaseAddress;	/**< Register base address */
	u32 AckBeforeService;	/**< Ack location per interrupt */
	int FastIntr;		/**< Fast Interrupt enabled */
	u32 IntVectorAddr;	/**< Interrupt Vector Address */
	int NumberofIntrs;      /**< Number of Interrupt sources */
	u32 Options;		/**< Device options */
	int IntcType;		/**< Intc type 0 - No Cascade Mode
				               1 - primary instance
				               2 - secondary instance
				               3 - last instance */

/** Static vector table of interrupt handlers */
#if XPAR_INTC_0_INTC_TYPE != XIN_INTC_NOCASCADE
	XIntc_VectorTableEntry HandlerTable[XIN_CONTROLLER_MAX_INTRS];
#else
	XIntc_VectorTableEntry HandlerTable[XPAR_INTC_MAX_NUM_INTR_INPUTS];
#endif

} XIntc_Config;

/**
 * The XIntc driver instance data. The user is required to allocate a
 * variable of this type for every intc device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	u32 BaseAddress;	 /**< Base address of registers */
	u32 IsReady;		 /**< Device is initialized and ready */
	u32 IsStarted;		 /**< Device has been started */
	u32 UnhandledInterrupts; /**< Intc Statistics */
	XIntc_Config *CfgPtr;	 /**< Pointer to instance config entry */

} XIntc;

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/*
 * Required functions in xintc.c
 */
int XIntc_Initialize(XIntc * InstancePtr, u16 DeviceId);

int XIntc_Start(XIntc * InstancePtr, u8 Mode);
void XIntc_Stop(XIntc * InstancePtr);

int XIntc_Connect(XIntc * InstancePtr, u8 Id,
		  XInterruptHandler Handler, void *CallBackRef);
void XIntc_Disconnect(XIntc * InstancePtr, u8 Id);

void XIntc_Enable(XIntc * InstancePtr, u8 Id);
void XIntc_Disable(XIntc * InstancePtr, u8 Id);

void XIntc_Acknowledge(XIntc * InstancePtr, u8 Id);

XIntc_Config *XIntc_LookupConfig(u16 DeviceId);

int XIntc_ConnectFastHandler(XIntc *InstancePtr, u8 Id,
				XFastInterruptHandler Handler);
void XIntc_SetNormalIntrMode(XIntc *InstancePtr, u8 Id);

/*
 * Interrupt functions in xintr_intr.c
 */
void XIntc_VoidInterruptHandler(void);
void XIntc_InterruptHandler(XIntc * InstancePtr);

/*
 * Options functions in xintc_options.c
 */
int XIntc_SetOptions(XIntc * InstancePtr, u32 Options);
u32 XIntc_GetOptions(XIntc * InstancePtr);

/*
 * Self-test functions in xintc_selftest.c
 */
int XIntc_SelfTest(XIntc * InstancePtr);
int XIntc_SimulateIntr(XIntc * InstancePtr, u8 Id);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
