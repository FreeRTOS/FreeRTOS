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
* @file xbram.h
* @addtogroup bram_v4_0
* @{
* @details
*
* If ECC is not enabled, this driver exists only to allow the tools to
* create a memory test application and to populate xparameters.h with memory
* range constants. In this case there is no source code.
*
* If ECC is enabled, this file contains the software API definition of the
* Xilinx BRAM Interface Controller (XBram) device driver.
*
* The Xilinx BRAM controller is a soft IP core designed for Xilinx
* FPGAs and contains the following general features:
*   - LMB v2.0 bus interfaces with byte enable support
*   - Used in conjunction with bram_block peripheral to provide fast BRAM
*     memory solution for MicroBlaze ILMB and DLMB ports
*   - Supports byte, half-word, and word transfers
*   - Supports optional BRAM error correction and detection.
*
* The driver provides interrupt management functions. Implementation of
* interrupt handlers is left to the user. Refer to the provided interrupt
* example in the examples directory for details.
*
* This driver is intended to be RTOS and processor independent. Any needs for
* dynamic memory management, threads or thread mutual exclusion, virtual
* memory, or cache control must be satisfied by the layer above this driver.
*
* <b>Initialization & Configuration</b>
*
* The XBram_Config structure is used by the driver to configure
* itself. This configuration structure is typically created by the tool-chain
* based on HW build properties.
*
* To support multiple runtime loading and initialization strategies employed
* by various operating systems, the driver instance can be initialized as
* follows:
*
*   - XBram_CfgInitialize(InstancePtr, CfgPtr, EffectiveAddr) -
*     Uses a configuration structure provided by the caller. If running in a
*     system with address translation, the provided virtual memory base address
*     replaces the physical address present in the configuration structure.
*
* @note
*
* This API utilizes 32 bit I/O to the BRAM registers. With less
* than 32 bits, the unused bits from registers are read as zero and written as
* don't cares.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 3.00a sa  05/11/10 Added ECC support
* 3.01a sa  01/13/12  Changed Selftest API from
*		      XBram_SelfTest(XBram *InstancePtr) to
*		      XBram_SelfTest(XBram *InstancePtr, u8 IntMask) and
*		      fixed a problem with interrupt generation for CR 639274
*		      Modified Selftest example to return XST_SUCCESS when
*		      ECC is not enabled and return XST_FAILURE when ECC is
*		      enabled and Control Base Address is zero (CR 636581)
*		      Modified Selftest to use correct CorrectableCounterBits
*		      for CR 635655
*		      Updated to check CorrectableFailingDataRegs in the case
*		      of LMB BRAM.
* 		      Added CorrectableFailingDataRegs and
*		      UncorrectableFailingDataRegs to the config structure to
*		      distinguish between AXI BRAM and LMB BRAM.
*		      These registers are not present in the current version of
*		      the AXI BRAM Controller.
* 3.02a sa 04/16/12   Added test of byte and halfword read-modify-write
* 3.02a sa 04/16/12   Modified driver tcl to sort the address parameters
*  	       	      to support both xps and vivado designs.
* 3.02a adk 24/4/13   Modified the tcl file to avoid warnings
*	       	      when ecc is disabled cr:705002.
* 3.03a bss 05/22/13  Added Xil_DCacheFlushRange in xbram_selftest.c to
*		      flush the Cache after writing to BRAM in InjectErrors
*		      API(CR #719011)
* 4.0   adk  19/12/13 Updated as per the New Tcl API's
* 4.1   sk   11/10/15 Used UINTPTR instead of u32 for Baseaddress CR# 867425.
*                     Changed the prototype of XBram_CfgInitialize API.
* </pre>
*****************************************************************************/
#ifndef XBRAM_H		/* prevent circular inclusions */
#define XBRAM_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xbram_hw.h"

/************************** Constant Definitions ****************************/


/**************************** Type Definitions ******************************/

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;			   /**< Unique ID  of device */
	u32 DataWidth;			   /**< BRAM data width */
	int EccPresent;			   /**< Is ECC supported in H/W */
	int FaultInjectionPresent;	   /**< Is Fault Injection
					     *  supported in H/W */
	int CorrectableFailingRegisters;   /**< Is Correctable Failing Registers
					     *  supported in H/W */
	int CorrectableFailingDataRegs;    /**< Is Correctable Failing Data
					    *   Registers supported in H/W */
	int UncorrectableFailingRegisters; /**< Is Un-correctable Failing
					     *  Registers supported in H/W */
	int UncorrectableFailingDataRegs;  /**< Is Un-correctable Failing Data
					     *  Registers supported in H/W */
	int EccStatusInterruptPresent;	   /**< Are ECC status and interrupts
					     *  supported in H/W */
	int CorrectableCounterBits;	   /**< Number of bits in the
					     *  Correctable Error Counter */
	int EccOnOffRegister;		   /**< Is ECC on/off register supported
					     *  in h/w */
	int EccOnOffResetValue;		   /**< Reset value of the ECC on/off
					     *  register in h/w */
	int WriteAccess;		   /**< Is write access enabled in
					     *  h/w */
	u32 MemBaseAddress;		   /**< Device memory base address */
	u32 MemHighAddress;		   /**< Device memory high address */
	UINTPTR CtrlBaseAddress;		   /**< Device register base address.*/
	UINTPTR CtrlHighAddress;		   /**< Device register base address.*/
} XBram_Config;

/**
 * The XBram driver instance data. The user is required to
 * allocate a variable of this type for every BRAM device in the
 * system. A pointer to a variable of this type is then passed to the driver
 * API functions.
 */
typedef struct {
	XBram_Config  Config;		/* BRAM config structure */
	u32 IsReady;			/* Device is initialized and ready */
} XBram;

/***************** Macros (Inline Functions) Definitions ********************/


/************************** Function Prototypes *****************************/

/*
 * Functions in xbram_sinit.c
 */
XBram_Config *XBram_LookupConfig(u16 DeviceId);

/*
 * Functions implemented in xbram.c
 */
int XBram_CfgInitialize(XBram *InstancePtr, XBram_Config *Config,
			UINTPTR EffectiveAddr);

/*
 * Functions implemented in xbram_selftest.c
 */
int XBram_SelfTest(XBram *InstancePtr, u8 IntMask);

/*
 * Functions implemented in xbram_intr.c
 */
void XBram_InterruptEnable(XBram *InstancePtr, u32 Mask);
void XBram_InterruptDisable(XBram *InstancePtr, u32 Mask);
void XBram_InterruptClear(XBram *InstancePtr, u32 Mask);
u32 XBram_InterruptGetEnabled(XBram *InstancePtr);
u32 XBram_InterruptGetStatus(XBram *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
