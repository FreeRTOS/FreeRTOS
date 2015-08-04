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
* @file xintc_l.c
*
* This file contains low-level driver functions that can be used to access the
* device.  The user should refer to the hardware device specification for more
* details of the device operation.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00b jhl  04/24/02 First release
* 1.00c rpm  10/17/03 New release. Support the static vector table created
*                     in the xintc_g.c configuration table.
* 1.00c rpm  04/09/04 Added conditional compilation around the old handler
*                     XIntc_LowLevelInterruptHandler(). This handler will only
*                     be include/compiled if XPAR_INTC_SINGLE_DEVICE_ID is
*                     defined.
* 1.10c mta  03/21/07 Updated to new coding style
* 1.10c ecm  07/09/07 Read the ISR after the Acknowledge in the interrupt
*		      handler to support architectures with posted write bus
*		      access issues.
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs and  _m is removed
*		      from all the macro definitions.
* 2.04a bss  01/13/12 Removed the unused Register variable for warnings.
* 2.05a bss  08/18/12 Added XIntc_RegisterFastHandler API to register fast
*		      interrupt handlers using base address.
* 2.06a bss  01/28/13 To support Cascade mode:
*		      Modified XIntc_DeviceInterruptHandler,
*		      XIntc_SetIntrSvcOption,XIntc_RegisterHandler and
*		      XIntc_RegisterFastHandler APIs.
*		      Added XIntc_CascadeHandler API.
* 2.07a bss  10/18/13 Modified XIntc_DeviceInterruptHandler to support
*		      nested interrupts.
*
* </pre>
*
******************************************************************************/


/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xil_types.h"
#include "xil_assert.h"
#include "xintc.h"
#include "xintc_i.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

static XIntc_Config *LookupConfigByBaseAddress(u32 BaseAddress);

#if XPAR_INTC_0_INTC_TYPE != XIN_INTC_NOCASCADE
static void XIntc_CascadeHandler(void *DeviceId);
#endif

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
*
* This is the interrupt handler for the driver interface provided in this file
* when there can be no argument passed to the handler. In this case, we just
* use the globally defined device ID for the interrupt controller. This function
* is provided mostly for backward compatibility. The user should use
* XIntc_DeviceInterruptHandler() if possible.
*
* This function does not support multiple interrupt controller instances to be
* handled.
*
* The user must connect this function to the interrupt system such that it is
* called whenever the devices which are connected to it cause an interrupt.
*
* @return	None.
*
* @note
*
* The constant XPAR_INTC_SINGLE_DEVICE_ID must be defined for this handler
* to be included in the driver compilation.
*
******************************************************************************/
#ifdef XPAR_INTC_SINGLE_DEVICE_ID
void XIntc_LowLevelInterruptHandler(void)
{
	/*
	 * A level of indirection here because the interrupt handler used with
	 * the driver interface given in this file needs to remain void - no
	 * arguments.  So we need the globally defined device ID of THE
	 * interrupt controller.
	 */
	XIntc_DeviceInterruptHandler((void *) XPAR_INTC_SINGLE_DEVICE_ID);
}
#endif

/*****************************************************************************/
/**
*
* This function is the primary interrupt handler for the driver. It must be
* connected to the interrupt source such that is called when an interrupt of
* the interrupt controller is active. It will resolve which interrupts are
* active and enabled and call the appropriate interrupt handler. It uses
* the AckBeforeService flag in the configuration data to determine when to
* acknowledge the interrupt. Highest priority interrupts are serviced first.
* This function assumes that an interrupt vector table has been previously
* initialized.It does not verify that entries in the table are valid before
* calling an interrupt handler. In Cascade mode this function calls
* XIntc_CascadeHandler to handle interrupts of Master and Slave controllers.
* This functions also handles interrupts nesting by  saving and restoring link
* register of Microblaze and Interrupt Level register of interrupt controller
* properly.

* @param	DeviceId is the zero-based device ID defined in xparameters.h
*		of the interrupting interrupt controller. It is used as a direct
*		index into the configuration data, which contains the vector
*		table for the interrupt controller. Note that even though the
*		argument is a void pointer, the value is not a pointer but the
*		actual device ID.  The void pointer type is necessary to meet
*		the XInterruptHandler typedef for interrupt handlers.
*
* @return	None.
*
* @note		For nested interrupts, this function saves microblaze r14
*		register on entry and restores on exit. This is required since
*		compiler does not support nesting. This function enables
*		Microblaze interrupts after blocking further interrupts
*		from the current interrupt number and interrupts below current
*		interrupt proirity by writing to Interrupt Level Register of
*		INTC on entry. On exit, it disables microblaze interrupts and
*		restores ILR register default value(0xFFFFFFFF)back. It is
*		recommended to increase STACK_SIZE in linker script for nested
*		interrupts.
*
******************************************************************************/
void XIntc_DeviceInterruptHandler(void *DeviceId)
{
	u32 IntrStatus;
	u32 IntrMask = 1;
	int IntrNumber;
	XIntc_Config *CfgPtr;
	u32 Imr;

	/* Get the configuration data using the device ID */
	CfgPtr = &XIntc_ConfigTable[(u32)DeviceId];

#if XPAR_INTC_0_INTC_TYPE != XIN_INTC_NOCASCADE
	if (CfgPtr->IntcType != XIN_INTC_NOCASCADE) {
		XIntc_CascadeHandler(DeviceId);
	}
	else
#endif
	{ /* This extra brace is required for compilation in Cascade Mode */

#if XPAR_XINTC_HAS_ILR == TRUE
#ifdef __MICROBLAZE__
		volatile u32 R14_register;
		/* Save r14 register */
		R14_register = mfgpr(r14);
#endif
		volatile u32 ILR_reg;
		/* Save ILR register */
		ILR_reg = Xil_In32(CfgPtr->BaseAddress + XIN_ILR_OFFSET);
#endif
		/* Get the interrupts that are waiting to be serviced */
		IntrStatus = XIntc_GetIntrStatus(CfgPtr->BaseAddress);

		/* Mask the Fast Interrupts */
		if (CfgPtr->FastIntr == TRUE) {
			Imr = XIntc_In32(CfgPtr->BaseAddress + XIN_IMR_OFFSET);
			IntrStatus &=  ~Imr;
		}

		/* Service each interrupt that is active and enabled by
		 * checking each bit in the register from LSB to MSB which
		 * corresponds to an interrupt input signal
		 */
		for (IntrNumber = 0; IntrNumber < CfgPtr->NumberofIntrs;
								IntrNumber++) {
			if (IntrStatus & 1) {
				XIntc_VectorTableEntry *TablePtr;
#if XPAR_XINTC_HAS_ILR == TRUE
				/* Write to ILR the current interrupt
		 		* number
		 		*/
				Xil_Out32(CfgPtr->BaseAddress +
						XIN_ILR_OFFSET, IntrNumber);

				/* Read back ILR to ensure the value
			 	* has been updated and it is safe to
			 	* enable interrupts
		 		*/

				Xil_In32(CfgPtr->BaseAddress +
						XIN_ILR_OFFSET);

				/* Enable interrupts */
				Xil_ExceptionEnable();
#endif
				/* If the interrupt has been setup to
				 * acknowledge it before servicing the
				 * interrupt, then ack it */
				if (CfgPtr->AckBeforeService & IntrMask) {
					XIntc_AckIntr(CfgPtr->BaseAddress,
								IntrMask);
				}

				/* The interrupt is active and enabled, call
				 * the interrupt handler that was setup with
				 * the specified parameter
				 */
				TablePtr = &(CfgPtr->HandlerTable[IntrNumber]);
				TablePtr->Handler(TablePtr->CallBackRef);

				/* If the interrupt has been setup to
				 * acknowledge it after it has been serviced
				 * then ack it
				 */
				if ((CfgPtr->AckBeforeService &
							IntrMask) == 0) {
					XIntc_AckIntr(CfgPtr->BaseAddress,
								IntrMask);
				}

#if XPAR_XINTC_HAS_ILR == TRUE
				/* Disable interrupts */
				Xil_ExceptionDisable();
				/* Restore ILR */
				Xil_Out32(CfgPtr->BaseAddress + XIN_ILR_OFFSET,
					 			ILR_reg);
#endif
				/*
				 * Read the ISR again to handle architectures
				 * with posted write bus access issues.
				 */
				 XIntc_GetIntrStatus(CfgPtr->BaseAddress);

				/*
				 * If only the highest priority interrupt is to
				 * be serviced, exit loop and return after
				 * servicing
				 * the interrupt
				 */
				if (CfgPtr->Options == XIN_SVC_SGL_ISR_OPTION) {

#if XPAR_XINTC_HAS_ILR == TRUE
#ifdef __MICROBLAZE__
					/* Restore r14 */
					mtgpr(r14, R14_register);
#endif
#endif
					return;
				}
			}

			/* Move	 to the next interrupt to check */
			IntrMask <<= 1;
			IntrStatus >>= 1;

			/* If there are no other bits set indicating that all
			 * interrupts have been serviced, then exit the loop
			 */
			if (IntrStatus == 0) {
				break;
			}
		}
#if XPAR_XINTC_HAS_ILR == TRUE
#ifdef __MICROBLAZE__
		/* Restore r14 */
		mtgpr(r14, R14_register);
#endif
#endif
	}
}

/*****************************************************************************/
/**
*
* Set the interrupt service option, which can configure the driver so that it
* services only a single interrupt at a time when an interrupt occurs, or
* services all pending interrupts when an interrupt occurs. The default
* behavior when using the driver interface given in xintc.h file is to service
* only a single interrupt, whereas the default behavior when using the driver
* interface given in this file is to service all outstanding interrupts when an
* interrupt occurs. In Cascade mode same Option is set to Slave controllers.
*
* @param	BaseAddress is the unique identifier for a device.
* @param 	Option is XIN_SVC_SGL_ISR_OPTION if you want only a single
*		interrupt serviced when an interrupt occurs, or
*		XIN_SVC_ALL_ISRS_OPTION if you want all pending interrupts
*		serviced when an interrupt occurs.
*
* @return	None.
*
* @note
*
* Note that this function has no effect if the input base address is invalid.
*
******************************************************************************/
void XIntc_SetIntrSvcOption(u32 BaseAddress, int Option)
{
	XIntc_Config *CfgPtr;

	CfgPtr = LookupConfigByBaseAddress(BaseAddress);
	if (CfgPtr != NULL) {
		CfgPtr->Options = Option;
		/* If Cascade mode set the option for all Slaves */
		if (CfgPtr->IntcType != XIN_INTC_NOCASCADE) {
			int Index;
			for (Index = 1; Index <= XPAR_XINTC_NUM_INSTANCES - 1;
					Index++) {
				CfgPtr = XIntc_LookupConfig(Index);
				CfgPtr->Options = Option;
			}
		}
	}
}

/*****************************************************************************/
/**
*
* Register a handler function for a specific interrupt ID.  The vector table
* of the interrupt controller is updated, overwriting any previous handler.
* The handler function will be called when an interrupt occurs for the given
* interrupt ID.
*
* This function can also be used to remove a handler from the vector table
* by passing in the XIntc_DefaultHandler() as the handler and NULL as the
* callback reference.
* In Cascade mode Interrupt Id is used to set Handler for corresponding Slave
* Controller
*
* @param 	BaseAddress is the base address of the interrupt controller
*		whose vector table will be modified.
* @param 	InterruptId is the interrupt ID to be associated with the input
*		handler.
* @param 	Handler is the function pointer that will be added to
*		the vector table for the given interrupt ID.
* @param	CallBackRef is the argument that will be passed to the new
*		handler function when it is called. This is user-specific.
*
* @return	None.
*
* @note
*
* Note that this function has no effect if the input base address is invalid.
*
******************************************************************************/
void XIntc_RegisterHandler(u32 BaseAddress, int InterruptId,
			   XInterruptHandler Handler, void *CallBackRef)
{
	XIntc_Config *CfgPtr;

	CfgPtr = LookupConfigByBaseAddress(BaseAddress);

	if (CfgPtr != NULL) {

		if (InterruptId > 31) {
			CfgPtr = XIntc_LookupConfig(InterruptId/32);
			CfgPtr->HandlerTable[InterruptId%32].Handler = Handler;
			CfgPtr->HandlerTable[InterruptId%32].CallBackRef =
								CallBackRef;
		}
		else {
			CfgPtr->HandlerTable[InterruptId].Handler = Handler;
			CfgPtr->HandlerTable[InterruptId].CallBackRef =
								CallBackRef;
		}
	}
}


/*****************************************************************************/
/**
*
* Looks up the device configuration based on the base address of the device.
* A table contains the configuration info for each device in the system.
*
* @param	BaseAddress is the unique identifier for a device.
*
* @return
*
* A pointer to the configuration structure for the specified device, or
* NULL if the device was not found.
*
* @note		None.
*
******************************************************************************/
static XIntc_Config *LookupConfigByBaseAddress(u32 BaseAddress)
{
	XIntc_Config *CfgPtr = NULL;
	int Index;

	for (Index = 0; Index < XPAR_XINTC_NUM_INSTANCES; Index++) {
		if (XIntc_ConfigTable[Index].BaseAddress == BaseAddress) {
			CfgPtr = &XIntc_ConfigTable[Index];
			break;
		}
	}

	return CfgPtr;
}

/*****************************************************************************/
/**
*
* Register a fast handler function for a specific interrupt ID. The handler
* function will be called when an interrupt occurs for the given interrupt ID.
* In Cascade mode Interrupt Id is used to set Handler for corresponding Slave
* Controller
*
* @param 	BaseAddress is the base address of the interrupt controller
*		whose vector table will be modified.
* @param 	InterruptId is the interrupt ID to be associated with the input
*		handler.
* @param 	FastHandler is the function pointer that will be called when
*   		interrupt occurs
*
* @return	None.
*
* @note
*
* Note that this function has no effect if the input base address is invalid.
*
******************************************************************************/
void XIntc_RegisterFastHandler(u32 BaseAddress, u8 Id,
					XFastInterruptHandler FastHandler)
{
	u32 CurrentIER;
	u32 Mask;
	u32 Imr;
	XIntc_Config *CfgPtr;


	if (Id > 31) {
		/* Enable user required Id in Slave controller */
		CfgPtr = XIntc_LookupConfig(Id/32);

		/* Get the Enabled Interrupts */
		CurrentIER = XIntc_In32(CfgPtr->BaseAddress + XIN_IER_OFFSET);

		/* Convert from integer id to bit mask */
		Mask = XIntc_BitPosMask[(Id%32)];

		/* Disable the Interrupt if it was enabled before calling
		 * this function
		 */
		if (CurrentIER & Mask) {
			XIntc_Out32(CfgPtr->BaseAddress + XIN_IER_OFFSET,
		    					(CurrentIER & ~Mask));
		}

		XIntc_Out32(CfgPtr->BaseAddress + XIN_IVAR_OFFSET +
					((Id%32) * 4), (u32) FastHandler);

		/* Slave controllers in Cascade Mode should have all as Fast
		 * interrupts or Normal interrupts, mixed interrupts are not
		 * supported
		 */
		XIntc_Out32(CfgPtr->BaseAddress + XIN_IMR_OFFSET, 0xFFFFFFFF);

		/* Enable the Interrupt if it was enabled before calling this
		 * function
		 */
		if (CurrentIER & Mask) {
			XIntc_Out32(CfgPtr->BaseAddress + XIN_IER_OFFSET,
		    				(CurrentIER | Mask));
		}
	}
	else {

		CurrentIER = XIntc_In32(BaseAddress + XIN_IER_OFFSET);

		/* Convert from integer id to bit mask */
		Mask = XIntc_BitPosMask[Id];

		if (CurrentIER & Mask) {
			/* Disable Interrupt if it was enabled */
			CurrentIER = XIntc_In32(BaseAddress + XIN_IER_OFFSET);
			XIntc_Out32(BaseAddress + XIN_IER_OFFSET,
							(CurrentIER & ~Mask));
		}

		XIntc_Out32(BaseAddress + XIN_IVAR_OFFSET + (Id * 4),
					    	(u32) FastHandler);

		Imr = XIntc_In32(BaseAddress + XIN_IMR_OFFSET);
		XIntc_Out32(BaseAddress + XIN_IMR_OFFSET, Imr | Mask);


		/* Enable Interrupt if it was enabled before calling
		 * this function
		 */
		if (CurrentIER & Mask) {
			CurrentIER = XIntc_In32(BaseAddress + XIN_IER_OFFSET);
			XIntc_Out32(BaseAddress + XIN_IER_OFFSET,
							(CurrentIER | Mask));
		}
	}
}

#if XPAR_INTC_0_INTC_TYPE != XIN_INTC_NOCASCADE
/*****************************************************************************/
/**
*
* This function is called by primary interrupt handler for the driver to handle
* all Controllers in Cascade mode.It will resolve which interrupts are active
* and enabled and call the appropriate interrupt handler. It uses the
* AckBeforeService flag in the configuration data to determine when to
* acknowledge the interrupt. Highest priority interrupts are serviced first.
* This function assumes that an interrupt vector table has been previously
* initialized.  It does not verify that entries in the table are valid before
* calling an interrupt handler.This function calls itself recursively to handle
* all interrupt controllers.
*
* @param	DeviceId is the zero-based device ID defined in xparameters.h
*		of the interrupting interrupt controller. It is used as a direct
*		index into the configuration data, which contains the vector
*		table for the interrupt controller.
*
* @return	None.
*
* @note
*
******************************************************************************/
static void XIntc_CascadeHandler(void *DeviceId)
{
	u32 IntrStatus;
	u32 IntrMask = 1;
	int IntrNumber;
	u32 Imr;
	XIntc_Config *CfgPtr;
	static int Id = 0;

	/* Get the configuration data using the device ID */
	CfgPtr = &XIntc_ConfigTable[(u32)DeviceId];

	/* Get the interrupts that are waiting to be serviced */
	IntrStatus = XIntc_GetIntrStatus(CfgPtr->BaseAddress);

	/* Mask the Fast Interrupts */
	if (CfgPtr->FastIntr == TRUE) {
		Imr = XIntc_In32(CfgPtr->BaseAddress + XIN_IMR_OFFSET);
		IntrStatus &=  ~Imr;
	}

	/* Service each interrupt that is active and enabled by
	 * checking each bit in the register from LSB to MSB which
	 * corresponds to an interrupt input signal
	 */
	for (IntrNumber = 0; IntrNumber < CfgPtr->NumberofIntrs; IntrNumber++) {
		if (IntrStatus & 1) {
			XIntc_VectorTableEntry *TablePtr;

			/* In Cascade mode call this function recursively
			 * for interrupt id 31 and until interrupts of last
			 * instance/controller are handled
			 */
			if ((IntrNumber == 31) &&
			  (CfgPtr->IntcType != XIN_INTC_LAST) &&
			  (CfgPtr->IntcType != XIN_INTC_NOCASCADE)) {
				XIntc_CascadeHandler((void *)++Id);
				Id--;
			}

			/* If the interrupt has been setup to
			 * acknowledge it before servicing the
			 * interrupt, then ack it */
			if (CfgPtr->AckBeforeService & IntrMask) {
				XIntc_AckIntr(CfgPtr->BaseAddress, IntrMask);
			}

			/* Handler of 31 interrupt Id has to be called only
			 * for Last controller in cascade Mode
			 */
			if (!((IntrNumber == 31) &&
			  (CfgPtr->IntcType != XIN_INTC_LAST) &&
			  (CfgPtr->IntcType != XIN_INTC_NOCASCADE))) {

				/* The interrupt is active and enabled, call
				 * the interrupt handler that was setup with
				 * the specified parameter
				 */
				TablePtr = &(CfgPtr->HandlerTable[IntrNumber]);
				TablePtr->Handler(TablePtr->CallBackRef);
			}
			/* If the interrupt has been setup to acknowledge it
			 * after it has been serviced then ack it
			 */
			if ((CfgPtr->AckBeforeService & IntrMask) == 0) {
				XIntc_AckIntr(CfgPtr->BaseAddress, IntrMask);
			}

			/*
			 * Read the ISR again to handle architectures with
			 * posted write bus access issues.
			 */
			 XIntc_GetIntrStatus(CfgPtr->BaseAddress);

			/*
			 * If only the highest priority interrupt is to be
			 * serviced, exit loop and return after servicing
			 * the interrupt
			 */
			if (CfgPtr->Options == XIN_SVC_SGL_ISR_OPTION) {
				return;
			}
		}

		/* Move	 to the next interrupt to check */
		IntrMask <<= 1;
		IntrStatus >>= 1;

		/* If there are no other bits set indicating that all interrupts
		 * have been serviced, then exit the loop
		 */
		if (IntrStatus == 0) {
			break;
		}
	}
}
#endif
