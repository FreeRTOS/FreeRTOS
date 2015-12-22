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
* @file xscugic_hw.c
*
* This file contains low-level driver functions that can be used to access the
* device.  The user should refer to the hardware device specification for more
* details of the device operation.
* These routines are used when the user does not want to create an instance of
* XScuGic structure but still wants to use the ScuGic device. Hence the
* routines provided here take device id or scugic base address as arguments.
* Separate static versions of DistInit and CPUInit are provided to implement
* the low level driver routines.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.01a sdm  07/18/11 First release
* 1.03a srt  02/27/13 Moved Offset calculation macros from *_hw.c (CR
*		      702687).
*					  Added support to direct interrupts to the appropriate CPU.
*			  Earlier interrupts were directed to CPU1 (hard coded). Now
*			  depending upon the CPU selected by the user (xparameters.h),
*			  interrupts will be directed to the relevant CPU.
*			  This fixes CR 699688.
* 1.04a hk   05/04/13 Fix for CR#705621. Moved functions
*			  XScuGic_SetPriTrigTypeByDistAddr and
*             XScuGic_GetPriTrigTypeByDistAddr here from xscugic.c
* 3.00  kvn  02/13/15 Modified code for MISRA-C:2012 compliance.
*
* </pre>
*
******************************************************************************/


/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xscugic.h"
#include "xparameters.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

static void DistInit(XScuGic_Config *Config, u32 CpuID);
static void CPUInit(XScuGic_Config *Config);
static XScuGic_Config *LookupConfigByBaseAddress(u32 CpuBaseAddress);

/************************** Variable Definitions *****************************/

extern XScuGic_Config XScuGic_ConfigTable[XPAR_XSCUGIC_NUM_INSTANCES];

/*****************************************************************************/
/**
*
* DistInit initializes the distributor of the GIC. The
* initialization entails:
*
* - Write the trigger mode, priority and target CPU
* - All interrupt sources are disabled
* - Enable the distributor
*
* @param	InstancePtr is a pointer to the XScuGic instance.
* @param	CpuID is the Cpu ID to be initialized.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static void DistInit(XScuGic_Config *Config, u32 CpuID)
{
	u32 Int_Id;
	u32 LocalCpuID = CpuID;

#if USE_AMP==1
	#warning "Building GIC for AMP"

	/*
	 * The distrubutor should not be initialized by FreeRTOS in the case of
	 * AMP -- it is assumed that Linux is the master of this device in that
	 * case.
	 */
	return;
#endif

	XScuGic_WriteReg(Config->DistBaseAddress, XSCUGIC_DIST_EN_OFFSET, 0U);

	/*
	 * Set the security domains in the int_security registers for non-secure
	 * interrupts. All are secure, so leave at the default. Set to 1 for
	 * non-secure interrupts.
	 */


	/*
	 * For the Shared Peripheral Interrupts INT_ID[MAX..32], set:
	 */

	/*
	 * 1. The trigger mode in the int_config register
	 * Only write to the SPI interrupts, so start at 32
	 */
	for (Int_Id = 32U; Int_Id<XSCUGIC_MAX_NUM_INTR_INPUTS;Int_Id=Int_Id+16U) {
	/*
	 * Each INT_ID uses two bits, or 16 INT_ID per register
	 * Set them all to be level sensitive, active HIGH.
	 */
		XScuGic_WriteReg(Config->DistBaseAddress,
			XSCUGIC_INT_CFG_OFFSET_CALC(Int_Id), 0U);
	}


#define DEFAULT_PRIORITY	0xa0a0a0a0U
	for (Int_Id = 0U; Int_Id<XSCUGIC_MAX_NUM_INTR_INPUTS;Int_Id=Int_Id+4U) {
		/*
		 * 2. The priority using int the priority_level register
		 * The priority_level and spi_target registers use one byte per
		 * INT_ID.
		 * Write a default value that can be changed elsewhere.
		 */
		XScuGic_WriteReg(Config->DistBaseAddress,
				XSCUGIC_PRIORITY_OFFSET_CALC(Int_Id),
				DEFAULT_PRIORITY);
	}

	for (Int_Id = 32U; Int_Id<XSCUGIC_MAX_NUM_INTR_INPUTS;Int_Id=Int_Id+4U) {
		/*
		 * 3. The CPU interface in the spi_target register
		 * Only write to the SPI interrupts, so start at 32
		 */
		LocalCpuID |= LocalCpuID << 8U;
		LocalCpuID |= LocalCpuID << 16U;

		XScuGic_WriteReg(Config->DistBaseAddress,
				XSCUGIC_SPI_TARGET_OFFSET_CALC(Int_Id), LocalCpuID);
	}

	for (Int_Id = 0U; Int_Id<XSCUGIC_MAX_NUM_INTR_INPUTS;Int_Id=Int_Id+32U) {
	/*
	 * 4. Enable the SPI using the enable_set register. Leave all disabled
	 * for now.
	 */
		XScuGic_WriteReg(Config->DistBaseAddress,
		XSCUGIC_EN_DIS_OFFSET_CALC(XSCUGIC_DISABLE_OFFSET,
		Int_Id),
		0xFFFFFFFFU);

	}

	XScuGic_WriteReg(Config->DistBaseAddress, XSCUGIC_DIST_EN_OFFSET,
						XSCUGIC_EN_INT_MASK);

}

/*****************************************************************************/
/**
*
* CPUInit initializes the CPU Interface of the GIC. The initialization entails:
*
* - Set the priority of the CPU.
* - Enable the CPU interface
*
* @param	ConfigPtr is a pointer to a config table for the particular
*		device this driver is associated with.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static void CPUInit(XScuGic_Config *Config)
{
	/*
	 * Program the priority mask of the CPU using the Priority mask
	 * register
	 */
	XScuGic_WriteReg(Config->CpuBaseAddress, XSCUGIC_CPU_PRIOR_OFFSET,
									0xF0U);

	/*
	 * If the CPU operates in both security domains, set parameters in the
	 * control_s register.
	 * 1. Set FIQen=1 to use FIQ for secure interrupts,
	 * 2. Program the AckCtl bit
	 * 3. Program the SBPR bit to select the binary pointer behavior
	 * 4. Set EnableS = 1 to enable secure interrupts
	 * 5. Set EnbleNS = 1 to enable non secure interrupts
	 */

	/*
	 * If the CPU operates only in the secure domain, setup the
	 * control_s register.
	 * 1. Set FIQen=1,
	 * 2. Set EnableS=1, to enable the CPU interface to signal secure .
	 * interrupts Only enable the IRQ output unless secure interrupts
	 * are needed.
	 */
	XScuGic_WriteReg(Config->CpuBaseAddress, XSCUGIC_CONTROL_OFFSET, 0x07U);

}

/*****************************************************************************/
/**
*
* CfgInitialize a specific interrupt controller instance/driver. The
* initialization entails:
*
* - Initialize fields of the XScuGic structure
* - Initial vector table with stub function calls
* - All interrupt sources are disabled
*
* @param InstancePtr is a pointer to the XScuGic instance to be worked on.
* @param ConfigPtr is a pointer to a config table for the particular device
*        this driver is associated with.
* @param EffectiveAddr is the device base address in the virtual memory address
*        space. The caller is responsible for keeping the address mapping
*        from EffectiveAddr to the device physical base address unchanged
*        once this function is invoked. Unexpected errors may occur if the
*        address mapping changes after this function is called. If address
*        translation is not used, use Config->BaseAddress for this parameters,
*        passing the physical address instead.
*
* @return
*
* - XST_SUCCESS if initialization was successful
*
* @note
*
* None.
*
******************************************************************************/
s32 XScuGic_DeviceInitialize(u32 DeviceId)
{
	XScuGic_Config *Config;
	u32 Cpu_Id = (u32)XPAR_CPU_ID + (u32)1;

	Config = &XScuGic_ConfigTable[(u32 )DeviceId];

	DistInit(Config, Cpu_Id);

	CPUInit(Config);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* This function is the primary interrupt handler for the driver.  It must be
* connected to the interrupt source such that it is called when an interrupt of
* the interrupt controller is active. It will resolve which interrupts are
* active and enabled and call the appropriate interrupt handler. It uses
* the Interrupt Type information to determine when to acknowledge the
* interrupt.Highest priority interrupts are serviced first.
*
* This function assumes that an interrupt vector table has been previously
* initialized.  It does not verify that entries in the table are valid before
* calling an interrupt handler.
*
* @param	DeviceId is the unique identifier for the ScuGic device.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XScuGic_DeviceInterruptHandler(void *DeviceId)
{

	u32 InterruptID;
	u32 IntIDFull;
	XScuGic_VectorTableEntry *TablePtr;
	XScuGic_Config *CfgPtr;

	CfgPtr = &XScuGic_ConfigTable[(INTPTR )DeviceId];

	/*
	 * Read the int_ack register to identify the highest priority
	 * interrupt ID and make sure it is valid. Reading Int_Ack will
	 * clear the interrupt in the GIC.
	 */
	IntIDFull = XScuGic_ReadReg(CfgPtr->CpuBaseAddress, XSCUGIC_INT_ACK_OFFSET);
	InterruptID = IntIDFull & XSCUGIC_ACK_INTID_MASK;
	if(XSCUGIC_MAX_NUM_INTR_INPUTS < InterruptID){
		goto IntrExit;
	}

	/*
	 * If the interrupt is shared, do some locking here if there are
	 * multiple processors.
	 */
	/*
	 * If pre-eption is required:
	 * Re-enable pre-emption by setting the CPSR I bit for non-secure ,
	 * interrupts or the F bit for secure interrupts
	 */

	/*
	 * If we need to change security domains, issue a SMC instruction here.
	 */

	/*
	 * Execute the ISR. Jump into the Interrupt service routine based on
	 * the IRQSource. A software trigger is cleared by the ACK.
	 */
	TablePtr = &(CfgPtr->HandlerTable[InterruptID]);
	if(TablePtr != NULL) {
		TablePtr->Handler(TablePtr->CallBackRef);
	}

IntrExit:
	/*
	 * Write to the EOI register, we are all done here.
	 * Let this function return, the boot code will restore the stack.
	 */
	XScuGic_WriteReg(CfgPtr->CpuBaseAddress, XSCUGIC_EOI_OFFSET, IntIDFull);

	/*
	 * Return from the interrupt. Change security domains could happen
	 * here.
	 */
}

/*****************************************************************************/
/**
*
* Register a handler function for a specific interrupt ID.  The vector table
* of the interrupt controller is updated, overwriting any previous handler.
* The handler function will be called when an interrupt occurs for the given
* interrupt ID.
*
* @param	BaseAddress is the CPU Interface Register base address of the
*		interrupt controller whose vector table will be modified.
* @param	InterruptId is the interrupt ID to be associated with the input
*		handler.
* @param	Handler is the function pointer that will be added to
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
void XScuGic_RegisterHandler(u32 BaseAddress, s32 InterruptID,
			     Xil_InterruptHandler IntrHandler, void *CallBackRef)
{
	XScuGic_Config *CfgPtr;
	CfgPtr = LookupConfigByBaseAddress(BaseAddress);

	if(CfgPtr != NULL) {
		if( IntrHandler != NULL) {
			CfgPtr->HandlerTable[InterruptID].Handler = IntrHandler;
		}
		if( CallBackRef != NULL) {
			CfgPtr->HandlerTable[InterruptID].CallBackRef = CallBackRef;
		}
	}
}

/*****************************************************************************/
/**
*
* Looks up the device configuration based on the CPU interface base address of
* the device. A table contains the configuration info for each device in the
* system.
*
* @param	CpuBaseAddress is the CPU Interface Register base address.
*
* @return 	A pointer to the configuration structure for the specified
*		device, or NULL if the device was not found.
*
* @note		None.
*
******************************************************************************/
static XScuGic_Config *LookupConfigByBaseAddress(u32 CpuBaseAddress)
{
	XScuGic_Config *CfgPtr = NULL;
	u32 Index;

	for (Index = 0U; Index < XPAR_SCUGIC_NUM_INSTANCES; Index++) {
		if (XScuGic_ConfigTable[Index].CpuBaseAddress ==
				CpuBaseAddress) {
			CfgPtr = &XScuGic_ConfigTable[Index];
			break;
		}
	}

	return (XScuGic_Config *)CfgPtr;
}

/****************************************************************************/
/**
* Sets the interrupt priority and trigger type for the specificd IRQ source.
*
* @param	BaseAddr is the device base address
* @param	Int_Id is the IRQ source number to modify
* @param	Priority is the new priority for the IRQ source. 0 is highest
* 			priority, 0xF8 (248) is lowest. There are 32 priority levels
*			supported with a step of 8. Hence the supported priorities are
*			0, 8, 16, 32, 40 ..., 248.
* @param	Trigger is the new trigger type for the IRQ source.
* Each bit pair describes the configuration for an INT_ID.
* SFI    Read Only    b10 always
* PPI    Read Only    depending on how the PPIs are configured.
*                    b01    Active HIGH level sensitive
*                    b11 Rising edge sensitive
* SPI                LSB is read only.
*                    b01    Active HIGH level sensitive
*                    b11 Rising edge sensitive/
*
* @return	None.
*
* @note		This API has the similar functionality of XScuGic_SetPriority
*	        TriggerType() and should be used when there is no InstancePtr.
*
*****************************************************************************/
void XScuGic_SetPriTrigTypeByDistAddr(u32 DistBaseAddress, u32 Int_Id,
					u8 Priority, u8 Trigger)
{
	u32 RegValue;
	u8 LocalPriority = Priority;

	Xil_AssertVoid(Int_Id < XSCUGIC_MAX_NUM_INTR_INPUTS);
	Xil_AssertVoid(Trigger <= XSCUGIC_INT_CFG_MASK);
	Xil_AssertVoid(LocalPriority <= XSCUGIC_MAX_INTR_PRIO_VAL);

	/*
	 * Determine the register to write to using the Int_Id.
	 */
	RegValue = XScuGic_ReadReg(DistBaseAddress,
			XSCUGIC_PRIORITY_OFFSET_CALC(Int_Id));

	/*
	 * The priority bits are Bits 7 to 3 in GIC Priority Register. This
	 * means the number of priority levels supported are 32 and they are
	 * in steps of 8. The priorities can be 0, 8, 16, 32, 48, ... etc.
	 * The lower order 3 bits are masked before putting it in the register.
	 */
	LocalPriority = LocalPriority & XSCUGIC_INTR_PRIO_MASK;
	/*
	 * Shift and Mask the correct bits for the priority and trigger in the
	 * register
	 */
	RegValue &= ~(XSCUGIC_PRIORITY_MASK << ((Int_Id%4U)*8U));
	RegValue |= (u32)LocalPriority << ((Int_Id%4U)*8U);

	/*
	 * Write the value back to the register.
	 */
	XScuGic_WriteReg(DistBaseAddress, XSCUGIC_PRIORITY_OFFSET_CALC(Int_Id),
					RegValue);
	/*
	 * Determine the register to write to using the Int_Id.
	 */
	RegValue = XScuGic_ReadReg(DistBaseAddress,
			XSCUGIC_INT_CFG_OFFSET_CALC (Int_Id));

	/*
	 * Shift and Mask the correct bits for the priority and trigger in the
	 * register
	 */
	RegValue &= ~(XSCUGIC_INT_CFG_MASK << ((Int_Id%16U)*2U));
	RegValue |= (u32)Trigger << ((Int_Id%16U)*2U);

	/*
	 * Write the value back to the register.
	 */
	XScuGic_WriteReg(DistBaseAddress, XSCUGIC_INT_CFG_OFFSET_CALC(Int_Id),
				RegValue);
}

/****************************************************************************/
/**
* Gets the interrupt priority and trigger type for the specificd IRQ source.
*
* @param	BaseAddr is the device base address
* @param	Int_Id is the IRQ source number to modify
* @param	Priority is a pointer to the value of the priority of the IRQ
*		source. This is a return value.
* @param	Trigger is pointer to the value of the trigger of the IRQ
*		source. This is a return value.
*
* @return	None.
*
* @note		This API has the similar functionality of XScuGic_GetPriority
*	        TriggerType() and should be used when there is no InstancePtr.
*
*****************************************************************************/
void XScuGic_GetPriTrigTypeByDistAddr(u32 DistBaseAddress, u32 Int_Id,
					u8 *Priority, u8 *Trigger)
{
	u32 RegValue;

	Xil_AssertVoid(Int_Id < XSCUGIC_MAX_NUM_INTR_INPUTS);
	Xil_AssertVoid(Priority != NULL);
	Xil_AssertVoid(Trigger != NULL);

	/*
	 * Determine the register to read to using the Int_Id.
	 */
	RegValue = XScuGic_ReadReg(DistBaseAddress,
	    XSCUGIC_PRIORITY_OFFSET_CALC(Int_Id));

	/*
	 * Shift and Mask the correct bits for the priority and trigger in the
	 * register
	 */
	RegValue = RegValue >> ((Int_Id%4U)*8U);
	*Priority = (u8)(RegValue & XSCUGIC_PRIORITY_MASK);

	/*
	 * Determine the register to read to using the Int_Id.
	 */
	RegValue = XScuGic_ReadReg(DistBaseAddress,
	    XSCUGIC_INT_CFG_OFFSET_CALC (Int_Id));

	/*
	 * Shift and Mask the correct bits for the priority and trigger in the
	 * register
	 */
	RegValue = RegValue >> ((Int_Id%16U)*2U);

	*Trigger = (u8)(RegValue & XSCUGIC_INT_CFG_MASK);
}
