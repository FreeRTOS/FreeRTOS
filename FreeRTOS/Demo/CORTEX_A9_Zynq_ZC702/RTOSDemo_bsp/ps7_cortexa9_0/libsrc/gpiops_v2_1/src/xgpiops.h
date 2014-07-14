/******************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
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
* @file xgpiops.h
*
* The Xilinx PS GPIO driver. This driver supports the Xilinx PS GPIO
* Controller.
*
* The GPIO Controller supports the following features:
*	- 4 banks
*	- Masked writes (There are no masked reads)
*	- Bypass mode
*	- Configurable Interrupts (Level/Edge)
*
* This driver is intended to be RTOS and processor independent. Any needs for
* dynamic memory management, threads or thread mutual exclusion, virtual
* memory, or cache control must be satisfied by the layer above this driver.

* This driver supports all the features listed above, if applicable.
*
* <b>Driver Description</b>
*
* The device driver enables higher layer software (e.g., an application) to
* communicate to the GPIO.
*
* <b>Interrupts</b>
*
* The driver provides interrupt management functions and an interrupt handler.
* Users of this driver need to provide callback functions. An interrupt handler
* example is available with the driver.
*
* <b>Threads</b>
*
* This driver is not thread safe. Any needs for threads or thread mutual
* exclusion must be satisfied by the layer above this driver.
*
* <b>Asserts</b>
*
* Asserts are used within all Xilinx drivers to enforce constraints on argument
* values. Asserts can be turned off on a system-wide basis by defining, at
* compile time, the NDEBUG identifier. By default, asserts are turned on and it
* is recommended that users leave asserts on during development.
*
* <b>Building the driver</b>
*
* The XGpioPs driver is composed of several source files. This allows the user
* to build and link only those parts of the driver that are necessary.
* <br><br>
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sv   01/15/10 First Release
* 1.01a sv   04/15/12 Removed the APIs XGpioPs_SetMode, XGpioPs_SetModePin
*                     XGpioPs_GetMode, XGpioPs_GetModePin as they are not
*		      relevant to Zynq device.The interrupts are disabled
*		      for output pins on all banks during initialization.
* 1.02a hk   08/22/13 Added low level reset API
* 2.1   hk   04/29/14 Use Input data register DATA_RO for read. CR# 771667.
*
* </pre>
*
******************************************************************************/
#ifndef XGPIOPS_H		/* prevent circular inclusions */
#define XGPIOPS_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xgpiops_hw.h"

/************************** Constant Definitions *****************************/

/** @name Interrupt types
 *  @{
 * The following constants define the interrupt types that can be set for each
 * GPIO pin.
 */
#define XGPIOPS_IRQ_TYPE_EDGE_RISING	0  /**< Interrupt on Rising edge */
#define XGPIOPS_IRQ_TYPE_EDGE_FALLING	1  /**< Interrupt Falling edge */
#define XGPIOPS_IRQ_TYPE_EDGE_BOTH	2  /**< Interrupt on both edges */
#define XGPIOPS_IRQ_TYPE_LEVEL_HIGH	3  /**< Interrupt on high level */
#define XGPIOPS_IRQ_TYPE_LEVEL_LOW	4  /**< Interrupt on low level */
/*@}*/

#define XGPIOPS_BANK0			0  /**< GPIO Bank 0 */
#define XGPIOPS_BANK1			1  /**< GPIO Bank 1 */
#define XGPIOPS_BANK2			2  /**< GPIO Bank 2 */
#define XGPIOPS_BANK3			3  /**< GPIO Bank 3 */

#define XGPIOPS_MAX_BANKS		4  /**< Max banks in a GPIO device */
#define XGPIOPS_BANK_MAX_PINS		32 /**< Max pins in a GPIO bank */

#define XGPIOPS_DEVICE_MAX_PIN_NUM	118 /*< Max pins in the GPIO device
					      * 0 - 31,  Bank 0
					      * 32 - 53, Bank 1
					      *	54 - 85, Bank 2
					      *	86 - 117, Bank 3
					      */

/**************************** Type Definitions *******************************/

/****************************************************************************/
/**
 * This handler data type allows the user to define a callback function to
 * handle the interrupts for the GPIO device. The application using this
 * driver is expected to define a handler of this type, to support interrupt
 * driven mode. The handler executes in an interrupt context such that minimal
 * processing should be performed.
 *
 * @param	CallBackRef is a callback reference passed in by the upper layer
 *		when setting the callback functions for a GPIO bank. It is
 *		passed back to the upper layer when the callback is invoked. Its
 *		type is not important to the driver component, so it is a void
 *		pointer.
 * @param	Bank is the bank for which the interrupt status has changed.
 * @param	Status is the Interrupt status of the GPIO bank.
 *
 *****************************************************************************/
typedef void (*XGpioPs_Handler) (void *CallBackRef, int Bank, u32 Status);

/**
 * This typedef contains configuration information for a device.
 */
typedef struct {
	u16 DeviceId;		/**< Unique ID of device */
	u32 BaseAddr;		/**< Register base address */
} XGpioPs_Config;

/**
 * The XGpioPs driver instance data. The user is required to allocate a
 * variable of this type for the GPIO device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XGpioPs_Config GpioConfig;	/**< Device configuration */
	u32 IsReady;			/**< Device is initialized and ready */
	XGpioPs_Handler Handler;	/**< Status handlers for all banks */
	void *CallBackRef; 		/**< Callback ref for bank handlers */
} XGpioPs;

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/*
 * Functions in xgpiops.c
 */
int XGpioPs_CfgInitialize(XGpioPs *InstancePtr, XGpioPs_Config *ConfigPtr,
			   u32 EffectiveAddr);

/*
 * Bank APIs in xgpiops.c
 */
u32 XGpioPs_Read(XGpioPs *InstancePtr, u8 Bank);
void XGpioPs_Write(XGpioPs *InstancePtr, u8 Bank, u32 Data);
void XGpioPs_SetDirection(XGpioPs *InstancePtr, u8 Bank, u32 Direction);
u32 XGpioPs_GetDirection(XGpioPs *InstancePtr, u8 Bank);
void XGpioPs_SetOutputEnable(XGpioPs *InstancePtr, u8 Bank, u32 Enable);
u32 XGpioPs_GetOutputEnable(XGpioPs *InstancePtr, u8 Bank);
void XGpioPs_GetBankPin(u8 PinNumber,	u8 *BankNumber, u8 *PinNumberInBank);

/*
 * Pin APIs in xgpiops.c
 */
int XGpioPs_ReadPin(XGpioPs *InstancePtr, int Pin);
void XGpioPs_WritePin(XGpioPs *InstancePtr, int Pin, int Data);
void XGpioPs_SetDirectionPin(XGpioPs *InstancePtr, int Pin, int Direction);
int XGpioPs_GetDirectionPin(XGpioPs *InstancePtr, int Pin);
void XGpioPs_SetOutputEnablePin(XGpioPs *InstancePtr, int Pin, int Enable);
int XGpioPs_GetOutputEnablePin(XGpioPs *InstancePtr, int Pin);

/*
 * Diagnostic functions in xgpiops_selftest.c
 */
int XGpioPs_SelfTest(XGpioPs *InstancePtr);

/*
 * Functions in xgpiops_intr.c
 */
/*
 * Bank APIs in xgpiops_intr.c
 */
void XGpioPs_IntrEnable(XGpioPs *InstancePtr, u8 Bank, u32 Mask);
void XGpioPs_IntrDisable(XGpioPs *InstancePtr, u8 Bank, u32 Mask);
u32 XGpioPs_IntrGetEnabled(XGpioPs *InstancePtr, u8 Bank);
u32 XGpioPs_IntrGetStatus(XGpioPs *InstancePtr, u8 Bank);
void XGpioPs_IntrClear(XGpioPs *InstancePtr, u8 Bank, u32 Mask);
void XGpioPs_SetIntrType(XGpioPs *InstancePtr, u8 Bank, u32 IntrType,
			  u32 IntrPolarity, u32 IntrOnAny);
void XGpioPs_GetIntrType(XGpioPs *InstancePtr, u8 Bank, u32 *IntrType,
			  u32 *IntrPolarity, u32 *IntrOnAny);
void XGpioPs_SetCallbackHandler(XGpioPs *InstancePtr, void *CallBackRef,
			     XGpioPs_Handler FuncPtr);
void XGpioPs_IntrHandler(XGpioPs *InstancePtr);

/*
 * Pin APIs in xgpiops_intr.c
 */
void XGpioPs_SetIntrTypePin(XGpioPs *InstancePtr, int Pin, u8 IrqType);
u8 XGpioPs_GetIntrTypePin(XGpioPs *InstancePtr, int Pin);

void XGpioPs_IntrEnablePin(XGpioPs *InstancePtr, int Pin);
void XGpioPs_IntrDisablePin(XGpioPs *InstancePtr, int Pin);
int XGpioPs_IntrGetEnabledPin(XGpioPs *InstancePtr, int Pin);
int XGpioPs_IntrGetStatusPin(XGpioPs *InstancePtr, int Pin);
void XGpioPs_IntrClearPin(XGpioPs *InstancePtr, int Pin);

/*
 * Functions in xgpiops_sinit.c
 */
XGpioPs_Config *XGpioPs_LookupConfig(u16 DeviceId);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
