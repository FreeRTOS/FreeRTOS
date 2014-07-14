/******************************************************************************
*
* (c) Copyright 2010-12 Xilinx, Inc. All rights reserved.
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
/****************************************************************************/
/**
*
* @file xscuwdt.h
*
* The Xilinx SCU watchdog timer driver (XScuWdt) supports the Xilinx SCU private
* watchdog timer hardware.
*
* The XScuWdt driver supports the following features:
* - Watchdog mode
* - Timer mode
* - Auto reload (timer mode only)
*
* The watchdog counter register is a down counter and starts decrementing when
* the watchdog is started.
* In watchdog mode, when the counter reaches 0, the Reset flag is set in the
* Reset status register and the WDRESETREQ pin is asserted, causing a system
* reset. The Reset flag is not reset by normal processor reset and is cleared
* when written with a value of 1. This enables the user to differentiate a
* normal reset and a reset caused by watchdog time-out. The user needs to call
* XScuWdt_RestartWdt() periodically, to avoid the watchdog from being timed-out.
*
* The IsWdtExpired function can be used to check if the watchdog was the cause
* of the last reset. In this situation, call Initialize then call IsWdtExpired.
* If the result is true, watchdog timeout caused the last system reset. The
* application then needs to clear the Reset flag.
*
* In timer mode, when the counter reaches 0, the Event flag is set in the
* Interrupt status register and if interrupts are enabled, interrupt ID 30 is
* set as pending in the interrupt distributor. The IsTimerExpired function
* is used to check if the watchdog counter has decremented to 0 in timer mode.
* If auto-reload mode is enabled, the Counter register is automatically reloaded
* from the Load register.
*
* <b> Initialization and Configuration </b>
*
* The device driver enables higher layer software (e.g., an application) to
* communicate with the Watchdog Timer.
*
* XScuWdt_CfgInitialize() API is used to initialize the Watchdog Timer. The
* user needs to first call the XScuWdt_LookupConfig() API which returns
* the Configuration structure pointer which is passed as a parameter to
* the XScuWdt_CfgInitialize() API.
*
* <b>Interrupts</b>
*
* The SCU Watchdog Timer supports interrupts in Timer mode.
*
* This driver does not provide a Interrupt Service Routine (ISR) for the device.
* It is the responsibility of the application to provide one if needed. Refer to
* the interrupt example provided with this driver for details on using the
* Timer in interrupt mode.
*
* <b> Virtual Memory </b>
*
* This driver supports Virtual Memory. The RTOS is responsible for calculating
* the correct device base address in Virtual Memory space.
*
* <b> Threads </b>
*
* This driver is not thread safe. Any needs for threads or thread mutual
* exclusion must be satisfied by the layer above this driver.
*
* <b> Asserts </b>
*
* Asserts are used within all Xilinx drivers to enforce constraints on argument
* values. Asserts can be turned off on a system-wide basis by defining, at
* compile time, the NDEBUG identifier. By default, asserts are turned on and it
* is recommended that users leave asserts on during development.
*
* <b> Building the driver </b>
*
* The XScuWdt driver is composed of several source files. This allows the user
* to build and link only those parts of the driver that are necessary.
*
* <br><br>
*
* NOTE:
* The watchdog timer is not a part of the snoop control unit as indicated
* by the prefix "scu" in the name of the driver.
* It is an independent module in APU.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a sdm 01/15/10 First release
* 1.02a  sg 07/17/12 Included xil_assert.h for CR 667947. This is an issue
*		     when the xstatus.h in the common driver overwrites
*		     the xstatus.h of the standalone BSP during the
*		     libgen.
* </pre>
*
******************************************************************************/
#ifndef XSCUWDT_H		/* prevent circular inclusions */
#define XSCUWDT_H		/* by using protection macros */

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xscuwdt_hw.h"

#ifdef __cplusplus
extern "C" {
#endif

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;		/**< Unique ID of device */
	u32 BaseAddr;		/**< Base address of the device */
} XScuWdt_Config;

/**
 * The XScuWdt driver instance data. The user is required to allocate a
 * variable of this type for every watchdog/timer device in the system.
 * A pointer to a variable of this type is then passed to the driver API
 * functions.
 */
typedef struct {
	XScuWdt_Config Config;/**< Hardware Configuration */
	u32 IsReady;		/**< Device is initialized and ready */
	u32 IsStarted;		/**< Device watchdog timer is running */
} XScuWdt;

/***************** Macros (Inline Functions) Definitions *********************/
/****************************************************************************/
/**
*
* This function is used to check if the watchdog has timed-out and the last
* reset was caused by the watchdog reset.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return
*		- TRUE if the watchdog has expired.
*		- FALSE if the watchdog has not expired.
*
* @note		C-style signature:
*		int XScuWdt_IsWdtExpired(XScuWdt *InstancePtr)
*
******************************************************************************/
#define XScuWdt_IsWdtExpired(InstancePtr)				\
	((XScuWdt_ReadReg((InstancePtr)->Config.BaseAddr,		\
			  XSCUWDT_RST_STS_OFFSET) &			\
	 XSCUWDT_RST_STS_RESET_FLAG_MASK) == XSCUWDT_RST_STS_RESET_FLAG_MASK)

/****************************************************************************/
/**
*
* This function is used to check if the watchdog counter has reached 0 in timer
* mode.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return
*		- TRUE if the watchdog has expired.
*		- FALSE if the watchdog has not expired.
*
* @note		C-style signature:
*		int XScuWdt_IsTimerExpired(XScuWdt *InstancePtr)
*
******************************************************************************/
#define XScuWdt_IsTimerExpired(InstancePtr)				\
	((XScuWdt_ReadReg((InstancePtr)->Config.BaseAddr,		\
			  XSCUWDT_ISR_OFFSET) &				\
	 XSCUWDT_ISR_EVENT_FLAG_MASK) == XSCUWDT_ISR_EVENT_FLAG_MASK)

/****************************************************************************/
/**
*
* Re-start the watchdog timer. This macro will read the watchdog load register
* and write the same value to load register to update the counter register.
* An application needs to call this function periodically to keep the watchdog
* from asserting the WDRESETREQ reset request output pin.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuWdt_RestartWdt(XScuWdt *InstancePtr)
*
******************************************************************************/
#define XScuWdt_RestartWdt(InstancePtr)					 \
	XScuWdt_LoadWdt(InstancePtr,					 \
			(XScuWdt_ReadReg((InstancePtr)->Config.BaseAddr, \
					 XSCUWDT_LOAD_OFFSET)))

/****************************************************************************/
/**
*
* Write to the watchdog timer load register. This will also update the
* watchdog counter register with the new value. This macro can be used to
* change the time-out value.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
* @param	Value is the value to be written to the Watchdog Load register.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuWdt_LoadWdt(XScuWdt *InstancePtr, u32 Value)
*
******************************************************************************/
#define XScuWdt_LoadWdt(InstancePtr, Value)				\
	XScuWdt_WriteReg((InstancePtr)->Config.BaseAddr,		\
			XSCUWDT_LOAD_OFFSET, Value)

/****************************************************************************/
/**
*
* Put the watchdog timer in Watchdog mode by setting the WD mode bit of the
* Watchdog control register.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuWdt_SetWdMode(XScuWdt *InstancePtr)
*
******************************************************************************/
#define XScuWdt_SetWdMode(InstancePtr)					  \
	XScuWdt_WriteReg((InstancePtr)->Config.BaseAddr,		  \
			 XSCUWDT_CONTROL_OFFSET,			  \
			 (XScuWdt_ReadReg((InstancePtr)->Config.BaseAddr, \
			  XSCUWDT_CONTROL_OFFSET) |			  \
			  XSCUWDT_CONTROL_WD_MODE_MASK))

/****************************************************************************/
/**
*
* Put the watchdog timer in Timer mode by writing 0x12345678 and 0x87654321
* successively to the Watchdog Disable Register.
* The software must write 0x12345678 and 0x87654321 successively to the
* Watchdog Disable Register so that the watchdog mode bit in the Watchdog
* Control Register is set to zero.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuWdt_SetTimerMode(XScuWdt *InstancePtr)
*
******************************************************************************/
#define XScuWdt_SetTimerMode(InstancePtr)				\
{									\
	XScuWdt_WriteReg((InstancePtr)->Config.BaseAddr,		\
			XSCUWDT_DISABLE_OFFSET,				\
			XSCUWDT_DISABLE_VALUE1);			\
	XScuWdt_WriteReg((InstancePtr)->Config.BaseAddr,		\
			XSCUWDT_DISABLE_OFFSET,				\
			XSCUWDT_DISABLE_VALUE2);			\
}

/****************************************************************************/
/**
*
* Get the contents of the watchdog control register.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return	Contents of the watchdog control register.
*
* @note		C-style signature:
		u32 XScuWdt_GetControlReg(XScuWdt *InstancePtr)
*
******************************************************************************/
#define XScuWdt_GetControlReg(InstancePtr)				\
	XScuWdt_ReadReg((InstancePtr)->Config.BaseAddr,			\
			XSCUWDT_CONTROL_OFFSET)

/****************************************************************************/
/**
*
* Write to the watchdog control register.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
* @param	ControlReg is the value to be written to the watchdog control
*		register.
*
* @return	None.
*
* @note		C-style signature:
		void XScuWdt_SetControlReg(XScuWdt *InstancePtr, u32 ControlReg)
*
******************************************************************************/
#define XScuWdt_SetControlReg(InstancePtr, ControlReg)			\
	XScuWdt_WriteReg((InstancePtr)->Config.BaseAddr,		\
			 XSCUWDT_CONTROL_OFFSET, ControlReg)

/****************************************************************************/
/**
*
* Enable auto-reload mode.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuWdt_EnableAutoReload(XScuWdt *InstancePtr)
*
******************************************************************************/
#define XScuWdt_EnableAutoReload(InstancePtr)				\
	XScuWdt_SetControlReg((InstancePtr),				\
			      (XScuWdt_GetControlReg(InstancePtr) |	\
			      XSCUWDT_CONTROL_AUTO_RELOAD_MASK))

/************************** Function Prototypes ******************************/

/*
 * Lookup configuration in xscuwdt_sinit.c.
 */
XScuWdt_Config *XScuWdt_LookupConfig(u16 DeviceId);

/*
 * Selftest function in xscuwdt_selftest.c
 */
int XScuWdt_SelfTest(XScuWdt *InstancePtr);

/*
 * Interface functions in xscuwdt.c
 */
int XScuWdt_CfgInitialize(XScuWdt *InstancePtr,
			  XScuWdt_Config *ConfigPtr, u32 EffectiveAddress);

void XScuWdt_Start(XScuWdt *InstancePtr);

void XScuWdt_Stop(XScuWdt *InstancePtr);

/*
 * Self-test function in xwdttb_selftest.c.
 */
int XScuWdt_SelfTest(XScuWdt *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif	/* end of protection macro */
