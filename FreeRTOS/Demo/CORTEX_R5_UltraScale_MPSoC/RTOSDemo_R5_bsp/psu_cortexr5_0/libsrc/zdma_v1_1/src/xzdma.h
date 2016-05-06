/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xzdma.h
* @addtogroup zdma_v1_0
* @{
* @details
*
* ZDMA is a general purpose DMA designed to support memory to memory and memory
* to IO buffer transfers. ALTO has two instance of general purpose ZDMA.
* One is located in FPD (full power domain) which is GDMA and other is located
* in LPD (low power domain) which is ADMA.
*
* GMDA & ADMA are configured each with 8 DMA channels and and each channel can
* be programmed secure or non-secure.
* Each channel is divided into two functional sides, Source (Read) and
* Destination (Write). Each DMA channel can be independently programmed
* in one of following DMA modes.
*	- Simple DMA
*		- Normal data transfer from source to destination.
*		- Write Only mode.
*		- Read Only mode.
*	- Scatter Gather DMA
*		- Only Normal mode it can't support other two modes.
* In Scatter gather descriptor can be of 3 types
*	- Linear descriptor.
*	- Linked list descriptor
*	- Hybrid descriptor (Combination of both Linear and Linked list)
* Our driver will not support Hybrid type of descriptor.
*
* <b>Initialization & Configuration</b>
*
* The device driver enables higher layer software (e.g., an application) to
* communicate to the ZDMA core.
*
* XZDma_CfgInitialize() API is used to initialize the ZDMA core.
* The user needs to first call the XZDma_LookupConfig() API which returns
* the Configuration structure pointer which is passed as a parameter to the
* XZDma_CfgInitialize() API.
*
* <b> Interrupts </b>
* The driver provides an interrupt handler XZDma_IntrHandler for handling
* the interrupt from the ZDMA core. The users of this driver have to
* register this handler with the interrupt system and provide the callback
* functions by using XZDma_SetCallBack API. In this version Descriptor done
* option is disabled.
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
* The XZDma driver is composed of several source files. This allows the user
* to build and link only those parts of the driver that are necessary.
*
* This header file contains identifiers and register-level driver functions (or
* macros), range macros, structure typedefs that can be used to access the
* Xilinx ZDMA core instance.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- ------------------------------------------------------
* 1.0   vns     2/27/15  First release
* 1.1   vns    15/02/16  Corrected Destination descriptor addresss calculation
*                        in XZDma_CreateBDList API
*                        Modified XZDma_SetMode to return XST_FAILURE on
*                        selecting DMA mode other than normal mode in
*                        scatter gather mode data transfer and corrected
*                        XZDma_SetChDataConfig API to set over fetch and
*                        src issue parameters correctly.

* </pre>
*
******************************************************************************/
#ifndef XZDMA_H_
#define XZDMA_H_

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xzdma_hw.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xil_cache.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/

/** @name ZDMA Handler Types
 * @{
 */
typedef enum {
	XZDMA_HANDLER_DONE,	/**< For Done Handler */
	XZDMA_HANDLER_ERROR,	/**< For Error Handler */
} XZDma_Handler;
/*@}*/

/** @name ZDMA Descriptors Types
 * @{
 */
typedef enum {
	XZDMA_LINEAR,		/**< Linear descriptor */
	XZDMA_LINKEDLIST,	/**< Linked list descriptor */
} XZDma_DscrType;
/*@}*/

/** @name ZDMA Operation modes
 * @{
 */
typedef enum {
	XZDMA_NORMAL_MODE,	/**< Normal transfer from source to
				  *  destination*/
	XZDMA_WRONLY_MODE,	/**< Write only mode */
	XZDMA_RDONLY_MODE	/**< Read only mode */
} XZDma_Mode;
/*@}*/

/** @name ZDMA state
 * @{
 */
typedef enum {
	XZDMA_IDLE,		/**< ZDMA is in Idle state */
	XZDMA_PAUSE,		/**< Paused state */
	XZDMA_BUSY,		/**< Busy state */
} XZDmaState;
/*@}*/

/** @name ZDMA AXI Burst type
 * @{
 */
typedef enum {
	XZDMA_FIXED_BURST = 0,	/**< Fixed burst type */
	XZDMA_INCR_BURST	/**< Increment burst type */
} XZDma_BurstType;
/*@}*/

/******************************************************************************/
/**
* This typedef contains scatter gather descriptor fields for ZDMA core.
*/
typedef struct {
	void *SrcDscrPtr;	/**< Source Descriptor pointer */
	void *DstDscrPtr;	/**< Destination Descriptor pointer */
	u32 DscrCount;		/**< Count of descriptors available */
	XZDma_DscrType DscrType;/**< Type of descriptor either Linear or
				  *  Linked list type */
} XZDma_Descriptor;

/******************************************************************************/
/**
* This typedef contains scatter gather descriptor fields for ZDMA core.
*/
typedef struct {
	u64 Address;	/**< Address */
	u32 Size;	/**< Word2, Size of data */
	u32 Cntl;	/**< Word3 Control data */
	u64 NextDscr; 	/**< Address of next descriptor */
	u64 Reserved;	/**< Reserved address */
} __attribute__ ((packed)) XZDma_LlDscr;

/******************************************************************************/
/**
* This typedef contains Linear descriptor fields for ZDMA core.
*/
typedef struct {
	u64 Address;	/**< Address */
	u32 Size;	/**< Word3, Size of data */
	u32 Cntl;	/**< Word4, control data */
}  __attribute__ ((packed)) XZDma_LiDscr;

/******************************************************************************/
/**
*
* This typedef contains the data configurations of ZDMA core
*/
typedef struct {
	u8 OverFetch;		/**< Enable Over fetch */
	u8 SrcIssue;		/**< Outstanding transactions for Source */
	XZDma_BurstType SrcBurstType;
				/**< Burst type for SRC */
	u8 SrcBurstLen;		/**< AXI length for data read */
	XZDma_BurstType DstBurstType;
				/**< Burst type for DST */
	u8 DstBurstLen;		/**< AXI length for data write */
	u8 SrcCache;		/**< AXI cache bits for data read */
	u8 SrcQos;		/**< AXI QOS bits for data read */
	u8 DstCache;		/**< AXI cache bits for data write */
	u8 DstQos;		/**< AXI QOS bits for data write */
} XZDma_DataConfig;

/******************************************************************************/
/**
*
* This typedef contains the descriptor configurations of ZDMA core
*/
typedef struct{
	u8 AxCoherent;	/**< AXI transactions are coherent or non-coherent */
	u8 AXCache;	/**< AXI cache for DSCR fetch */
	u8 AXQos;	/**< Qos bit for DSCR fetch */
} XZDma_DscrConfig;

/******************************************************************************/
/**
* Callback type for Completion of all data transfers.
*
* @param 	CallBackRef is a callback reference passed in by the upper layer
*		when setting the callback functions, and passed back to the
*		upper layer when the callback is invoked.
*******************************************************************************/
typedef void (*XZDma_DoneHandler) (void *CallBackRef);

/******************************************************************************/
/**
* Callback type for all error interrupts.
*
* @param 	CallBackRef is a callback reference passed in by the upper layer
*		when setting the callback functions, and passed back to the
*		upper layer when the callback is invoked.
* @param	ErrorMask is a bit mask indicating the cause of the error. Its
*		value equals 'OR'ing one or more XZDMA_IXR_* values defined in
*		xzdma_hw.h
****************************************************************************/
typedef void (*XZDma_ErrorHandler) (void *CallBackRef, u32 ErrorMask);

/**
* This typedef contains configuration information for a ZDMA core
* Each ZDMA core should have a configuration structure associated.
*/
typedef struct {
	u16 DeviceId;		/**< Device Id of ZDMA */
	u32 BaseAddress;	/**< BaseAddress of ZDMA */
	u8 DmaType;		/**< Type of DMA */
} XZDma_Config;

/******************************************************************************/
/**
*
* The XZDma driver instance data structure. A pointer to an instance data
* structure is passed around by functions to refer to a specific driver
* instance.
*/
typedef struct {
	XZDma_Config Config;	/**< Hardware configuration */
	u32 IsReady;		/**< Device and the driver instance
				  *  are initialized */
	u32 IntrMask;		/**< Mask for enabling interrupts */

	XZDma_Mode Mode;	/**< Mode of ZDMA core to be operated */
	u8 IsSgDma;		/**< Is ZDMA core is in scatter gather or
				  *  not will be specified */
	XZDma_Descriptor Descriptor;	/**< It contains information about
					  * descriptors */

	XZDma_DoneHandler DoneHandler;	/**< Call back for transfer
					  *  done interrupt */
	void *DoneRef;			/**< To be passed to the done
					  * interrupt callback */

	XZDma_ErrorHandler ErrorHandler;/**< Call back for error
					  *  interrupt */
	void *ErrorRef;			/**< To be passed to the error
					  * interrupt callback */
	XZDma_DataConfig DataConfig;	/**< Current configurations */
	XZDma_DscrConfig DscrConfig;	/**< Current configurations */
	XZDmaState ChannelState;	 /**< ZDMA channel is busy */

} XZDma;

/******************************************************************************/
/**
*
* This typedef contains the fields for transfer of data.
*/
typedef struct {
	UINTPTR SrcAddr;	/**< Source address */
	UINTPTR DstAddr;	/**< Destination Address */
	u32 Size;		/**< Size of the data to be transferred */
	u8 SrcCoherent;		/**< Source coherent */
	u8 DstCoherent;		/**< Destination coherent */
	u8 Pause;		/**< Will pause data transmission after
				  *  this transfer only for SG mode */
} XZDma_Transfer;

/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
*
* This function returns interrupt status read from Interrupt Status Register.
* Use the XZDMA_IXR_DMA_*_MASK constants defined in xzdma_hw.h to interpret the
* returned value.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	The pending interrupts of the ZDMA core.
*		Use the masks specified in xzdma_hw.h to interpret
*		the returned value.
* @note
* 		C-style signature:
*		void XZDma_IntrGetStatus(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_IntrGetStatus(InstancePtr) \
	XZDma_ReadReg((InstancePtr)->Config.BaseAddress, XZDMA_CH_ISR_OFFSET)

/*****************************************************************************/
/**
*
* This function clears interrupt(s). Every bit set in Interrupt Status
* Register indicates that a specific type of interrupt is occurring, and this
* function clears one or more interrupts by writing a bit mask to Interrupt
* Clear Register.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Mask is the type of the interrupts to enable. Use OR'ing of
*		XZDMA_IXR_DMA_*_MASK constants defined in xzdma_hw.h to create
*		this parameter value.
*
* @return	None.
*
* @note
* 		C-style signature:
*		void XZDma_IntrClear(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_IntrClear(InstancePtr, Mask) \
	XZDma_WriteReg( (InstancePtr)->Config.BaseAddress, \
	XZDMA_CH_ISR_OFFSET, ((u32)(Mask) & (u32)XZDMA_IXR_ALL_INTR_MASK))

/*****************************************************************************/
/**
*
* This function returns interrupt mask to know which interrupts are
* enabled and which of them were disabled.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	The current interrupt mask. The mask indicates which interrupts
*		are enabled/disabled.
*		0 bit represents .....corresponding interrupt is enabled.
*		1 bit represents .....Corresponding interrupt is disabled.
*
* @note
* 		C-style signature:
*		void XZDma_GetIntrMask(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_GetIntrMask(InstancePtr) \
	XZDma_ReadReg((InstancePtr)->Config.BaseAddress,  \
			(u32)(XZDMA_CH_IMR_OFFSET))

/*****************************************************************************/
/**
*
* This function enables individual interrupts of the ZDMA core by updating
* the Interrupt Enable register.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Mask is the type of the interrupts to enable. Use OR'ing of
*		XZDMA_IXR_DMA_*_MASK constants defined in xzdma_hw.h to create
*		this parameter value.
*
* @return	None.
*
* @note		The existing enabled interrupt(s) will remain enabled.
* 		C-style signature:
*		void XZDma_EnableIntr(XZDma *InstancePtr, u32 Mask)
*
******************************************************************************/
#define XZDma_EnableIntr(InstancePtr, Mask) \
	(InstancePtr)->IntrMask = ((InstancePtr)->IntrMask | (Mask))

/*****************************************************************************/
/**
*
* This function disables individual interrupts of the ZDMA core by updating
* the Interrupt Disable register.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Mask is the type of the interrupts to disable. Use OR'ing of
*		XZDMA_IXR_DMA_*_MASK constants defined in xzdma_hw.h to create
*		this parameter value.
*
* @return	None.
*
* @note		The existing disabled interrupt(s) will remain disabled.
* 		C-style signature:
*		void XZDma_DisableIntr(XZDma *InstancePtr, u32 Mask)
*
******************************************************************************/
#define XZDma_DisableIntr(InstancePtr, Mask) \
	XZDma_WriteReg( (InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_IDS_OFFSET, \
	((u32)XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
	XZDMA_CH_IDS_OFFSET) | ((u32)(Mask) & (u32)XZDMA_IXR_ALL_INTR_MASK)))

/*****************************************************************************/
/**
*
* This function returns source current payload address under process
* of ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		This address may not be precise due to ZDMA pipeline structure
*		C-style signature:
*		u64 XZDma_SrcCurPyld(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_SrcCurPyld(InstancePtr) \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_SRC_CUR_PYLD_LSB_OFFSET)) | \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
	XZDMA_CH_SRC_CUR_PYLD_MSB_OFFSET)) << XZDMA_WORD1_MSB_SHIFT))

/*****************************************************************************/
/**
*
* This function returns destination current payload address under process
* of ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		This address may not be precise due to ZDMA pipeline structure
*		C-style signature:
*		u64 XZDma_DstCurPyld(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_DstCurPyld(InstancePtr) \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_DST_CUR_PYLD_LSB_OFFSET)) | \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
	XZDMA_CH_DST_CUR_PYLD_MSB_OFFSET)) << XZDMA_WORD1_MSB_SHIFT))

/*****************************************************************************/
/**
*
* This function returns source descriptor current payload address under
* process of ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		This address may not be precise due to ZDMA pipeline structure
*		C-style signature:
*		u64 XZDma_SrcDscrCurPyld(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_SrcDscrCurPyld(InstancePtr) \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_SRC_CUR_DSCR_LSB_OFFSET)) | \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
	XZDMA_CH_SRC_CUR_DSCR_MSB_OFFSET)) << XZDMA_WORD1_MSB_SHIFT))


/*****************************************************************************/
/**
*
* This function returns destination descriptor current payload address under
* process of ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		This address may not be precise due to ZDMA pipeline structure
*		C-style signature:
*		u64 XZDma_DstDscrCurPyld(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_DstDscrCurPyld(InstancePtr) \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_DST_CUR_DSCR_LSB_OFFSET)) | \
	((u64)(XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
	XZDMA_CH_DST_CUR_DSCR_MSB_OFFSET)) << XZDMA_WORD1_MSB_SHIFT))

/*****************************************************************************/
/**
*
* This function gets the count of total bytes transferred through core
* since last clear in ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note
*		C-style signature:
*		void XZDma_GetTotalByte(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_GetTotalByte(InstancePtr) \
	XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_TOTAL_BYTE_OFFSET)

/*****************************************************************************/
/**
*
* This function clears the count of total bytes transferred in ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note
*		C-style signature:
*		void XZDma_TotalByteClear(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_TotalByteClear(InstancePtr) \
	XZDma_WriteReg((InstancePtr)->Config.BaseAddress, \
		XZDMA_CH_TOTAL_BYTE_OFFSET, \
	XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
		XZDMA_CH_TOTAL_BYTE_OFFSET))

/*****************************************************************************/
/**
*
* This function gets the total number of Interrupt count for source after last
* call of this API.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		Once this API is called then count will become zero.
*		C-style signature:
*		void XZDma_GetSrcIntrCnt(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_GetSrcIntrCnt(InstancePtr) \
	XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_IRQ_SRC_ACCT_OFFSET)

/*****************************************************************************/
/**
*
* This function gets the total number of Interrupt count for destination
* after last call of this API.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		Once this API is called then count will become zero.
*		C-style signature:
*		void XZDma_GetDstIntrCnt(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_GetDstIntrCnt(InstancePtr) \
	XZDma_ReadReg((InstancePtr)->Config.BaseAddress, \
			XZDMA_CH_IRQ_DST_ACCT_OFFSET)

/*****************************************************************************/
/**
*
* This function Enable's the ZDMA core for initiating the data transfer once the
* data transfer completes it will be automatically disabled.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		None.
*		C-style signature:
*		void XZDma_EnableCh(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_EnableCh(InstancePtr) \
	XZDma_WriteReg((InstancePtr)->Config.BaseAddress, \
			(XZDMA_CH_CTRL2_OFFSET), (XZDMA_CH_CTRL2_EN_MASK))

/*****************************************************************************/
/**
*
* This function Disable's the ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		None.
*		C-style signature:
*		void XZDma_DisableCh(XZDma *InstancePtr)
*
******************************************************************************/
#define XZDma_DisableCh(InstancePtr) \
	XZDma_WriteReg((InstancePtr)->Config.BaseAddress,\
		(XZDMA_CH_CTRL2_OFFSET), (XZDMA_CH_CTRL2_DIS_MASK))

/************************ Prototypes of functions **************************/

XZDma_Config *XZDma_LookupConfig(u16 DeviceId);

s32 XZDma_CfgInitialize(XZDma *InstancePtr, XZDma_Config *CfgPtr,
			u32 EffectiveAddr);
s32 XZDma_SetMode(XZDma *InstancePtr, u8 IsSgDma, XZDma_Mode Mode);
u32 XZDma_CreateBDList(XZDma *InstancePtr, XZDma_DscrType TypeOfDscr,
					UINTPTR Dscr_MemPtr, u32 NoOfBytes);
s32 XZDma_SetChDataConfig(XZDma *InstancePtr, XZDma_DataConfig *Configure);
void XZDma_GetChDataConfig(XZDma *InstancePtr, XZDma_DataConfig *Configure);
s32 XZDma_SetChDscrConfig(XZDma *InstancePtr, XZDma_DscrConfig *Configure);
void XZDma_GetChDscrConfig(XZDma *InstancePtr, XZDma_DscrConfig *Configure);
s32 XZDma_Start(XZDma *InstancePtr, XZDma_Transfer *Data, u32 Num);
void XZDma_WOData(XZDma *InstancePtr, u32 *Buffer);
void XZDma_Resume(XZDma *InstancePtr);
void XZDma_Reset(XZDma *InstancePtr);
XZDmaState XZDma_ChannelState(XZDma *InstancePtr);

s32 XZDma_SelfTest(XZDma *InstancePtr);

void XZDma_IntrHandler(void *Instance);
s32 XZDma_SetCallBack(XZDma *InstancePtr, XZDma_Handler HandlerType,
	void *CallBackFunc, void *CallBackRef);

/*@}*/

#ifdef __cplusplus
}

#endif

#endif /* XZDMA_H_ */
/** @} */
