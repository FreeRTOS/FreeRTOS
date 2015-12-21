/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
 * @file xusbps_endpoint.h
* @addtogroup usbps_v2_1
* @{
 *
 * This is an internal file containung the definitions for endpoints. It is
 * included by the xusbps_endpoint.c which is implementing the endpoint
 * functions and by xusbps_intr.c.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- --------------------------------------------------------
 * 1.00a wgr  10/10/10 First release
 * </pre>
 *
 ******************************************************************************/
#ifndef XUSBPS_ENDPOINT_H
#define XUSBPS_ENDPOINT_H

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_cache.h"
#include "xusbps.h"
#include "xil_types.h"

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/


/**
 * Endpoint Device Transfer Descriptor
 *
 * The dTD describes to the device controller the location and quantity of data
 * to be sent/received for given transfer. The driver does not attempt to
 * modify any field in an active dTD except the Next Link Pointer.
 */
#define XUSBPS_dTDNLP		0x00 /**< Pointer to the next descriptor */
#define XUSBPS_dTDTOKEN	0x04 /**< Descriptor Token */
#define XUSBPS_dTDBPTR0	0x08 /**< Buffer Pointer 0 */
#define XUSBPS_dTDBPTR1	0x0C /**< Buffer Pointer 1 */
#define XUSBPS_dTDBPTR2	0x10 /**< Buffer Pointer 2 */
#define XUSBPS_dTDBPTR3	0x14 /**< Buffer Pointer 3 */
#define XUSBPS_dTDBPTR4	0x18 /**< Buffer Pointer 4 */
#define XUSBPS_dTDBPTR(n)	(XUSBPS_dTDBPTR0 + (n) * 0x04)
#define XUSBPS_dTDRSRVD	0x1C /**< Reserved field */

/* We use the reserved field in the dTD to store user data. */
#define XUSBPS_dTDUSERDATA	XUSBPS_dTDRSRVD /**< Reserved field */


/** @name dTD Next Link Pointer (dTDNLP) bit positions.
 *  @{
 */
#define XUSBPS_dTDNLP_T_MASK		0x00000001
				/**< USB dTD Next Link Pointer Terminate Bit */
#define XUSBPS_dTDNLP_ADDR_MASK	0xFFFFFFE0
				/**< USB dTD Next Link Pointer Address [31:5] */
/* @} */


/** @name dTD Token (dTDTOKEN) bit positions.
 *  @{
 */
#define XUSBPS_dTDTOKEN_XERR_MASK	0x00000008 /**< dTD Transaction Error */
#define XUSBPS_dTDTOKEN_BUFERR_MASK	0x00000020 /**< dTD Data Buffer Error */
#define XUSBPS_dTDTOKEN_HALT_MASK	0x00000040 /**< dTD Halted Flag */
#define XUSBPS_dTDTOKEN_ACTIVE_MASK	0x00000080 /**< dTD Active Bit */
#define XUSBPS_dTDTOKEN_MULTO_MASK	0x00000C00 /**< Multiplier Override Field [1:0] */
#define XUSBPS_dTDTOKEN_IOC_MASK	0x00008000 /**< Interrupt on Complete Bit */
#define XUSBPS_dTDTOKEN_LEN_MASK	0x7FFF0000 /**< Transfer Length Field */
/* @} */


/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
 *
 * IMPORTANT NOTE:
 * ===============
 *
 * Many of the following macros modify Device Queue Head (dQH) data structures
 * and Device Transfer Descriptor (dTD) data structures. Those structures can
 * potentially reside in CACHED memory. Therefore, it's the callers
 * responsibility to ensure cache coherency by using provided
 *
 * 	XUsbPs_dQHInvalidateCache()
 * 	XUsbPs_dQHFlushCache()
 * 	XUsbPs_dTDInvalidateCache()
 * 	XUsbPs_dTDFlushCache()
 *
 * function calls.
 *
 ******************************************************************************/
#define XUsbPs_dTDInvalidateCache(dTDPtr) \
		Xil_DCacheInvalidateRange((unsigned int)dTDPtr, sizeof(XUsbPs_dTD))

#define XUsbPs_dTDFlushCache(dTDPtr) \
		Xil_DCacheFlushRange((unsigned int)dTDPtr, sizeof(XUsbPs_dTD))

#define XUsbPs_dQHInvalidateCache(dQHPtr) \
		Xil_DCacheInvalidateRange((unsigned int)dQHPtr, sizeof(XUsbPs_dQH))

#define XUsbPs_dQHFlushCache(dQHPtr) \
		Xil_DCacheFlushRange((unsigned int)dQHPtr, sizeof(XUsbPs_dQH))

/*****************************************************************************/
/**
 *
 * This macro sets the Transfer Length for the given Transfer Descriptor.
 *
 * @param	dTDPtr is pointer to the dTD element.
 * @param	Len is the length to be set. Range: 0..16384
 *
 * @note	C-style signature:
 *		void XUsbPs_dTDSetTransferLen(u32 dTDPtr, u32 Len)
 *
 ******************************************************************************/
#define XUsbPs_dTDSetTransferLen(dTDPtr, Len)				\
		XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDTOKEN, 		\
			(XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDTOKEN) &	\
				~XUSBPS_dTDTOKEN_LEN_MASK) | ((Len) << 16))


/*****************************************************************************/
/**
 *
 * This macro gets the Next Link pointer of the given Transfer Descriptor.
 *
 * @param	dTDPtr is pointer to the dTD element.
 *
 * @return 	TransferLength field of the descriptor.
 *
 * @note	C-style signature:
 *		u32 XUsbPs_dTDGetTransferLen(u32 dTDPtr)
 *
 ******************************************************************************/
#define XUsbPs_dTDGetNLP(dTDPtr)					\
		(XUsbPs_dTD *) ((XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDNLP)\
					& XUSBPS_dTDNLP_ADDR_MASK))


/*****************************************************************************/
/**
 *
 * This macro sets the Next Link pointer of the given Transfer Descriptor.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 * @param	NLP is the Next Link Pointer
 *
 * @note	C-style signature:
 *		void XUsbPs_dTDSetTransferLen(u32 dTDPtr, u32 Len)
 *
 ******************************************************************************/
#define XUsbPs_dTDSetNLP(dTDPtr, NLP)					\
		XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDNLP, 		\
			(XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDNLP) &	\
				~XUSBPS_dTDNLP_ADDR_MASK) |		\
					((NLP) & XUSBPS_dTDNLP_ADDR_MASK))


/*****************************************************************************/
/**
 *
 * This macro gets the Transfer Length for the given Transfer Descriptor.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 *
 * @return 	TransferLength field of the descriptor.
 *
 * @note	C-style signature:
 *		u32 XUsbPs_dTDGetTransferLen(u32 dTDPtr)
 *
 ******************************************************************************/
#define XUsbPs_dTDGetTransferLen(dTDPtr)				\
		(u32) ((XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDTOKEN) 	\
				& XUSBPS_dTDTOKEN_LEN_MASK) >> 16)


/*****************************************************************************/
/**
 *
 * This macro sets the Interrupt On Complete (IOC) bit for the given Transfer
 * Descriptor.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dTDSetIOC(u32 dTDPtr)
 *
 ******************************************************************************/
#define XUsbPs_dTDSetIOC(dTDPtr)					\
		XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDTOKEN, 		\
			XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDTOKEN) |	\
						XUSBPS_dTDTOKEN_IOC_MASK)


/*****************************************************************************/
/**
 *
 * This macro sets the Terminate bit for the given Transfer Descriptor.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dTDSetTerminate(u32 dTDPtr)
 *
 ******************************************************************************/
#define XUsbPs_dTDSetTerminate(dTDPtr)				\
		XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDNLP, 		\
			XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDNLP) |	\
						XUSBPS_dTDNLP_T_MASK)


/*****************************************************************************/
/**
 *
 * This macro clears the Terminate bit for the given Transfer Descriptor.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dTDClrTerminate(u32 dTDPtr)
 *
 ******************************************************************************/
#define XUsbPs_dTDClrTerminate(dTDPtr)				\
		XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDNLP, 		\
			XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDNLP) &	\
						~XUSBPS_dTDNLP_T_MASK)


/*****************************************************************************/
/**
 *
 * This macro checks if the given descriptor is active.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 *
 * @return
 * 		- TRUE: The buffer is active.
 * 		- FALSE: The buffer is not active.
 *
 * @note	C-style signature:
 *		int XUsbPs_dTDIsActive(u32 dTDPtr)
 *
 ******************************************************************************/
#define XUsbPs_dTDIsActive(dTDPtr)					\
		((XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDTOKEN) &		\
				XUSBPS_dTDTOKEN_ACTIVE_MASK) ? TRUE : FALSE)


/*****************************************************************************/
/**
 *
 * This macro sets the Active bit for the given Transfer Descriptor.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dTDSetActive(u32 dTDPtr)
 *
 ******************************************************************************/
#define XUsbPs_dTDSetActive(dTDPtr)					\
		XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDTOKEN, 		\
			XUsbPs_ReaddTD(dTDPtr, XUSBPS_dTDTOKEN) |	\
						XUSBPS_dTDTOKEN_ACTIVE_MASK)


/*****************************************************************************/
/**
 *
 * This macro reads the content of a field in a Transfer Descriptor.
 *
 * @param	dTDPtr is a pointer to the dTD element.
 * @param	Id is the field ID inside the dTD element to read.
 *
 * @note	C-style signature:
 *		u32 XUsbPs_ReaddTD(u32 dTDPtr, u32 Id)
 *
 ******************************************************************************/
#define XUsbPs_ReaddTD(dTDPtr, Id)	(*(u32 *)((u32)(dTDPtr) + (u32)(Id)))

/*****************************************************************************/
/**
 *
 * This macro writes a value to a field in a Transfer Descriptor.
 *
 * @param	dTDPtr is pointer to the dTD element.
 * @param	Id is the field ID inside the dTD element to read.
 * @param	Val is the value to write to the field.
 *
 * @note	C-style signature:
 *		u32 XUsbPs_WritedTD(u32 dTDPtr, u32 Id, u32 Val)
 *
 ******************************************************************************/
#define XUsbPs_WritedTD(dTDPtr, Id, Val)	\
			(*(u32 *) ((u32)(dTDPtr) + (u32)(Id)) = (u32)(Val))


/******************************************************************************/
/**
 * Endpoint Device Queue Head
 *
 * Device queue heads are arranged in an array in a continuous area of memory
 * pointed to by the ENDPOINTLISTADDR pointer. The device controller will index
 * into this array based upon the endpoint number received from the USB bus.
 * All information necessary to respond to transactions for all primed
 * transfers is contained in this list so the Device Controller can readily
 * respond to incoming requests without having to traverse a linked list.
 *
 * The device Endpoint Queue Head (dQH) is where all transfers are managed. The
 * dQH is a 48-byte data structure, but must be aligned on a 64-byte boundary.
 * During priming of an endpoint, the dTD (device transfer descriptor) is
 * copied into the overlay area of the dQH, which starts at the nextTD pointer
 * DWord and continues through the end of the buffer pointers DWords. After a
 * transfer is complete, the dTD status DWord is updated in the dTD pointed to
 * by the currentTD pointer. While a packet is in progress, the overlay area of
 * the dQH is used as a staging area for the dTD so that the Device Controller
 * can access needed information with little minimal latency.
 *
 * @note
 *    Software must ensure that no interface data structure reachable by the
 *    Device Controller spans a 4K-page boundary.  The first element of the
 *    Endpoint Queue Head List must be aligned on a 4K boundary.
 */
#define XUSBPS_dQHCFG			0x00 /**< dQH Configuration */
#define XUSBPS_dQHCPTR			0x04 /**< dQH Current dTD Pointer */
#define XUSBPS_dQHdTDNLP		0x08 /**< dTD Next Link Ptr in dQH
					       overlay */
#define XUSBPS_dQHdTDTOKEN		0x0C /**< dTD Token in dQH overlay */
#define XUSBPS_dQHSUB0			0x28 /**< USB dQH Setup Buffer 0 */
#define XUSBPS_dQHSUB1			0x2C /**< USB dQH Setup Buffer 1 */


/** @name dQH Configuration (dQHCFG) bit positions.
 *  @{
 */
#define XUSBPS_dQHCFG_IOS_MASK		0x00008000
					/**< USB dQH Interrupt on Setup Bit */
#define XUSBPS_dQHCFG_MPL_MASK		0x07FF0000
					/**< USB dQH Maximum Packet Length
					 * Field [10:0] */
#define XUSBPS_dQHCFG_MPL_SHIFT    16
#define XUSBPS_dQHCFG_ZLT_MASK		0x20000000
					/**< USB dQH Zero Length Termination
					 * Select Bit */
#define XUSBPS_dQHCFG_MULT_MASK		0xC0000000
					/* USB dQH Number of Transactions Field
					 * [1:0] */
#define XUSBPS_dQHCFG_MULT_SHIFT       30
/* @} */


/*****************************************************************************/
/**
 *
 * This macro sets the Maximum Packet Length field of the give Queue Head.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 * @param	Len is the length to be set.
 *
 * @note	C-style signature:
 *		void XUsbPs_dQHSetMaxPacketLen(u32 dQHPtr, u32 Len)
 *
 ******************************************************************************/
#define XUsbPs_dQHSetMaxPacketLen(dQHPtr, Len)			\
		XUsbPs_WritedQH(dQHPtr, XUSBPS_dQHCFG, 		\
			(XUsbPs_ReaddQH(dQHPtr, XUSBPS_dQHCFG) &	\
				~XUSBPS_dQHCFG_MPL_MASK) | ((Len) << 16))

/*****************************************************************************/
/**
 *
 * This macro sets the Interrupt On Setup (IOS) bit for an endpoint.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dQHSetIOS(u32 dQHPtr)
 *
 ******************************************************************************/
#define XUsbPs_dQHSetIOS(dQHPtr)					\
		XUsbPs_WritedQH(dQHPtr, XUSBPS_dQHCFG, 		\
			XUsbPs_ReaddQH(dQHPtr, XUSBPS_dQHCFG) |	\
						XUSBPS_dQHCFG_IOS_MASK)

/*****************************************************************************/
/**
 *
 * This macro clears the Interrupt On Setup (IOS) bit for an endpoint.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dQHClrIOS(u32 dQHPtr)
 *
 ******************************************************************************/
#define XUsbPs_dQHClrIOS(dQHPtr)					\
		XUsbPs_WritedQH(dQHPtr, XUSBPS_dQHCFG, 		\
			XUsbPs_ReaddQH(dQHPtr, XUSBPS_dQHCFG) &	\
						~XUSBPS_dQHCFG_IOS_MASK)

/*****************************************************************************/
/**
 *
 * This macro enables Zero Length Termination for the endpoint.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dQHEnableZLT(u32 dQHPtr)
 *
 *
 ******************************************************************************/
#define XUsbPs_dQHEnableZLT(dQHPtr)					\
		XUsbPs_WritedQH(dQHPtr, XUSBPS_dQHCFG, 		\
			XUsbPs_ReaddQH(dQHPtr, XUSBPS_dQHCFG) &	\
						~XUSBPS_dQHCFG_ZLT_MASK)


/*****************************************************************************/
/**
 *
 * This macro disables Zero Length Termination for the endpoint.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 *
 * @note	C-style signature:
 *		void XUsbPs_dQHDisableZLT(u32 dQHPtr)
 *
 *
 ******************************************************************************/
#define XUsbPs_dQHDisableZLT(dQHPtr)					\
		XUsbPs_WritedQH(dQHPtr, XUSBPS_dQHCFG, 		\
			XUsbPs_ReaddQH(dQHPtr, XUSBPS_dQHCFG) |	\
						XUSBPS_dQHCFG_ZLT_MASK)

/*****************************************************************************/
/**
 *
 * This macro reads the content of a field in a Queue Head.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 * @param	Id is the Field ID inside the dQH element to read.
 *
 * @note	C-style signature:
 *		u32 XUsbPs_ReaddQH(u32 dQHPtr, u32 Id)
 *
 ******************************************************************************/
#define XUsbPs_ReaddQH(dQHPtr, Id)	(*(u32 *)((u32)(dQHPtr) + (u32) (Id)))

/*****************************************************************************/
/**
 *
 * This macro writes a value to a field in a Queue Head.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 * @param	Id is the Field ID inside the dQH element to read.
 * @param	Val is the Value to write to the field.
 *
 * @note	C-style signature:
 *		u32 XUsbPs_WritedQH(u32 dQHPtr, u32 Id, u32 Val)
 *
 ******************************************************************************/
#define XUsbPs_WritedQH(dQHPtr, Id, Val)	\
			(*(u32 *) ((u32)(dQHPtr) + (u32)(Id)) = (u32)(Val))



#ifdef __cplusplus
}
#endif

#endif /* XUSBPS_ENDPOINT_H */
/** @} */
