/*****************************************************************************
*
* (c) Copyright 2009-2013 Xilinx, Inc. All rights reserved.
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
*****************************************************************************/
/****************************************************************************/
/**
*
* @file xdmaps.h
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  	Date     Changes
* ----- ------ -------- ----------------------------------------------
* 1.00	hbm    08/19/10 First Release
* 1.01a nm     12/20/12 Added definition XDMAPS_CHANNELS_PER_DEV which specifies
*		        the maximum number of channels.
*		        Replaced the usage of XPAR_XDMAPS_CHANNELS_PER_DEV
*                       with XDMAPS_CHANNELS_PER_DEV defined in xdmaps_hw.h.
*			Added the tcl file to automatically generate the
*			xparameters.h
* 1.02a sg     05/16/12 Made changes for doxygen and moved some function
*			header from the xdmaps.h file to xdmaps.c file
*			Other cleanup for coding guidelines and CR 657109
*			and CR 657898
*			The xdmaps_example_no_intr.c example is removed
*			as it is using interrupts  and is similar to
*			the interrupt example - CR 652477
* 1.03a sg     07/16/2012 changed inline to __inline for CR665681
* 1.04a nm     10/22/2012 Fixed CR# 681671.
* 1.05a nm     04/15/2013 Fixed CR# 704396. Removed warnings when compiled
*			  with -Wall and -Wextra option in bsp.
*	       05/01/2013 Fixed CR# 700189. Changed XDmaPs_BuildDmaProg()
*			  function description.
*			  Fixed CR# 704396. Removed unused variables
*			  UseM2MByte & MemBurstLen from XDmaPs_BuildDmaProg()
*			  function.
* 1.07a asa    11/02/13. Made changes to fix compilation issues for iarcc.
*			   Removed the PDBG prints. By default they were always
*			   defined out and never used. The PDBG is non-standard for
*			   Xilinx drivers and no other driver does something similar.
*			   Since there is no easy way to fix compilation issues with
*			   the IARCC compiler around PDBG, it is better to remove it.
*			   Users can always use xil_printfs if they want to debug.
* 2.0   adk    10/12/13  Updated as per the New Tcl API's
* </pre>
*
*****************************************************************************/

#ifndef XDMAPS_H		/* prevent circular inclusions */
#define XDMAPS_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xparameters.h"
#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"

#include "xdmaps_hw.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;	 /**< Unique ID  of device */
	u32 BaseAddress; /**< Base address of device (IPIF) */
} XDmaPs_Config;


/** DMA channle control structure. It's for AXI bus transaction.
 * This struct will be translated into a 32-bit channel control register value.
 */
typedef struct {
	unsigned int EndianSwapSize;	/**< Endian swap size. */
	unsigned int DstCacheCtrl;	/**< Destination cache control */
	unsigned int DstProtCtrl;	/**< Destination protection control */
	unsigned int DstBurstLen;	/**< Destination burst length */
	unsigned int DstBurstSize;	/**< Destination burst size */
	unsigned int DstInc;		/**< Destination incrementing or fixed
					 *   address */
	unsigned int SrcCacheCtrl;	/**< Source cache control */
	unsigned int SrcProtCtrl;	/**< Source protection control */
	unsigned int SrcBurstLen;	/**< Source burst length */
	unsigned int SrcBurstSize;	/**< Source burst size */
	unsigned int SrcInc;		/**< Source incrementing or fixed
					 *   address */
} XDmaPs_ChanCtrl;

/** DMA block descriptor stucture.
 */
typedef struct {
	u32 SrcAddr;		/**< Source starting address */
	u32 DstAddr;		/**< Destination starting address */
	unsigned int Length;	/**< Number of bytes for the block */
} XDmaPs_BD;

/**
 * A DMA command consisits of a channel control struct, a block descriptor,
 * a user defined program, a pointer pointing to generated DMA program, and
 * execution result.
 *
 */
typedef struct {
	XDmaPs_ChanCtrl ChanCtrl; 	/**< Channel Control Struct */
	XDmaPs_BD BD;			/**< Together with SgLength field,
					  *  it's a scatter-gather list.
					  */
	void *UserDmaProg;		/**< If user wants the driver to
					  *  execute their own DMA program,
					  *  this field points to the DMA
					  *  program.
					  */
	int UserDmaProgLength;		/**< The length of user defined
					  *  DMA program.
					  */

	void *GeneratedDmaProg;		/**< The DMA program genreated
					 * by the driver. This field will be
					 * set if a user invokes the DMA
					 * program generation function. Or
					 * the DMA command is finished and
					 * a user informs the driver not to
					 * release the program buffer.
					 * This field has two purposes, one
					 * is to ask the driver to generate
					 * a DMA program while the DMAC is
					 * performaning DMA transactions. The
					 * other purpose is to debug the
					 * driver.
					 */
	int GeneratedDmaProgLength;	 /**< The length of the DMA program
					  * generated by the driver
					  */
	int DmaStatus;			/**< 0 on success, otherwise error code
					 */
	u32 ChanFaultType;	/**< Channel fault type in case of fault
				 */
	u32 ChanFaultPCAddr;	/**< Channel fault PC address
				 */
} XDmaPs_Cmd;

/**
 * It's the done handler a user can set for a channel
 */
typedef void (*XDmaPsDoneHandler) (unsigned int Channel,
				    XDmaPs_Cmd *DmaCmd,
				    void *CallbackRef);

/**
 * It's the fault handler a user can set for a channel
 */
typedef void (*XDmaPsFaultHandler) (unsigned int Channel,
				     XDmaPs_Cmd *DmaCmd,
				     void *CallbackRef);

#define XDMAPS_MAX_CHAN_BUFS	2
#define XDMAPS_CHAN_BUF_LEN	128

/**
 * The XDmaPs_ProgBuf is the struct for a DMA program buffer.
 */
typedef struct {
	char Buf[XDMAPS_CHAN_BUF_LEN];  /**< The actual buffer the holds the
					  *  content */
	unsigned Len;			/**< The actual length of the DMA
					  *  program in bytes. */
	int Allocated;			/**< A tag indicating whether the
					  *  buffer is allocated or not */
} XDmaPs_ProgBuf;

/**
 * The XDmaPs_ChannelData is a struct to book keep individual channel of
 * the DMAC.
 */
typedef struct {
	unsigned DevId;		 	/**< Device id indicating which DMAC */
	unsigned ChanId; 		/**< Channel number of the DMAC */
	XDmaPs_ProgBuf ProgBufPool[XDMAPS_MAX_CHAN_BUFS]; /**< A pool of
							      program buffers*/
	XDmaPsDoneHandler DoneHandler; 	/**< Done interrupt handler */
	void *DoneRef;			/**< Done interrupt callback data */
	XDmaPs_Cmd *DmaCmdToHw; 	/**< DMA command being executed */
	XDmaPs_Cmd *DmaCmdFromHw; 	/**< DMA  command that is finished.
				     	  *  This field is for debugging purpose
				     	  */
	int HoldDmaProg;		/**< A tag indicating whether to hold the
					  *  DMA program after the DMA is done.
					  */

} XDmaPs_ChannelData;

/**
 * The XDmaPs driver instance data structure. A pointer to an instance data
 * structure is passed around by functions to refer to a specific driver
 * instance.
 */
typedef struct {
	XDmaPs_Config Config;	/**< Configuration data structure */
	int IsReady;		/**< Device is Ready */
	int CacheLength;	/**< icache length */
	XDmaPsFaultHandler FaultHandler; /**< fault interrupt handler */
	void *FaultRef;	/**< fault call back data */
	XDmaPs_ChannelData Chans[XDMAPS_CHANNELS_PER_DEV];
	/**<
	 * channel data
	 */
} XDmaPs;

/*
 * Functions implemented in xdmaps.c
 */
int XDmaPs_CfgInitialize(XDmaPs *InstPtr,
			  XDmaPs_Config *Config,
			  u32 EffectiveAddr);

int XDmaPs_Start(XDmaPs *InstPtr, unsigned int Channel,
		  XDmaPs_Cmd *Cmd,
		  int HoldDmaProg);

int XDmaPs_IsActive(XDmaPs *InstPtr, unsigned int Channel);
int XDmaPs_GenDmaProg(XDmaPs *InstPtr, unsigned int Channel,
		       XDmaPs_Cmd *Cmd);
int XDmaPs_FreeDmaProg(XDmaPs *InstPtr, unsigned int Channel,
			XDmaPs_Cmd *Cmd);
void XDmaPs_Print_DmaProg(XDmaPs_Cmd *Cmd);


int XDmaPs_ResetManager(XDmaPs *InstPtr);
int XDmaPs_ResetChannel(XDmaPs *InstPtr, unsigned int Channel);


int XDmaPs_SetDoneHandler(XDmaPs *InstPtr,
			   unsigned Channel,
			   XDmaPsDoneHandler DoneHandler,
			   void *CallbackRef);

int XDmaPs_SetFaultHandler(XDmaPs *InstPtr,
			    XDmaPsFaultHandler FaultHandler,
			    void *CallbackRef);

void XDmaPs_Print_DmaProg(XDmaPs_Cmd *Cmd);

/**
 * Driver done interrupt service routines for the channels.
 * We need this done ISR mainly because the driver needs to release the
 * DMA program buffer. This is the one that connects the GIC
 */
void XDmaPs_DoneISR_0(XDmaPs *InstPtr);
void XDmaPs_DoneISR_1(XDmaPs *InstPtr);
void XDmaPs_DoneISR_2(XDmaPs *InstPtr);
void XDmaPs_DoneISR_3(XDmaPs *InstPtr);
void XDmaPs_DoneISR_4(XDmaPs *InstPtr);
void XDmaPs_DoneISR_5(XDmaPs *InstPtr);
void XDmaPs_DoneISR_6(XDmaPs *InstPtr);
void XDmaPs_DoneISR_7(XDmaPs *InstPtr);

/**
 * Driver fault interrupt service routine
 */
void XDmaPs_FaultISR(XDmaPs *InstPtr);


/*
 * Static loopup function implemented in xdmaps_sinit.c
 */
XDmaPs_Config *XDmaPs_LookupConfig(u16 DeviceId);


/*
 * self-test functions in xdmaps_selftest.c
 */
int XDmaPs_SelfTest(XDmaPs *InstPtr);


#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
