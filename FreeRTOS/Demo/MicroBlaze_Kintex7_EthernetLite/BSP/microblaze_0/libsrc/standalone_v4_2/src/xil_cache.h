/******************************************************************************
*
* Copyright (C) 2009 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xil_cache.h
*
* This header file contains cache related driver functions (or macros)
* that can be used to access the device.  The user should refer to the
* hardware device specification for more details of the device operation.
* The functions in this header file can be used across all Xilinx supported
* processors.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00  hbm  07/28/09 Initial release
* 3.02a sdm  10/24/11 Updated the file to include xparameters.h so that
*                     the correct cache flush routines are used based on
*                     whether the write-back or write-through caches are
*                     used (cr #630532).
* 3.10a asa  05/04/13 This version of MicroBlaze BSP adds support for system
*					  cache/L2 cache. The existing/old APIs/macros in this
*					  file are renamed to imply that they deal with L1 cache.
*					  New macros/APIs are added to address similar features for
*					  L2 cache. Users can include this file in their application
*					  to use the various cache related APIs. These changes are
*					  done for implementing PR #697214.
*
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

#ifndef XIL_CACHE_H
#define XIL_CACHE_H

#if defined XENV_VXWORKS
/* VxWorks environment */
#error "Unknown processor / architecture. Must be PPC for VxWorks."
#else
/* standalone environment */

#include "mb_interface.h"
#include "xil_types.h"
#include "xparameters.h"

#ifdef __cplusplus
extern "C" {
#endif

/****************************************************************************/
/**
*
* Invalidate the entire L1 data cache. If the cacheline is modified (dirty),
* the modified contents are lost.
*
* @param    None.
*
* @return   None.
*
* @note
*
* Processor must be in real mode.
****************************************************************************/
#define Xil_L1DCacheInvalidate() microblaze_invalidate_dcache()

/****************************************************************************/
/**
*
* Invalidate the entire L2 data cache. If the cacheline is modified (dirty),
* the modified contents are lost.
*
* @param    None.
*
* @return   None.
*
* @note
*
* Processor must be in real mode.
****************************************************************************/
#define Xil_L2CacheInvalidate() microblaze_invalidate_cache_ext()

/****************************************************************************/
/**
*
* Invalidate the L1 data cache for the given address range.
* If the bytes specified by the address (Addr) are cached by the L1 data cache,
* the cacheline containing that byte is invalidated.  If the cacheline
* is modified (dirty), the modified contents are lost.
*
* @param    Addr is address of ragne to be invalidated.
* @param    Len is the length in bytes to be invalidated.
*
* @return   None.
*
* @note
*
* Processor must be in real mode.
****************************************************************************/
#define Xil_L1DCacheInvalidateRange(Addr, Len) \
			microblaze_invalidate_dcache_range(Addr, Len)

/****************************************************************************/
/**
*
* Invalidate the L1 data cache for the given address range.
* If the bytes specified by the address (Addr) are cached by the L1 data cache,
* the cacheline containing that byte is invalidated.  If the cacheline
* is modified (dirty), the modified contents are lost.
*
* @param    Addr is address of ragne to be invalidated.
* @param    Len is the length in bytes to be invalidated.
*
* @return   None.
*
* @note
*
* Processor must be in real mode.
****************************************************************************/
#define Xil_L2CacheInvalidateRange(Addr, Len) \
		microblaze_invalidate_cache_ext_range(Addr, Len)

/****************************************************************************/
/**
* Flush the L1 data cache for the given address range.
* If the bytes specified by the address (Addr) are cached by the data cache,
* and is modified (dirty), the cacheline will be written to system memory.
* The cacheline will also be invalidated.
*
* @param    Addr is the starting address of the range to be flushed.
* @param    Len is the length in byte to be flushed.
*
* @return   None.
*
****************************************************************************/
#if (XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK == 1)
#   define Xil_L1DCacheFlushRange(Addr, Len) \
		microblaze_flush_dcache_range(Addr, Len)
#else
#   define Xil_L1DCacheFlushRange(Addr, Len) \
		microblaze_invalidate_dcache_range(Addr, Len)
#endif /* XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK */

/****************************************************************************/
/**
* Flush the L2 data cache for the given address range.
* If the bytes specified by the address (Addr) are cached by the data cache,
* and is modified (dirty), the cacheline will be written to system memory.
* The cacheline will also be invalidated.
*
* @param    Addr is the starting address of the range to be flushed.
* @param    Len is the length in byte to be flushed.
*
* @return   None.
*
****************************************************************************/
#define Xil_L2CacheFlushRange(Addr, Len) \
		microblaze_flush_cache_ext_range(Addr, Len)

/****************************************************************************/
/**
* Flush the entire L1 data cache. If any cacheline is dirty, the cacheline will be
* written to system memory. The entire data cache will be invalidated.
*
* @return   None.
*
* @note
*
****************************************************************************/
#if (XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK == 1)
#   define Xil_L1DCacheFlush() microblaze_flush_dcache()
#else
#   define Xil_L1DCacheFlush() microblaze_invalidate_dcache()
#endif /* XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK */

/****************************************************************************/
/**
* Flush the entire L2 data cache. If any cacheline is dirty, the cacheline will be
* written to system memory. The entire data cache will be invalidated.
*
* @return   None.
*
* @note
*
****************************************************************************/
#define Xil_L2CacheFlush() microblaze_flush_cache_ext()

/****************************************************************************/
/**
*
* Invalidate the instruction cache for the given address range.
*
* @param    Addr is address of ragne to be invalidated.
* @param    Len is the length in bytes to be invalidated.
*
* @return   None.
*
****************************************************************************/
#define Xil_L1ICacheInvalidateRange(Addr, Len) \
			microblaze_invalidate_icache_range(Addr, Len)

/****************************************************************************/
/**
*
* Invalidate the entire instruction cache.
*
* @param    None
*
* @return   None.
*
****************************************************************************/
#define Xil_L1ICacheInvalidate() \
			microblaze_invalidate_icache()


/****************************************************************************/
/**
*
* Enable the L1 data cache.
*
* @return   None.
*
* @note     This is processor specific.
*
****************************************************************************/
#define Xil_L1DCacheEnable() \
			microblaze_enable_dcache()

/****************************************************************************/
/**
*
* Disable the L1 data cache.
*
* @return   None.
*
* @note     This is processor specific.
*
****************************************************************************/
#define Xil_L1DCacheDisable() \
			microblaze_disable_dcache()

/****************************************************************************/
/**
*
* Enable the instruction cache.
*
* @return   None.
*
* @note     This is processor specific.
*
****************************************************************************/
#define Xil_L1ICacheEnable() \
			microblaze_enable_icache()

/****************************************************************************/
/**
*
* Disable the L1 Instruction cache.
*
* @return   None.
*
* @note     This is processor specific.
*
****************************************************************************/
#define Xil_L1ICacheDisable() \
			microblaze_disable_icache()

/****************************************************************************/
/**
*
* Enable the data cache.
*
* @param    None
*
* @return   None.
*
****************************************************************************/
#define Xil_DCacheEnable() Xil_L1DCacheEnable()

/****************************************************************************/
/**
*
* Enable the instruction cache.
*
* @param    None
*
* @return   None.
*
* @note
*
*
****************************************************************************/
#define Xil_ICacheEnable() Xil_L1ICacheEnable()

/****************************************************************************
*
* Invalidate the entire Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#define Xil_DCacheInvalidate() \
	Xil_L2CacheInvalidate(); \
	Xil_L1DCacheInvalidate();


/****************************************************************************
*
* Invalidate the Data cache for the given address range.
* If the bytes specified by the address (adr) are cached by the Data cache,
* the cacheline containing that byte is invalidated.	If the cacheline
* is modified (dirty), the modified contents are lost and are NOT
* written to system memory before the line is invalidated.
*
* @param	Start address of ragne to be invalidated.
* @param	Length of range to be invalidated in bytes.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#define Xil_DCacheInvalidateRange(Addr, Len) \
	Xil_L2CacheInvalidateRange(Addr, Len); \
	Xil_L1DCacheInvalidateRange(Addr, Len);


/****************************************************************************
*
* Flush the entire Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#define Xil_DCacheFlush() \
	Xil_L2CacheFlush(); \
	Xil_L1DCacheFlush();

/****************************************************************************
* Flush the Data cache for the given address range.
* If the bytes specified by the address (adr) are cached by the Data cache,
* the cacheline containing that byte is invalidated.	If the cacheline
* is modified (dirty), the written to system memory first before the
* before the line is invalidated.
*
* @param	Start address of range to be flushed.
* @param	Length of range to be flushed in bytes.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#define Xil_DCacheFlushRange(Addr, Len) \
	Xil_L2CacheFlushRange(Addr, Len); \
	Xil_L1DCacheFlushRange(Addr, Len);


/****************************************************************************
*
* Invalidate the entire instruction cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#define Xil_ICacheInvalidate() \
	Xil_L2CacheInvalidate(); \
	Xil_L1ICacheInvalidate();


/****************************************************************************
*
* Invalidate the instruction cache for the given address range.
* If the bytes specified by the address (adr) are cached by the Data cache,
* the cacheline containing that byte is invalidated. If the cacheline
* is modified (dirty), the modified contents are lost and are NOT
* written to system memory before the line is invalidated.
*
* @param	Start address of ragne to be invalidated.
* @param	Length of range to be invalidated in bytes.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#define Xil_ICacheInvalidateRange(Addr, Len) \
	Xil_L2CacheInvalidateRange(Addr, Len); \
	Xil_L1ICacheInvalidateRange(Addr, Len);

void Xil_DCacheDisable(void);
void Xil_ICacheDisable(void);

#ifdef __cplusplus
}
#endif

#endif

#endif
