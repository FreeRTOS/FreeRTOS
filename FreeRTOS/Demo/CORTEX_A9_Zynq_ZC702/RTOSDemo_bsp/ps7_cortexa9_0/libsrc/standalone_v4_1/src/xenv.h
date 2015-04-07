/******************************************************************************
*
*       XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS"
*       AS A COURTESY TO YOU, SOLELY FOR USE IN DEVELOPING PROGRAMS AND
*       SOLUTIONS FOR XILINX DEVICES.  BY PROVIDING THIS DESIGN, CODE,
*       OR INFORMATION AS ONE POSSIBLE IMPLEMENTATION OF THIS FEATURE,
*       APPLICATION OR STANDARD, XILINX IS MAKING NO REPRESENTATION
*       THAT THIS IMPLEMENTATION IS FREE FROM ANY CLAIMS OF INFRINGEMENT,
*       AND YOU ARE RESPONSIBLE FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE
*       FOR YOUR IMPLEMENTATION.  XILINX EXPRESSLY DISCLAIMS ANY
*       WARRANTY WHATSOEVER WITH RESPECT TO THE ADEQUACY OF THE
*       IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OR
*       REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE FROM CLAIMS OF
*       INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
*       FOR A PARTICULAR PURPOSE.
*
*       (c) Copyright 2002 Xilinx Inc.
*       All rights reserved.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xenv.h
*
* Defines common services that are typically found in a host operating.
* environment. This include file simply includes an OS specific file based
* on the compile-time constant BUILD_ENV_*, where * is the name of the target
* environment.
*
* All services are defined as macros.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b ch   10/24/02 Added XENV_LINUX
* 1.00a rmm  04/17/02 First release
* </pre>
*
******************************************************************************/

#ifndef XENV_H /* prevent circular inclusions */
#define XENV_H /* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Select which target environment we are operating under
 */

/* VxWorks target environment */
#if defined XENV_VXWORKS
#include "xenv_vxworks.h"

/* Linux target environment */
#elif defined XENV_LINUX
#include "xenv_linux.h"

/* Unit test environment */
#elif defined XENV_UNITTEST
#include "ut_xenv.h"

/* Integration test environment */
#elif defined XENV_INTTEST
#include "int_xenv.h"

/* Standalone environment selected */
#else
#include "xenv_standalone.h"
#endif


/*
 * The following comments specify the types and macro wrappers that are
 * expected to be defined by the target specific header files
 */

/**************************** Type Definitions *******************************/

/*****************************************************************************/
/**
 *
 * XENV_TIME_STAMP
 *
 * A structure that contains a time stamp used by other time stamp macros
 * defined below. This structure is processor dependent.
 */


/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
 *
 * XENV_MEM_COPY(void *DestPtr, void *SrcPtr, unsigned Bytes)
 *
 * Copies a non-overlapping block of memory.
 *
 * @param   DestPtr is the destination address to copy data to.
 * @param   SrcPtr is the source address to copy data from.
 * @param   Bytes is the number of bytes to copy.
 *
 * @return  None
 */

/*****************************************************************************/
/**
 *
 * XENV_MEM_FILL(void *DestPtr, char Data, unsigned Bytes)
 *
 * Fills an area of memory with constant data.
 *
 * @param   DestPtr is the destination address to set.
 * @param   Data contains the value to set.
 * @param   Bytes is the number of bytes to set.
 *
 * @return  None
 */
/*****************************************************************************/
/**
 *
 * XENV_TIME_STAMP_GET(XTIME_STAMP *StampPtr)
 *
 * Samples the processor's or external timer's time base counter.
 *
 * @param   StampPtr is the storage for the retrieved time stamp.
 *
 * @return  None
 */

/*****************************************************************************/
/**
 *
 * XENV_TIME_STAMP_DELTA_US(XTIME_STAMP *Stamp1Ptr, XTIME_STAMP* Stamp2Ptr)
 *
 * Computes the delta between the two time stamps.
 *
 * @param   Stamp1Ptr - First sampled time stamp.
 * @param   Stamp1Ptr - Sedond sampled time stamp.
 *
 * @return  An unsigned int value with units of microseconds.
 */

/*****************************************************************************/
/**
 *
 * XENV_TIME_STAMP_DELTA_MS(XTIME_STAMP *Stamp1Ptr, XTIME_STAMP* Stamp2Ptr)
 *
 * Computes the delta between the two time stamps.
 *
 * @param   Stamp1Ptr - First sampled time stamp.
 * @param   Stamp1Ptr - Sedond sampled time stamp.
 *
 * @return  An unsigned int value with units of milliseconds.
 */

/*****************************************************************************//**
 *
 * XENV_USLEEP(unsigned delay)
 *
 * Delay the specified number of microseconds.
 *
 * @param   delay is the number of microseconds to delay.
 *
 * @return  None
 */

#ifdef __cplusplus
}
#endif

#endif            /* end of protection macro */

