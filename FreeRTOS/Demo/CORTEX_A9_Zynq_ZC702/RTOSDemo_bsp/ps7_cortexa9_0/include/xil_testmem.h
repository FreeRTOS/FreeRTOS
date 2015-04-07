/******************************************************************************
*
*
* (c) Copyright 2009 Xilinx, Inc. All rights reserved.
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
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xil_testmem.h
*
* This file contains utility functions to test memory.
*
* <b>Memory test description</b>
*
* A subset of the memory tests can be selected or all of the tests can be run
* in order. If there is an error detected by a subtest, the test stops and the
* failure code is returned. Further tests are not run even if all of the tests
* are selected.
*
* Subtest descriptions:
* <pre>
* XIL_TESTMEM_ALLMEMTESTS:
*       Runs all of the following tests
*
* XIL_TESTMEM_INCREMENT:
*       Incrementing Value Test.
*       This test starts at 'XIL_TESTMEM_INIT_VALUE' and uses the
*	incrementing value as the test value for memory.
*
* XIL_TESTMEM_WALKONES:
*       Walking Ones Test.
*       This test uses a walking '1' as the test value for memory.
*       location 1 = 0x00000001
*       location 2 = 0x00000002
*       ...
*
* XIL_TESTMEM_WALKZEROS:
*       Walking Zero's Test.
*       This test uses the inverse value of the walking ones test
*       as the test value for memory.
*       location 1 = 0xFFFFFFFE
*       location 2 = 0xFFFFFFFD
*       ...
*
* XIL_TESTMEM_INVERSEADDR:
*       Inverse Address Test.
*       This test uses the inverse of the address of the location under test
*       as the test value for memory.
*
* XIL_TESTMEM_FIXEDPATTERN:
*       Fixed Pattern Test.
*       This test uses the provided patters as the test value for memory.
*       If zero is provided as the pattern the test uses '0xDEADBEEF".
* </pre>
*
* <i>WARNING</i>
*
* The tests are <b>DESTRUCTIVE</b>. Run before any initialized memory spaces
* have been set up.
*
* The address provided to the memory tests is not checked for
* validity except for the NULL case. It is possible to provide a code-space
* pointer for this test to start with and ultimately destroy executable code
* causing random failures.
*
* @note
*
* Used for spaces where the address range of the region is smaller than
* the data width. If the memory range is greater than 2 ** width,
* the patterns used in XIL_TESTMEM_WALKONES and XIL_TESTMEM_WALKZEROS will
* repeat on a boundry of a power of two making it more difficult to detect
* addressing errors. The XIL_TESTMEM_INCREMENT and XIL_TESTMEM_INVERSEADDR
* tests suffer the same problem. Ideally, if large blocks of memory are to be
* tested, break them up into smaller regions of memory to allow the test
* patterns used not to repeat over the region tested.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver    Who    Date    Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a hbm  08/25/09 First release
* </pre>
*
******************************************************************************/

#ifndef XIL_TESTMEM_H	/* prevent circular inclusions */
#define XIL_TESTMEM_H	/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/
#include "xil_types.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/

/* xutil_memtest defines */

#define XIL_TESTMEM_INIT_VALUE  1

/** @name Memory subtests
 * @{
 */
/**
 * See the detailed description of the subtests in the file description.
 */
#define XIL_TESTMEM_ALLMEMTESTS     0
#define XIL_TESTMEM_INCREMENT       1
#define XIL_TESTMEM_WALKONES        2
#define XIL_TESTMEM_WALKZEROS       3
#define XIL_TESTMEM_INVERSEADDR     4
#define XIL_TESTMEM_FIXEDPATTERN    5
#define XIL_TESTMEM_MAXTEST         XIL_TESTMEM_FIXEDPATTERN
/* @} */

/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

/* xutil_testmem prototypes */

extern int Xil_TestMem32(u32 *Addr, u32 Words, u32 Pattern, u8 Subtest);
extern int Xil_TestMem16(u16 *Addr, u32 Words, u16 Pattern, u8 Subtest);
extern int Xil_TestMem8(u8 *Addr, u32 Words, u8 Pattern, u8 Subtest);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
