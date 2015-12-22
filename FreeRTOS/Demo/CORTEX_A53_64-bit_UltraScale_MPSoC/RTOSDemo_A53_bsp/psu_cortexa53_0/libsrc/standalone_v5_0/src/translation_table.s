/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc. All rights reserved.
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
* @file translation_table.s
*
* This file contains the initialization for the MMU table in RAM
* needed by the Cortex A53 processor
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 5.00  pkp  05/21/14 Initial version
*
*
* @note
*
* None.
*
******************************************************************************/
	.globl  MMUTableL0
	.globl  MMUTableL1
	.globl  MMUTableL2

	.set reserved,	0x0 					/* Fault*/
	.set Memory,	0x405 | (3 << 8) | (0x0)		/* normal writeback write allocate inner shared read write */
	.set Device,	0x409 | (1 << 53)| (1 << 54) |(0x0)	/* strongly ordered read write non executable*/
	.section .mmu_tbl0,"a"

MMUTableL0:

.set SECT, MMUTableL1
.8byte	SECT + 0x3
.set SECT, MMUTableL1+0x1000
.8byte	SECT + 0x3

	.section .mmu_tbl1,"a"

MMUTableL1:

.set SECT, MMUTableL2			/*1GB DDR*/
.8byte	SECT + 0x3

.rept	0x3				/*1GB DDR, 1GB PL, 2GB other devices n memory*/
.set SECT, SECT + 0x1000
.8byte	SECT + 0x3
.endr

.set SECT,0x100000000
.rept	0xC
.8byte	SECT + reserved
.set SECT, SECT + 0x40000000	/*12GB Reserved*/
.endr

.rept	0x10
.8byte	SECT + Device
.set SECT, SECT + 0x40000000	/*8GB PL, 8GB PCIe*/

.endr

.rept	0x20
.8byte	SECT + Memory

.set SECT, SECT + 0x40000000	/*32GB DDR*/
.endr


.rept	0xC0
.8byte	SECT + Device
.set SECT, SECT + 0x40000000	/*192GB PL*/
.endr


.rept	0x100
.8byte	SECT + Device
.set SECT, SECT + 0x40000000	/*256GB PL/PCIe*/
.endr


.rept	0x200
.8byte	SECT + Device
.set SECT, SECT + 0x40000000	/*512GB PL/DDR*/
.endr


.section .mmu_tbl2,"a"

MMUTableL2:

.set SECT, 0

.rept	0x0400			/*2GB DDR */
.8byte	SECT + Memory
.set	SECT, SECT+0x200000
.endr

.rept	0x0200			/*1GB lower PL*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr
.rept	0x0100			/*512MB QSPI*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr
.rept	0x080			/*256MB lower PCIe*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr
.rept	0x040			/*128MB Reserved*/
.8byte	SECT + reserved
.set	SECT, SECT+0x200000
.endr
.rept	0x8			/*16MB coresight*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr
.rept	0x8			/*16MB RPU low latency port*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr

.rept	0x022			/*68MB Device*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr
.rept	0x8			/*8MB FPS*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr

.rept	0x4			/*16MB LPS*/
.8byte	SECT + Device
.set	SECT, SECT+0x200000
.endr

.8byte	SECT + Device 		/*2MB PMU/CSU */
.set	SECT, SECT+0x200000
.8byte  SECT + Memory		/*2MB OCM/TCM*/
.end
