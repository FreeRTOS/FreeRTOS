/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
* 5.04	pkp  12/18/15 Updated the address map according to proper address map
*
* @note
*
* None.
*
******************************************************************************/
#include "xparameters.h"

	.globl  MMUTableL0
	.globl  MMUTableL1
	.globl  MMUTableL2

	.set reserved,	0x0 					/* Fault*/
	.set Memory,	0x405 | (3 << 8) | (0x0)		/* normal writeback write allocate inner shared read write */
	.set Device,	0x409 | (1 << 53)| (1 << 54) |(0x0)	/* strongly ordered read write non executable*/
	.section .mmu_tbl0,"a"

MMUTableL0:

.set SECT, MMUTableL1		/* 0x0000_0000 -  0x7F_FFFF_FFFF */
.8byte	SECT + 0x3
.set SECT, MMUTableL1+0x1000	/* 0x80_0000_0000 - 0xFF_FFFF_FFFF */
.8byte	SECT + 0x3

	.section .mmu_tbl1,"a"

MMUTableL1:

.set SECT, MMUTableL2		/* 0x0000_0000 - 0x3FFF_FFFF */
.8byte	SECT + 0x3		/* 1GB DDR */

.rept	0x3			/* 0x4000_0000 - 0xFFFF_FFFF */
.set SECT, SECT + 0x1000	/*1GB DDR, 1GB PL, 2GB other devices n memory */
.8byte	SECT + 0x3
.endr

.set SECT,0x100000000
.rept	0xC			/* 0x0001_0000_0000 - 0x0003_FFFF_FFFF */
.8byte	SECT + reserved		/* 12GB Reserved */
.set SECT, SECT + 0x40000000
.endr

.rept	0x10			/* 0x0004_0000_0000 - 0x0007_FFFF_FFFF */
.8byte	SECT + Device		/* 8GB PL, 8GB PCIe */
.set SECT, SECT + 0x40000000
.endr

.rept	0x20			/* 0x0008_0000_0000 - 0x000F_FFFF_FFFF */
.8byte	SECT + Memory		/* 32GB DDR */
.set SECT, SECT + 0x40000000
.endr

.rept	0x1C0			/* 0x0010_0000_0000 - 0x007F_FFFF_FFFF */
.8byte	SECT + Device		/* 448 GB PL */
.set SECT, SECT + 0x40000000
.endr


.rept	0x100			/* 0x0080_0000_0000 - 0x00BF_FFFF_FFFF */
.8byte	SECT + Device		/* 256GB PCIe */
.set SECT, SECT + 0x40000000
.endr


.rept	0x100			/* 0x00C0_0000_0000 - 0x00FF_FFFF_FFFF */
.8byte	SECT + reserved		/* 256GB reserved */
.set SECT, SECT + 0x40000000
.endr


.section .mmu_tbl2,"a"

MMUTableL2:

.set SECT, 0

#ifdef XPAR_PSU_DDR_0_S_AXI_BASEADDR
.set DDR_START, XPAR_PSU_DDR_0_S_AXI_BASEADDR
.set DDR_END, XPAR_PSU_DDR_0_S_AXI_HIGHADDR
.set DDR_SIZE, (DDR_END - DDR_START)+1
.if DDR_SIZE > 0x80000000
/* If DDR size is larger than 2GB, truncate to 2GB */
.set DDR_REG, 0x400
.else
.set DDR_REG, DDR_SIZE/0x200000
.endif
#else
.set DDR_REG, 0
#endif

.set UNDEF_REG, 0x400 - DDR_REG

.rept	DDR_REG			/* DDR based on size in hdf*/
.8byte	SECT + Memory
.set	SECT, SECT+0x200000
.endr

.rept	UNDEF_REG		/* reserved for region where ddr is absent */
.8byte	SECT + reserved
.set	SECT, SECT+0x200000
.endr

.rept	0x0200			/* 0x8000_0000 - 0xBFFF_FFFF */
.8byte	SECT + Device		/* 1GB lower PL */
.set	SECT, SECT+0x200000
.endr

.rept	0x0100			/* 0xC000_0000 - 0xDFFF_FFFF */
.8byte	SECT + Device		/* 512MB QSPI */
.set	SECT, SECT+0x200000
.endr

.rept	0x080			/* 0xE000_0000 - 0xEFFF_FFFF */
.8byte	SECT + Device		/* 256MB lower PCIe */
.set	SECT, SECT+0x200000
.endr

.rept	0x040			/* 0xF000_0000 - 0xF7FF_FFFF */
.8byte	SECT + reserved		/* 128MB Reserved */
.set	SECT, SECT+0x200000
.endr

.rept	0x8			/* 0xF800_0000 - 0xF8FF_FFFF */
.8byte	SECT + Device		/* 16MB coresight */
.set	SECT, SECT+0x200000
.endr

/* 1MB RPU LLP is marked for 2MB region as the minimum block size in
   translation table is 2MB and adjacent 63MB reserved region is
   converted to 62MB */

.rept	0x1			/* 0xF900_0000 - 0xF91F_FFFF */
.8byte	SECT + Device		/* 2MB RPU low latency port */
.set	SECT, SECT+0x200000
.endr

.rept	0x1F			/* 0xF920_0000 - 0xFCFF_FFFF */
.8byte	SECT + reserved		/* 62MB Reserved */
.set	SECT, SECT+0x200000
.endr

.rept	0x8			/* 0xFD00_0000 - 0xFDFF_FFFF */
.8byte	SECT + Device		/* 16MB FPS */
.set	SECT, SECT+0x200000
.endr

.rept	0xE			/* 0xFE00_0000 -  0xFFBF_FFFF */
.8byte	SECT + Device		/* 28MB LPS */
.set	SECT, SECT+0x200000
.endr

				/* 0xFFC0_0000 - 0xFFDF_FFFF */
.8byte	SECT + Device 		/*2MB PMU/CSU */

.set	SECT, SECT+0x200000	/* 0xFFE0_0000 - 0xFFFF_FFFF*/
.8byte  SECT + Memory		/*2MB OCM/TCM*/

.end
