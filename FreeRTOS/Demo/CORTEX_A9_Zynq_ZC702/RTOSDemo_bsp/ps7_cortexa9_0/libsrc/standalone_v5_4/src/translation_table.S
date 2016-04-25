/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc.  All rights reserved.
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
* needed by the Cortex A9 processor
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a ecm  10/20/09 Initial version
* 3.04a sdm  01/13/12 Updated MMU table to mark DDR memory as Shareable
* 3.07a sgd  07/05/2012 Configuring device address spaces as shareable device
*		       instead of strongly-ordered.
* 3.07a asa  07/17/2012 Changed the property of the ".mmu_tbl" section.
* 4.2	pkp  09/02/2014 added entries for 0xfe000000 to 0xffefffff as reserved
*			and  0xe0000000 - 0xe1ffffff is broken down into
*			0xe0000000 - 0xe02fffff (memory mapped devides)
*			0xe0300000 - 0xe0ffffff (reserved) and
*			0xe1000000 - 0xe1ffffff (NAND)
* 5.2	pkp  06/08/2015 put a check for XPAR_PS7_DDR_0_S_AXI_BASEADDR to confirm
*			if DDR is present or not and accordingly generate the
*			translation table
* </pre>
*
* @note
*
* None.
*
******************************************************************************/
#include "xparameters.h"
	.globl  MMUTable

	.section .mmu_tbl,"a"

MMUTable:
	/* Each table entry occupies one 32-bit word and there are
	 * 4096 entries, so the entire table takes up 16KB.
	 * Each entry covers a 1MB section.
	 */
.set SECT, 0

#ifdef XPAR_PS7_DDR_0_S_AXI_BASEADDR
.set DDR_START, XPAR_PS7_DDR_0_S_AXI_BASEADDR
.set DDR_END, XPAR_PS7_DDR_0_S_AXI_HIGHADDR
.set DDR_SIZE, (DDR_END - DDR_START)+1
.set DDR_REG, DDR_SIZE/0x100000
#else
.set DDR_REG, 0
#endif

.set UNDEF_REG, 0x3FF - DDR_REG

				/*0x00000000 - 0x00100000 (cacheable )*/
.word	SECT + 0x15de6		/* S=b1 TEX=b101 AP=b11, Domain=b1111, C=b0, B=b1 */
.set	SECT, SECT+0x100000

.rept	DDR_REG			/*  (DDR Cacheable) */
.word	SECT + 0x15de6		/* S=b1 TEX=b101 AP=b11, Domain=b1111, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	UNDEF_REG			/*  (unassigned/reserved).
				 * Generates a translation fault if accessed */
.word	SECT + 0x0		/* S=b0 TEX=b000 AP=b00, Domain=b0, C=b0, B=b0 */
.set	SECT, SECT+0x100000
.endr


.rept	0x0400			/* 0x40000000 - 0x7fffffff (FPGA slave0) */
.word	SECT + 0xc02		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0400			/* 0x80000000 - 0xbfffffff (FPGA slave1) */
.word	SECT + 0xc02		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0200			/* 0xc0000000 - 0xdfffffff (unassigned/reserved).
				 * Generates a translation fault if accessed */
.word	SECT + 0x0		/* S=b0 TEX=b000 AP=b00, Domain=b0, C=b0, B=b0 */
.set	SECT, SECT+0x100000
.endr

.rept	0x003			/* 0xe0000000 - 0xe02fffff (Memory mapped devices)
				 * UART/USB/IIC/SPI/CAN/GEM/GPIO/QSPI/SD/NAND */
.word	SECT + 0xc06		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0D			/* 0xe0300000 - 0xe0ffffff (unassigned/reserved).
				 * Generates a translation fault if accessed */
.word	SECT + 0x0		/* S=b0 TEX=b000 AP=b00, Domain=b0, C=b0, B=b0 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0010			/* 0xe1000000 - 0xe1ffffff (NAND) */
.word	SECT + 0xc06		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0020			/* 0xe2000000 - 0xe3ffffff (NOR) */
.word	SECT + 0xc06		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0020			/* 0xe4000000 - 0xe5ffffff (SRAM) */
.word	SECT + 0xc0e		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b1, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0120			/* 0xe6000000 - 0xf7ffffff (unassigned/reserved).
				 * Generates a translation fault if accessed */
.word	SECT + 0x0		/* S=b0 TEX=b000 AP=b00, Domain=b0, C=b0, B=b0 */
.set	SECT, SECT+0x100000
.endr

/* 0xf8000c00 to 0xf8000fff, 0xf8010000 to 0xf88fffff and
   0xf8f03000 to 0xf8ffffff are reserved  but due to granual size of
   1MB, it is not possible to define separate regions for them */

.rept	0x0010			/* 0xf8000000 - 0xf8ffffff (AMBA APB Peripherals) */

.word	SECT + 0xc06		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0030			/* 0xf9000000 - 0xfbffffff (unassigned/reserved).
				 * Generates a translation fault if accessed */
.word	SECT + 0x0		/* S=b0 TEX=b000 AP=b00, Domain=b0, C=b0, B=b0 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0020			/* 0xfc000000 - 0xfdffffff (Linear QSPI - XIP) */
.word	SECT + 0xc0a		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b1, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x001F			/* 0xfe000000 - 0xffefffff (unassigned/reserved).
				 * Generates a translation fault if accessed */
.word	SECT + 0x0		/* S=b0 TEX=b000 AP=b00, Domain=b0, C=b0, B=b0 */
.set	SECT, SECT+0x100000
.endr

/* 0xfff00000 to 0xfffb0000 is reserved but due to granual size of
   1MB, it is not possible to define separate region for  it

/* 0xfff00000 - 0xffffffff
   256K OCM when mapped to high address space
   inner-cacheable */
.word	SECT + 0x4c0e		/* S=b0 TEX=b100 AP=b11, Domain=b0, C=b1, B=b1 */
.set	SECT, SECT+0x100000

.end
