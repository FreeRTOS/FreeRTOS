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
* </pre>
*
* @note
*
* None.
*
******************************************************************************/
	.globl  MMUTable

	.section .mmu_tbl,"a"

MMUTable:
	/* Each table entry occupies one 32-bit word and there are
	 * 4096 entries, so the entire table takes up 16KB.
	 * Each entry covers a 1MB section.
	 */

.set SECT, 0

.rept	0x0400			/* 0x00000000 - 0x3fffffff (DDR Cacheable) */
.word	SECT + 0x15de6		/* S=b1 TEX=b101 AP=b11, Domain=b1111, C=b0, B=b1 */
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

.rept	0x0020			/* 0xe0000000 - 0xe1ffffff (Memory mapped devices)
				 * UART/USB/IIC/SPI/CAN/GEM/GPIO/QSPI/SD/NAND */
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

.rept	0x0010			/* 0xf8000000 - 0xf8ffffff (AMBA APB Peripherals) */
.word	SECT + 0xc06		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b0, B=b1 */
.set	SECT, SECT+0x100000
.endr

.rept	0x0030			/* 0xf9000000 - 0xfbffffff (unassigned/reserved).
				 * Generates a translation fault if accessed */
.word	SECT + 0x0		/* S=b0 TEX=b000 AP=b00, Domain=b0, C=b0, B=b0 */
.set	SECT, SECT+0x100000
.endr

.rept	0x003f			/* 0xfc000000 - 0xffefffff (Linear QSPI - XIP) */
.word	SECT + 0xc0a		/* S=b0 TEX=b000 AP=b11, Domain=b0, C=b1, B=b1 */
.set	SECT, SECT+0x100000
.endr

				/* 256K OCM when mapped to high address space
				 * inner-cacheable */
.word	SECT + 0x4c0e		/* S=b0 TEX=b100 AP=b11, Domain=b0, C=b1, B=b1 */
.set	SECT, SECT+0x100000

.end
