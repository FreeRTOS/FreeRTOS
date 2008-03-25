###################################-*-asm*- 
# 
# Copyright (c) 2001 Xilinx, Inc.  All rights reserved. 
# 
# Xilinx, Inc. CONFIDENTIAL 
#
# XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A 
# COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
# ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR 
# STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION
# IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE 
# FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION.  
# XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO 
# THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO 
# ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE 
# FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY 
# AND FITNESS FOR A PARTICULAR PURPOSE.
# 
# crt0.s 
# 
#	C RunTime:
#	Used for initialization of small data 
#	anchors and stack for programs compiled using 
#	Xilinx Gnu Tools. This routine also intializes the 
#	exception and interrupt handlers
#
# $Id: crt0.s,v 1.1.4.2 2005/05/26 21:50:39 vasanth Exp $
# 
#######################################

/*      Vector map (Interrupts, Exceptions, Breakpoints)                 */
#	# 0x00 #		Jump to Start
#	# 0x04 #		nop 
#	# 0x08 #		Imm instr for soft exception address [Hi halfword]
#	# 0x0c #		Jump to sof Exception handler        [Lo halfword]
#	# 0x10 #		Imm instr for interrupt address      [Hi halfword]
#	# 0x14 #		Jump to interrupt handler            [Lo halfword]
#       # 0x18 #                nop - Reserved for breakpoint vector
#       # 0x1C #                nop - Reserved for breakpoint vector
#       # 0x20 #                Imm instr for hw exception address   [Hi halfword]
#       # 0x24 #                Jump instr to hw exception handler   [Lo halfword]                        

	.globl _start

/*	Set the exception and interrupt address vectors    */
/*	to jump to the appropriate handlers                */

	.align 2
	.ent _start
	_start:
        bri     _start1                 # 0x00
        nop                             # 0x04
        nop                             # 0x08          # Reserve space for software exception vector
        nop                             # 0x0c
        nop                             # 0x10          # Reserve space for interrupt vector
        nop                             # 0x14
        nop                             # 0x18          # Reserve space for breakpoint vector
        nop                             # 0x1c
        nop                             # 0x18          # Reserve space for hw exception vector
        nop                             # 0x1c        

        _start1:
/*	Set the Small Data Anchors and the Stack pointer  */
	la	r13, r0, _SDA_BASE_
	la	r2, r0, _SDA2_BASE_
	la	r1, r0, _stack-16   	# 16 bytes (4 words are needed by
					# crt for args and link reg )

/*      Set the opcodes brai and imm for handlers         */
	la	r6,r0,0xb8080000	# [opcode for brai ]
	swi	r6,r0,0x4		# [brai opcode for reset]        
	swi	r6,r0,0xc		# [brai opcode for exception]
	swi	r6,r0,0x14		# [brai opcode for interrupt]
	swi	r6,r0,0x24		# [brai opcode for hw exceptions]        

	la	r6,r0,0xb0000000	# [opcode for imm ]
	swi	r6,r0,0x0		# [imm opcode for reset]        
	swi	r6,r0,0x8		# [imm opcode for exception]
	swi	r6,r0,0x10		# [imm opocde for interrupt]
	swi	r6,r0,0x20		# [imm opocde for hw exceptions]        

/* 	Set Reset vector        */
	la	r6,r0,_start1
	sw	r6,r1,r0
	lhu	r7,r1,r0
	shi	r7,r0, 0x2  		# [imm for reset]
	shi	r6,r0, 0x6		# [lower half for reset]
        
/* 	Set Software Exception Handler */
	la	r6,r0,_exception_handler
	sw	r6,r1,r0
	lhu	r7,r1,r0
	shi	r7,r0, 0xa  		# [imm for exception]
	shi	r6,r0, 0xe		# [lower half for exception ]

/* 	Set Interrupt Handler */
	la	r6,r0,_interrupt_handler
	sw	r6,r1,r0
	lhu	r7,r1,r0
	shi	r7,r0, 0x12 		# [imm for exception]
	shi	r6,r0, 0x16		# [lower half for intterupt ]

/*      Set HW Exception Handler */
        la      r6,r0,_hw_exception_handler
        sw      r6,r1,r0
        lhu     r7,r1,r0
        shi     r7,r0, 0x22             # [imm for exception]
        shi     r6,r0, 0x26             # [lower half for hw exception]
                
/*	initialize bss sections				  */
	brlid	r15,_crtinit
	nop

/* 	Adjust the stack pointer 			  */
	addi	r1,r1,16

/*      Fall through to exit                              */
        .end _start
                
/* 	Use this exit function 	                          */
        .globl exit                  # exit library call 
        .ent exit        
exit:
	bri	exit
	.end exit        

