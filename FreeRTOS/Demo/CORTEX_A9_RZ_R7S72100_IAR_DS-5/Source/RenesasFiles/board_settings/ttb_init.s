;/*******************************************************************************
;* DISCLAIMER
;* This software is supplied by Renesas Electronics Corporation and is only
;* intended for use with Renesas products. No other uses are authorized. This
;* software is owned by Renesas Electronics Corporation and is protected under
;* all applicable laws, including copyright laws.
;* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
;* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
;* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
;* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
;* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
;* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
;* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
;* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
;* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
;* Renesas reserves the right, without notice, to make changes to this software
;* and to discontinue the availability of this software. By using this software,
;* you agree to the additional terms and conditions found by accessing the
;* following link:
;* http://www.renesas.com/disclaimer
;*
;* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
;*******************************************************************************/
;/*******************************************************************************
;* File Name     : ttb_init.s
;* Version       : 0.01
;* Device(s)     : Aragon
;* Tool-Chain    : DS-5 Ver 5.8
;*                 ARM Complier 
;*               : 
;* H/W Platform  : Aragon CPU Board
;* Description   : Aragon Sample Program - TTB initialize
;*******************************************************************************/
;/*******************************************************************************
;* History : DD.MM.YYYY Version Description
;*         : 23.05.2012 0.01
;*******************************************************************************/

; ---- Parameter setting to level1 descriptor (bits 19:0) ----
; setting for Strongly-ordered memory
TTB_PARA_STRGLY				EQU		2_00000000000000000000110111100010
; setting for Outer and inner not cache normal memory
TTB_PARA_NORMAL_NOT_CACHE	EQU		2_00000000000000000001110111100010
; setting for Outer and inner write back, write allocate normal memory (Cacheable)
TTB_PARA_NORMAL_CACHE		EQU		2_00000000000000000001110111101110
; setting for Outer and inner write back, write allocate normal memory (Cacheable)
;TTB_PARA_NORMAL_CACHE		EQU		2_00000000000000000101110111100110

; ---- Memory area size (MB) ----
M_SIZE_NOR		EQU		128				; [Area00] CS0, CS1 area (for NOR flash)
M_SIZE_SDRAM	EQU		128				; [Area01] CS2, CS3 area (for SDRAM)
M_SIZE_CS45		EQU		128				; [Area02] CS4, CS5 area
M_SIZE_SPI		EQU		128				; [Area03] SPI, SP2 area (for Serial flash)
M_SIZE_RAM		EQU		10				; [Area04] Internal RAM
M_SIZE_IO_1		EQU		502				; [Area05] I/O area 1
M_SIZE_NOR_M	EQU		128				; [Area06] CS0, CS1 area (for NOR flash) (mirror)
M_SIZE_SDRAM_M	EQU		128				; [Area07] CS2, CS3 area (for SDRAM) (mirror)
M_SIZE_CS45_M	EQU		128				; [Area08] CS4, CS5 area (mirror)
M_SIZE_SPI_M	EQU		128				; [Area09] SPI, SP2 area (for Serial flash) (mirror)
M_SIZE_RAM_M	EQU		10				; [Area10] Internal RAM (mirror)
M_SIZE_IO_2		EQU		2550			; [Area11] I/O area 2

;==================================================================
; This code provides basic global enable for Cortex-A9 cache.
; It also enables branch prediction
; This code must be run from a privileged mode
;==================================================================
	AREA   INIT_TTB, CODE, READONLY

	IMPORT ||Image$$TTB$$ZI$$Base||		;;; From scatter file
	
	EXPORT	init_TTB

init_TTB	FUNCTION

;===================================================================
; Cortex-A9 MMU Configuration
; Set translation table base
;===================================================================
	;;; Cortex-A9 supports two translation tables
	;;; Configure translation table base (TTB) control register cp15,c2
	;;; to a value of all zeros, indicates we are using TTB register 0.
	MOV  r0,#0x0
	MCR  p15, 0, r0, c2, c0, 2		;;; TTBCR

	;;; write the address of our page table base to TTB register 0
	LDR  r0,=||Image$$TTB$$ZI$$Base||
	MOV  r1, #0x08					;;; RGN=b01  (outer cacheable write-back cached, write allocate)
									;;; S=0      (translation table walk to non-shared memory)
	ORR  r1,r1,#0x40				;;; IRGN=b01 (inner cacheability for the translation table walk is Write-back Write-allocate)
	ORR  r0,r0,r1
	MCR  p15, 0, r0, c2, c0, 0		;;; TTBR0

;===================================================================
; PAGE TABLE generation 
; Generate the page tables
; Build a flat translation table for the whole address space.
; ie: Create 4096 1MB sections from 0x000xxxxx to 0xFFFxxxxx
; 31                 20 19  18  17  16 15  14   12 11 10  9  8     5   4    3 2   1 0
; |section base address| 0  0  |nG| S |AP2|  TEX  |  AP | P | Domain | XN | C B | 1 0|
;
; Bits[31:20]   - Top 12 bits of VA is pointer into table
; nG[17]=0      - Non global, enables matching against ASID in the TLB when set.
; S[16]=0       - Indicates normal memory is shared when set.
; AP2[15]=0  
; AP[11:10]=11  - Configure for full read/write access in all modes
; TEX[14:12]=000
; CB[3:2]= 00   - Set attributes to Strongly-ordered memory.
;                 (except for the descriptor where code segment is based, see below)
; IMPP[9]=0     - Ignored
; Domain[5:8]=1111   - Set all pages to use domain 15
; XN[4]=0       - Execute never disabled
; Bits[1:0]=10  - Indicate entry is a 1MB section
;===================================================================
	LDR  r0,=||Image$$TTB$$ZI$$Base||
	LDR  r1,=0xFFF
	LDR  r2,=11
	LDR  r3,=0
	LDR	 r4,=0
	LDR  r5,=0

	;;; r0 contains the address of the translation table base
	;;; r1 is loop counter
	;;; r2 is target area counter (Initialize value = Last area No.)
	;;; r3 is loop counter by area

	;;; use loop counter to create 4096 individual table entries.
	;;; this writes from address 'Image$$TTB$$ZI$$Base' + 
	;;; offset 0x3FFC down to offset 0x0 in word steps (4 bytes)

set_mem_accsess
	CMP  r2, #11
	BEQ  setting_area11
	CMP  r2, #10
	BEQ  setting_area10
	CMP  r2, #9
	BEQ  setting_area9
	CMP  r2, #8
	BEQ  setting_area8
	CMP  r2, #7
	BEQ  setting_area7
	CMP  r2, #6
	BEQ  setting_area6
	CMP  r2, #5
	BEQ  setting_area5
	CMP  r2, #4
	BEQ  setting_area4
	CMP  r2, #3
	BEQ  setting_area3
	CMP  r2, #2
	BEQ  setting_area2
	CMP  r2, #1
	BEQ  setting_area1
	CMP  r2, #0
	BEQ  setting_area0
setting_area11						;;; [area11] I/O area 2
	LDR  r3, =M_SIZE_IO_2
	LDR  r4, =TTB_PARA_STRGLY		;;; 	Strongly-ordered
	BAL  init_counter
setting_area10						;;; [area10] Internal RAM (mirror)
	LDR  r3, =M_SIZE_RAM_M
	LDR  r4, =TTB_PARA_NORMAL_NOT_CACHE	;;; Normal (not cache)
	BAL  init_counter
setting_area9						;;; [area09] SPI, SP2 area (for Serial flash) (mirror)
	LDR  r3, =M_SIZE_SPI_M
	LDR  r4, =TTB_PARA_NORMAL_NOT_CACHE	;;; Normal (not cache)
	BAL  init_counter
setting_area8						;;; [area08] CS4, CS5 area (mirror)
	LDR  r3, =M_SIZE_CS45_M
	LDR  r4, =TTB_PARA_STRGLY		;;; 	Strongly-ordered
	BAL  init_counter	
setting_area7						;;; [area07] CS2, CS3 area (for SDRAM) (mirror)
	LDR  r3, =M_SIZE_SDRAM_M
	LDR  r4, =TTB_PARA_NORMAL_NOT_CACHE	;;; Normal (not cache)
	BAL  init_counter
setting_area6						;;; [area06] CS0, CS1 area (for NOR flash) (mirror)
	LDR  r3, =M_SIZE_NOR_M
	LDR  r4, =TTB_PARA_NORMAL_NOT_CACHE	;;; Normal (not cache)
	BAL  init_counter
setting_area5						;;; [area05] I/O area 1
	LDR  r3, =M_SIZE_IO_1
	LDR  r4, =TTB_PARA_STRGLY		;;; 	Strongly-ordered
	BAL  init_counter
setting_area4						;;; [area04] Internal RAM
	LDR  r3, =M_SIZE_RAM
	LDR  r4, =TTB_PARA_NORMAL_CACHE	;;; 	Normal (Cacheable)
	BAL  init_counter
setting_area3						;;; [area03] SPI, SP2 area (for Serial flash)
	LDR  r3, =M_SIZE_SPI
	LDR  r4, =TTB_PARA_NORMAL_CACHE	;;; 	Normal (Cacheable)
	BAL  init_counter
setting_area2						;;; [area02] CS4, CS5 area
	LDR  r3, =M_SIZE_CS45
	LDR  r4, =TTB_PARA_STRGLY		;;; 	Strongly-ordered
	BAL  init_counter
setting_area1						;;; [area01] CS2, CS3 area (for SDRAM)
	LDR  r3, =M_SIZE_SDRAM
	LDR  r4, =TTB_PARA_NORMAL_CACHE	;;; 	Normal (Cacheable)
	BAL  init_counter	
setting_area0						;;; [area00] CS0, CS1 area (for NOR flash)
	LDR  r3, =M_SIZE_NOR
	LDR  r4, =TTB_PARA_NORMAL_CACHE	;;; 	Normal (Cacheable)
	BAL  init_counter
init_counter
	SUBS r3, r3, #1					;;; memory size -> loop counter value
write_ttb
	ORR  r5, r4, r1, LSL#20			;;; R5 now contains full level1 descriptor to write
	STR  r5, [r0, r1, LSL#2]		;;; Str table entry at TTB base + loopcount*4
	SUB  r1, r1, #1					;;; Decrement loop counter
	SUBS r3, r3, #1					;;; Decrement loop counter by area
	BPL  write_ttb
	SUBS r2, r2, #1					;;; target area counter
	BPL  set_mem_accsess			;;; To the next area

	BX   lr

	ENDFUNC


	END
