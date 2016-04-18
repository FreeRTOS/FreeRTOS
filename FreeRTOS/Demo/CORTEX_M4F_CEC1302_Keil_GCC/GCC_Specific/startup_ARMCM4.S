/* File: startup_ARMCM4.S
 * Purpose: startup file for Cortex-M4 devices. Should use with
 *   GCC for ARM Embedded Processors
 * Version: V2.0
 * Date: 16 August 2013
 *
/* Copyright (c) 2011 - 2013 ARM LIMITED

   All rights reserved.
   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:
   - Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
   - Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
   - Neither the name of ARM nor the names of its contributors may be used
     to endorse or promote products derived from this software without
     specific prior written permission.
   *
   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
   AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
   ARE DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDERS AND CONTRIBUTORS BE
   LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
   CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
   SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
   INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
   CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
   ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
   POSSIBILITY OF SUCH DAMAGE.
   ---------------------------------------------------------------------------*/
	.syntax	unified
	.arch	armv7e-m

	.extern __SRAM_segment_end__

	.section .isr_vector,"a",%progbits
	.align	4
	.globl	__isr_vector
	.global __Vectors

__Vectors:
__isr_vector:
	.long	__SRAM_segment_end__ - 4  /* Top of Stack at top of RAM*/
	.long	Reset_Handler         /* Reset Handler */
	.long	NMI_Handler           /* NMI Handler */
	.long	HardFault_Handler     /* Hard Fault Handler */
	.long	MemManage_Handler     /* MPU Fault Handler */
	.long	BusFault_Handler      /* Bus Fault Handler */
	.long	UsageFault_Handler    /* Usage Fault Handler */
	.long	0                     /* Reserved */
	.long	0                     /* Reserved */
	.long	0                     /* Reserved */
	.long	0                     /* Reserved */
	.long	SVC_Handler           /* SVCall Handler */
	.long	DebugMon_Handler      /* Debug Monitor Handler */
	.long	0                     /* Reserved */
	.long	PendSV_Handler        /* PendSV Handler */
	.long	SysTick_Handler       /* SysTick Handler */

	/* External interrupts */
	.long     NVIC_Handler_I2C0
	.long     NVIC_Handler_I2C1
	.long     NVIC_Handler_I2C2
	.long     NVIC_Handler_I2C3
	.long     NVIC_Handler_DMA0
	.long     NVIC_Handler_DMA1
	.long     NVIC_Handler_DMA2
	.long     NVIC_Handler_DMA3
	.long     NVIC_Handler_DMA4
	.long     NVIC_Handler_DMA5
	.long     NVIC_Handler_DMA6
	.long     NVIC_Handler_DMA7
	.long     NVIC_Handler_LPCBERR
	.long     NVIC_Handler_UART0
	.long     NVIC_Handler_IMAP0
	.long     NVIC_Handler_EC0_IBF
	.long     NVIC_Handler_EC0_OBF
	.long     NVIC_Handler_EC1_IBF
	.long     NVIC_Handler_EC1_OBF
	.long     NVIC_Handler_PM1_CTL
	.long     NVIC_Handler_PM1_EN
	.long     NVIC_Handler_PM1_STS
	.long     NVIC_Handler_MIF8042_OBF
	.long     NVIC_Handler_MIF8042_IBF
	.long     NVIC_Handler_MAILBOX
	.long     NVIC_Handler_PECI
	.long     NVIC_Handler_TACH0
	.long     NVIC_Handler_TACH1
	.long     NVIC_Handler_ADC_SNGL
	.long     NVIC_Handler_ADC_RPT
	.long     NVIC_Handler_V2P_INT0
	.long     NVIC_Handler_V2P_INT1
	.long     NVIC_Handler_PS2_CH0
	.long     NVIC_Handler_PS2_CH1
	.long     NVIC_Handler_PS2_CH2
	.long     NVIC_Handler_PS2_CH3
	.long     NVIC_Handler_SPI0_TX
	.long     NVIC_Handler_SPI0_RX
	.long     NVIC_Handler_HIB_TMR
	.long     NVIC_Handler_KEY_INT
	.long     NVIC_Handler_KEY_WAKE
	.long     NVIC_Handler_RPM_STALL
	.long     NVIC_Handler_RPM_SPIN
	.long     NVIC_Handler_VBAT
	.long     NVIC_Handler_LED0
	.long     NVIC_Handler_LED1
	.long     NVIC_Handler_LED2
	.long     NVIC_Handler_MBC_ERR
	.long     NVIC_Handler_MBC_BUSY
	.long     NVIC_Handler_TMR0
	.long     NVIC_Handler_TMR1
	.long     NVIC_Handler_TMR2
	.long     NVIC_Handler_TMR3
	.long     NVIC_Handler_TMR4
	.long     NVIC_Handler_TMR5
	.long     NVIC_Handler_SPI1_TX
	.long     NVIC_Handler_SPI1_RX
	.long     NVIC_Handler_GIRQ08
	.long     NVIC_Handler_GIRQ09
	.long     NVIC_Handler_GIRQ10
	.long     NVIC_Handler_GIRQ11
	;.long     NVIC_Handler_GIRQ12
	.long     interrupt_irq12
	;.long     NVIC_Handler_GIRQ13
	.long     NVIC_Handler_GIRQ13
	.long     NVIC_Handler_GIRQ14
	.long     NVIC_Handler_GIRQ15
	.long     NVIC_Handler_GIRQ16
	.long     NVIC_Handler_GIRQ17
	.long     NVIC_Handler_GIRQ18
	.long     NVIC_Handler_GIRQ19
	.long     NVIC_Handler_GIRQ20
	.long     NVIC_Handler_GIRQ21
	.long     NVIC_Handler_GIRQ22
	.long     NVIC_Handler_GIRQ23
	.long     NVIC_Handler_073
	.long     NVIC_Handler_074
	.long     NVIC_Handler_075
	.long     NVIC_Handler_076
	.long     NVIC_Handler_077
	.long     NVIC_Handler_078
	.long     NVIC_Handler_079
	.long     NVIC_Handler_080
	.long     NVIC_Handler_DMA8
	.long     NVIC_Handler_DMA9
	.long     NVIC_Handler_DMA10
	.long     NVIC_Handler_DMA11
	.long     NVIC_Handler_LED3
	.long     NVIC_Handler_PKE_ERR
	.long     NVIC_Handler_PKE_END
	.long     NVIC_Handler_TRNG
	.long     NVIC_Handler_AES
	.long     NVIC_Handler_HASH


	.text
	.thumb
	.thumb_func
	.align	2
	.globl _start
	.extern main
	.globl	Reset_Handler
	.type	Reset_Handler, %function
_start:
Reset_Handler:
/*  Firstly it copies data from read only memory to RAM. There are two schemes
 *  to copy. One can copy more than one sections. Another can only copy
 *  one section.  The former scheme needs more instructions and read-only
 *  data to implement than the latter.
 *  Macro __STARTUP_COPY_MULTIPLE is used to choose between two schemes.  */

/*  Single section scheme.
 *
 *  The ranges of copy from/to are specified by following symbols
 *    __etext: LMA of start of the section to copy from. Usually end of text
 *    __data_start__: VMA of start of the section to copy to
 *    __data_end__: VMA of end of the section to copy to
 *
 *  All addresses must be aligned to 4 bytes boundary.
 */
	ldr	r1, =__etext
	ldr	r2, =__data_start__
	ldr	r3, =__data_end__

.L_loop1:
	cmp	r2, r3
	ittt	lt
	ldrlt	r0, [r1], #4
	strlt	r0, [r2], #4
	blt	.L_loop1

/*  This part of work usually is done in C library startup code. Otherwise,
 *  define this macro to enable it in this startup.
 *
 *  There are two schemes too. One can clear multiple BSS sections. Another
 *  can only clear one section. The former is more size expensive than the
 *  latter.
 *
 *  Define macro __STARTUP_CLEAR_BSS_MULTIPLE to choose the former.
 *  Otherwise efine macro __STARTUP_CLEAR_BSS to choose the later.
 */

 /*  Single BSS section scheme.
 *
 *  The BSS section is specified by following symbols
 *    __bss_start__: start of the BSS section.
 *    __bss_end__: end of the BSS section.
 *
 *  Both addresses must be aligned to 4 bytes boundary.
 */
	ldr	r1, =__bss_start__
	ldr	r2, =__bss_end__

	movs	r0, 0
.L_loop3:
	cmp	r1, r2
	itt	lt
	strlt	r0, [r1], #4
	blt	.L_loop3

#ifndef __NO_SYSTEM_INIT
/*	bl	SystemInit */
#endif

	bl	main

	.pool
	.size	Reset_Handler, . - Reset_Handler

	.align	1
	.thumb_func
	.weak	Default_Handler
	.type	Default_Handler, %function
Default_Handler:
	b	.
	.size	Default_Handler, . - Default_Handler

/*    Macro to define default handlers. Default handler
 *    will be weak symbol and just dead loops. They can be
 *    overwritten by other handlers */
	.macro	def_irq_handler	handler_name
	.weak	\handler_name
	.set	\handler_name, Default_Handler
	.endm

	def_irq_handler	NMI_Handler
	def_irq_handler	HardFault_Handler
	def_irq_handler	MemManage_Handler
	def_irq_handler	BusFault_Handler
	def_irq_handler	UsageFault_Handler
	def_irq_handler	SVC_Handler
	def_irq_handler	DebugMon_Handler
	def_irq_handler	PendSV_Handler
	def_irq_handler	SysTick_Handler
	def_irq_handler	DEF_IRQHandler

	def_irq_handler     NVIC_Handler_I2C0
	def_irq_handler     NVIC_Handler_I2C1
	def_irq_handler     NVIC_Handler_I2C2
	def_irq_handler     NVIC_Handler_I2C3
	def_irq_handler     NVIC_Handler_DMA0
	def_irq_handler     NVIC_Handler_DMA1
	def_irq_handler     NVIC_Handler_DMA2
	def_irq_handler     NVIC_Handler_DMA3
	def_irq_handler     NVIC_Handler_DMA4
	def_irq_handler     NVIC_Handler_DMA5
	def_irq_handler     NVIC_Handler_DMA6
	def_irq_handler     NVIC_Handler_DMA7
	def_irq_handler     NVIC_Handler_LPCBERR
	def_irq_handler     NVIC_Handler_UART0
	def_irq_handler     NVIC_Handler_IMAP0
	def_irq_handler     NVIC_Handler_EC0_IBF
	def_irq_handler     NVIC_Handler_EC0_OBF
	def_irq_handler     NVIC_Handler_EC1_IBF
	def_irq_handler     NVIC_Handler_EC1_OBF
	def_irq_handler     NVIC_Handler_PM1_CTL
	def_irq_handler     NVIC_Handler_PM1_EN
	def_irq_handler     NVIC_Handler_PM1_STS
	def_irq_handler     NVIC_Handler_MIF8042_OBF
	def_irq_handler     NVIC_Handler_MIF8042_IBF
	def_irq_handler     NVIC_Handler_MAILBOX
	def_irq_handler     NVIC_Handler_PECI
	def_irq_handler     NVIC_Handler_TACH0
	def_irq_handler     NVIC_Handler_TACH1
	def_irq_handler     NVIC_Handler_ADC_SNGL
	def_irq_handler     NVIC_Handler_ADC_RPT
	def_irq_handler     NVIC_Handler_V2P_INT0
	def_irq_handler     NVIC_Handler_V2P_INT1
	def_irq_handler     NVIC_Handler_PS2_CH0
	def_irq_handler     NVIC_Handler_PS2_CH1
	def_irq_handler     NVIC_Handler_PS2_CH2
	def_irq_handler     NVIC_Handler_PS2_CH3
	def_irq_handler     NVIC_Handler_SPI0_TX
	def_irq_handler     NVIC_Handler_SPI0_RX
	def_irq_handler     NVIC_Handler_HIB_TMR
	def_irq_handler     NVIC_Handler_KEY_INT
	def_irq_handler     NVIC_Handler_KEY_WAKE
	def_irq_handler     NVIC_Handler_RPM_STALL
	def_irq_handler     NVIC_Handler_RPM_SPIN
	def_irq_handler     NVIC_Handler_VBAT
	def_irq_handler     NVIC_Handler_LED0
	def_irq_handler     NVIC_Handler_LED1
	def_irq_handler     NVIC_Handler_LED2
	def_irq_handler     NVIC_Handler_MBC_ERR
	def_irq_handler     NVIC_Handler_MBC_BUSY
	def_irq_handler     NVIC_Handler_TMR0
	def_irq_handler     NVIC_Handler_TMR1
	def_irq_handler     NVIC_Handler_TMR2
	def_irq_handler     NVIC_Handler_TMR3
	def_irq_handler     NVIC_Handler_TMR4
	def_irq_handler     NVIC_Handler_TMR5
	def_irq_handler     NVIC_Handler_SPI1_TX
	def_irq_handler     NVIC_Handler_SPI1_RX
	def_irq_handler     NVIC_Handler_GIRQ08
	def_irq_handler     NVIC_Handler_GIRQ09
	def_irq_handler     NVIC_Handler_GIRQ10
	def_irq_handler     NVIC_Handler_GIRQ11
	;def_irq_handler     NVIC_Handler_GIRQ12
	def_irq_handler     interrupt_irq12
	;def_irq_handler     NVIC_Handler_GIRQ13
	def_irq_handler     interrupt_irq13
	def_irq_handler     NVIC_Handler_GIRQ14
	def_irq_handler     NVIC_Handler_GIRQ15
	def_irq_handler     NVIC_Handler_GIRQ16
	def_irq_handler     NVIC_Handler_GIRQ17
	def_irq_handler     NVIC_Handler_GIRQ18
	def_irq_handler     NVIC_Handler_GIRQ19
	def_irq_handler     NVIC_Handler_GIRQ20
	def_irq_handler     NVIC_Handler_GIRQ21
	def_irq_handler     NVIC_Handler_GIRQ22
	def_irq_handler     NVIC_Handler_GIRQ23
	def_irq_handler     NVIC_Handler_073
	def_irq_handler     NVIC_Handler_074
	def_irq_handler     NVIC_Handler_075
	def_irq_handler     NVIC_Handler_076
	def_irq_handler     NVIC_Handler_077
	def_irq_handler     NVIC_Handler_078
	def_irq_handler     NVIC_Handler_079
	def_irq_handler     NVIC_Handler_080
	def_irq_handler     NVIC_Handler_DMA8
	def_irq_handler     NVIC_Handler_DMA9
	def_irq_handler     NVIC_Handler_DMA10
	def_irq_handler     NVIC_Handler_DMA11
	def_irq_handler     NVIC_Handler_LED3
	def_irq_handler     NVIC_Handler_PKE_ERR
	def_irq_handler     NVIC_Handler_PKE_END
	def_irq_handler     NVIC_Handler_TRNG
	def_irq_handler     NVIC_Handler_AES
	def_irq_handler     NVIC_Handler_HASH

	.end
