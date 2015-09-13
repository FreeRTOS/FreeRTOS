/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_interrupthandlers.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file declares interrupt handlers.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef INTERRUPT_HANDLERS_H
#define INTERRUPT_HANDLERS_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
/* FIQ exception handler */
#ifdef __ICCARM__
	__irq __arm void r_fiq_handler(void);

	/* ICU IRQ12 */
	__irq __arm void r_icu_irq12_interrupt(void);

	/* RSPI1 SPTI1 */
	__irq __arm void r_rspi1_transmit_interrupt(void);

	/* RSPI1 SPEI1 */
	__irq __arm void r_rspi1_error_interrupt(void);

	/* RSPI1 SPII1 */
	__irq __arm void r_rspi1_idle_interrupt(void);
#endif /* __ICCARM__ */

#ifdef __GNUC__
	void r_fiq_handler(void) __attribute__((interrupt ("FIQ")));

	/* ICU IRQ12 */
	void r_icu_irq12_interrupt(void) __attribute__((interrupt ("IRQ")));

	/* RSPI1 SPTI1 */
	void r_rspi1_transmit_interrupt(void) __attribute__((interrupt ("IRQ")));

	/* RSPI1 SPEI1 */
	void r_rspi1_error_interrupt(void) __attribute__((interrupt ("IRQ")));

	/* RSPI1 SPII1 */
	void r_rspi1_idle_interrupt(void) __attribute__((interrupt ("IRQ")));
#endif /* __GNUC__ */

#endif
