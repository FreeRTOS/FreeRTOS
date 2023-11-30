/**
 * \file
 *
 * \brief This file contains the default exception handlers.
 *
 * Copyright (c) 2011 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 * \par Purpose
 *
 * This file provides basic support for Cortex-M processor based 
 * microcontrollers.
 *
 * \note
 * The exception handler has weak aliases.
 * As they are weak aliases, any function with the same name will override
 * this definition.
 *
 */


#include "exceptions.h"

/* @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/* @endcond */

#ifdef __GNUC__
/* Cortex-M3 core handlers */
void Reset_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void NMI_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void HardFault_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void MemManage_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void BusFault_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void UsageFault_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void SVC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void DebugMon_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void PendSV_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void SysTick_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));

/* Peripherals handlers */
void ACC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void ADC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void CRCCU_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void DACC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void EFC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void HSMCI_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void PIOA_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void PIOB_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void PIOC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void PMC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void PWM_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void RSTC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void RTC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void RTT_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void SMC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void SPI_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void SSC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void SUPC_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TC0_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TC1_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TC2_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TC3_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TC4_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TC5_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TWI0_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void TWI1_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void UART0_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void UART1_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void USART0_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void USART1_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void UDP_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
void WDT_Handler(void) __attribute__ ((weak, alias("Dummy_Handler")));
#endif /* __GNUC__ */

#ifdef __ICCARM__
/* Cortex-M3 core handlers */
#pragma weak Reset_Handler=Dummy_Handler
#pragma weak NMI_Handler=Dummy_Handler
#pragma weak HardFault_Handler=Dummy_Handler
#pragma weak MemManage_Handler=Dummy_Handler
#pragma weak BusFault_Handler=Dummy_Handler
#pragma weak UsageFault_Handler=Dummy_Handler
#pragma weak SVC_Handler=Dummy_Handler
#pragma weak DebugMon_Handler=Dummy_Handler
#pragma weak PendSV_Handler=Dummy_Handler
#pragma weak SysTick_Handler=Dummy_Handler

/* Peripherals handlers */
#pragma weak ACC_Handler=Dummy_Handler
#pragma weak ADC_Handler=Dummy_Handler
#pragma weak CRCCU_Handler=Dummy_Handler
#pragma weak DACC_Handler=Dummy_Handler
#pragma weak EFC_Handler=Dummy_Handler
#pragma weak HSMCI_Handler=Dummy_Handler
#pragma weak PIOA_Handler=Dummy_Handler
#pragma weak PIOB_Handler=Dummy_Handler
#pragma weak PIOC_Handler=Dummy_Handler
#pragma weak PMC_Handler=Dummy_Handler
#pragma weak PWM_Handler=Dummy_Handler
#pragma weak RSTC_Handler=Dummy_Handler
#pragma weak RTC_Handler=Dummy_Handler
#pragma weak RTT_Handler=Dummy_Handler
#pragma weak SMC_Handler=Dummy_Handler
#pragma weak SPI_Handler=Dummy_Handler
#pragma weak SSC_Handler=Dummy_Handler
#pragma weak SUPC_Handler=Dummy_Handler
#pragma weak TC0_Handler=Dummy_Handler
#pragma weak TC1_Handler=Dummy_Handler
#pragma weak TC2_Handler=Dummy_Handler
#pragma weak TC3_Handler=Dummy_Handler
#pragma weak TC4_Handler=Dummy_Handler
#pragma weak TC5_Handler=Dummy_Handler
#pragma weak TWI0_Handler=Dummy_Handler
#pragma weak TWI1_Handler=Dummy_Handler
#pragma weak UART0_Handler=Dummy_Handler
#pragma weak UART1_Handler=Dummy_Handler
#pragma weak USART0_Handler=Dummy_Handler
#pragma weak USART1_Handler=Dummy_Handler
#pragma weak UDP_Handler=Dummy_Handler
#pragma weak WDT_Handler=Dummy_Handler
#endif /* __ICCARM__ */

/**
 * \brief Default interrupt handler for unused IRQs.
 */
void Dummy_Handler(void)
{
	while (1) {
	}
}

/* @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/* @endcond */
