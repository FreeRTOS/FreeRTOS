/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Interface for the low-level initialization function.
 *
 */

#ifndef BOARD_LOWLEVEL_H
#define BOARD_LOWLEVEL_H

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
extern void defaultSpuriousHandler( void );
extern void defaultFiqHandler( void );
extern void defaultIrqHandler( void );

/* Cortex-A5 core handlers */
/*
*/

extern void SYS_IrqHandler( void ) ;
extern void Spurious_handler( void ) ;

/* Peripherals handlers */
extern void SAIC0_Handler(void);
extern void ARM_IrqHandler(void);
extern void PIT_IrqHandler(void);
extern void WDT_IrqHandler(void);
extern void PIOD_IrqHandler(void);
extern void USART0_IrqHandler(void);
extern void USART1_IrqHandler(void);
extern void XDMAC0_IrqHandler(void);
extern void ICM_IrqHandler(void);
extern void PKCC_IrqHandler(void);
extern void SCI_IrqHandler(void);
extern void AES_IrqHandler(void);
extern void AESB_IrqHandler(void);
extern void TDES_IrqHandler(void);
extern void SHA_IrqHandler(void);
extern void MPDDRC_IrqHandler(void);
extern void H32MX_IrqHandler(void);
extern void H64MX_IrqHandler(void);
extern void VDEC_IrqHandler(void);
extern void SECUMOD_IrqHandler(void);
extern void MSADCC_IrqHandler(void);
extern void HSMC_IrqHandler(void);
extern void PIOA_IrqHandler(void);
extern void PIOB_IrqHandler(void);
extern void PIOC_IrqHandler(void);
extern void PIOE_IrqHandler(void);
extern void UART0_IrqHandler(void);
extern void UART1_IrqHandler(void);
extern void USART2_IrqHandler(void);
extern void USART3_IrqHandler(void);
extern void USART4_IrqHandler(void);
extern void TWI0_IrqHandler(void);
extern void TWI1_IrqHandler(void);
extern void TWI2_IrqHandler(void);
extern void HSMCI0_IrqHandler(void);
extern void HSMCI1_IrqHandler(void);
extern void SPI0_IrqHandler(void);
extern void SPI1_IrqHandler(void);
extern void SPI2_IrqHandler(void);
extern void TC0_IrqHandler(void);
extern void TC1_IrqHandler(void);
extern void TC2_IrqHandler(void);
extern void PWM_IrqHandler(void);
extern void ADC_IrqHandler(void);
extern void DBGU_IrqHandler(void);
extern void UHPHS_IrqHandler(void);
extern void UDPHS_IrqHandler(void);
extern void SSC0_IrqHandler(void);
extern void SSC1_IrqHandler(void);
extern void XDMAC1_IrqHandler(void);
extern void LCDC_IrqHandler(void);
extern void ISI_IrqHandler(void);
extern void TRNG_IrqHandler(void);
extern void GMAC0_IrqHandler(void);
extern void GMAC1_IrqHandler(void);
extern void AIC0_IrqHandler(void);
extern void SFC_IrqHandler(void);
extern void SECURAM_IrqHandler(void);
extern void CTB_IrqHandler(void);
extern void SMD_IrqHandler(void);
extern void TWI3_IrqHandler(void);
extern void CATB_IrqHandler(void);
extern void SFR_IrqHandler(void);
extern void AIC1_IrqHandler(void);
extern void SAIC1_IrqHandler(void); 
extern void L2CC_IrqHandler(void);
extern void LowLevelInit( void ) ;

#endif /* BOARD_LOWLEVEL_H */

