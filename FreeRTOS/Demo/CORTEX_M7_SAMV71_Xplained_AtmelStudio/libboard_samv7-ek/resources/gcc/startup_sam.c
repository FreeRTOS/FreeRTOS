/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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


#include "samv71.h"

/* Initialize segments */
extern uint32_t _sfixed;
extern uint32_t _efixed;
extern uint32_t _etext;
extern uint32_t _srelocate;
extern uint32_t _erelocate;
extern uint32_t _szero;
extern uint32_t _ezero;
extern uint32_t _sstack;
extern uint32_t _estack;

/** \cond DOXYGEN_SHOULD_SKIP_THIS */
int main(void);
/** \endcond */

void __libc_init_array(void);
void LowLevelInit(void);


/* Default empty handler */
void Dummy_Handler(void);

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
#pragma weak SUPC_Handler=Dummy_Handler
#pragma weak RSTC_Handler=Dummy_Handler
#pragma weak RTC_Handler=Dummy_Handler
#pragma weak RTT_Handler=Dummy_Handler
#pragma weak WDT_Handler=Dummy_Handler
#pragma weak PMC_Handler=Dummy_Handler
#pragma weak EFC_Handler=Dummy_Handler
#pragma weak UART0_Handler=Dummy_Handler
#pragma weak UART1_Handler=Dummy_Handler
#pragma weak PIOA_Handler=Dummy_Handler
#pragma weak PIOB_Handler=Dummy_Handler
#ifdef _SAMV71_PIOC_INSTANCE_
#pragma weak PIOC_Handler=Dummy_Handler
#endif /* _SAM_PIOC_INSTANCE_ */
#pragma weak USART0_Handler=Dummy_Handler
#pragma weak USART1_Handler=Dummy_Handler
#pragma weak USART2_Handler=Dummy_Handler
#pragma weak PIOD_Handler=Dummy_Handler
#ifdef _SAMV71_PIOE_INSTANCE_
#pragma weak PIOE_Handler=Dummy_Handler
#endif /* _SAM_PIOE_INSTANCE_ */
#ifdef _SAMV71_HSMCI_INSTANCE_
#pragma weak HSMCI_Handler=Dummy_Handler
#endif /* _SAM_HSMCI_INSTANCE_ */
#pragma weak TWIHS0_Handler=Dummy_Handler
#pragma weak TWIHS1_Handler=Dummy_Handler
#pragma weak SPI0_Handler=Dummy_Handler
#pragma weak SSC_Handler=Dummy_Handler
#pragma weak TC0_Handler=Dummy_Handler
#pragma weak TC1_Handler=Dummy_Handler
#pragma weak TC2_Handler=Dummy_Handler
#ifdef _SAMV71_TC1_INSTANCE_
#pragma weak TC3_Handler=Dummy_Handler
#endif /* _SAM_TC1_INSTANCE_ */
#ifdef _SAMV71_TC1_INSTANCE_
#pragma weak TC4_Handler=Dummy_Handler
#endif /* _SAM_TC1_INSTANCE_ */
#ifdef _SAMV71_TC1_INSTANCE_
#pragma weak TC5_Handler=Dummy_Handler
#endif /* _SAM_TC1_INSTANCE_ */
#pragma weak AFEC0_Handler=Dummy_Handler
#ifdef _SAMV71_DACC_INSTANCE_
#pragma weak DACC_Handler=Dummy_Handler
#endif /* _SAM_DACC_INSTANCE_ */
#pragma weak PWM0_Handler=Dummy_Handler
#pragma weak ICM_Handler=Dummy_Handler
#pragma weak ACC_Handler=Dummy_Handler
#pragma weak USBHS_Handler=Dummy_Handler
#pragma weak MCAN0_Handler=Dummy_Handler
#pragma weak MCAN0_Line1_Handler=Dummy_Handler
#pragma weak MCAN1_Handler=Dummy_Handler
#pragma weak MCAN1_Line1_Handler=Dummy_Handler
#pragma weak GMAC_Handler=Dummy_Handler
#pragma weak GMACQ1_Handler=Dummy_Handler
#pragma weak GMACQ2_Handler=Dummy_Handler
#pragma weak AFEC1_Handler=Dummy_Handler
#ifdef _SAMV71_TWIHS2_INSTANCE_
#pragma weak TWIHS2_Handler=Dummy_Handler
#endif /* _SAM_TWI2_INSTANCE_ */
#pragma weak SPI1_Handler=Dummy_Handler
#pragma weak QSPI_Handler=Dummy_Handler
#pragma weak UART2_Handler=Dummy_Handler
#pragma weak UART3_Handler=Dummy_Handler
#pragma weak UART4_Handler=Dummy_Handler
#ifdef _SAMV71_TC2_INSTANCE_
#pragma weak TC6_Handler=Dummy_Handler
#endif /* _SAM_TC2_INSTANCE_ */
#ifdef _SAMV71_TC2_INSTANCE_
#pragma weak TC7_Handler=Dummy_Handler
#endif /* _SAM_TC2_INSTANCE_ */
#ifdef _SAMV71_TC2_INSTANCE_
#pragma weak TC8_Handler=Dummy_Handler
#endif /* _SAM_TC2_INSTANCE_ */
#pragma weak TC9_Handler=Dummy_Handler
#pragma weak TC10_Handler=Dummy_Handler
#pragma weak TC11_Handler=Dummy_Handler
#pragma weak MLB_Handler=Dummy_Handler
#pragma weak AES_Handler=Dummy_Handler
#pragma weak TRNG_Handler=Dummy_Handler
#pragma weak XDMAC_Handler=Dummy_Handler
#pragma weak ISI_Handler=Dummy_Handler
#pragma weak PWM1_Handler=Dummy_Handler
#pragma weak FPU_Handler=Dummy_Handler
#ifdef _SAMV71_SDRAMC_INSTANCE_
#pragma weak SDRAMC_Handler=Dummy_Handler
#endif /* _SAM_SDRAMC_INSTANCE_ */
#pragma weak RSWDT_Handler=Dummy_Handler
#pragma weak CCF_Handler=Dummy_Handler
#pragma weak CCW_Handler=Dummy_Handler


/* Exception Table */
__attribute__ ((section(".vectors")))
const DeviceVectors exception_table = {

		/* Configure Initial Stack Pointer, using linker-generated symbols */
		.pvStack = (void*) (&_estack),

		.pfnReset_Handler      = (void*) Reset_Handler,
		.pfnNMI_Handler        = (void*) NMI_Handler,
		.pfnHardFault_Handler  = (void*) HardFault_Handler,
		.pfnMemManage_Handler  = (void*) MemManage_Handler,
		.pfnBusFault_Handler   = (void*) BusFault_Handler,
		.pfnUsageFault_Handler = (void*) UsageFault_Handler,
		.pfnReserved1_Handler  = (void*) (0UL),          /* Reserved */
		.pfnReserved2_Handler  = (void*) (0UL),          /* Reserved */
		.pfnReserved3_Handler  = (void*) (0UL),          /* Reserved */
		.pfnReserved4_Handler  = (void*) (0UL),          /* Reserved */
		.pfnSVC_Handler        = (void*) SVC_Handler,
		.pfnDebugMon_Handler   = (void*) DebugMon_Handler,
		.pfnReserved5_Handler  = (void*) (0UL),          /* Reserved */
		.pfnPendSV_Handler     = (void*) PendSV_Handler,
		.pfnSysTick_Handler    = (void*) SysTick_Handler,

		/* Configurable interrupts */
		.pfnSUPC_Handler   = (void*) SUPC_Handler,   /* 0  Supply Controller */
		.pfnRSTC_Handler   = (void*) RSTC_Handler,   /* 1  Reset Controller */
		.pfnRTC_Handler    = (void*) RTC_Handler,    /* 2  Real Time Clock */
		.pfnRTT_Handler    = (void*) RTT_Handler,    /* 3  Real Time Timer */
		.pfnWDT_Handler    = (void*) WDT_Handler,    /* 4  Watchdog Timer 0 */
		.pfnPMC_Handler    = (void*) PMC_Handler,    /* 5  Power Management Controller */
		.pfnEFC_Handler    = (void*) EFC_Handler,    /* 6  Enhanced Embedded Flash Controller */
		.pfnUART0_Handler  = (void*) UART0_Handler,  /* 7  UART 0 */
		.pfnUART1_Handler  = (void*) UART1_Handler,  /* 8  UART 1 */
		.pvReserved9       = (void*) (0UL),          /* 9  Reserved */
		.pfnPIOA_Handler   = (void*) PIOA_Handler,   /* 10 Parallel I/O Controller A */
		.pfnPIOB_Handler   = (void*) PIOB_Handler,   /* 11 Parallel I/O Controller B */
#ifdef _SAMV71_PIOC_INSTANCE_
		.pfnPIOC_Handler   = (void*) PIOC_Handler,   /* 12 Parallel I/O Controller C */
#else
		.pvReserved12      = (void*) (0UL),          /* 12 Reserved */
#endif /* _SAMV71_PIOC_INSTANCE_ */
		.pfnUSART0_Handler = (void*) USART0_Handler, /* 13 USART 0 */
		.pfnUSART1_Handler = (void*) USART1_Handler, /* 14 USART 1 */
		.pfnUSART2_Handler = (void*) USART2_Handler, /* 15 USART 2 */
		.pfnPIOD_Handler   = (void*) PIOD_Handler,   /* 16 Parallel I/O Controller D */
#ifdef _SAMV71_PIOE_INSTANCE_
		.pfnPIOE_Handler   = (void*) PIOE_Handler,   /* 17 Parallel I/O Controller E */
#else
		.pvReserved17      = (void*) (0UL),          /* 17 Reserved */
#endif /* _SAMV71_PIOE_INSTANCE_ */
#ifdef _SAMV71_HSMCI_INSTANCE_
		.pfnHSMCI_Handler  = (void*) HSMCI_Handler,  /* 18 Multimedia Card Interface */
#else
		.pvReserved18      = (void*) (0UL),          /* 18 Reserved */
#endif /* _SAMV71_HSMCI_INSTANCE_ */
		.pfnTWIHS0_Handler = (void*) TWIHS0_Handler, /* 19 Two Wire Interface 0 HS */
		.pfnTWIHS1_Handler = (void*) TWIHS1_Handler, /* 20 Two Wire Interface 1 HS */
		.pfnSPI0_Handler   = (void*) SPI0_Handler,   /* 21 Serial Peripheral Interface 0 */
		.pfnSSC_Handler    = (void*) SSC_Handler,    /* 22 Synchronous Serial Controller */
		.pfnTC0_Handler    = (void*) TC0_Handler,    /* 23 Timer/Counter 0 */
		.pfnTC1_Handler    = (void*) TC1_Handler,    /* 24 Timer/Counter 1 */
		.pfnTC2_Handler    = (void*) TC2_Handler,    /* 25 Timer/Counter 2 */
#ifdef _SAMV71_TC1_INSTANCE_
		.pfnTC3_Handler    = (void*) TC3_Handler,    /* 26 Timer/Counter 3 */
#else
		.pvReserved26      = (void*) (0UL),          /* 26 Reserved */
#endif /* _SAMV71_TC1_INSTANCE_ */
#ifdef _SAMV71_TC1_INSTANCE_
		.pfnTC4_Handler    = (void*) TC4_Handler,    /* 27 Timer/Counter 4 */
#else
		.pvReserved27      = (void*) (0UL),          /* 27 Reserved */
#endif /* _SAMV71_TC1_INSTANCE_ */
#ifdef _SAMV71_TC1_INSTANCE_
		.pfnTC5_Handler    = (void*) TC5_Handler,    /* 28 Timer/Counter 5 */
#else
		.pvReserved28      = (void*) (0UL),          /* 28 Reserved */
#endif /* _SAMV71_TC1_INSTANCE_ */
		.pfnAFEC0_Handler  = (void*) AFEC0_Handler,  /* 29 Analog Front End 0 */
#ifdef _SAMV71_DACC_INSTANCE_
		.pfnDACC_Handler   = (void*) DACC_Handler,   /* 30 Digital To Analog Converter */
#else
		.pvReserved30      = (void*) (0UL),          /* 30 Reserved */
#endif /* _SAMV71_DACC_INSTANCE_ */
		.pfnPWM0_Handler   = (void*) PWM0_Handler,   /* 31 Pulse Width Modulation 0 */
		.pfnICM_Handler    = (void*) ICM_Handler,    /* 32 Integrity Check Monitor */
		.pfnACC_Handler    = (void*) ACC_Handler,    /* 33 Analog Comparator */
		.pfnUSBHS_Handler  = (void*) USBHS_Handler,  /* 34 USB Host / Device Controller */
		.pfnMCAN0_Handler  = (void*) MCAN0_Handler,  /* 35 CAN Controller 0 */
		.pfnMCAN0_Line1_Handler = (void*) MCAN0_Line1_Handler, /* 36 CAN Controller 0 - Line 1  */
		.pfnMCAN1_Handler  = (void*) MCAN1_Handler,  /* 37 CAN Controller 1 */
		.pfnMCAN1_Line1_Handler = (void*) MCAN1_Line1_Handler, /* 38 CAN Controller 1 - Line 1  */
		.pfnGMAC_Handler   = (void*) GMAC_Handler,   /* 39 Ethernet MAC */
		.pfnAFEC1_Handler  = (void*) AFEC1_Handler,  /* 40 Analog Front End 1 */
#ifdef _SAMV71_TWIHS2_INSTANCE_
		.pfnTWIHS2_Handler = (void*) TWIHS2_Handler, /* 41 Two Wire Interface 2 HS */
#else
		.pvReserved41      = (void*) (0UL),          /* 41 Reserved */
#endif /* _SAMV71_TWI2_INSTANCE_ */
		.pfnSPI1_Handler   = (void*) SPI1_Handler,   /* 42 Serial Peripheral Interface 1 */
		.pfnQSPI_Handler   = (void*) QSPI_Handler,   /* 43 Quad I/O Serial Peripheral Interface */
		.pfnUART2_Handler  = (void*) UART2_Handler,  /* 44 UART 2 */
		.pfnUART3_Handler  = (void*) UART3_Handler,  /* 45 UART 3 */
		.pfnUART4_Handler  = (void*) UART4_Handler,  /* 46 UART 4 */
#ifdef _SAMV71_TC2_INSTANCE_
		.pfnTC6_Handler    = (void*) TC6_Handler,    /* 47 Timer/Counter 6 */
#else
		.pvReserved47      = (void*) (0UL),          /* 47 Reserved */
#endif /* _SAMV71_TC2_INSTANCE_ */
#ifdef _SAMV71_TC2_INSTANCE_
		.pfnTC7_Handler    = (void*) TC7_Handler,    /* 48 Timer/Counter 7 */
#else
		.pvReserved48      = (void*) (0UL),          /* 48 Reserved */
#endif /* _SAMV71_TC2_INSTANCE_ */
#ifdef _SAMV71_TC2_INSTANCE_
		.pfnTC8_Handler    = (void*) TC8_Handler,    /* 49 Timer/Counter 8 */
#else
		.pvReserved49      = (void*) (0UL),          /* 49 Reserved */
#endif /* _SAMV71_TC2_INSTANCE_ */
		.pfnTC9_Handler    = (void*) TC9_Handler,    /* 50 Timer/Counter 9 */
		.pfnTC10_Handler   = (void*) TC10_Handler,   /* 51 Timer/Counter 10 */
		.pfnTC11_Handler   = (void*) TC11_Handler,   /* 52 Timer/Counter 11 */
		.pfnMLB_Handler    = (void*) MLB_Handler,    /* 53 MediaLB */
		.pvReserved54      = (void*) (0UL),          /* 54 Reserved */
		.pvReserved55      = (void*) (0UL),          /* 55 Reserved */
		.pfnAES_Handler    = (void*) AES_Handler,    /* 56 AES */
		.pfnTRNG_Handler   = (void*) TRNG_Handler,   /* 57 True Random Generator */
		.pfnXDMAC_Handler  = (void*) XDMAC_Handler,  /* 58 DMA */
		.pfnISI_Handler    = (void*) ISI_Handler,    /* 59 Camera Interface */
		.pfnPWM1_Handler   = (void*) PWM1_Handler,   /* 60 Pulse Width Modulation 1 */
		.pvReserved61      = (void*) (0UL),          /* 61 Reserved */
#ifdef _SAMV71_SDRAMC_INSTANCE_
		.pfnSDRAMC_Handler = (void*) SDRAMC_Handler, /* 62 SDRAM Controller */
#else
		.pvReserved62      = (void*) (0UL),          /* 62 Reserved */
#endif /* _SAMV71_SDRAMC_INSTANCE_ */
		.pfnRSWDT_Handler   = (void*) RSWDT_Handler    /* 63 Watchdog Timer 1 */
};


#ifdef ENABLE_TCM 
/** \brief  TCM memory enable

	The function enables TCM memories
 */
__STATIC_INLINE void TCM_Enable(void) 
{

	__DSB();
	__ISB();
	SCB->ITCMCR = (SCB_ITCMCR_EN_Msk  | SCB_ITCMCR_RMW_Msk 
					| SCB_ITCMCR_RETEN_Msk);
	SCB->DTCMCR = ( SCB_DTCMCR_EN_Msk | SCB_DTCMCR_RMW_Msk 
					| SCB_DTCMCR_RETEN_Msk);
	__DSB();
	__ISB();
}
#endif

/** \brief  TCM memory Disable

	The function enables TCM memories
 */
__STATIC_INLINE void TCM_Disable(void) 
{

	__DSB();
	__ISB();
	SCB->ITCMCR &= ~(uint32_t)SCB_ITCMCR_EN_Msk;
	SCB->DTCMCR &= ~(uint32_t)SCB_ITCMCR_EN_Msk;
	__DSB();
	__ISB();
}

/**
 * \brief This is the code that gets called on processor reset.
 * To initialize the device, and call the main() routine.
 */
void Reset_Handler(void)
{
		uint32_t *pSrc, *pDest;

		/* Initialize the relocate segment */
		pSrc = &_etext;
		pDest = &_srelocate;

		if (pSrc != pDest) {
				for (; pDest < &_erelocate;) {
						*pDest++ = *pSrc++;
				}
		}

		/* Clear the zero segment */
		for (pDest = &_szero; pDest < &_ezero;) {
				*pDest++ = 0;
		}

		/* Set the vector table base address */
		pSrc = (uint32_t *) & _sfixed;
		SCB->VTOR = ((uint32_t) pSrc & SCB_VTOR_TBLOFF_Msk);

	#ifdef ENABLE_TCM 
	// 32 Kb
		EFC->EEFC_FCR = (EEFC_FCR_FKEY_PASSWD | EEFC_FCR_FCMD_CGPB 
						| EEFC_FCR_FARG(8));
		EFC->EEFC_FCR = (EEFC_FCR_FKEY_PASSWD | EEFC_FCR_FCMD_SGPB
						| EEFC_FCR_FARG(7));
 
		TCM_Enable();
	#else
		EFC->EEFC_FCR = (EEFC_FCR_FKEY_PASSWD | EEFC_FCR_FCMD_CGPB 
						| EEFC_FCR_FARG(8));
		EFC->EEFC_FCR = (EEFC_FCR_FKEY_PASSWD | EEFC_FCR_FCMD_CGPB 
						| EEFC_FCR_FARG(7));
	
		TCM_Disable();
	#endif

		LowLevelInit();
		/* Initialize the C library */
		__libc_init_array();

		/* Branch to main function */
		main();

		/* Infinite loop */
		while (1);
}

/**
 * \brief Default interrupt handler for unused IRQs.
 */
void Dummy_Handler(void)
{
		while (1) {
		}
}


