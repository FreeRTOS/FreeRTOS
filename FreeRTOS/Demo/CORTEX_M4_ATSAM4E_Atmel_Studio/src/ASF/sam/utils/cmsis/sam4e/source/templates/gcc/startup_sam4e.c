/**
 * \file
 *
 * \brief Startup file for SAM4E.
 *
 * Copyright (c) 2012 - 2013 Atmel Corporation. All rights reserved.
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
 */

#include "sam4e.h"
#include "exceptions.h"
#include "system_sam4e.h"
#if __FPU_USED /* CMSIS defined value to indicate usage of FPU */
#include "fpu.h"
#endif

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

/* Exception Table */
__attribute__ ((section(".vectors")))
const DeviceVectors exception_table = {

	/* Configure Initial Stack Pointer, using linker-generated symbols */
	(void*) (&_estack),

	(void*) Reset_Handler,
	(void*) NMI_Handler,
	(void*) HardFault_Handler,
	(void*) MemManage_Handler,
	(void*) BusFault_Handler,
	(void*) UsageFault_Handler,
	(void*) (0UL),          /* Reserved */
	(void*) (0UL),          /* Reserved */
	(void*) (0UL),          /* Reserved */
	(void*) (0UL),          /* Reserved */
	(void*) SVC_Handler,
	(void*) DebugMon_Handler,
	(void*) (0UL),          /* Reserved */
	(void*) PendSV_Handler,
	(void*) SysTick_Handler,

	/* Configurable interrupts */
	(void*) SUPC_Handler,   /* 0  Supply Controller */
	(void*) RSTC_Handler,   /* 1  Reset Controller */
	(void*) RTC_Handler,    /* 2  Real Time Clock */
	(void*) RTT_Handler,    /* 3  Real Time Timer */
	(void*) WDT_Handler,    /* 4  Watchdog/Dual Watchdog Timer */
	(void*) PMC_Handler,    /* 5  Power Management Controller */
	(void*) EFC_Handler,    /* 6  Enhanced Embedded Flash Controller */
	(void*) UART0_Handler,  /* 7  UART 0 */
	(void*) Dummy_Handler,
	(void*) PIOA_Handler,   /* 9  Parallel I/O Controller A */
	(void*) PIOB_Handler,   /* 10 Parallel I/O Controller B */
	(void*) PIOC_Handler,   /* 11 Parallel I/O Controller C */
#ifdef _SAM4E_PIOD_INSTANCE_
	(void*) PIOD_Handler,   /* 12 Parallel I/O Controller D */
#else
	(void*) Dummy_Handler,
#endif
#ifdef _SAM4E_PIOE_INSTANCE_
	(void*) PIOE_Handler,   /* 13 Parallel I/O Controller E */
#else
	(void*) Dummy_Handler,
#endif
	(void*) USART0_Handler, /* 14 USART 0 */
	(void*) USART1_Handler, /* 15 USART 1 */
	(void*) HSMCI_Handler,  /* 16 Multimedia Card Interface */
	(void*) TWI0_Handler,   /* 17 Two Wire Interface 0 */
	(void*) TWI1_Handler,   /* 18 Two Wire Interface 1 */
	(void*) SPI_Handler,    /* 19 Serial Peripheral Interface */
	(void*) DMAC_Handler,   /* 20 DMAC */
	(void*) TC0_Handler,    /* 21 Timer/Counter 0 */
	(void*) TC1_Handler,    /* 22 Timer/Counter 1 */
	(void*) TC2_Handler,    /* 23 Timer/Counter 2 */
	(void*) TC3_Handler,    /* 24 Timer/Counter 3 */
	(void*) TC4_Handler,    /* 25 Timer/Counter 4 */
	(void*) TC5_Handler,    /* 26 Timer/Counter 5 */
	(void*) TC6_Handler,    /* 27 Timer/Counter 6 */
	(void*) TC7_Handler,    /* 28 Timer/Counter 7 */
	(void*) TC8_Handler,    /* 29 Timer/Counter 8 */
	(void*) AFEC0_Handler,  /* 30 Analog Front End 0 */
	(void*) AFEC1_Handler,  /* 31 Analog Front End 1 */
	(void*) DACC_Handler,   /* 32 Digital To Analog Converter */
	(void*) ACC_Handler,    /* 33 Analog Comparator */
	(void*) ARM_Handler,    /* 34 FPU signals : FPIXC, FPOFC, FPUFC, FPIOC, FPDZC, FPIDC, FPIXC */
	(void*) UDP_Handler,    /* 35 USB DEVICE */
	(void*) PWM_Handler,    /* 36 PWM */
	(void*) CAN0_Handler,   /* 37 CAN0 */
	(void*) CAN1_Handler,   /* 38 CAN1 */
	(void*) AES_Handler,    /* 39 AES */
	(void*) Dummy_Handler,
	(void*) Dummy_Handler,
	(void*) Dummy_Handler,
	(void*) Dummy_Handler,
#ifdef _SAM4E_GMAC_INSTANCE_
	(void*) GMAC_Handler,   /* 44 EMAC */
#else
	(void*) Dummy_Handler,
#endif
	(void*) UART1_Handler   /* 45 UART */
};

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

#if __FPU_USED
	fpu_enable();
#endif

	/* Initialize the C library */
	__libc_init_array();

	/* Branch to main function */
	main();

	/* Infinite loop */
	while (1);
}
