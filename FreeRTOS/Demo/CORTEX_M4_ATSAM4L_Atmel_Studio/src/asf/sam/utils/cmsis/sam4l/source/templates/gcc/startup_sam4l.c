/**
 * \file
 *
 * \brief GCC Startup file for SAM4L.
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
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

#include "exceptions.h"
#include "sam4l.h"
#include "system_sam4l.h"

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
IntFunc exception_table[] = {

	/* Configure Initial Stack Pointer, using linker-generated symbols */
	(IntFunc) (&_estack),
	Reset_Handler,

	NMI_Handler,
	HardFault_Handler,
	MemManage_Handler,
	BusFault_Handler,
	UsageFault_Handler,
	0, 0, 0, 0,        /* Reserved */
	SVC_Handler,
	DebugMon_Handler,
	0,                 /* Reserved  */
	PendSV_Handler,
	SysTick_Handler,

	// Configurable interrupts
	HFLASHC_Handler,      // 0
	PDCA_0_Handler,       // 1
	PDCA_1_Handler,       // 2
	PDCA_2_Handler,       // 3
	PDCA_3_Handler,       // 4
	PDCA_4_Handler,       // 5
	PDCA_5_Handler,       // 6
	PDCA_6_Handler,       // 7
	PDCA_7_Handler,       // 8
	PDCA_8_Handler,       // 9
	PDCA_9_Handler,       // 10
	PDCA_10_Handler,      // 11
	PDCA_11_Handler,      // 12
	PDCA_12_Handler,      // 13
	PDCA_13_Handler,      // 14
	PDCA_14_Handler,      // 15
	PDCA_15_Handler,      // 16
	CRCCU_Handler,        // 17
	USBC_Handler,         // 18
	PEVC_TR_Handler,      // 19
	PEVC_OV_Handler,      // 20
	AESA_Handler,         // 21
	PM_Handler,           // 22
	SCIF_Handler,         // 23
	FREQM_Handler,        // 24
	GPIO_0_Handler,       // 25
	GPIO_1_Handler,       // 26
	GPIO_2_Handler,       // 27
	GPIO_3_Handler,       // 28
	GPIO_4_Handler,       // 29
	GPIO_5_Handler,       // 30
	GPIO_6_Handler,       // 31
	GPIO_7_Handler,       // 32
	GPIO_8_Handler,       // 33
	GPIO_9_Handler,       // 34
	GPIO_10_Handler,      // 35
	GPIO_11_Handler,      // 36
	BPM_Handler,          // 37
	BSCIF_Handler,        // 38
	AST_ALARM_Handler,    // 39
	AST_PER_Handler,      // 40
	AST_OVF_Handler,      // 41
	AST_READY_Handler,    // 42
	AST_CLKREADY_Handler, // 43
	WDT_Handler,          // 44
	EIC_1_Handler,        // 45
	EIC_2_Handler,        // 46
	EIC_3_Handler,        // 47
	EIC_4_Handler,        // 48
	EIC_5_Handler,        // 49
	EIC_6_Handler,        // 50
	EIC_7_Handler,        // 51
	EIC_8_Handler,        // 52
	IISC_Handler,         // 53
	SPI_Handler,          // 54
	TC00_Handler,         // 55
	TC01_Handler,         // 56
	TC02_Handler,         // 57
	TC10_Handler,         // 58
	TC11_Handler,         // 59
	TC12_Handler,         // 60
	TWIM0_Handler,        // 61
	TWIS0_Handler,        // 62
	TWIM1_Handler,        // 63
	TWIS1_Handler,        // 64
	USART0_Handler,       // 65
	USART1_Handler,       // 66
	USART2_Handler,       // 67
	USART3_Handler,       // 68
	ADCIFE_Handler,       // 69
	DACC_Handler,         // 70
	ACIFC_Handler,        // 71
	ABDACB_Handler,       // 72
	TRNG_Handler,         // 73
	PARC_Handler,         // 74
	CATB_Handler,         // 75
	Dummy_Handler,        // one not used
	TWIM2_Handler,        // 77
	TWIM3_Handler,        // 78
	LCDCA_Handler         // 79

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
	pSrc = (uint32_t *) &_sfixed;
	SCB->VTOR = ((uint32_t) pSrc & SCB_VTOR_TBLOFF_Msk);

	/* Initialize the C library */
	__libc_init_array();

	/* Branch to main function */
	main();

	/* Infinite loop */
	while (1);
}
