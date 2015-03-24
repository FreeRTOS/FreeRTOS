/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2014, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#include "sam.h"

typedef void (*intfunc) (void);
typedef union { intfunc __fun; void * __ptr; } intvec_elem;

extern int Image$$ARM_LIB_STACK$$ZI$$Limit ;
extern int Image$$Vector_region$$Base ;
extern int Image$$Vector_region$$Limit ;

extern void __main( void ) ;
static void Reset_Handler( void ) ;

int __low_level_init(void);

/* Default empty handler */
void Dummy_Handler(void);
void NMI_Handler(void);

/* Cortex-M7 core handlers */
//#pragma weak NMI_Handler=Dummy_Handler
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
#pragma weak WDT0_Handler=Dummy_Handler
#pragma weak PMC_Handler=Dummy_Handler
#pragma weak EFC_Handler=Dummy_Handler
#pragma weak UART0_Handler=Dummy_Handler
#pragma weak UART1_Handler=Dummy_Handler
#pragma weak PIOA_Handler=Dummy_Handler
#pragma weak PIOB_Handler=Dummy_Handler
#ifdef _SAM_PIOC_INSTANCE_
#pragma weak PIOC_Handler=Dummy_Handler
#endif /* _SAM_PIOC_INSTANCE_ */
#pragma weak USART0_Handler=Dummy_Handler
#pragma weak USART1_Handler=Dummy_Handler
#pragma weak USART2_Handler=Dummy_Handler
#pragma weak PIOD_Handler=Dummy_Handler
#ifdef _SAM_PIOE_INSTANCE_
#pragma weak PIOE_Handler=Dummy_Handler
#endif /* _SAM_PIOE_INSTANCE_ */
#ifdef _SAM_HSMCI_INSTANCE_
#pragma weak HSMCI_Handler=Dummy_Handler
#endif /* _SAM_HSMCI_INSTANCE_ */
#pragma weak TWI0_Handler=Dummy_Handler
#pragma weak TWI1_Handler=Dummy_Handler
#pragma weak SPI0_Handler=Dummy_Handler
#pragma weak SSC_Handler=Dummy_Handler
#pragma weak TC0_Handler=Dummy_Handler
#pragma weak TC1_Handler=Dummy_Handler
#pragma weak TC2_Handler=Dummy_Handler
#ifdef _SAM_TC1_INSTANCE_
#pragma weak TC3_Handler=Dummy_Handler
#endif /* _SAM_TC1_INSTANCE_ */
#ifdef _SAM_TC1_INSTANCE_
#pragma weak TC4_Handler=Dummy_Handler
#endif /* _SAM_TC1_INSTANCE_ */
#ifdef _SAM_TC1_INSTANCE_
#pragma weak TC5_Handler=Dummy_Handler
#endif /* _SAM_TC1_INSTANCE_ */
#pragma weak AFEC0_Handler=Dummy_Handler
#ifdef _SAM_DACC_INSTANCE_
#pragma weak DACC_Handler=Dummy_Handler
#endif /* _SAM_DACC_INSTANCE_ */
#pragma weak PWM0_Handler=Dummy_Handler
#pragma weak ICM_Handler=Dummy_Handler
#pragma weak ACC_Handler=Dummy_Handler
#pragma weak USBHS_Handler=Dummy_Handler
#pragma weak CAN0_Handler=Dummy_Handler
#pragma weak CAN1_Handler=Dummy_Handler
#pragma weak GMAC_Handler=Dummy_Handler
#pragma weak GMACQ1_Handler=Dummy_Handler
#pragma weak GMACQ2_Handler=Dummy_Handler
#pragma weak AFEC1_Handler=Dummy_Handler
#ifdef _SAM_TWI2_INSTANCE_
#pragma weak TWI2_Handler=Dummy_Handler
#endif /* _SAM_TWI2_INSTANCE_ */
#pragma weak SPI1_Handler=Dummy_Handler
#pragma weak QSPI_Handler=Dummy_Handler
#pragma weak UART2_Handler=Dummy_Handler
#pragma weak UART3_Handler=Dummy_Handler
#pragma weak UART4_Handler=Dummy_Handler
#ifdef _SAM_TC2_INSTANCE_
#pragma weak TC6_Handler=Dummy_Handler
#endif /* _SAM_TC2_INSTANCE_ */
#ifdef _SAM_TC2_INSTANCE_
#pragma weak TC7_Handler=Dummy_Handler
#endif /* _SAM_TC2_INSTANCE_ */
#ifdef _SAM_TC2_INSTANCE_
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
#ifdef _SAM_SDRAMC_INSTANCE_
#pragma weak SDRAMC_Handler=Dummy_Handler
#endif /* _SAM_SDRAMC_INSTANCE_ */
#pragma weak WDT1_Handler=Dummy_Handler
#pragma weak CCF_Handler=Dummy_Handler
#pragma weak CCW_Handler=Dummy_Handler


/* The name "__vector_table" has special meaning for C-SPY: */
/* it is where the SP start value is found, and the NVIC vector */
/* table register (VTOR) is initialized to this address if != 0 */
#pragma arm section rodata = "vectors"
const intvec_elem __vector_table[] =
{
    (intfunc)&Image$$ARM_LIB_STACK$$ZI$$Limit,
    Reset_Handler,
    NMI_Handler,
	  HardFault_Handler,
    MemManage_Handler,
	  BusFault_Handler,
    UsageFault_Handler,
    (0UL), (0UL), (0UL), (0UL),          /* Reserved */
    SVC_Handler,
    DebugMon_Handler,
    (0UL),          /* Reserved */
    PendSV_Handler,
    SysTick_Handler,

    SUPC_Handler,   /* 0  Supply Controller */
    RSTC_Handler,   /* 1  Reset Controller */
    RTC_Handler,    /* 2  Real Time Clock */
    RTT_Handler,    /* 3  Real Time Timer */
    WDT0_Handler,   /* 4  Watchdog Timer 0 */
    PMC_Handler,    /* 5  Power Management Controller */
    EFC_Handler,    /* 6  Enhanced Embedded Flash Controller */
    UART0_Handler,  /* 7  UART 0 */
    UART1_Handler,  /* 8  UART 1 */
    (0UL),          /* 9  Reserved */
    PIOA_Handler,   /* 10 Parallel I/O Controller A */
    PIOB_Handler,   /* 11 Parallel I/O Controller B */
    PIOC_Handler,   /* 12 Parallel I/O Controller C */
    USART0_Handler, /* 13 USART 0 */
    USART1_Handler, /* 14 USART 1 */
    USART2_Handler, /* 15 USART 2 */
    PIOD_Handler,   /* 16 Parallel I/O Controller D */
    PIOE_Handler,   /* 17 Parallel I/O Controller E */    
    HSMCI_Handler,  /* 18 Multimedia Card Interface */
    TWI0_Handler,   /* 19 Two Wire Interface 0 HS */
    TWI1_Handler,   /* 20 Two Wire Interface 1 HS */
    SPI0_Handler,   /* 21 Serial Peripheral Interface 0 */
    SSC_Handler,    /* 22 Synchronous Serial Controller */
    TC0_Handler,    /* 23 Timer/Counter 0 */
    TC1_Handler,    /* 24 Timer/Counter 1 */
    TC2_Handler,    /* 25 Timer/Counter 2 */
    TC3_Handler,    /* 26 Timer/Counter 3 */
    TC4_Handler,    /* 27 Timer/Counter 4 */
    TC5_Handler,    /* 28 Timer/Counter 5 */
    AFEC0_Handler,  /* 29 Analog Front End 0 */
    DACC_Handler,   /* 30 Digital To Analog Converter */
    PWM0_Handler,   /* 31 Pulse Width Modulation 0 */
    ICM_Handler,    /* 32 Integrity Check Monitor */
    ACC_Handler,    /* 33 Analog Comparator */
    USBHS_Handler,  /* 34 USB Host / Device Controller */
    CAN0_Handler,   /* 35 CAN Controller 0 */
    (0UL),          /* 36 Reserved */
    CAN1_Handler,   /* 37 CAN Controller 1 */
    (0UL),          /* 38 Reserved */
    GMAC_Handler,   /* 39 Ethernet MAC */
    AFEC1_Handler,  /* 40 Analog Front End 1 */
    TWI2_Handler,   /* 41 Two Wire Interface 2 HS */
    SPI1_Handler,   /* 42 Serial Peripheral Interface 1 */
    QSPI_Handler,   /* 43 Quad I/O Serial Peripheral Interface */
    UART2_Handler,  /* 44 UART 2 */
    UART3_Handler,  /* 45 UART 3 */
    UART4_Handler,  /* 46 UART 4 */
    TC6_Handler,    /* 47 Timer/Counter 6 */
    TC7_Handler,    /* 48 Timer/Counter 7 */
    TC8_Handler,    /* 49 Timer/Counter 8 */
    TC9_Handler,    /* 50 Timer/Counter 9 */
    TC10_Handler,   /* 51 Timer/Counter 10 */
    TC11_Handler,   /* 52 Timer/Counter 11 */
    MLB_Handler,    /* 53 MediaLB */
    (0UL),          /* 54 Reserved */
    (0UL),          /* 55 Reserved */
    AES_Handler,    /* 56 AES */
    TRNG_Handler,   /* 57 True Random Generator */
    XDMAC_Handler,  /* 58 DMA */
    ISI_Handler,    /* 59 Camera Interface */
    PWM1_Handler,   /* 60 Pulse Width Modulation 1 */
    FPU_Handler,    /* 61 Floating Point Unit */
    SDRAMC_Handler, /* 62 SDRAM Controller */
    WDT1_Handler,   /* 63 Watchdog Timer 1 */
    CCW_Handler,    /* 64 ARM Cache ECC Warning */
    CCF_Handler,    /* 65 ARM Cache ECC Fault */
    GMACQ1_Handler, /* 66 GMAC Queue 1 Handler */
    GMACQ2_Handler  /* 67 GMAC Queue 2 Handler */
};
#pragma arm section


void LowLevelInit(void);
/**------------------------------------------------------------------------------
 * This is the code that gets called on processor reset. To initialize the
 * device.
 *------------------------------------------------------------------------------*/
int __low_level_init(void)
{
//        uint32_t *pSrc = __section_begin(".intvec");
        LowLevelInit();
//        SCB->VTOR = ((uint32_t) pSrc & SCB_VTOR_TBLOFF_Msk);
        
        SCB_EnableICache();        
        SCB_EnableDCache();
        
        
        
        return 1; /* if return 0, the data sections will not be initialized */
}

/** \brief  TCM memory enable

    The function enables TCM memories
 */

/* Correct errors in early version core_cm7.h */
#undef SCB_ITCMCR_RETEN_Msk
#undef SCB_ITCMCR_RMW_Msk
#undef SCB_ITCMCR_EN_Msk
#define SCB_ITCMCR_RETEN_Msk               (0x1FFUL << SCB_ITCMCR_RETEN_Pos)                /*!< SCB ITCMCR: RETEN Mask */
#define SCB_ITCMCR_RMW_Msk                 (0x1FFUL << SCB_ITCMCR_RMW_Pos)                  /*!< SCB ITCMCR: RMW Mask */
#define SCB_ITCMCR_EN_Msk                  (0x1FFUL << SCB_ITCMCR_EN_Pos)                   /*!< SCB ITCMCR: EN Mask */


__STATIC_INLINE void TCM_Enable(void) 
{

  __DSB();
  __ISB();
  SCB->ITCMCR = ( SCB_ITCMCR_EN_Msk | SCB_ITCMCR_RMW_Msk | SCB_ITCMCR_RETEN_Msk);
  SCB->DTCMCR = ( SCB_DTCMCR_EN_Msk | SCB_DTCMCR_RMW_Msk | SCB_DTCMCR_RETEN_Msk);
  __DSB();
  __ISB();
}

/**------------------------------------------------------------------------------
 * This is the code that gets called on processor reset. To initialize the
 * device.
 *------------------------------------------------------------------------------*/
void Reset_Handler(void)
{
    uint32_t *pSrc = (uint32_t*)&Image$$Vector_region$$Base ;

    /* Low level Initialize */
    LowLevelInit() ;
		SCB->VTOR = ((uint32_t) pSrc & SCB_VTOR_TBLOFF_Msk);

    SCB_EnableICache();        
    SCB_EnableDCache(); 

    /* Branch to main function */
    __main() ;

	/* Will not execute, but removes warning about TCM_Enable() not being called. */
	( void ) TCM_Enable;

    /* Infinite loop */
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for unused IRQs.
 */
void Dummy_Handler(void)
{
        while (1) {
        }
}

void NMI_Handler(void)
{
        while (1) {
        }
}
