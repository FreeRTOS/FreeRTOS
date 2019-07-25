/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 * Provides the low-level initialization function that called on chip startup.
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"


/*----------------------------------------------------------------------------
 *        Definiation
 *----------------------------------------------------------------------------*/
#define CPSR_MASK_IRQ 0x00000080
#define CPSR_MASK_FIQ 0x00000040

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/



/** Array of Max peripheral Frequence support for SAMA5 chip*/
const PeripheralClockMaxFreq periClkMaxFreq[] = {
    /* peripheral ID, Max frequency */
       {ID_DBGU    , (BOARD_MCK >>1) },
       {ID_PIT     , (BOARD_MCK >>1) },
       {ID_WDT     , (BOARD_MCK >>1) },
       {ID_HSMC    , (BOARD_MCK >>1) },
       {ID_PIOA    , (BOARD_MCK >>1) },
       {ID_PIOB    , (BOARD_MCK >>1) },
       {ID_PIOC    , (BOARD_MCK >>1) },
       {ID_PIOD    , (BOARD_MCK >>1) },
       {ID_PIOE    , (BOARD_MCK >>1) },
       {ID_USART0  , (BOARD_MCK >>1) },
       {ID_USART1  , (BOARD_MCK >>1) },
       {ID_USART2  , (BOARD_MCK >>1) },
       {ID_USART3  , (BOARD_MCK >>1) },
       {ID_UART0   , (BOARD_MCK >>1) },
       {ID_UART1   , (BOARD_MCK >>1) },
       {ID_TWI0    , (BOARD_MCK >>1) },
       {ID_TWI1    , (BOARD_MCK >>1) },
       {ID_TWI2    , (BOARD_MCK >>1) },
       {ID_HSMCI0  , (BOARD_MCK >>1) },
       {ID_HSMCI1  , (BOARD_MCK >>1) },
       {ID_SPI0    , (BOARD_MCK >>1) },
       {ID_SPI1    , (BOARD_MCK >>1) },
       {ID_TC0     , (BOARD_MCK >>1) },
       {ID_TC1     , (BOARD_MCK >>1) },
       {ID_PWM     , (BOARD_MCK >>1) },
       {ID_ADC     , (BOARD_MCK >>1) },
       {ID_XDMAC0  , BOARD_MCK },
       {ID_XDMAC1  , BOARD_MCK },
       {ID_UHPHS   , (BOARD_MCK >>1) },
       {ID_UDPHS   , (BOARD_MCK >>1) },
       {ID_GMAC0   , (BOARD_MCK >>1) },
       {ID_GMAC1   , (BOARD_MCK >>1) },
       {ID_LCDC    , BOARD_MCK },
       {ID_ISI     , BOARD_MCK },
       {ID_SSC0    , (BOARD_MCK >>1) },
       {ID_SSC1    , (BOARD_MCK >>1) },
       {ID_SHA     , (BOARD_MCK >>1) },
       {ID_AES     , (BOARD_MCK >>1) },
       {ID_TDES    , (BOARD_MCK >>1) },
       {ID_TDES    , (BOARD_MCK >>1) },
       {ID_TRNG    , (BOARD_MCK >>1) },
       {ID_ICM     , (BOARD_MCK >>1) },
       {ID_ARM     , (BOARD_MCK >>1) },
       {ID_IRQ     , (BOARD_MCK >>1) },
       {ID_SFC     , (BOARD_MCK >>1) },
       {ID_MPDDRC  , BOARD_MCK }
};

static const char* abort_status[][2]=
{
  // IFSR status        ,       DFSR status
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//0
  {"Unknown(reserved status)",                          "Alignment Fault"                               },//1
  {"Debug Event",                                       "Debug Event"                                   },//2
  {"Access flag - section",                             "Access flag - section"                         },//3
  {"Unknown(reserved status)",                          "Instruction cache maintenance"                 },//4
  {"Translation fault - section",                       "Translation fault - section"                   },//5
  {"Access flag - Page",                                "Access flag - Page"                            },//6
  {"Translation fault -Page",                           "Translation fault -Page"                       },//7
  {"Synchronous external abort",                        "Synchronous external abort, nontranslation"    },//8
  {"Domain fault - Section",                            "Domain fault - Section"                        },//9
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//10
  {"Domain fault - Page",                               "Domain fault - Page"                           },//11
  {"Synchronous external abort - L1 Translation",       "Synchronous external abort - L1 Translation"   },//12
  {"Permission fault - Section",                        "Permission fault - Section"                    },//13
  {"Synchronous external abort - L2 Translation",       "Synchronous external abort - L2 Translation"   },//14
  {"Permission fault - Page",                           "Permission fault - Page"                       },//15
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//16
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//17
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//18
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//19
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//20
  {"Unknown(reserved status)",                          "Unknown(reserved status)"                      },//21
  {"Unknown(reserved status)",                          "Asynchronous external abort"}

};

/*----------------------------------------------------------------------------
 *        Internal functions
 *----------------------------------------------------------------------------*/


void v_ARM_ClrCPSR_bits(unsigned int mask);
void NonSecureITInit (void);
void SecureITInit (void);
void Prefetch_C_Handler( void);
void Abort_C_Handler( void);
void Undefined_C_Handler(void);

/**
 * \brief Default spurious interrupt handler. Infinite loop.
 */
void defaultSpuriousHandler( void )
{
    while (1);
}

void Abort_C_Handler( void)
{
    uint32_t v1,v2, dfsr;
    v1= 0;
    v2= 0;
    asm("mrc   p15, 0, %0, c5, c0, 0" : : "r"(v1));
    asm("mrc   p15, 0, %0, c6, c0, 0" : : "r"(v2));

    dfsr = ((v1 >> 4) & 0x0F);
    printf("\n\r######################################################################\n\r");
    printf("Data Abort occured in %x domain\n\r", (unsigned int)dfsr);
    dfsr = (((v1 & 0x400) >> 6) | (v1 & 0x0F));
    printf("Data abort fault reason is: %s\n\r", (char*)abort_status[dfsr][1]);
    printf("Data fault occured at Address = 0x%08x\n\n\r",(unsigned int)v2);


    printf("-[Info]-Data fault status register value = 0x%x\n\r",(unsigned int)v1);

    while(1);

}


void Prefetch_C_Handler( void)
{
    uint32_t v1,v2, ifsr;
    v1= 0;
    v2= 0;

    asm("mrc   p15, 0, %0, c5, c0, 1" : : "r"(v1));
    asm("mrc   p15, 0, %0, c6, c0, 2" : : "r"(v2));

    ifsr = (((v1 & 0x400) >> 6) | (v1 & 0x0F));
    printf("\n\r######################################################################\n\r");
    printf("Instruction prefetch abort reason is: %s\n\r", (char*)abort_status[ifsr][0]);
    printf("Instruction prefetch Fault occured at Address = 0x%08x\n\n\r",(unsigned int)v2);

    printf("-[INFO]- Prefetch Fault status register value by = 0x%x\n\r",(unsigned int)v1);

    while(1);

}

void Undefined_C_Handler( void)
{
  printf("Undefined abort \n\r");
  while(1);
}

void v_ARM_ClrCPSR_bits(unsigned int mask)
{
  asm("MRS R1, CPSR");   // Get current CPSR
  asm("MVN R0, R0");     // invert
  asm("AND R0, R0, R1"); // Calculate new CPSR value
  asm("MSR CPSR_c,R0");  // Set new value
  asm("bx lr");
  ( void ) mask;
}

void Dummy_Handler( void );
void Spurious_Handler( void );
#pragma weak SAIC0_Handler=Dummy_Handler
#pragma weak SYS_IrqHandler=Dummy_Handler
#pragma weak ARM_IrqHandler=Dummy_Handler
#pragma weak PIT_IrqHandler=Dummy_Handler
#pragma weak WDT_IrqHandler=Dummy_Handler
#pragma weak PIOD_IrqHandler=Dummy_Handler
#pragma weak USART0_IrqHandler=Dummy_Handler
#pragma weak USART1_IrqHandler=Dummy_Handler
#pragma weak XDMAC0_IrqHandler=Dummy_Handler
#pragma weak ICM_IrqHandler=Dummy_Handler
#pragma weak PKCC_IrqHandler=Dummy_Handler
#pragma weak SCI_IrqHandler=Dummy_Handler
#pragma weak AES_IrqHandler=Dummy_Handler
#pragma weak AESB_IrqHandler=Dummy_Handler
#pragma weak TDES_IrqHandler=Dummy_Handler
#pragma weak SHA_IrqHandler=Dummy_Handler
#pragma weak MPDDRC_IrqHandler=Dummy_Handler
#pragma weak H32MX_IrqHandler=Dummy_Handler
#pragma weak H64MX_IrqHandler=Dummy_Handler
#pragma weak VDEC_IrqHandler=Dummy_Handler
#pragma weak SECUMOD_IrqHandler=Dummy_Handler
#pragma weak MSADCC_IrqHandler=Dummy_Handler
#pragma weak HSMC_IrqHandler=Dummy_Handler
#pragma weak PIOA_IrqHandler=Dummy_Handler
#pragma weak PIOB_IrqHandler=Dummy_Handler
#pragma weak PIOC_IrqHandler=Dummy_Handler
#pragma weak PIOE_IrqHandler=Dummy_Handler
#pragma weak UART0_IrqHandler=Dummy_Handler
#pragma weak UART1_IrqHandler=Dummy_Handler
#pragma weak USART2_IrqHandler=Dummy_Handler
#pragma weak USART3_IrqHandler=Dummy_Handler
#pragma weak USART4_IrqHandler=Dummy_Handler
#pragma weak TWI0_IrqHandler=Dummy_Handler
#pragma weak TWI1_IrqHandler=Dummy_Handler
#pragma weak TWI2_IrqHandler=Dummy_Handler
#pragma weak HSMCI0_IrqHandler=Dummy_Handler
#pragma weak HSMCI1_IrqHandler=Dummy_Handler
#pragma weak SPI0_IrqHandler=Dummy_Handler
#pragma weak SPI1_IrqHandler=Dummy_Handler
#pragma weak SPI2_IrqHandler=Dummy_Handler
#pragma weak TC0_IrqHandler=Dummy_Handler
#pragma weak TC1_IrqHandler=Dummy_Handler
#pragma weak TC2_IrqHandler=Dummy_Handler
#pragma weak PWM_IrqHandler=Dummy_Handler
#pragma weak ADC_IrqHandler=Dummy_Handler
#pragma weak DBGU_IrqHandler=Dummy_Handler
#pragma weak UHPHS_IrqHandler=Dummy_Handler
#pragma weak UDPHS_IrqHandler=Dummy_Handler
#pragma weak SSC0_IrqHandler=Dummy_Handler
#pragma weak SSC1_IrqHandler=Dummy_Handler
#pragma weak XDMAC1_IrqHandler=Dummy_Handler
#pragma weak LCDC_IrqHandler=Dummy_Handler
#pragma weak ISI_IrqHandler=Dummy_Handler
#pragma weak TRNG_IrqHandler=Dummy_Handler
#pragma weak GMAC0_IrqHandler=Dummy_Handler
#pragma weak GMAC1_IrqHandler=Dummy_Handler
#pragma weak AIC0_IrqHandler=Dummy_Handler
#pragma weak SFC_IrqHandler=Dummy_Handler
#pragma weak SECURAM_IrqHandler=Dummy_Handler
#pragma weak CTB_IrqHandler=Dummy_Handler
#pragma weak SMD_IrqHandler=Dummy_Handler
#pragma weak TWI3_IrqHandler=Dummy_Handler
#pragma weak CATB_IrqHandler=Dummy_Handler
#pragma weak SFR_IrqHandler=Dummy_Handler
#pragma weak AIC1_IrqHandler=Dummy_Handler
#pragma weak SAIC1_IrqHandler=Dummy_Handler
#pragma weak L2CC_IrqHandler=Dummy_Handler
#pragma weak Spurious_handler=Spurious_Handler


/**
 * \brief Dummy default handler.
 */
void Dummy_Handler( void )
{
    while ( 1 ) ;
}

volatile uint32_t ulSpuriousCount = 0;
void Spurious_Handler( void )
{
	ulSpuriousCount++;
}

/**
 * \brief Non-secure Interupt Init.
 */
void NonSecureITInit (void)
{
    uint32_t i;
    /* Assign handler addesses */
    AIC->AIC_SSR = 0;  AIC->AIC_SVR = (unsigned int) SAIC0_Handler;
    AIC->AIC_SSR = 1;  AIC->AIC_SVR = (unsigned int) SYS_IrqHandler;
    AIC->AIC_SSR = 2;  AIC->AIC_SVR = (unsigned int) ARM_IrqHandler;
    AIC->AIC_SSR = 3;  AIC->AIC_SVR = (unsigned int) PIT_IrqHandler;
    AIC->AIC_SSR = 4;  AIC->AIC_SVR = (unsigned int) WDT_IrqHandler;
    AIC->AIC_SSR = 5;  AIC->AIC_SVR = (unsigned int) PIOD_IrqHandler;
    AIC->AIC_SSR = 6;  AIC->AIC_SVR = (unsigned int) USART0_IrqHandler;
    AIC->AIC_SSR = 7;  AIC->AIC_SVR = (unsigned int) USART1_IrqHandler;
    AIC->AIC_SSR = 8;  AIC->AIC_SVR = (unsigned int) XDMAC0_IrqHandler;
    AIC->AIC_SSR = 9;  AIC->AIC_SVR = (unsigned int) ICM_IrqHandler;
    AIC->AIC_SSR = 10; AIC->AIC_SVR = (unsigned int) PKCC_IrqHandler;
    AIC->AIC_SSR = 11; AIC->AIC_SVR = (unsigned int) SCI_IrqHandler;
    AIC->AIC_SSR = 12; AIC->AIC_SVR = (unsigned int) AES_IrqHandler;
    AIC->AIC_SSR = 13; AIC->AIC_SVR = (unsigned int) AESB_IrqHandler;
    AIC->AIC_SSR = 14; AIC->AIC_SVR = (unsigned int) TDES_IrqHandler;
    AIC->AIC_SSR = 15; AIC->AIC_SVR = (unsigned int) SHA_IrqHandler;
    AIC->AIC_SSR = 16; AIC->AIC_SVR = (unsigned int) MPDDRC_IrqHandler;
    AIC->AIC_SSR = 17; AIC->AIC_SVR = (unsigned int) H32MX_IrqHandler;
    AIC->AIC_SSR = 18; AIC->AIC_SVR = (unsigned int) H64MX_IrqHandler;
    AIC->AIC_SSR = 19; AIC->AIC_SVR = (unsigned int) VDEC_IrqHandler;
    AIC->AIC_SSR = 20; AIC->AIC_SVR = (unsigned int) SECUMOD_IrqHandler;
    AIC->AIC_SSR = 21; AIC->AIC_SVR = (unsigned int) MSADCC_IrqHandler;
    AIC->AIC_SSR = 22; AIC->AIC_SVR = (unsigned int) HSMC_IrqHandler;
    AIC->AIC_SSR = 23; AIC->AIC_SVR = (unsigned int) PIOA_IrqHandler;
    AIC->AIC_SSR = 24; AIC->AIC_SVR = (unsigned int) PIOB_IrqHandler;
    AIC->AIC_SSR = 25; AIC->AIC_SVR = (unsigned int) PIOC_IrqHandler;
    AIC->AIC_SSR = 26; AIC->AIC_SVR = (unsigned int) PIOE_IrqHandler;
    AIC->AIC_SSR = 27; AIC->AIC_SVR = (unsigned int) UART0_IrqHandler;
    AIC->AIC_SSR = 28; AIC->AIC_SVR = (unsigned int) UART1_IrqHandler;
    AIC->AIC_SSR = 29; AIC->AIC_SVR = (unsigned int) USART2_IrqHandler;
    AIC->AIC_SSR = 30; AIC->AIC_SVR = (unsigned int) USART3_IrqHandler;
    AIC->AIC_SSR = 31; AIC->AIC_SVR = (unsigned int) USART4_IrqHandler;
    AIC->AIC_SSR = 32; AIC->AIC_SVR = (unsigned int) TWI0_IrqHandler;
    AIC->AIC_SSR = 33; AIC->AIC_SVR = (unsigned int) TWI1_IrqHandler;
    AIC->AIC_SSR = 34; AIC->AIC_SVR = (unsigned int) TWI2_IrqHandler;
    AIC->AIC_SSR = 35; AIC->AIC_SVR = (unsigned int) HSMCI0_IrqHandler;
    AIC->AIC_SSR = 36; AIC->AIC_SVR = (unsigned int) HSMCI1_IrqHandler;
    AIC->AIC_SSR = 37; AIC->AIC_SVR = (unsigned int) SPI0_IrqHandler;
    AIC->AIC_SSR = 38; AIC->AIC_SVR = (unsigned int) SPI1_IrqHandler;
    AIC->AIC_SSR = 39; AIC->AIC_SVR = (unsigned int) SPI2_IrqHandler;
    AIC->AIC_SSR = 40; AIC->AIC_SVR = (unsigned int) TC0_IrqHandler;
    AIC->AIC_SSR = 41; AIC->AIC_SVR = (unsigned int) TC1_IrqHandler;
    AIC->AIC_SSR = 42; AIC->AIC_SVR = (unsigned int) TC2_IrqHandler;
    AIC->AIC_SSR = 43; AIC->AIC_SVR = (unsigned int) PWM_IrqHandler;
    AIC->AIC_SSR = 44; AIC->AIC_SVR = (unsigned int) ADC_IrqHandler;
    AIC->AIC_SSR = 45; AIC->AIC_SVR = (unsigned int) DBGU_IrqHandler;
    AIC->AIC_SSR = 46; AIC->AIC_SVR = (unsigned int) UHPHS_IrqHandler;
    AIC->AIC_SSR = 47; AIC->AIC_SVR = (unsigned int) UDPHS_IrqHandler;
    AIC->AIC_SSR = 48; AIC->AIC_SVR = (unsigned int) SSC0_IrqHandler;
    AIC->AIC_SSR = 49; AIC->AIC_SVR = (unsigned int) SSC1_IrqHandler;
    AIC->AIC_SSR = 50; AIC->AIC_SVR = (unsigned int) XDMAC1_IrqHandler;
    AIC->AIC_SSR = 51; AIC->AIC_SVR = (unsigned int) LCDC_IrqHandler;
    AIC->AIC_SSR = 52; AIC->AIC_SVR = (unsigned int) ISI_IrqHandler;
    AIC->AIC_SSR = 53; AIC->AIC_SVR = (unsigned int) TRNG_IrqHandler;
    AIC->AIC_SSR = 54; AIC->AIC_SVR = (unsigned int) GMAC0_IrqHandler;
    AIC->AIC_SSR = 55; AIC->AIC_SVR = (unsigned int) GMAC1_IrqHandler;
    AIC->AIC_SSR = 56; AIC->AIC_SVR = (unsigned int) AIC0_IrqHandler;
    AIC->AIC_SSR = 57; AIC->AIC_SVR = (unsigned int) SFC_IrqHandler;
    AIC->AIC_SSR = 59; AIC->AIC_SVR = (unsigned int) SECURAM_IrqHandler;
    AIC->AIC_SSR = 60; AIC->AIC_SVR = (unsigned int) CTB_IrqHandler;
    AIC->AIC_SSR = 61; AIC->AIC_SVR = (unsigned int) SMD_IrqHandler;
    AIC->AIC_SSR = 62; AIC->AIC_SVR = (unsigned int) TWI3_IrqHandler;
    AIC->AIC_SSR = 63; AIC->AIC_SVR = (unsigned int) CATB_IrqHandler;
    AIC->AIC_SSR = 64; AIC->AIC_SVR = (unsigned int) SFR_IrqHandler;
    AIC->AIC_SSR = 65; AIC->AIC_SVR = (unsigned int) AIC1_IrqHandler;
    AIC->AIC_SSR = 66; AIC->AIC_SVR = (unsigned int) SAIC1_IrqHandler;
    AIC->AIC_SSR = 67; AIC->AIC_SVR = (unsigned int) L2CC_IrqHandler;

    AIC->AIC_SPU = (unsigned int) Spurious_handler;
    /* Disable all interrupts */
    for (i = 1; i < ID_PERIPH_COUNT; i++){
        AIC->AIC_SSR=i;
        AIC->AIC_IDCR=AIC_IDCR_INTD;
    }
    /* Clear All pending interrupts flags */
    for (i = 0; i < ID_PERIPH_COUNT; i++){
        AIC->AIC_SSR  = i;
        AIC->AIC_ICCR = AIC_ICCR_INTCLR;
    }

    /* Perform 8 IT acknoledge (write any value in EOICR) (VPy) */
    for (i = 0; i < 8; i++){
        AIC->AIC_EOICR = 0;
    }
    /* Enable IRQ and FIQ at core level */
    v_ARM_ClrCPSR_bits(CPSR_MASK_IRQ|CPSR_MASK_FIQ);
}

/**
 * \brief Secure Interupt Init.
 */
void SecureITInit (void)
{
    uint32_t i;

    /* Assign handler addesses */
    SAIC->AIC_SSR = 0;  SAIC->AIC_SVR = (unsigned int) SAIC0_Handler;
    SAIC->AIC_SSR = 1;  SAIC->AIC_SVR = (unsigned int) SYS_IrqHandler;
    SAIC->AIC_SSR = 2;  SAIC->AIC_SVR = (unsigned int) ARM_IrqHandler;
    SAIC->AIC_SSR = 3;  SAIC->AIC_SVR = (unsigned int) PIT_IrqHandler;
    SAIC->AIC_SSR = 4;  SAIC->AIC_SVR = (unsigned int) WDT_IrqHandler;
    SAIC->AIC_SSR = 5;  SAIC->AIC_SVR = (unsigned int) PIOD_IrqHandler;
    SAIC->AIC_SSR = 6;  SAIC->AIC_SVR = (unsigned int) USART0_IrqHandler;
    SAIC->AIC_SSR = 7;  SAIC->AIC_SVR = (unsigned int) USART1_IrqHandler;
    SAIC->AIC_SSR = 8;  SAIC->AIC_SVR = (unsigned int) XDMAC0_IrqHandler;
    SAIC->AIC_SSR = 9;  SAIC->AIC_SVR = (unsigned int) ICM_IrqHandler;
    SAIC->AIC_SSR = 10; SAIC->AIC_SVR = (unsigned int) PKCC_IrqHandler;
    SAIC->AIC_SSR = 11; SAIC->AIC_SVR = (unsigned int) SCI_IrqHandler;
    SAIC->AIC_SSR = 12; SAIC->AIC_SVR = (unsigned int) AES_IrqHandler;
    SAIC->AIC_SSR = 13; SAIC->AIC_SVR = (unsigned int) AESB_IrqHandler;
    SAIC->AIC_SSR = 14; SAIC->AIC_SVR = (unsigned int) TDES_IrqHandler;
    SAIC->AIC_SSR = 15; SAIC->AIC_SVR = (unsigned int) SHA_IrqHandler;
    SAIC->AIC_SSR = 16; SAIC->AIC_SVR = (unsigned int) MPDDRC_IrqHandler;
    SAIC->AIC_SSR = 17; SAIC->AIC_SVR = (unsigned int) H32MX_IrqHandler;
    SAIC->AIC_SSR = 18; SAIC->AIC_SVR = (unsigned int) H64MX_IrqHandler;
    SAIC->AIC_SSR = 19; SAIC->AIC_SVR = (unsigned int) VDEC_IrqHandler;
    SAIC->AIC_SSR = 20; SAIC->AIC_SVR = (unsigned int) SECUMOD_IrqHandler;
    SAIC->AIC_SSR = 21; SAIC->AIC_SVR = (unsigned int) MSADCC_IrqHandler;
    SAIC->AIC_SSR = 22; SAIC->AIC_SVR = (unsigned int) HSMC_IrqHandler;
    SAIC->AIC_SSR = 23; SAIC->AIC_SVR = (unsigned int) PIOA_IrqHandler;
    SAIC->AIC_SSR = 24; SAIC->AIC_SVR = (unsigned int) PIOB_IrqHandler;
    SAIC->AIC_SSR = 25; SAIC->AIC_SVR = (unsigned int) PIOC_IrqHandler;
    SAIC->AIC_SSR = 26; SAIC->AIC_SVR = (unsigned int) PIOE_IrqHandler;
    SAIC->AIC_SSR = 27; SAIC->AIC_SVR = (unsigned int) UART0_IrqHandler;
    SAIC->AIC_SSR = 28; SAIC->AIC_SVR = (unsigned int) UART1_IrqHandler;
    SAIC->AIC_SSR = 29; SAIC->AIC_SVR = (unsigned int) USART2_IrqHandler;
    SAIC->AIC_SSR = 30; SAIC->AIC_SVR = (unsigned int) USART3_IrqHandler;
    SAIC->AIC_SSR = 31; SAIC->AIC_SVR = (unsigned int) USART4_IrqHandler;
    SAIC->AIC_SSR = 32; SAIC->AIC_SVR = (unsigned int) TWI0_IrqHandler;
    SAIC->AIC_SSR = 33; SAIC->AIC_SVR = (unsigned int) TWI1_IrqHandler;
    SAIC->AIC_SSR = 34; SAIC->AIC_SVR = (unsigned int) TWI2_IrqHandler;
    SAIC->AIC_SSR = 35; SAIC->AIC_SVR = (unsigned int) HSMCI0_IrqHandler;
    SAIC->AIC_SSR = 36; SAIC->AIC_SVR = (unsigned int) HSMCI1_IrqHandler;
    SAIC->AIC_SSR = 37; SAIC->AIC_SVR = (unsigned int) SPI0_IrqHandler;
    SAIC->AIC_SSR = 38; SAIC->AIC_SVR = (unsigned int) SPI1_IrqHandler;
    SAIC->AIC_SSR = 39; SAIC->AIC_SVR = (unsigned int) SPI2_IrqHandler;
    SAIC->AIC_SSR = 40; SAIC->AIC_SVR = (unsigned int) TC0_IrqHandler;
    SAIC->AIC_SSR = 41; SAIC->AIC_SVR = (unsigned int) TC1_IrqHandler;
    SAIC->AIC_SSR = 42; SAIC->AIC_SVR = (unsigned int) TC2_IrqHandler;
    SAIC->AIC_SSR = 43; SAIC->AIC_SVR = (unsigned int) PWM_IrqHandler;
    SAIC->AIC_SSR = 44; SAIC->AIC_SVR = (unsigned int) ADC_IrqHandler;
    SAIC->AIC_SSR = 45; SAIC->AIC_SVR = (unsigned int) DBGU_IrqHandler;
    SAIC->AIC_SSR = 46; SAIC->AIC_SVR = (unsigned int) UHPHS_IrqHandler;
    SAIC->AIC_SSR = 47; SAIC->AIC_SVR = (unsigned int) UDPHS_IrqHandler;
    SAIC->AIC_SSR = 48; SAIC->AIC_SVR = (unsigned int) SSC0_IrqHandler;
    SAIC->AIC_SSR = 49; SAIC->AIC_SVR = (unsigned int) SSC1_IrqHandler;
    SAIC->AIC_SSR = 50; SAIC->AIC_SVR = (unsigned int) XDMAC1_IrqHandler;
    SAIC->AIC_SSR = 51; SAIC->AIC_SVR = (unsigned int) LCDC_IrqHandler;
    SAIC->AIC_SSR = 52; SAIC->AIC_SVR = (unsigned int) ISI_IrqHandler;
    SAIC->AIC_SSR = 53; SAIC->AIC_SVR = (unsigned int) TRNG_IrqHandler;
    SAIC->AIC_SSR = 54; SAIC->AIC_SVR = (unsigned int) GMAC0_IrqHandler;
    SAIC->AIC_SSR = 55; SAIC->AIC_SVR = (unsigned int) GMAC1_IrqHandler;
    SAIC->AIC_SSR = 56; SAIC->AIC_SVR = (unsigned int) AIC0_IrqHandler;
    SAIC->AIC_SSR = 57; SAIC->AIC_SVR = (unsigned int) SFC_IrqHandler;
    SAIC->AIC_SSR = 59; SAIC->AIC_SVR = (unsigned int) SECURAM_IrqHandler;
    SAIC->AIC_SSR = 60; SAIC->AIC_SVR = (unsigned int) CTB_IrqHandler;
    SAIC->AIC_SSR = 61; SAIC->AIC_SVR = (unsigned int) SMD_IrqHandler;
    SAIC->AIC_SSR = 62; SAIC->AIC_SVR = (unsigned int) TWI3_IrqHandler;
    SAIC->AIC_SSR = 63; SAIC->AIC_SVR = (unsigned int) CATB_IrqHandler;
    SAIC->AIC_SSR = 64; SAIC->AIC_SVR = (unsigned int) SFR_IrqHandler;
    SAIC->AIC_SSR = 65; SAIC->AIC_SVR = (unsigned int) AIC1_IrqHandler;
    SAIC->AIC_SSR = 66; SAIC->AIC_SVR = (unsigned int) SAIC1_IrqHandler;
    SAIC->AIC_SSR = 67; SAIC->AIC_SVR = (unsigned int) L2CC_IrqHandler;

    SAIC->AIC_SPU = (unsigned int) Spurious_handler;

    /* Disable all interrupts */
    for (i = 1; i < ID_PERIPH_COUNT; i++){
        SAIC->AIC_SSR=i;
        SAIC->AIC_IDCR=AIC_IDCR_INTD;
    }
    /* Clear All pending interrupts flags */
    for (i = 0; i < ID_PERIPH_COUNT; i++){
        SAIC->AIC_SSR  = i;
        SAIC->AIC_ICCR = AIC_ICCR_INTCLR;
    }

    /* Perform 8 IT acknoledge (write any value in EOICR) (VPy) */
    for (i = 0; i < 8; i++){
        SAIC->AIC_EOICR = 0;
    }
    /* Enable IRQ and FIQ at core level */
    v_ARM_ClrCPSR_bits(CPSR_MASK_IRQ|CPSR_MASK_FIQ);
}

/**
 * \brief Performs the low-level initialization of the chip.
 * It also enable a low level on the pin NRST triggers a user reset.
 */
extern WEAK void LowLevelInit( void )
{
    volatile unsigned int * pAicFuse = (volatile unsigned int *) REG_SFR_AICREDIR;

    NonSecureITInit();
    if(!(*pAicFuse))
    {
      SecureITInit();
    }

    if ((uint32_t)LowLevelInit < DDR_CS_ADDR) /* Code not in external mem */ {
        PMC_SelectExt12M_Osc();
        PMC_SwitchMck2Main();
        PMC_SetPllA( CKGR_PLLAR_ONE |
                     CKGR_PLLAR_PLLACOUNT(0x3F) |
                     CKGR_PLLAR_OUTA(0x0) |
                     CKGR_PLLAR_MULA(87) |
                     1,
                     PMC_PLLICPR_IPLL_PLLA(0x0));
        PMC_SetMckPllaDiv(PMC_MCKR_PLLADIV2);
        PMC_SetMckPrescaler(PMC_MCKR_PRES_CLOCK);
        PMC_SetMckDivider(PMC_MCKR_MDIV_PCK_DIV3);
        PMC_SwitchMck2Pll();
    }
    /* Remap */
   BOARD_RemapRam();
}
