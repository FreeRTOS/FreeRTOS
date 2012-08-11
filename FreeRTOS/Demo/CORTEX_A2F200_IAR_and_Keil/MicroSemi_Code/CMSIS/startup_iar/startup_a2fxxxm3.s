/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 *
 * Startup code for SmartFusion A2FM3Fxxx
 *
 * SVN $Revision: 2068 $
 * SVN $Date: 2010-01-27 17:27:41 +0000 (Wed, 27 Jan 2010) $
 */

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION CSTACK:DATA:NOROOT(3)

        SECTION .intvec:CODE:NOROOT(2)
	
        EXTERN  __iar_program_start
;        EXTERN  SystemInit
        PUBLIC  __vector_table

        DATA
__vector_table
        DCD     sfe(CSTACK)
        DCD     Reset_Handler

        DCD     NMI_Handler
        DCD     HardFault_Handler
        DCD     MemManage_Handler
        DCD     BusFault_Handler
        DCD     UsageFault_Handler
        DCD     0
        DCD     0
        DCD     0
        DCD     0
        DCD     SVC_Handler
        DCD     DebugMon_Handler
        DCD     0
        DCD     PendSV_Handler
        DCD     SysTick_Handler

        ; External Interrupts
        DCD     WdogWakeup_IRQHandler
        DCD     BrownOut_1_5V_IRQHandler
        DCD     BrownOut_3_3V_IRQHandler
        DCD     RTC_Match_IRQHandler
        DCD     RTCIF_Pub_IRQHandler
        DCD     EthernetMAC_IRQHandler
        DCD     IAP_IRQHandler
        DCD     ENVM0_IRQHandler
        DCD     ENVM1_IRQHandler
        DCD     DMA_IRQHandler
        DCD     UART0_IRQHandler
        DCD     UART1_IRQHandler
        DCD     SPI0_IRQHandler
        DCD     SPI1_IRQHandler
        DCD     I2C0_IRQHandler
        DCD     I2C0_SMBAlert_IRQHandler
        DCD     I2C0_SMBus_IRQHandler
        DCD     I2C1_IRQHandler
        DCD     I2C1_SMBAlert_IRQHandler
        DCD     I2C1_SMBus_IRQHandler
        DCD     Timer1_IRQHandler
        DCD     Timer2_IRQHandler
        DCD     PLL_Lock_IRQHandler
        DCD     PLL_LockLost_IRQHandler
        DCD     CommError_IRQHandler
        DCD     0
        DCD     0
        DCD     0
        DCD     0
        DCD     0
        DCD     0
        DCD     Fabric_IRQHandler
        DCD     GPIO0_IRQHandler
        DCD     GPIO1_IRQHandler
        DCD     GPIO2_IRQHandler
        DCD     GPIO3_IRQHandler
        DCD     GPIO4_IRQHandler
        DCD     GPIO5_IRQHandler
        DCD     GPIO6_IRQHandler
        DCD     GPIO7_IRQHandler
        DCD     GPIO8_IRQHandler
        DCD     GPIO9_IRQHandler
        DCD     GPIO10_IRQHandler
        DCD     GPIO11_IRQHandler
        DCD     GPIO12_IRQHandler
        DCD     GPIO13_IRQHandler
        DCD     GPIO14_IRQHandler
        DCD     GPIO15_IRQHandler
        DCD     GPIO16_IRQHandler
        DCD     GPIO17_IRQHandler
        DCD     GPIO18_IRQHandler
        DCD     GPIO19_IRQHandler
        DCD     GPIO20_IRQHandler
        DCD     GPIO21_IRQHandler
        DCD     GPIO22_IRQHandler
        DCD     GPIO23_IRQHandler
        DCD     GPIO24_IRQHandler
        DCD     GPIO25_IRQHandler
        DCD     GPIO26_IRQHandler
        DCD     GPIO27_IRQHandler
        DCD     GPIO28_IRQHandler
        DCD     GPIO29_IRQHandler
        DCD     GPIO30_IRQHandler
        DCD     GPIO31_IRQHandler
        DCD     ACE_PC0_Flag0_IRQHandler
        DCD     ACE_PC0_Flag1_IRQHandler
        DCD     ACE_PC0_Flag2_IRQHandler
        DCD     ACE_PC0_Flag3_IRQHandler
        DCD     ACE_PC1_Flag0_IRQHandler
        DCD     ACE_PC1_Flag1_IRQHandler
        DCD     ACE_PC1_Flag2_IRQHandler
        DCD     ACE_PC1_Flag3_IRQHandler
        DCD     ACE_PC2_Flag0_IRQHandler
        DCD     ACE_PC2_Flag1_IRQHandler
        DCD     ACE_PC2_Flag2_IRQHandler
        DCD     ACE_PC2_Flag3_IRQHandler
        DCD     ACE_ADC0_DataValid_IRQHandler
        DCD     ACE_ADC1_DataValid_IRQHandler
        DCD     ACE_ADC2_DataValid_IRQHandler
        DCD     ACE_ADC0_CalDone_IRQHandler
        DCD     ACE_ADC1_CalDone_IRQHandler
        DCD     ACE_ADC2_CalDone_IRQHandler
        DCD     ACE_ADC0_CalStart_IRQHandler
        DCD     ACE_ADC1_CalStart_IRQHandler
        DCD     ACE_ADC2_CalStart_IRQHandler
        DCD     ACE_Comp0_Fall_IRQHandler
        DCD     ACE_Comp1_Fall_IRQHandler
        DCD     ACE_Comp2_Fall_IRQHandler
        DCD     ACE_Comp3_Fall_IRQHandler
        DCD     ACE_Comp4_Fall_IRQHandler
        DCD     ACE_Comp5_Fall_IRQHandler
        DCD     ACE_Comp6_Fall_IRQHandler
        DCD     ACE_Comp7_Fall_IRQHandler
        DCD     ACE_Comp8_Fall_IRQHandler
        DCD     ACE_Comp9_Fall_IRQHandler
        DCD     ACE_Comp10_Fall_IRQHandler
        DCD     ACE_Comp11_Fall_IRQHandler
        DCD     ACE_Comp0_Rise_IRQHandler
        DCD     ACE_Comp1_Rise_IRQHandler
        DCD     ACE_Comp2_Rise_IRQHandler
        DCD     ACE_Comp3_Rise_IRQHandler
        DCD     ACE_Comp4_Rise_IRQHandler
        DCD     ACE_Comp5_Rise_IRQHandler
        DCD     ACE_Comp6_Rise_IRQHandler
        DCD     ACE_Comp7_Rise_IRQHandler
        DCD     ACE_Comp8_Rise_IRQHandler
        DCD     ACE_Comp9_Rise_IRQHandler
        DCD     ACE_Comp10_Rise_IRQHandler
        DCD     ACE_Comp11_Rise_IRQHandler
        DCD     ACE_ADC0_FifoFull_IRQHandler
        DCD     ACE_ADC0_FifoAFull_IRQHandler
        DCD     ACE_ADC0_FifoEmpty_IRQHandler
        DCD     ACE_ADC1_FifoFull_IRQHandler
        DCD     ACE_ADC1_FifoAFull_IRQHandler
        DCD     ACE_ADC1_FifoEmpty_IRQHandler
        DCD     ACE_ADC2_FifoFull_IRQHandler
        DCD     ACE_ADC2_FifoAFull_IRQHandler
        DCD     ACE_ADC2_FifoEmpty_IRQHandler
        DCD     ACE_PPE_Flag0_IRQHandler
        DCD     ACE_PPE_Flag1_IRQHandler
        DCD     ACE_PPE_Flag2_IRQHandler
        DCD     ACE_PPE_Flag3_IRQHandler
        DCD     ACE_PPE_Flag4_IRQHandler
        DCD     ACE_PPE_Flag5_IRQHandler
        DCD     ACE_PPE_Flag6_IRQHandler
        DCD     ACE_PPE_Flag7_IRQHandler
        DCD     ACE_PPE_Flag8_IRQHandler
        DCD     ACE_PPE_Flag9_IRQHandler
        DCD     ACE_PPE_Flag10_IRQHandler
        DCD     ACE_PPE_Flag11_IRQHandler
        DCD     ACE_PPE_Flag12_IRQHandler
        DCD     ACE_PPE_Flag13_IRQHandler
        DCD     ACE_PPE_Flag14_IRQHandler
        DCD     ACE_PPE_Flag15_IRQHandler
        DCD     ACE_PPE_Flag16_IRQHandler
        DCD     ACE_PPE_Flag17_IRQHandler
        DCD     ACE_PPE_Flag18_IRQHandler
        DCD     ACE_PPE_Flag19_IRQHandler
        DCD     ACE_PPE_Flag20_IRQHandler
        DCD     ACE_PPE_Flag21_IRQHandler
        DCD     ACE_PPE_Flag22_IRQHandler
        DCD     ACE_PPE_Flag23_IRQHandler
        DCD     ACE_PPE_Flag24_IRQHandler
        DCD     ACE_PPE_Flag25_IRQHandler
        DCD     ACE_PPE_Flag26_IRQHandler
        DCD     ACE_PPE_Flag27_IRQHandler
        DCD     ACE_PPE_Flag28_IRQHandler
        DCD     ACE_PPE_Flag29_IRQHandler
        DCD     ACE_PPE_Flag30_IRQHandler
        DCD     ACE_PPE_Flag31_IRQHandler


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Default interrupt handlers.
;;
        THUMB

        PUBWEAK Reset_Handler
        SECTION .text:CODE:REORDER(2)
Reset_Handler
;       LDR     R0, =SystemInit
;       BLX     R0
        LDR     R0, =__iar_program_start
        BX      R0

        PUBWEAK NMI_Handler
        SECTION .text:CODE:REORDER(1)
NMI_Handler
        B NMI_Handler
		
        PUBWEAK HardFault_Handler
        SECTION .text:CODE:REORDER(1)
HardFault_Handler
        B HardFault_Handler
		
        PUBWEAK MemManage_Handler
        SECTION .text:CODE:REORDER(1)
MemManage_Handler
        B MemManage_Handler
		
        PUBWEAK BusFault_Handler
        SECTION .text:CODE:REORDER(1)
BusFault_Handler
        B BusFault_Handler
		
        PUBWEAK UsageFault_Handler
        SECTION .text:CODE:REORDER(1)
UsageFault_Handler
        B UsageFault_Handler
		
        PUBWEAK SVC_Handler
        SECTION .text:CODE:REORDER(1)
SVC_Handler
        B SVC_Handler
		
        PUBWEAK DebugMon_Handler
        SECTION .text:CODE:REORDER(1)
DebugMon_Handler
        B DebugMon_Handler
		
        PUBWEAK PendSV_Handler
        SECTION .text:CODE:REORDER(1)
PendSV_Handler
        B PendSV_Handler
		
        PUBWEAK SysTick_Handler
        SECTION .text:CODE:REORDER(1)
SysTick_Handler
        B SysTick_Handler

        PUBWEAK WdogWakeup_IRQHandler
        SECTION .text:CODE:REORDER(1)
WdogWakeup_IRQHandler
        B WdogWakeup_IRQHandler
		
        PUBWEAK BrownOut_1_5V_IRQHandler
        SECTION .text:CODE:REORDER(1)
BrownOut_1_5V_IRQHandler
        B BrownOut_1_5V_IRQHandler
		
        PUBWEAK BrownOut_3_3V_IRQHandler
        SECTION .text:CODE:REORDER(1)
BrownOut_3_3V_IRQHandler
        B BrownOut_3_3V_IRQHandler
		
        PUBWEAK RTC_Match_IRQHandler
        SECTION .text:CODE:REORDER(1)
RTC_Match_IRQHandler
        B RTC_Match_IRQHandler
		
        PUBWEAK RTCIF_Pub_IRQHandler
        SECTION .text:CODE:REORDER(1)
RTCIF_Pub_IRQHandler
        B RTCIF_Pub_IRQHandler
		
        PUBWEAK EthernetMAC_IRQHandler
        SECTION .text:CODE:REORDER(1)
EthernetMAC_IRQHandler
        B EthernetMAC_IRQHandler
		
        PUBWEAK IAP_IRQHandler
        SECTION .text:CODE:REORDER(1)
IAP_IRQHandler
        B IAP_IRQHandler
		
        PUBWEAK ENVM0_IRQHandler
        SECTION .text:CODE:REORDER(1)
ENVM0_IRQHandler
        B ENVM0_IRQHandler
		
        PUBWEAK ENVM1_IRQHandler
        SECTION .text:CODE:REORDER(1)
ENVM1_IRQHandler
        B ENVM1_IRQHandler
		
        PUBWEAK DMA_IRQHandler
        SECTION .text:CODE:REORDER(1)
DMA_IRQHandler
        B DMA_IRQHandler
		
        PUBWEAK UART0_IRQHandler
        SECTION .text:CODE:REORDER(1)
UART0_IRQHandler
        B UART0_IRQHandler
		
        PUBWEAK UART1_IRQHandler
        SECTION .text:CODE:REORDER(1)
UART1_IRQHandler
        B UART1_IRQHandler
		
        PUBWEAK SPI0_IRQHandler
        SECTION .text:CODE:REORDER(1)
SPI0_IRQHandler
        B SPI0_IRQHandler
		
        PUBWEAK SPI1_IRQHandler
        SECTION .text:CODE:REORDER(1)
SPI1_IRQHandler
        B SPI1_IRQHandler
		
        PUBWEAK I2C0_IRQHandler
        SECTION .text:CODE:REORDER(1)
I2C0_IRQHandler
        B I2C0_IRQHandler
		
        PUBWEAK I2C0_SMBAlert_IRQHandler
        SECTION .text:CODE:REORDER(1)
I2C0_SMBAlert_IRQHandler
        B I2C0_SMBAlert_IRQHandler

        PUBWEAK I2C0_SMBus_IRQHandler
        SECTION .text:CODE:REORDER(1)
I2C0_SMBus_IRQHandler
        B I2C0_SMBus_IRQHandler
		
        PUBWEAK I2C1_IRQHandler
        SECTION .text:CODE:REORDER(1)
I2C1_IRQHandler
        B I2C1_IRQHandler
		
        PUBWEAK I2C1_SMBAlert_IRQHandler
        SECTION .text:CODE:REORDER(1)
I2C1_SMBAlert_IRQHandler
        B I2C1_SMBAlert_IRQHandler
		
        PUBWEAK I2C1_SMBus_IRQHandler
        SECTION .text:CODE:REORDER(1)
I2C1_SMBus_IRQHandler
        B I2C1_SMBus_IRQHandler
		
        PUBWEAK Timer1_IRQHandler
        SECTION .text:CODE:REORDER(1)
Timer1_IRQHandler
        B Timer1_IRQHandler
		
        PUBWEAK Timer2_IRQHandler
        SECTION .text:CODE:REORDER(1)
Timer2_IRQHandler
        B Timer2_IRQHandler
		
        PUBWEAK PLL_Lock_IRQHandler
        SECTION .text:CODE:REORDER(1)
PLL_Lock_IRQHandler
        B PLL_Lock_IRQHandler
		
        PUBWEAK PLL_LockLost_IRQHandler
        SECTION .text:CODE:REORDER(1)
PLL_LockLost_IRQHandler
        B PLL_LockLost_IRQHandler
		
        PUBWEAK CommError_IRQHandler
        SECTION .text:CODE:REORDER(1)
CommError_IRQHandler
        B CommError_IRQHandler
		
        PUBWEAK Fabric_IRQHandler
        SECTION .text:CODE:REORDER(1)
Fabric_IRQHandler
        B Fabric_IRQHandler
		
        PUBWEAK GPIO0_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO0_IRQHandler
        B GPIO0_IRQHandler
		
        PUBWEAK GPIO1_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO1_IRQHandler
        B GPIO1_IRQHandler
		
        PUBWEAK GPIO2_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO2_IRQHandler
        B GPIO2_IRQHandler
		
        PUBWEAK GPIO3_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO3_IRQHandler
        B GPIO3_IRQHandler
		
        PUBWEAK GPIO4_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO4_IRQHandler
        B GPIO4_IRQHandler
		
        PUBWEAK GPIO5_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO5_IRQHandler
        B GPIO5_IRQHandler
		
        PUBWEAK GPIO6_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO6_IRQHandler
        B GPIO6_IRQHandler
		
        PUBWEAK GPIO7_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO7_IRQHandler
        B GPIO7_IRQHandler
		
        PUBWEAK GPIO8_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO8_IRQHandler
        B GPIO8_IRQHandler
		
        PUBWEAK GPIO9_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO9_IRQHandler
        B GPIO9_IRQHandler
		
        PUBWEAK GPIO10_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO10_IRQHandler
        B GPIO10_IRQHandler
		
        PUBWEAK GPIO11_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO11_IRQHandler
        B GPIO11_IRQHandler
		
        PUBWEAK GPIO12_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO12_IRQHandler
        B GPIO12_IRQHandler
		
        PUBWEAK GPIO13_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO13_IRQHandler
        B GPIO13_IRQHandler
		
        PUBWEAK GPIO14_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO14_IRQHandler
        B GPIO14_IRQHandler
		
        PUBWEAK GPIO15_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO15_IRQHandler
        B GPIO15_IRQHandler
		
        PUBWEAK GPIO16_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO16_IRQHandler
        B GPIO16_IRQHandler
		
        PUBWEAK GPIO17_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO17_IRQHandler
        B GPIO17_IRQHandler
		
        PUBWEAK GPIO18_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO18_IRQHandler
        B GPIO18_IRQHandler
		
        PUBWEAK GPIO19_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO19_IRQHandler
        B GPIO19_IRQHandler
		
        PUBWEAK GPIO20_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO20_IRQHandler
        B GPIO20_IRQHandler
		
        PUBWEAK GPIO21_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO21_IRQHandler
        B GPIO21_IRQHandler
		
        PUBWEAK GPIO22_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO22_IRQHandler
        B GPIO22_IRQHandler
		
        PUBWEAK GPIO23_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO23_IRQHandler
        B GPIO23_IRQHandler
		
        PUBWEAK GPIO24_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO24_IRQHandler
        B GPIO24_IRQHandler
		
        PUBWEAK GPIO25_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO25_IRQHandler
        B GPIO25_IRQHandler
		
        PUBWEAK GPIO26_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO26_IRQHandler
        B GPIO26_IRQHandler
		
        PUBWEAK GPIO27_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO27_IRQHandler
        B GPIO27_IRQHandler
		
        PUBWEAK GPIO28_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO28_IRQHandler
        B GPIO28_IRQHandler
		
        PUBWEAK GPIO29_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO29_IRQHandler
        B GPIO29_IRQHandler
		
        PUBWEAK GPIO30_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO30_IRQHandler
        B GPIO30_IRQHandler
		
        PUBWEAK GPIO31_IRQHandler
        SECTION .text:CODE:REORDER(1)
GPIO31_IRQHandler
        B GPIO31_IRQHandler

        PUBWEAK ACE_PC0_Flag0_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC0_Flag0_IRQHandler
        B ACE_PC0_Flag0_IRQHandler

        PUBWEAK ACE_PC0_Flag1_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC0_Flag1_IRQHandler
        B ACE_PC0_Flag1_IRQHandler

        PUBWEAK ACE_PC0_Flag2_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC0_Flag2_IRQHandler
        B ACE_PC0_Flag2_IRQHandler

        PUBWEAK ACE_PC0_Flag3_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC0_Flag3_IRQHandler
        B ACE_PC0_Flag3_IRQHandler

        PUBWEAK ACE_PC1_Flag0_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC1_Flag0_IRQHandler
        B ACE_PC1_Flag0_IRQHandler

        PUBWEAK ACE_PC1_Flag1_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC1_Flag1_IRQHandler
        B ACE_PC1_Flag1_IRQHandler

        PUBWEAK ACE_PC1_Flag2_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC1_Flag2_IRQHandler
        B ACE_PC1_Flag2_IRQHandler

        PUBWEAK ACE_PC1_Flag3_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC1_Flag3_IRQHandler
        B ACE_PC1_Flag3_IRQHandler

        PUBWEAK ACE_PC2_Flag0_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC2_Flag0_IRQHandler
        B ACE_PC2_Flag0_IRQHandler

        PUBWEAK ACE_PC2_Flag1_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC2_Flag1_IRQHandler
        B ACE_PC2_Flag1_IRQHandler

        PUBWEAK ACE_PC2_Flag2_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC2_Flag2_IRQHandler
        B ACE_PC2_Flag2_IRQHandler

        PUBWEAK ACE_PC2_Flag3_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PC2_Flag3_IRQHandler
        B ACE_PC2_Flag3_IRQHandler

        PUBWEAK ACE_ADC0_DataValid_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC0_DataValid_IRQHandler
        B ACE_ADC0_DataValid_IRQHandler

        PUBWEAK ACE_ADC1_DataValid_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC1_DataValid_IRQHandler
        B ACE_ADC1_DataValid_IRQHandler

        PUBWEAK ACE_ADC2_DataValid_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC2_DataValid_IRQHandler
        B ACE_ADC2_DataValid_IRQHandler

        PUBWEAK ACE_ADC0_CalDone_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC0_CalDone_IRQHandler
        B ACE_ADC0_CalDone_IRQHandler

        PUBWEAK ACE_ADC1_CalDone_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC1_CalDone_IRQHandler
        B ACE_ADC1_CalDone_IRQHandler

        PUBWEAK ACE_ADC2_CalDone_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC2_CalDone_IRQHandler
        B ACE_ADC2_CalDone_IRQHandler

        PUBWEAK ACE_ADC0_CalStart_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC0_CalStart_IRQHandler
        B ACE_ADC0_CalStart_IRQHandler

        PUBWEAK ACE_ADC1_CalStart_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC1_CalStart_IRQHandler
        B ACE_ADC1_CalStart_IRQHandler

        PUBWEAK ACE_ADC2_CalStart_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC2_CalStart_IRQHandler
        B ACE_ADC2_CalStart_IRQHandler

        PUBWEAK ACE_Comp0_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp0_Fall_IRQHandler
        B ACE_Comp0_Fall_IRQHandler

        PUBWEAK ACE_Comp1_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp1_Fall_IRQHandler
        B ACE_Comp1_Fall_IRQHandler

        PUBWEAK ACE_Comp2_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp2_Fall_IRQHandler
        B ACE_Comp2_Fall_IRQHandler

        PUBWEAK ACE_Comp3_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp3_Fall_IRQHandler
        B ACE_Comp3_Fall_IRQHandler

        PUBWEAK ACE_Comp4_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp4_Fall_IRQHandler
        B ACE_Comp4_Fall_IRQHandler

        PUBWEAK ACE_Comp5_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp5_Fall_IRQHandler
        B ACE_Comp5_Fall_IRQHandler

        PUBWEAK ACE_Comp6_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp6_Fall_IRQHandler
        B ACE_Comp6_Fall_IRQHandler

        PUBWEAK ACE_Comp7_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp7_Fall_IRQHandler
        B ACE_Comp7_Fall_IRQHandler

        PUBWEAK ACE_Comp8_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp8_Fall_IRQHandler
        B ACE_Comp8_Fall_IRQHandler

        PUBWEAK ACE_Comp9_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp9_Fall_IRQHandler
        B ACE_Comp9_Fall_IRQHandler

        PUBWEAK ACE_Comp10_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp10_Fall_IRQHandler
        B ACE_Comp10_Fall_IRQHandler

        PUBWEAK ACE_Comp11_Fall_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp11_Fall_IRQHandler
        B ACE_Comp11_Fall_IRQHandler

        PUBWEAK ACE_Comp0_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp0_Rise_IRQHandler
        B ACE_Comp0_Rise_IRQHandler

        PUBWEAK ACE_Comp1_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp1_Rise_IRQHandler
        B ACE_Comp1_Rise_IRQHandler

        PUBWEAK ACE_Comp2_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp2_Rise_IRQHandler
        B ACE_Comp2_Rise_IRQHandler

        PUBWEAK ACE_Comp3_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp3_Rise_IRQHandler
        B ACE_Comp3_Rise_IRQHandler

        PUBWEAK ACE_Comp4_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp4_Rise_IRQHandler
        B ACE_Comp4_Rise_IRQHandler

        PUBWEAK ACE_Comp5_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp5_Rise_IRQHandler
        B ACE_Comp5_Rise_IRQHandler

        PUBWEAK ACE_Comp6_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp6_Rise_IRQHandler
        B ACE_Comp6_Rise_IRQHandler

        PUBWEAK ACE_Comp7_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp7_Rise_IRQHandler
        B ACE_Comp7_Rise_IRQHandler

        PUBWEAK ACE_Comp8_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp8_Rise_IRQHandler
        B ACE_Comp8_Rise_IRQHandler

        PUBWEAK ACE_Comp9_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp9_Rise_IRQHandler
        B ACE_Comp9_Rise_IRQHandler

        PUBWEAK ACE_Comp10_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp10_Rise_IRQHandler
        B ACE_Comp10_Rise_IRQHandler

        PUBWEAK ACE_Comp11_Rise_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_Comp11_Rise_IRQHandler
        B ACE_Comp11_Rise_IRQHandler

        PUBWEAK ACE_ADC0_FifoFull_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC0_FifoFull_IRQHandler
        B ACE_ADC0_FifoFull_IRQHandler

        PUBWEAK ACE_ADC0_FifoAFull_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC0_FifoAFull_IRQHandler
        B ACE_ADC0_FifoAFull_IRQHandler

        PUBWEAK ACE_ADC0_FifoEmpty_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC0_FifoEmpty_IRQHandler
        B ACE_ADC0_FifoEmpty_IRQHandler

        PUBWEAK ACE_ADC1_FifoFull_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC1_FifoFull_IRQHandler
        B ACE_ADC1_FifoFull_IRQHandler

        PUBWEAK ACE_ADC1_FifoAFull_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC1_FifoAFull_IRQHandler
        B ACE_ADC1_FifoAFull_IRQHandler

        PUBWEAK ACE_ADC1_FifoEmpty_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC1_FifoEmpty_IRQHandler
        B ACE_ADC1_FifoEmpty_IRQHandler

        PUBWEAK ACE_ADC2_FifoFull_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC2_FifoFull_IRQHandler
        B ACE_ADC2_FifoFull_IRQHandler

        PUBWEAK ACE_ADC2_FifoAFull_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC2_FifoAFull_IRQHandler
        B ACE_ADC2_FifoAFull_IRQHandler

        PUBWEAK ACE_ADC2_FifoEmpty_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_ADC2_FifoEmpty_IRQHandler
        B ACE_ADC2_FifoEmpty_IRQHandler

        PUBWEAK ACE_PPE_Flag0_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag0_IRQHandler
        B ACE_PPE_Flag0_IRQHandler

        PUBWEAK ACE_PPE_Flag1_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag1_IRQHandler
        B ACE_PPE_Flag1_IRQHandler

        PUBWEAK ACE_PPE_Flag2_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag2_IRQHandler
        B ACE_PPE_Flag2_IRQHandler

        PUBWEAK ACE_PPE_Flag3_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag3_IRQHandler
        B ACE_PPE_Flag3_IRQHandler

        PUBWEAK ACE_PPE_Flag4_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag4_IRQHandler
        B ACE_PPE_Flag4_IRQHandler

        PUBWEAK ACE_PPE_Flag5_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag5_IRQHandler
        B ACE_PPE_Flag5_IRQHandler

        PUBWEAK ACE_PPE_Flag6_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag6_IRQHandler
        B ACE_PPE_Flag6_IRQHandler

        PUBWEAK ACE_PPE_Flag7_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag7_IRQHandler
        B ACE_PPE_Flag7_IRQHandler

        PUBWEAK ACE_PPE_Flag8_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag8_IRQHandler
        B ACE_PPE_Flag8_IRQHandler

        PUBWEAK ACE_PPE_Flag9_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag9_IRQHandler
        B ACE_PPE_Flag9_IRQHandler

        PUBWEAK ACE_PPE_Flag10_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag10_IRQHandler
        B ACE_PPE_Flag10_IRQHandler

        PUBWEAK ACE_PPE_Flag11_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag11_IRQHandler
        B ACE_PPE_Flag11_IRQHandler

        PUBWEAK ACE_PPE_Flag12_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag12_IRQHandler
        B ACE_PPE_Flag12_IRQHandler

        PUBWEAK ACE_PPE_Flag13_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag13_IRQHandler
        B ACE_PPE_Flag13_IRQHandler

        PUBWEAK ACE_PPE_Flag14_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag14_IRQHandler
        B ACE_PPE_Flag14_IRQHandler

        PUBWEAK ACE_PPE_Flag15_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag15_IRQHandler
        B ACE_PPE_Flag15_IRQHandler

        PUBWEAK ACE_PPE_Flag16_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag16_IRQHandler
        B ACE_PPE_Flag16_IRQHandler

        PUBWEAK ACE_PPE_Flag17_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag17_IRQHandler
        B ACE_PPE_Flag17_IRQHandler

        PUBWEAK ACE_PPE_Flag18_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag18_IRQHandler
        B ACE_PPE_Flag18_IRQHandler

        PUBWEAK ACE_PPE_Flag19_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag19_IRQHandler
        B ACE_PPE_Flag19_IRQHandler

        PUBWEAK ACE_PPE_Flag20_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag20_IRQHandler
        B ACE_PPE_Flag20_IRQHandler

        PUBWEAK ACE_PPE_Flag21_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag21_IRQHandler
        B ACE_PPE_Flag21_IRQHandler

        PUBWEAK ACE_PPE_Flag22_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag22_IRQHandler
        B ACE_PPE_Flag22_IRQHandler

        PUBWEAK ACE_PPE_Flag23_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag23_IRQHandler
        B ACE_PPE_Flag23_IRQHandler

        PUBWEAK ACE_PPE_Flag24_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag24_IRQHandler
        B ACE_PPE_Flag24_IRQHandler

        PUBWEAK ACE_PPE_Flag25_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag25_IRQHandler
        B ACE_PPE_Flag25_IRQHandler

        PUBWEAK ACE_PPE_Flag26_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag26_IRQHandler
        B ACE_PPE_Flag26_IRQHandler

        PUBWEAK ACE_PPE_Flag27_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag27_IRQHandler
        B ACE_PPE_Flag27_IRQHandler

        PUBWEAK ACE_PPE_Flag28_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag28_IRQHandler
        B ACE_PPE_Flag28_IRQHandler

        PUBWEAK ACE_PPE_Flag29_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag29_IRQHandler
        B ACE_PPE_Flag29_IRQHandler

        PUBWEAK ACE_PPE_Flag30_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag30_IRQHandler
        B ACE_PPE_Flag30_IRQHandler

        PUBWEAK ACE_PPE_Flag31_IRQHandler
        SECTION .text:CODE:REORDER(1)
ACE_PPE_Flag31_IRQHandler
        B ACE_PPE_Flag31_IRQHandler

        END
