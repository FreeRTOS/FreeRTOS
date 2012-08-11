/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 *  SmartFusion A2FXXXM3 vector table and startup code.
 *
 * SVN $Revision: 2068 $
 * SVN $Date: 2010-01-27 17:27:41 +0000 (Wed, 27 Jan 2010) $
 */

	.syntax unified
    .cpu cortex-m3
    .thumb
    

/*==============================================================================
 * Vector table
 */
    .global     g_pfnVectors
    .section    .isr_vector,"a",%progbits
    .type       g_pfnVectors, %object
    .size       g_pfnVectors, .-g_pfnVectors
    
g_pfnVectors:
    .word  _estack
    .word  Reset_Handler
    .word  NMI_Handler
    .word  HardFault_Handler
    .word  MemManage_Handler
    .word  BusFault_Handler
    .word  UsageFault_Handler
    .word  0
    .word  0
    .word  0
    .word  0
    .word  SVC_Handler
    .word  DebugMon_Handler
    .word  0
    .word  PendSV_Handler
    .word  SysTick_Handler
    .word  WdogWakeup_IRQHandler
    .word  BrownOut_1_5V_IRQHandler
    .word  BrownOut_3_3V_IRQHandler
    .word  RTC_Match_IRQHandler
    .word  RTCIF_Pub_IRQHandler
    .word  EthernetMAC_IRQHandler
    .word  IAP_IRQHandler
    .word  ENVM0_IRQHandler
    .word  ENVM1_IRQHandler
    .word  DMA_IRQHandler
    .word  UART0_IRQHandler
    .word  UART1_IRQHandler
    .word  SPI0_IRQHandler
    .word  SPI1_IRQHandler
    .word  I2C0_IRQHandler
    .word  I2C0_SMBAlert_IRQHandler
    .word  I2C0_SMBus_IRQHandler
    .word  I2C1_IRQHandler
    .word  I2C1_SMBAlert_IRQHandler
    .word  I2C1_SMBus_IRQHandler
    .word  Timer1_IRQHandler
    .word  Timer2_IRQHandler
    .word  PLL_Lock_IRQHandler
    .word  PLL_LockLost_IRQHandler
    .word  CommError_IRQHandler
    .word  0
    .word  0
    .word  0
    .word  0
    .word  0
    .word  0
    .word  Fabric_IRQHandler
    .word  GPIO0_IRQHandler
    .word  GPIO1_IRQHandler
    .word  GPIO2_IRQHandler
    .word  GPIO3_IRQHandler
    .word  GPIO4_IRQHandler
    .word  GPIO5_IRQHandler
    .word  GPIO6_IRQHandler
    .word  GPIO7_IRQHandler
    .word  GPIO8_IRQHandler
    .word  GPIO9_IRQHandler
    .word  GPIO10_IRQHandler
    .word  GPIO11_IRQHandler
    .word  GPIO12_IRQHandler
    .word  GPIO13_IRQHandler
    .word  GPIO14_IRQHandler
    .word  GPIO15_IRQHandler
    .word  GPIO16_IRQHandler
    .word  GPIO17_IRQHandler
    .word  GPIO18_IRQHandler
    .word  GPIO19_IRQHandler
    .word  GPIO20_IRQHandler
    .word  GPIO21_IRQHandler
    .word  GPIO22_IRQHandler
    .word  GPIO23_IRQHandler
    .word  GPIO24_IRQHandler
    .word  GPIO25_IRQHandler
    .word  GPIO26_IRQHandler
    .word  GPIO27_IRQHandler
    .word  GPIO28_IRQHandler
    .word  GPIO29_IRQHandler
    .word  GPIO30_IRQHandler
    .word  GPIO31_IRQHandler
    .word  ACE_PC0_Flag0_IRQHandler
    .word  ACE_PC0_Flag1_IRQHandler
    .word  ACE_PC0_Flag2_IRQHandler
    .word  ACE_PC0_Flag3_IRQHandler
    .word  ACE_PC1_Flag0_IRQHandler
    .word  ACE_PC1_Flag1_IRQHandler
    .word  ACE_PC1_Flag2_IRQHandler
    .word  ACE_PC1_Flag3_IRQHandler
    .word  ACE_PC2_Flag0_IRQHandler
    .word  ACE_PC2_Flag1_IRQHandler
    .word  ACE_PC2_Flag2_IRQHandler
    .word  ACE_PC2_Flag3_IRQHandler
    .word  ACE_ADC0_DataValid_IRQHandler
    .word  ACE_ADC1_DataValid_IRQHandler
    .word  ACE_ADC2_DataValid_IRQHandler
    .word  ACE_ADC0_CalDone_IRQHandler
    .word  ACE_ADC1_CalDone_IRQHandler
    .word  ACE_ADC2_CalDone_IRQHandler
    .word  ACE_ADC0_CalStart_IRQHandler
    .word  ACE_ADC1_CalStart_IRQHandler
    .word  ACE_ADC2_CalStart_IRQHandler
    .word  ACE_Comp0_Fall_IRQHandler
    .word  ACE_Comp1_Fall_IRQHandler
    .word  ACE_Comp2_Fall_IRQHandler
    .word  ACE_Comp3_Fall_IRQHandler
    .word  ACE_Comp4_Fall_IRQHandler
    .word  ACE_Comp5_Fall_IRQHandler
    .word  ACE_Comp6_Fall_IRQHandler
    .word  ACE_Comp7_Fall_IRQHandler
    .word  ACE_Comp8_Fall_IRQHandler
    .word  ACE_Comp9_Fall_IRQHandler
    .word  ACE_Comp10_Fall_IRQHandler
    .word  ACE_Comp11_Fall_IRQHandler
    .word  ACE_Comp0_Rise_IRQHandler
    .word  ACE_Comp1_Rise_IRQHandler
    .word  ACE_Comp2_Rise_IRQHandler
    .word  ACE_Comp3_Rise_IRQHandler
    .word  ACE_Comp4_Rise_IRQHandler
    .word  ACE_Comp5_Rise_IRQHandler
    .word  ACE_Comp6_Rise_IRQHandler
    .word  ACE_Comp7_Rise_IRQHandler
    .word  ACE_Comp8_Rise_IRQHandler
    .word  ACE_Comp9_Rise_IRQHandler
    .word  ACE_Comp10_Rise_IRQHandler
    .word  ACE_Comp11_Rise_IRQHandler
    .word  ACE_ADC0_FifoFull_IRQHandler
    .word  ACE_ADC0_FifoAFull_IRQHandler
    .word  ACE_ADC0_FifoEmpty_IRQHandler
    .word  ACE_ADC1_FifoFull_IRQHandler
    .word  ACE_ADC1_FifoAFull_IRQHandler
    .word  ACE_ADC1_FifoEmpty_IRQHandler
    .word  ACE_ADC2_FifoFull_IRQHandler
    .word  ACE_ADC2_FifoAFull_IRQHandler
    .word  ACE_ADC2_FifoEmpty_IRQHandler
    .word  ACE_PPE_Flag0_IRQHandler
    .word  ACE_PPE_Flag1_IRQHandler
    .word  ACE_PPE_Flag2_IRQHandler
    .word  ACE_PPE_Flag3_IRQHandler
    .word  ACE_PPE_Flag4_IRQHandler
    .word  ACE_PPE_Flag5_IRQHandler
    .word  ACE_PPE_Flag6_IRQHandler
    .word  ACE_PPE_Flag7_IRQHandler
    .word  ACE_PPE_Flag8_IRQHandler
    .word  ACE_PPE_Flag9_IRQHandler
    .word  ACE_PPE_Flag10_IRQHandler
    .word  ACE_PPE_Flag11_IRQHandler
    .word  ACE_PPE_Flag12_IRQHandler
    .word  ACE_PPE_Flag13_IRQHandler
    .word  ACE_PPE_Flag14_IRQHandler
    .word  ACE_PPE_Flag15_IRQHandler
    .word  ACE_PPE_Flag16_IRQHandler
    .word  ACE_PPE_Flag17_IRQHandler
    .word  ACE_PPE_Flag18_IRQHandler
    .word  ACE_PPE_Flag19_IRQHandler
    .word  ACE_PPE_Flag20_IRQHandler
    .word  ACE_PPE_Flag21_IRQHandler
    .word  ACE_PPE_Flag22_IRQHandler
    .word  ACE_PPE_Flag23_IRQHandler
    .word  ACE_PPE_Flag24_IRQHandler
    .word  ACE_PPE_Flag25_IRQHandler
    .word  ACE_PPE_Flag26_IRQHandler
    .word  ACE_PPE_Flag27_IRQHandler
    .word  ACE_PPE_Flag28_IRQHandler
    .word  ACE_PPE_Flag29_IRQHandler
    .word  ACE_PPE_Flag30_IRQHandler
    .word  ACE_PPE_Flag31_IRQHandler

	
/*==============================================================================
 * Reset_Handler
 */
    .global Reset_Handler
    .type   Reset_Handler, %function
Reset_Handler:
_start:
/*------------------------------------------------------------------------------	
 * Call CMSIS system init function.
 * This is not actually required for SmartFusioon as all low initialisations are
 * done as part of the system boot.
 */
;    ldr     r0, =SystemInit
;    blx     r0
    
/*------------------------------------------------------------------------------	 
 * Check if the executable is built for NVM LMA mirrored to VMA address.
 * This is done for debugging executables running out of eNVM with SoftConsole.
 * The .text section should not be copied in this case since both the LMA and
 * VMA point at the eNVM despite the LMA and VMa having different values.
 */
    ldr r0, =__mirrored_nvm
    cmp r0, #0
    bne copy_data
    
/*------------------------------------------------------------------------------	 
 * Copy code section.
 */
	ldr r0, =__text_load
	ldr r1, =__text_start
	ldr r2, =_etext
	cmp r0, r1
	beq copy_data
copy_code_loop:
	cmp r1, r2
    itt ne
	ldrne r3, [r0], #4
	strne r3, [r1], #4
	bne copy_code_loop

/*------------------------------------------------------------------------------	
 * Copy data section.
 */
copy_data:
	ldr r0, =__data_load
	ldr r1, =__data_start
	ldr r2, =_edata
	cmp r0, r1
	beq clear_bss
copy_data_loop:
	cmp r1, r2
    itt ne
	ldrne r3, [r0], #4
	strne r3, [r1], #4
	bne copy_data_loop
	
/*------------------------------------------------------------------------------	
 * Clear .bss
 */
clear_bss:
	ldr r0, =0
	ldr r1, =__bss_start__
	ldr r2, =__bss_end__
clear_bss_loop:
	cmp r1, r2
    it ne
	strne r0, [r1], #4
	bne clear_bss_loop

/*------------------------------------------------------------------------------	
 * Call global constructors
 */
call_glob_ctor:
	ldr r0, =__libc_init_array
    add lr, pc, #3
 	bx r0

/*------------------------------------------------------------------------------	
 * branch to main.
 */
branch_to_main: 	 
	mov	r0, #0		/*  no arguments  */
	mov	r1, #0		/*  no argv either */
    ldr pc, =main

ExitLoop:
    B ExitLoop

/*==============================================================================
 * NMI_Handler
 */
    .weak   NMI_Handler
    .type   NMI_Handler, %function
NMI_Handler:
    B .

/*==============================================================================
 * HardFault_Handler
 */
    .weak   HardFault_Handler
    .type   HardFault_Handler, %function
HardFault_Handler:
    B .

/*==============================================================================
 * MemManage_Handler
 */
    .weak   MemManage_Handler
    .type   MemManage_Handler, %function
MemManage_Handler:
    B .

/*==============================================================================
 * BusFault_Handler
 */
    .weak   BusFault_Handler
    .type   BusFault_Handler, %function
BusFault_Handler:
    B .

/*==============================================================================
 * UsageFault_Handler
 */
    .weak   UsageFault_Handler
    .type   UsageFault_Handler, %function
UsageFault_Handler:
    B .

/*==============================================================================
 * SVC_Handler
 */
    .weak   SVC_Handler
    .type   SVC_Handler, %function
SVC_Handler:
    B .

/*==============================================================================
 * DebugMon_Handler
 */
    .weak   DebugMon_Handler
    .type   DebugMon_Handler, %function
DebugMon_Handler:
    B .

/*==============================================================================
 * PendSV_Handler
 */
    .weak   PendSV_Handler
    .type   PendSV_Handler, %function
PendSV_Handler:
    B .

/*==============================================================================
 * SysTick_Handler
 */
    .weak   SysTick_Handler
    .type   SysTick_Handler, %function
SysTick_Handler:
    B .

/*==============================================================================
 * WdogWakeup_IRQHandler
 */
    .weak   WdogWakeup_IRQHandler
    .type   WdogWakeup_IRQHandler, %function
WdogWakeup_IRQHandler:
    B .

/*==============================================================================
 * BrownOut_1_5V_IRQHandler
 */
    .weak   BrownOut_1_5V_IRQHandler
    .type   BrownOut_1_5V_IRQHandler, %function
BrownOut_1_5V_IRQHandler:
    B .

/*==============================================================================
 * BrownOut_3_3V_IRQHandler
 */
    .weak   BrownOut_3_3V_IRQHandler
    .type   BrownOut_3_3V_IRQHandler, %function
BrownOut_3_3V_IRQHandler:
    B .

/*==============================================================================
 * RTC_Match_IRQHandler
 */
    .weak   RTC_Match_IRQHandler
    .type   RTC_Match_IRQHandler, %function
RTC_Match_IRQHandler:
    B .

/*==============================================================================
 * RTCIF_Pub_IRQHandler
 */
    .weak   RTCIF_Pub_IRQHandler
    .type   RTCIF_Pub_IRQHandler, %function
RTCIF_Pub_IRQHandler:
    B .

/*==============================================================================
 * EthernetMAC_IRQHandler
 */
    .weak   EthernetMAC_IRQHandler
    .type   EthernetMAC_IRQHandler, %function
EthernetMAC_IRQHandler:
    B .

/*==============================================================================
 * IAP_IRQHandler
 */
    .weak   IAP_IRQHandler
    .type   IAP_IRQHandler, %function
IAP_IRQHandler:
    B .

/*==============================================================================
 * ENVM0_IRQHandler
 */
    .weak   ENVM0_IRQHandler
    .type   ENVM0_IRQHandler, %function
ENVM0_IRQHandler:
    B .

/*==============================================================================
 * ENVM1_IRQHandler
 */
    .weak   ENVM1_IRQHandler
    .type   ENVM1_IRQHandler, %function
ENVM1_IRQHandler:
    B .

/*==============================================================================
 * DMA_IRQHandler
 */
    .weak   DMA_IRQHandler
    .type   DMA_IRQHandler, %function
DMA_IRQHandler:
    B .

/*==============================================================================
 * UART0_IRQHandler
 */
    .weak   UART0_IRQHandler
    .type   UART0_IRQHandler, %function
UART0_IRQHandler:
    B .

/*==============================================================================
 * UART1_IRQHandler
 */
    .weak   UART1_IRQHandler
    .type   UART1_IRQHandler, %function
UART1_IRQHandler:
    B .

/*==============================================================================
 * SPI0_IRQHandler
 */
    .weak   SPI0_IRQHandler
    .type   SPI0_IRQHandler, %function
SPI0_IRQHandler:
    B .

/*==============================================================================
 * SPI1_IRQHandler
 */
    .weak   SPI1_IRQHandler
    .type   SPI1_IRQHandler, %function
SPI1_IRQHandler:
    B .

/*==============================================================================
 * I2C0_IRQHandler
 */
    .weak   I2C0_IRQHandler
    .type   I2C0_IRQHandler, %function
I2C0_IRQHandler:
    B .

/*==============================================================================
 * I2C0_SMBAlert_IRQHandler
 */
    .weak   I2C0_SMBAlert_IRQHandler
    .type   I2C0_SMBAlert_IRQHandler, %function
I2C0_SMBAlert_IRQHandler:
    B .

/*==============================================================================
 * I2C0_SMBus_IRQHandler
 */
    .weak   I2C0_SMBus_IRQHandler
    .type   I2C0_SMBus_IRQHandler, %function
I2C0_SMBus_IRQHandler:
    B .

/*==============================================================================
 * I2C1_IRQHandler
 */
    .weak   I2C1_IRQHandler
    .type   I2C1_IRQHandler, %function
I2C1_IRQHandler:
    B .

/*==============================================================================
 * I2C1_SMBAlert_IRQHandler
 */
    .weak   I2C1_SMBAlert_IRQHandler
    .type   I2C1_SMBAlert_IRQHandler, %function
I2C1_SMBAlert_IRQHandler:
    B .

/*==============================================================================
 * I2C1_SMBus_IRQHandler
 */
    .weak   I2C1_SMBus_IRQHandler
    .type   I2C1_SMBus_IRQHandler, %function
I2C1_SMBus_IRQHandler:
    B .

/*==============================================================================
 * Timer1_IRQHandler
 */
    .weak   Timer1_IRQHandler
    .type   Timer1_IRQHandler, %function
Timer1_IRQHandler:
    B .

/*==============================================================================
 * Timer2_IRQHandler
 */
    .weak   Timer2_IRQHandler
    .type   Timer2_IRQHandler, %function
Timer2_IRQHandler:
    B .

/*==============================================================================
 * PLL_Lock_IRQHandler
 */
    .weak   PLL_Lock_IRQHandler
    .type   PLL_Lock_IRQHandler, %function
PLL_Lock_IRQHandler:
    B .

/*==============================================================================
 * PLL_LockLost_IRQHandler
 */
    .weak   PLL_LockLost_IRQHandler
    .type   PLL_LockLost_IRQHandler, %function
PLL_LockLost_IRQHandler:
    B .

/*==============================================================================
 * CommError_IRQHandler
 */
    .weak   CommError_IRQHandler
    .type   CommError_IRQHandler, %function
CommError_IRQHandler:
    B .

/*==============================================================================
 * Fabric_IRQHandler
 */
    .weak   Fabric_IRQHandler
    .type   Fabric_IRQHandler, %function
Fabric_IRQHandler:
    B .

/*==============================================================================
 * GPIO0_IRQHandler
 */
    .weak   GPIO0_IRQHandler
    .type   GPIO0_IRQHandler, %function
GPIO0_IRQHandler:
    B .

/*==============================================================================
 * GPIO1_IRQHandler
 */
    .weak   GPIO1_IRQHandler
    .type   GPIO1_IRQHandler, %function
GPIO1_IRQHandler:
    B .

/*==============================================================================
 * GPIO2_IRQHandler
 */
    .weak   GPIO2_IRQHandler
    .type   GPIO2_IRQHandler, %function
GPIO2_IRQHandler:
    B .

/*==============================================================================
 * GPIO3_IRQHandler
 */
    .weak   GPIO3_IRQHandler
    .type   GPIO3_IRQHandler, %function
GPIO3_IRQHandler:
    B .

/*==============================================================================
 * GPIO4_IRQHandler
 */
    .weak   GPIO4_IRQHandler
    .type   GPIO4_IRQHandler, %function
GPIO4_IRQHandler:
    B .

/*==============================================================================
 * GPIO5_IRQHandler
 */
    .weak   GPIO5_IRQHandler
    .type   GPIO5_IRQHandler, %function
GPIO5_IRQHandler:
    B .

/*==============================================================================
 * GPIO6_IRQHandler
 */
    .weak   GPIO6_IRQHandler
    .type   GPIO6_IRQHandler, %function
GPIO6_IRQHandler:
    B .

/*==============================================================================
 * GPIO7_IRQHandler
 */
    .weak   GPIO7_IRQHandler
    .type   GPIO7_IRQHandler, %function
GPIO7_IRQHandler:
    B .

/*==============================================================================
 * GPIO8_IRQHandler
 */
    .weak   GPIO8_IRQHandler
    .type   GPIO8_IRQHandler, %function
GPIO8_IRQHandler:
    B .

/*==============================================================================
 * GPIO9_IRQHandler
 */
    .weak   GPIO9_IRQHandler
    .type   GPIO9_IRQHandler, %function
GPIO9_IRQHandler:
    B .

/*==============================================================================
 * GPIO10_IRQHandler
 */
    .weak   GPIO10_IRQHandler
    .type   GPIO10_IRQHandler, %function
GPIO10_IRQHandler:
    B .

/*==============================================================================
 * GPIO11_IRQHandler
 */
    .weak   GPIO11_IRQHandler
    .type   GPIO11_IRQHandler, %function
GPIO11_IRQHandler:
    B .

/*==============================================================================
 * GPIO12_IRQHandler
 */
    .weak   GPIO12_IRQHandler
    .type   GPIO12_IRQHandler, %function
GPIO12_IRQHandler:
    B .

/*==============================================================================
 * GPIO13_IRQHandler
 */
    .weak   GPIO13_IRQHandler
    .type   GPIO13_IRQHandler, %function
GPIO13_IRQHandler:
    B .

/*==============================================================================
 * GPIO14_IRQHandler
 */
    .weak   GPIO14_IRQHandler
    .type   GPIO14_IRQHandler, %function
GPIO14_IRQHandler:
    B .

/*==============================================================================
 * GPIO15_IRQHandler
 */
    .weak   GPIO15_IRQHandler
    .type   GPIO15_IRQHandler, %function
GPIO15_IRQHandler:
    B .

/*==============================================================================
 * GPIO16_IRQHandler
 */
    .weak   GPIO16_IRQHandler
    .type   GPIO16_IRQHandler, %function
GPIO16_IRQHandler:
    B .

/*==============================================================================
 * GPIO17_IRQHandler
 */
    .weak   GPIO17_IRQHandler
    .type   GPIO17_IRQHandler, %function
GPIO17_IRQHandler:
    B .

/*==============================================================================
 * GPIO18_IRQHandler
 */
    .weak   GPIO18_IRQHandler
    .type   GPIO18_IRQHandler, %function
GPIO18_IRQHandler:
    B .

/*==============================================================================
 * GPIO19_IRQHandler
 */
    .weak   GPIO19_IRQHandler
    .type   GPIO19_IRQHandler, %function
GPIO19_IRQHandler:
    B .

/*==============================================================================
 * GPIO20_IRQHandler
 */
    .weak   GPIO20_IRQHandler
    .type   GPIO20_IRQHandler, %function
GPIO20_IRQHandler:
    B .

/*==============================================================================
 * GPIO21_IRQHandler
 */
    .weak   GPIO21_IRQHandler
    .type   GPIO21_IRQHandler, %function
GPIO21_IRQHandler:
    B .

/*==============================================================================
 * GPIO22_IRQHandler
 */
    .weak   GPIO22_IRQHandler
    .type   GPIO22_IRQHandler, %function
GPIO22_IRQHandler:
    B .

/*==============================================================================
 * GPIO23_IRQHandler
 */
    .weak   GPIO23_IRQHandler
    .type   GPIO23_IRQHandler, %function
GPIO23_IRQHandler:
    B .

/*==============================================================================
 * GPIO24_IRQHandler
 */
    .weak   GPIO24_IRQHandler
    .type   GPIO24_IRQHandler, %function
GPIO24_IRQHandler:
    B .

/*==============================================================================
 * GPIO25_IRQHandler
 */
    .weak   GPIO25_IRQHandler
    .type   GPIO25_IRQHandler, %function
GPIO25_IRQHandler:
    B .

/*==============================================================================
 * GPIO26_IRQHandler
 */
    .weak   GPIO26_IRQHandler
    .type   GPIO26_IRQHandler, %function
GPIO26_IRQHandler:
    B .

/*==============================================================================
 * GPIO27_IRQHandler
 */
    .weak   GPIO27_IRQHandler
    .type   GPIO27_IRQHandler, %function
GPIO27_IRQHandler:
    B .

/*==============================================================================
 * GPIO28_IRQHandler
 */
    .weak   GPIO28_IRQHandler
    .type   GPIO28_IRQHandler, %function
GPIO28_IRQHandler:
    B .

/*==============================================================================
 * GPIO29_IRQHandler
 */
    .weak   GPIO29_IRQHandler
    .type   GPIO29_IRQHandler, %function
GPIO29_IRQHandler:
    B .

/*==============================================================================
 * GPIO30_IRQHandler
 */
    .weak   GPIO30_IRQHandler
    .type   GPIO30_IRQHandler, %function
GPIO30_IRQHandler:
    B .

/*==============================================================================
 * GPIO31_IRQHandler
 */
    .weak   GPIO31_IRQHandler
    .type   GPIO31_IRQHandler, %function
GPIO31_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC0_Flag0_IRQHandler
 */
    .weak   ACE_PC0_Flag0_IRQHandler
    .type   ACE_PC0_Flag0_IRQHandler, %function
ACE_PC0_Flag0_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC0_Flag1_IRQHandler
 */
    .weak   ACE_PC0_Flag1_IRQHandler
    .type   ACE_PC0_Flag1_IRQHandler, %function
ACE_PC0_Flag1_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC0_Flag2_IRQHandler
 */
    .weak   ACE_PC0_Flag2_IRQHandler
    .type   ACE_PC0_Flag2_IRQHandler, %function
ACE_PC0_Flag2_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC0_Flag3_IRQHandler
 */
    .weak   ACE_PC0_Flag3_IRQHandler
    .type   ACE_PC0_Flag3_IRQHandler, %function
ACE_PC0_Flag3_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC1_Flag0_IRQHandler
 */
    .weak   ACE_PC1_Flag0_IRQHandler
    .type   ACE_PC1_Flag0_IRQHandler, %function
ACE_PC1_Flag0_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC1_Flag1_IRQHandler
 */
    .weak   ACE_PC1_Flag1_IRQHandler
    .type   ACE_PC1_Flag1_IRQHandler, %function
ACE_PC1_Flag1_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC1_Flag2_IRQHandler
 */
    .weak   ACE_PC1_Flag2_IRQHandler
    .type   ACE_PC1_Flag2_IRQHandler, %function
ACE_PC1_Flag2_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC1_Flag3_IRQHandler
 */
    .weak   ACE_PC1_Flag3_IRQHandler
    .type   ACE_PC1_Flag3_IRQHandler, %function
ACE_PC1_Flag3_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC2_Flag0_IRQHandler
 */
    .weak   ACE_PC2_Flag0_IRQHandler
    .type   ACE_PC2_Flag0_IRQHandler, %function
ACE_PC2_Flag0_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC2_Flag1_IRQHandler
 */
    .weak   ACE_PC2_Flag1_IRQHandler
    .type   ACE_PC2_Flag1_IRQHandler, %function
ACE_PC2_Flag1_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC2_Flag2_IRQHandler
 */
    .weak   ACE_PC2_Flag2_IRQHandler
    .type   ACE_PC2_Flag2_IRQHandler, %function
ACE_PC2_Flag2_IRQHandler:
    B .

/*==============================================================================
 * ACE_PC2_Flag3_IRQHandler
 */
    .weak   ACE_PC2_Flag3_IRQHandler
    .type   ACE_PC2_Flag3_IRQHandler, %function
ACE_PC2_Flag3_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC0_DataValid_IRQHandler
 */
    .weak   ACE_ADC0_DataValid_IRQHandler
    .type   ACE_ADC0_DataValid_IRQHandler, %function
ACE_ADC0_DataValid_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC1_DataValid_IRQHandler
 */
    .weak   ACE_ADC1_DataValid_IRQHandler
    .type   ACE_ADC1_DataValid_IRQHandler, %function
ACE_ADC1_DataValid_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC2_DataValid_IRQHandler
 */
    .weak   ACE_ADC2_DataValid_IRQHandler
    .type   ACE_ADC2_DataValid_IRQHandler, %function
ACE_ADC2_DataValid_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC0_CalDone_IRQHandler
 */
    .weak   ACE_ADC0_CalDone_IRQHandler
    .type   ACE_ADC0_CalDone_IRQHandler, %function
ACE_ADC0_CalDone_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC1_CalDone_IRQHandler
 */
    .weak   ACE_ADC1_CalDone_IRQHandler
    .type   ACE_ADC1_CalDone_IRQHandler, %function
ACE_ADC1_CalDone_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC2_CalDone_IRQHandler
 */
    .weak   ACE_ADC2_CalDone_IRQHandler
    .type   ACE_ADC2_CalDone_IRQHandler, %function
ACE_ADC2_CalDone_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC0_CalStart_IRQHandler
 */
    .weak   ACE_ADC0_CalStart_IRQHandler
    .type   ACE_ADC0_CalStart_IRQHandler, %function
ACE_ADC0_CalStart_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC1_CalStart_IRQHandler
 */
    .weak   ACE_ADC1_CalStart_IRQHandler
    .type   ACE_ADC1_CalStart_IRQHandler, %function
ACE_ADC1_CalStart_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC2_CalStart_IRQHandler
 */
    .weak   ACE_ADC2_CalStart_IRQHandler
    .type   ACE_ADC2_CalStart_IRQHandler, %function
ACE_ADC2_CalStart_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp0_Fall_IRQHandler
 */
    .weak   ACE_Comp0_Fall_IRQHandler
    .type   ACE_Comp0_Fall_IRQHandler, %function
ACE_Comp0_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp1_Fall_IRQHandler
 */
    .weak   ACE_Comp1_Fall_IRQHandler
    .type   ACE_Comp1_Fall_IRQHandler, %function
ACE_Comp1_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp2_Fall_IRQHandler
 */
    .weak   ACE_Comp2_Fall_IRQHandler
    .type   ACE_Comp2_Fall_IRQHandler, %function
ACE_Comp2_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp3_Fall_IRQHandler
 */
    .weak   ACE_Comp3_Fall_IRQHandler
    .type   ACE_Comp3_Fall_IRQHandler, %function
ACE_Comp3_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp4_Fall_IRQHandler
 */
    .weak   ACE_Comp4_Fall_IRQHandler
    .type   ACE_Comp4_Fall_IRQHandler, %function
ACE_Comp4_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp5_Fall_IRQHandler
 */
    .weak   ACE_Comp5_Fall_IRQHandler
    .type   ACE_Comp5_Fall_IRQHandler, %function
ACE_Comp5_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp6_Fall_IRQHandler
 */
    .weak   ACE_Comp6_Fall_IRQHandler
    .type   ACE_Comp6_Fall_IRQHandler, %function
ACE_Comp6_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp7_Fall_IRQHandler
 */
    .weak   ACE_Comp7_Fall_IRQHandler
    .type   ACE_Comp7_Fall_IRQHandler, %function
ACE_Comp7_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp8_Fall_IRQHandler
 */
    .weak   ACE_Comp8_Fall_IRQHandler
    .type   ACE_Comp8_Fall_IRQHandler, %function
ACE_Comp8_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp9_Fall_IRQHandler
 */
    .weak   ACE_Comp9_Fall_IRQHandler
    .type   ACE_Comp9_Fall_IRQHandler, %function
ACE_Comp9_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp10_Fall_IRQHandler
 */
    .weak   ACE_Comp10_Fall_IRQHandler
    .type   ACE_Comp10_Fall_IRQHandler, %function
ACE_Comp10_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp11_Fall_IRQHandler
 */
    .weak   ACE_Comp11_Fall_IRQHandler
    .type   ACE_Comp11_Fall_IRQHandler, %function
ACE_Comp11_Fall_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp0_Rise_IRQHandler
 */
    .weak   ACE_Comp0_Rise_IRQHandler
    .type   ACE_Comp0_Rise_IRQHandler, %function
ACE_Comp0_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp1_Rise_IRQHandler
 */
    .weak   ACE_Comp1_Rise_IRQHandler
    .type   ACE_Comp1_Rise_IRQHandler, %function
ACE_Comp1_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp2_Rise_IRQHandler
 */
    .weak   ACE_Comp2_Rise_IRQHandler
    .type   ACE_Comp2_Rise_IRQHandler, %function
ACE_Comp2_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp3_Rise_IRQHandler
 */
    .weak   ACE_Comp3_Rise_IRQHandler
    .type   ACE_Comp3_Rise_IRQHandler, %function
ACE_Comp3_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp4_Rise_IRQHandler
 */
    .weak   ACE_Comp4_Rise_IRQHandler
    .type   ACE_Comp4_Rise_IRQHandler, %function
ACE_Comp4_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp5_Rise_IRQHandler
 */
    .weak   ACE_Comp5_Rise_IRQHandler
    .type   ACE_Comp5_Rise_IRQHandler, %function
ACE_Comp5_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp6_Rise_IRQHandler
 */
    .weak   ACE_Comp6_Rise_IRQHandler
    .type   ACE_Comp6_Rise_IRQHandler, %function
ACE_Comp6_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp7_Rise_IRQHandler
 */
    .weak   ACE_Comp7_Rise_IRQHandler
    .type   ACE_Comp7_Rise_IRQHandler, %function
ACE_Comp7_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp8_Rise_IRQHandler
 */
    .weak   ACE_Comp8_Rise_IRQHandler
    .type   ACE_Comp8_Rise_IRQHandler, %function
ACE_Comp8_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp9_Rise_IRQHandler
 */
    .weak   ACE_Comp9_Rise_IRQHandler
    .type   ACE_Comp9_Rise_IRQHandler, %function
ACE_Comp9_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp10_Rise_IRQHandler
 */
    .weak   ACE_Comp10_Rise_IRQHandler
    .type   ACE_Comp10_Rise_IRQHandler, %function
ACE_Comp10_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_Comp11_Rise_IRQHandler
 */
    .weak   ACE_Comp11_Rise_IRQHandler
    .type   ACE_Comp11_Rise_IRQHandler, %function
ACE_Comp11_Rise_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC0_FifoFull_IRQHandler
 */
    .weak   ACE_ADC0_FifoFull_IRQHandler
    .type   ACE_ADC0_FifoFull_IRQHandler, %function
ACE_ADC0_FifoFull_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC0_FifoAFull_IRQHandler
 */
    .weak   ACE_ADC0_FifoAFull_IRQHandler
    .type   ACE_ADC0_FifoAFull_IRQHandler, %function
ACE_ADC0_FifoAFull_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC0_FifoEmpty_IRQHandler
 */
    .weak   ACE_ADC0_FifoEmpty_IRQHandler
    .type   ACE_ADC0_FifoEmpty_IRQHandler, %function
ACE_ADC0_FifoEmpty_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC1_FifoFull_IRQHandler
 */
    .weak   ACE_ADC1_FifoFull_IRQHandler
    .type   ACE_ADC1_FifoFull_IRQHandler, %function
ACE_ADC1_FifoFull_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC1_FifoAFull_IRQHandler
 */
    .weak   ACE_ADC1_FifoAFull_IRQHandler
    .type   ACE_ADC1_FifoAFull_IRQHandler, %function
ACE_ADC1_FifoAFull_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC1_FifoEmpty_IRQHandler
 */
    .weak   ACE_ADC1_FifoEmpty_IRQHandler
    .type   ACE_ADC1_FifoEmpty_IRQHandler, %function
ACE_ADC1_FifoEmpty_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC2_FifoFull_IRQHandler
 */
    .weak   ACE_ADC2_FifoFull_IRQHandler
    .type   ACE_ADC2_FifoFull_IRQHandler, %function
ACE_ADC2_FifoFull_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC2_FifoAFull_IRQHandler
 */
    .weak   ACE_ADC2_FifoAFull_IRQHandler
    .type   ACE_ADC2_FifoAFull_IRQHandler, %function
ACE_ADC2_FifoAFull_IRQHandler:
    B .

/*==============================================================================
 * ACE_ADC2_FifoEmpty_IRQHandler
 */
    .weak   ACE_ADC2_FifoEmpty_IRQHandler
    .type   ACE_ADC2_FifoEmpty_IRQHandler, %function
ACE_ADC2_FifoEmpty_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag0_IRQHandler
 */
    .weak   ACE_PPE_Flag0_IRQHandler
    .type   ACE_PPE_Flag0_IRQHandler, %function
ACE_PPE_Flag0_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag1_IRQHandler
 */
    .weak   ACE_PPE_Flag1_IRQHandler
    .type   ACE_PPE_Flag1_IRQHandler, %function
ACE_PPE_Flag1_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag2_IRQHandler
 */
    .weak   ACE_PPE_Flag2_IRQHandler
    .type   ACE_PPE_Flag2_IRQHandler, %function
ACE_PPE_Flag2_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag3_IRQHandler
 */
    .weak   ACE_PPE_Flag3_IRQHandler
    .type   ACE_PPE_Flag3_IRQHandler, %function
ACE_PPE_Flag3_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag4_IRQHandler
 */
    .weak   ACE_PPE_Flag4_IRQHandler
    .type   ACE_PPE_Flag4_IRQHandler, %function
ACE_PPE_Flag4_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag5_IRQHandler
 */
    .weak   ACE_PPE_Flag5_IRQHandler
    .type   ACE_PPE_Flag5_IRQHandler, %function
ACE_PPE_Flag5_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag6_IRQHandler
 */
    .weak   ACE_PPE_Flag6_IRQHandler
    .type   ACE_PPE_Flag6_IRQHandler, %function
ACE_PPE_Flag6_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag7_IRQHandler
 */
    .weak   ACE_PPE_Flag7_IRQHandler
    .type   ACE_PPE_Flag7_IRQHandler, %function
ACE_PPE_Flag7_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag8_IRQHandler
 */
    .weak   ACE_PPE_Flag8_IRQHandler
    .type   ACE_PPE_Flag8_IRQHandler, %function
ACE_PPE_Flag8_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag9_IRQHandler
 */
    .weak   ACE_PPE_Flag9_IRQHandler
    .type   ACE_PPE_Flag9_IRQHandler, %function
ACE_PPE_Flag9_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag10_IRQHandler
 */
    .weak   ACE_PPE_Flag10_IRQHandler
    .type   ACE_PPE_Flag10_IRQHandler, %function
ACE_PPE_Flag10_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag11_IRQHandler
 */
    .weak   ACE_PPE_Flag11_IRQHandler
    .type   ACE_PPE_Flag11_IRQHandler, %function
ACE_PPE_Flag11_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag12_IRQHandler
 */
    .weak   ACE_PPE_Flag12_IRQHandler
    .type   ACE_PPE_Flag12_IRQHandler, %function
ACE_PPE_Flag12_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag13_IRQHandler
 */
    .weak   ACE_PPE_Flag13_IRQHandler
    .type   ACE_PPE_Flag13_IRQHandler, %function
ACE_PPE_Flag13_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag14_IRQHandler
 */
    .weak   ACE_PPE_Flag14_IRQHandler
    .type   ACE_PPE_Flag14_IRQHandler, %function
ACE_PPE_Flag14_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag15_IRQHandler
 */
    .weak   ACE_PPE_Flag15_IRQHandler
    .type   ACE_PPE_Flag15_IRQHandler, %function
ACE_PPE_Flag15_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag16_IRQHandler
 */
    .weak   ACE_PPE_Flag16_IRQHandler
    .type   ACE_PPE_Flag16_IRQHandler, %function
ACE_PPE_Flag16_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag17_IRQHandler
 */
    .weak   ACE_PPE_Flag17_IRQHandler
    .type   ACE_PPE_Flag17_IRQHandler, %function
ACE_PPE_Flag17_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag18_IRQHandler
 */
    .weak   ACE_PPE_Flag18_IRQHandler
    .type   ACE_PPE_Flag18_IRQHandler, %function
ACE_PPE_Flag18_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag19_IRQHandler
 */
    .weak   ACE_PPE_Flag19_IRQHandler
    .type   ACE_PPE_Flag19_IRQHandler, %function
ACE_PPE_Flag19_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag20_IRQHandler
 */
    .weak   ACE_PPE_Flag20_IRQHandler
    .type   ACE_PPE_Flag20_IRQHandler, %function
ACE_PPE_Flag20_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag21_IRQHandler
 */
    .weak   ACE_PPE_Flag21_IRQHandler
    .type   ACE_PPE_Flag21_IRQHandler, %function
ACE_PPE_Flag21_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag22_IRQHandler
 */
    .weak   ACE_PPE_Flag22_IRQHandler
    .type   ACE_PPE_Flag22_IRQHandler, %function
ACE_PPE_Flag22_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag23_IRQHandler
 */
    .weak   ACE_PPE_Flag23_IRQHandler
    .type   ACE_PPE_Flag23_IRQHandler, %function
ACE_PPE_Flag23_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag24_IRQHandler
 */
    .weak   ACE_PPE_Flag24_IRQHandler
    .type   ACE_PPE_Flag24_IRQHandler, %function
ACE_PPE_Flag24_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag25_IRQHandler
 */
    .weak   ACE_PPE_Flag25_IRQHandler
    .type   ACE_PPE_Flag25_IRQHandler, %function
ACE_PPE_Flag25_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag26_IRQHandler
 */
    .weak   ACE_PPE_Flag26_IRQHandler
    .type   ACE_PPE_Flag26_IRQHandler, %function
ACE_PPE_Flag26_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag27_IRQHandler
 */
    .weak   ACE_PPE_Flag27_IRQHandler
    .type   ACE_PPE_Flag27_IRQHandler, %function
ACE_PPE_Flag27_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag28_IRQHandler
 */
    .weak   ACE_PPE_Flag28_IRQHandler
    .type   ACE_PPE_Flag28_IRQHandler, %function
ACE_PPE_Flag28_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag29_IRQHandler
 */
    .weak   ACE_PPE_Flag29_IRQHandler
    .type   ACE_PPE_Flag29_IRQHandler, %function
ACE_PPE_Flag29_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag30_IRQHandler
 */
    .weak   ACE_PPE_Flag30_IRQHandler
    .type   ACE_PPE_Flag30_IRQHandler, %function
ACE_PPE_Flag30_IRQHandler:
    B .

/*==============================================================================
 * ACE_PPE_Flag31_IRQHandler
 */
    .weak   ACE_PPE_Flag31_IRQHandler
    .type   ACE_PPE_Flag31_IRQHandler, %function
ACE_PPE_Flag31_IRQHandler:
    B .

.end
