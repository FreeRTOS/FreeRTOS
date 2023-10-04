;/******************** (C) COPYRIGHT 2011 STMicroelectronics ********************
;* File Name          : startup_stm32f4xx.s
;* Author             : MCD Application Team
;* Version            : V1.0.0
;* Date               : 30-September-2011
;* Description        : STM32F4xx devices vector table for EWARM toolchain.
;*                      This module performs:
;*                      - Set the initial SP
;*                      - Set the initial PC == _iar_program_start,
;*                      - Set the vector table entries with the exceptions ISR 
;*                        address.
;*                      - Configure the system clock and the external SRAM mounted on 
;*                        STM324xG-EVAL board to be used as data memory (optional, 
;*                        to be enabled by user)
;*                      - Branches to main in the C library (which eventually
;*                        calls main()).
;*                      After Reset the Cortex-M4 processor is in Thread mode,
;*                      priority is Privileged, and the Stack is set to Main.
;********************************************************************************
;* THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
;* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
;* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
;* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
;* CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
;* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;*******************************************************************************/
;
;
; The modules in this file are included in the libraries, and may be replaced
; by any user-defined modules that define the PUBLIC symbol _program_start or
; a user defined start symbol.
; To override the cstartup defined in the library, simply add your modified
; version to the workbench project.
;
; The vector table is normally located at address 0.
; When debugging in RAM, it can be located in RAM, aligned to at least 2^6.
; The name "__vector_table" has special meaning for C-SPY:
; it is where the SP start value is found, and the NVIC vector
; table register (VTOR) is initialized to this address if != 0.
;
; Cortex-M version
;

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION CSTACK:DATA:NOROOT(3)

        SECTION .intvec:CODE:NOROOT(2)

        EXTERN  __iar_program_start
        EXTERN  SystemInit
        PUBLIC  __vector_table

        DATA
__vector_table
        DCD     sfe(CSTACK)
        DCD     Reset_Handler             ; Reset Handler

        DCD     NMI_Handler               ; NMI Handler
        DCD     HardFault_Handler         ; Hard Fault Handler
        DCD     MemManage_Handler         ; MPU Fault Handler
        DCD     BusFault_Handler          ; Bus Fault Handler
        DCD     UsageFault_Handler        ; Usage Fault Handler
        DCD     0                         ; Reserved
        DCD     0                         ; Reserved
        DCD     0                         ; Reserved
        DCD     0                         ; Reserved
        DCD     SVC_Handler               ; SVCall Handler
        DCD     DebugMon_Handler          ; Debug Monitor Handler
        DCD     0                         ; Reserved
        DCD     PendSV_Handler            ; PendSV Handler
        DCD     SysTick_Handler           ; SysTick Handler

         ; External Interrupts
        DCD     WWDG_IRQHandler                   ; Window WatchDog                                        
        DCD     PVD_IRQHandler                    ; PVD through EXTI Line detection                        
        DCD     TAMP_STAMP_IRQHandler             ; Tamper and TimeStamps through the EXTI line            
        DCD     RTC_WKUP_IRQHandler               ; RTC Wakeup through the EXTI line                       
        DCD     FLASH_IRQHandler                  ; FLASH                                           
        DCD     RCC_IRQHandler                    ; RCC                                             
        DCD     EXTI0_IRQHandler                  ; EXTI Line0                                             
        DCD     EXTI1_IRQHandler                  ; EXTI Line1                                             
        DCD     EXTI2_IRQHandler                  ; EXTI Line2                                             
        DCD     EXTI3_IRQHandler                  ; EXTI Line3                                             
        DCD     EXTI4_IRQHandler                  ; EXTI Line4                                             
        DCD     DMA1_Stream0_IRQHandler           ; DMA1 Stream 0                                   
        DCD     DMA1_Stream1_IRQHandler           ; DMA1 Stream 1                                   
        DCD     DMA1_Stream2_IRQHandler           ; DMA1 Stream 2                                   
        DCD     DMA1_Stream3_IRQHandler           ; DMA1 Stream 3                                   
        DCD     DMA1_Stream4_IRQHandler           ; DMA1 Stream 4                                   
        DCD     DMA1_Stream5_IRQHandler           ; DMA1 Stream 5                                   
        DCD     DMA1_Stream6_IRQHandler           ; DMA1 Stream 6                                   
        DCD     ADC_IRQHandler                    ; ADC1, ADC2 and ADC3s                            
        DCD     CAN1_TX_IRQHandler                ; CAN1 TX                                                
        DCD     CAN1_RX0_IRQHandler               ; CAN1 RX0                                               
        DCD     CAN1_RX1_IRQHandler               ; CAN1 RX1                                               
        DCD     CAN1_SCE_IRQHandler               ; CAN1 SCE                                               
        DCD     EXTI9_5_IRQHandler                ; External Line[9:5]s                                    
        DCD     TIM1_BRK_TIM9_IRQHandler          ; TIM1 Break and TIM9                   
        DCD     TIM1_UP_TIM10_IRQHandler          ; TIM1 Update and TIM10                 
        DCD     TIM1_TRG_COM_TIM11_IRQHandler     ; TIM1 Trigger and Commutation and TIM11
        DCD     TIM1_CC_IRQHandler                ; TIM1 Capture Compare                                   
        DCD     TIM2_IRQHandler                   ; TIM2                                            
        DCD     TIM3_IRQHandler                   ; TIM3                                            
        DCD     TIM4_IRQHandler                   ; TIM4                                            
        DCD     I2C1_EV_IRQHandler                ; I2C1 Event                                             
        DCD     I2C1_ER_IRQHandler                ; I2C1 Error                                             
        DCD     I2C2_EV_IRQHandler                ; I2C2 Event                                             
        DCD     I2C2_ER_IRQHandler                ; I2C2 Error                                               
        DCD     SPI1_IRQHandler                   ; SPI1                                            
        DCD     SPI2_IRQHandler                   ; SPI2                                            
        DCD     USART1_IRQHandler                 ; USART1                                          
        DCD     USART2_IRQHandler                 ; USART2                                          
        DCD     USART3_IRQHandler                 ; USART3                                          
        DCD     EXTI15_10_IRQHandler              ; External Line[15:10]s                                  
        DCD     RTC_Alarm_IRQHandler              ; RTC Alarm (A and B) through EXTI Line                  
        DCD     OTG_FS_WKUP_IRQHandler            ; USB OTG FS Wakeup through EXTI line                        
        DCD     TIM8_BRK_TIM12_IRQHandler         ; TIM8 Break and TIM12                  
        DCD     TIM8_UP_TIM13_IRQHandler          ; TIM8 Update and TIM13                 
        DCD     TIM8_TRG_COM_TIM14_IRQHandler     ; TIM8 Trigger and Commutation and TIM14
        DCD     TIM8_CC_IRQHandler                ; TIM8 Capture Compare                                   
        DCD     DMA1_Stream7_IRQHandler           ; DMA1 Stream7                                           
        DCD     FSMC_IRQHandler                   ; FSMC                                            
        DCD     SDIO_IRQHandler                   ; SDIO                                            
        DCD     TIM5_IRQHandler                   ; TIM5                                            
        DCD     SPI3_IRQHandler                   ; SPI3                                            
        DCD     UART4_IRQHandler                  ; UART4                                           
        DCD     UART5_IRQHandler                  ; UART5                                           
        DCD     TIM6_DAC_IRQHandler               ; TIM6 and DAC1&2 underrun errors                   
        DCD     TIM7_IRQHandler                   ; TIM7                   
        DCD     DMA2_Stream0_IRQHandler           ; DMA2 Stream 0                                   
        DCD     DMA2_Stream1_IRQHandler           ; DMA2 Stream 1                                   
        DCD     DMA2_Stream2_IRQHandler           ; DMA2 Stream 2                                   
        DCD     DMA2_Stream3_IRQHandler           ; DMA2 Stream 3                                   
        DCD     DMA2_Stream4_IRQHandler           ; DMA2 Stream 4                                   
        DCD     ETH_IRQHandler                    ; Ethernet                                        
        DCD     ETH_WKUP_IRQHandler               ; Ethernet Wakeup through EXTI line                      
        DCD     CAN2_TX_IRQHandler                ; CAN2 TX                                                
        DCD     CAN2_RX0_IRQHandler               ; CAN2 RX0                                               
        DCD     CAN2_RX1_IRQHandler               ; CAN2 RX1                                               
        DCD     CAN2_SCE_IRQHandler               ; CAN2 SCE                                               
        DCD     OTG_FS_IRQHandler                 ; USB OTG FS                                      
        DCD     DMA2_Stream5_IRQHandler           ; DMA2 Stream 5                                   
        DCD     DMA2_Stream6_IRQHandler           ; DMA2 Stream 6                                   
        DCD     DMA2_Stream7_IRQHandler           ; DMA2 Stream 7                                   
        DCD     USART6_IRQHandler                 ; USART6                                           
        DCD     I2C3_EV_IRQHandler                ; I2C3 event                                             
        DCD     I2C3_ER_IRQHandler                ; I2C3 error                                             
        DCD     OTG_HS_EP1_OUT_IRQHandler         ; USB OTG HS End Point 1 Out                      
        DCD     OTG_HS_EP1_IN_IRQHandler          ; USB OTG HS End Point 1 In                       
        DCD     OTG_HS_WKUP_IRQHandler            ; USB OTG HS Wakeup through EXTI                         
        DCD     OTG_HS_IRQHandler                 ; USB OTG HS                                      
        DCD     DCMI_IRQHandler                   ; DCMI                                            
        DCD     CRYP_IRQHandler                   ; CRYP crypto                                     
        DCD     HASH_RNG_IRQHandler               ; Hash and Rng
        DCD     FPU_IRQHandler                    ; FPU

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Default interrupt handlers.
;;
        THUMB
        PUBWEAK Reset_Handler
        SECTION .text:CODE:REORDER(2)
Reset_Handler

        LDR     R0, =SystemInit
        BLX     R0
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

        PUBWEAK WWDG_IRQHandler
        SECTION .text:CODE:REORDER(1)
WWDG_IRQHandler  
        B WWDG_IRQHandler

        PUBWEAK PVD_IRQHandler
        SECTION .text:CODE:REORDER(1)
PVD_IRQHandler  
        B PVD_IRQHandler

        PUBWEAK TAMP_STAMP_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TAMP_STAMP_IRQHandler  
        B TAMP_STAMP_IRQHandler

        PUBWEAK RTC_WKUP_IRQHandler
        SECTION .text:CODE:REORDER(1)  
RTC_WKUP_IRQHandler  
        B RTC_WKUP_IRQHandler

        PUBWEAK FLASH_IRQHandler
        SECTION .text:CODE:REORDER(1)
FLASH_IRQHandler  
        B FLASH_IRQHandler

        PUBWEAK RCC_IRQHandler
        SECTION .text:CODE:REORDER(1)
RCC_IRQHandler  
        B RCC_IRQHandler

        PUBWEAK EXTI0_IRQHandler
        SECTION .text:CODE:REORDER(1)
EXTI0_IRQHandler  
        B EXTI0_IRQHandler

        PUBWEAK EXTI1_IRQHandler
        SECTION .text:CODE:REORDER(1)
EXTI1_IRQHandler  
        B EXTI1_IRQHandler

        PUBWEAK EXTI2_IRQHandler
        SECTION .text:CODE:REORDER(1)
EXTI2_IRQHandler  
        B EXTI2_IRQHandler

        PUBWEAK EXTI3_IRQHandler
        SECTION .text:CODE:REORDER(1)
EXTI3_IRQHandler
        B EXTI3_IRQHandler

        PUBWEAK EXTI4_IRQHandler
        SECTION .text:CODE:REORDER(1)    
EXTI4_IRQHandler  
        B EXTI4_IRQHandler

        PUBWEAK DMA1_Stream0_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream0_IRQHandler  
        B DMA1_Stream0_IRQHandler

        PUBWEAK DMA1_Stream1_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream1_IRQHandler  
        B DMA1_Stream1_IRQHandler

        PUBWEAK DMA1_Stream2_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream2_IRQHandler  
        B DMA1_Stream2_IRQHandler

        PUBWEAK DMA1_Stream3_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream3_IRQHandler  
        B DMA1_Stream3_IRQHandler

        PUBWEAK DMA1_Stream4_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream4_IRQHandler  
        B DMA1_Stream4_IRQHandler

        PUBWEAK DMA1_Stream5_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream5_IRQHandler  
        B DMA1_Stream5_IRQHandler

        PUBWEAK DMA1_Stream6_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream6_IRQHandler  
        B DMA1_Stream6_IRQHandler

        PUBWEAK ADC_IRQHandler
        SECTION .text:CODE:REORDER(1)
ADC_IRQHandler  
        B ADC_IRQHandler

        PUBWEAK CAN1_TX_IRQHandler
        SECTION .text:CODE:REORDER(1) 
CAN1_TX_IRQHandler  
        B CAN1_TX_IRQHandler

        PUBWEAK CAN1_RX0_IRQHandler
        SECTION .text:CODE:REORDER(1)  
CAN1_RX0_IRQHandler  
        B CAN1_RX0_IRQHandler

        PUBWEAK CAN1_RX1_IRQHandler
        SECTION .text:CODE:REORDER(1)  
CAN1_RX1_IRQHandler  
        B CAN1_RX1_IRQHandler

        PUBWEAK CAN1_SCE_IRQHandler
        SECTION .text:CODE:REORDER(1)  
CAN1_SCE_IRQHandler  
        B CAN1_SCE_IRQHandler

        PUBWEAK EXTI9_5_IRQHandler
        SECTION .text:CODE:REORDER(1) 
EXTI9_5_IRQHandler  
        B EXTI9_5_IRQHandler

        PUBWEAK TIM1_BRK_TIM9_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TIM1_BRK_TIM9_IRQHandler  
        B TIM1_BRK_TIM9_IRQHandler

        PUBWEAK TIM1_UP_TIM10_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TIM1_UP_TIM10_IRQHandler  
        B TIM1_UP_TIM10_IRQHandler

        PUBWEAK TIM1_TRG_COM_TIM11_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TIM1_TRG_COM_TIM11_IRQHandler  
        B TIM1_TRG_COM_TIM11_IRQHandler
        
        PUBWEAK TIM1_CC_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TIM1_CC_IRQHandler  
        B TIM1_CC_IRQHandler

        PUBWEAK TIM2_IRQHandler
        SECTION .text:CODE:REORDER(1)
TIM2_IRQHandler  
        B TIM2_IRQHandler

        PUBWEAK TIM3_IRQHandler
        SECTION .text:CODE:REORDER(1)
TIM3_IRQHandler  
        B TIM3_IRQHandler

        PUBWEAK TIM4_IRQHandler
        SECTION .text:CODE:REORDER(1)
TIM4_IRQHandler  
        B TIM4_IRQHandler

        PUBWEAK I2C1_EV_IRQHandler
        SECTION .text:CODE:REORDER(1) 
I2C1_EV_IRQHandler  
        B I2C1_EV_IRQHandler

        PUBWEAK I2C1_ER_IRQHandler
        SECTION .text:CODE:REORDER(1) 
I2C1_ER_IRQHandler  
        B I2C1_ER_IRQHandler

        PUBWEAK I2C2_EV_IRQHandler
        SECTION .text:CODE:REORDER(1) 
I2C2_EV_IRQHandler  
        B I2C2_EV_IRQHandler

        PUBWEAK I2C2_ER_IRQHandler
        SECTION .text:CODE:REORDER(1) 
I2C2_ER_IRQHandler  
        B I2C2_ER_IRQHandler

        PUBWEAK SPI1_IRQHandler
        SECTION .text:CODE:REORDER(1)
SPI1_IRQHandler  
        B SPI1_IRQHandler

        PUBWEAK SPI2_IRQHandler
        SECTION .text:CODE:REORDER(1)
SPI2_IRQHandler  
        B SPI2_IRQHandler

        PUBWEAK USART1_IRQHandler
        SECTION .text:CODE:REORDER(1)
USART1_IRQHandler  
        B USART1_IRQHandler

        PUBWEAK USART2_IRQHandler
        SECTION .text:CODE:REORDER(1)
USART2_IRQHandler  
        B USART2_IRQHandler

        PUBWEAK USART3_IRQHandler
        SECTION .text:CODE:REORDER(1)
USART3_IRQHandler  
        B USART3_IRQHandler

        PUBWEAK EXTI15_10_IRQHandler
        SECTION .text:CODE:REORDER(1)   
EXTI15_10_IRQHandler  
        B EXTI15_10_IRQHandler

        PUBWEAK RTC_Alarm_IRQHandler
        SECTION .text:CODE:REORDER(1)   
RTC_Alarm_IRQHandler  
        B RTC_Alarm_IRQHandler

        PUBWEAK OTG_FS_WKUP_IRQHandler
        SECTION .text:CODE:REORDER(1)    
OTG_FS_WKUP_IRQHandler  
        B OTG_FS_WKUP_IRQHandler
      
        PUBWEAK TIM8_BRK_TIM12_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TIM8_BRK_TIM12_IRQHandler  
        B TIM8_BRK_TIM12_IRQHandler

        PUBWEAK TIM8_UP_TIM13_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TIM8_UP_TIM13_IRQHandler  
        B TIM8_UP_TIM13_IRQHandler

        PUBWEAK TIM8_TRG_COM_TIM14_IRQHandler
        SECTION .text:CODE:REORDER(1)    
TIM8_TRG_COM_TIM14_IRQHandler  
        B TIM8_TRG_COM_TIM14_IRQHandler

        PUBWEAK TIM8_CC_IRQHandler
        SECTION .text:CODE:REORDER(1) 
TIM8_CC_IRQHandler  
        B TIM8_CC_IRQHandler

        PUBWEAK DMA1_Stream7_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA1_Stream7_IRQHandler  
        B DMA1_Stream7_IRQHandler

        PUBWEAK FSMC_IRQHandler
        SECTION .text:CODE:REORDER(1)
FSMC_IRQHandler  
        B FSMC_IRQHandler

        PUBWEAK SDIO_IRQHandler
        SECTION .text:CODE:REORDER(1)
SDIO_IRQHandler  
        B SDIO_IRQHandler

        PUBWEAK TIM5_IRQHandler
        SECTION .text:CODE:REORDER(1)
TIM5_IRQHandler  
        B TIM5_IRQHandler

        PUBWEAK SPI3_IRQHandler
        SECTION .text:CODE:REORDER(1)
SPI3_IRQHandler  
        B SPI3_IRQHandler

        PUBWEAK UART4_IRQHandler
        SECTION .text:CODE:REORDER(1)
UART4_IRQHandler  
        B UART4_IRQHandler

        PUBWEAK UART5_IRQHandler
        SECTION .text:CODE:REORDER(1)
UART5_IRQHandler  
        B UART5_IRQHandler

        PUBWEAK TIM6_DAC_IRQHandler
        SECTION .text:CODE:REORDER(1)   
TIM6_DAC_IRQHandler  
        B TIM6_DAC_IRQHandler

        PUBWEAK TIM7_IRQHandler
        SECTION .text:CODE:REORDER(1)   
TIM7_IRQHandler  
        B TIM7_IRQHandler

        PUBWEAK DMA2_Stream0_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream0_IRQHandler  
        B DMA2_Stream0_IRQHandler

        PUBWEAK DMA2_Stream1_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream1_IRQHandler  
        B DMA2_Stream1_IRQHandler

        PUBWEAK DMA2_Stream2_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream2_IRQHandler  
        B DMA2_Stream2_IRQHandler

        PUBWEAK DMA2_Stream3_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream3_IRQHandler  
        B DMA2_Stream3_IRQHandler

        PUBWEAK DMA2_Stream4_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream4_IRQHandler  
        B DMA2_Stream4_IRQHandler

        PUBWEAK ETH_IRQHandler
        SECTION .text:CODE:REORDER(1)
ETH_IRQHandler  
        B ETH_IRQHandler

        PUBWEAK ETH_WKUP_IRQHandler
        SECTION .text:CODE:REORDER(1)  
ETH_WKUP_IRQHandler  
        B ETH_WKUP_IRQHandler

        PUBWEAK CAN2_TX_IRQHandler
        SECTION .text:CODE:REORDER(1) 
CAN2_TX_IRQHandler  
        B CAN2_TX_IRQHandler

        PUBWEAK CAN2_RX0_IRQHandler
        SECTION .text:CODE:REORDER(1)  
CAN2_RX0_IRQHandler  
        B CAN2_RX0_IRQHandler

        PUBWEAK CAN2_RX1_IRQHandler
        SECTION .text:CODE:REORDER(1)  
CAN2_RX1_IRQHandler  
        B CAN2_RX1_IRQHandler

        PUBWEAK CAN2_SCE_IRQHandler
        SECTION .text:CODE:REORDER(1)  
CAN2_SCE_IRQHandler  
        B CAN2_SCE_IRQHandler

        PUBWEAK OTG_FS_IRQHandler
        SECTION .text:CODE:REORDER(1)
OTG_FS_IRQHandler  
        B OTG_FS_IRQHandler

        PUBWEAK DMA2_Stream5_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream5_IRQHandler  
        B DMA2_Stream5_IRQHandler

        PUBWEAK DMA2_Stream6_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream6_IRQHandler  
        B DMA2_Stream6_IRQHandler

        PUBWEAK DMA2_Stream7_IRQHandler
        SECTION .text:CODE:REORDER(1)    
DMA2_Stream7_IRQHandler  
        B DMA2_Stream7_IRQHandler

        PUBWEAK USART6_IRQHandler
        SECTION .text:CODE:REORDER(1)
USART6_IRQHandler  
        B USART6_IRQHandler

        PUBWEAK I2C3_EV_IRQHandler
        SECTION .text:CODE:REORDER(1) 
I2C3_EV_IRQHandler  
        B I2C3_EV_IRQHandler

        PUBWEAK I2C3_ER_IRQHandler
        SECTION .text:CODE:REORDER(1) 
I2C3_ER_IRQHandler  
        B I2C3_ER_IRQHandler

        PUBWEAK OTG_HS_EP1_OUT_IRQHandler
        SECTION .text:CODE:REORDER(1)    
OTG_HS_EP1_OUT_IRQHandler  
        B OTG_HS_EP1_OUT_IRQHandler

        PUBWEAK OTG_HS_EP1_IN_IRQHandler
        SECTION .text:CODE:REORDER(1)    
OTG_HS_EP1_IN_IRQHandler  
        B OTG_HS_EP1_IN_IRQHandler

        PUBWEAK OTG_HS_WKUP_IRQHandler
        SECTION .text:CODE:REORDER(1)    
OTG_HS_WKUP_IRQHandler  
        B OTG_HS_WKUP_IRQHandler

        PUBWEAK OTG_HS_IRQHandler
        SECTION .text:CODE:REORDER(1)
OTG_HS_IRQHandler  
        B OTG_HS_IRQHandler

        PUBWEAK DCMI_IRQHandler
        SECTION .text:CODE:REORDER(1)
DCMI_IRQHandler  
        B DCMI_IRQHandler

        PUBWEAK CRYP_IRQHandler
        SECTION .text:CODE:REORDER(1)
CRYP_IRQHandler  
        B CRYP_IRQHandler

        PUBWEAK HASH_RNG_IRQHandler
        SECTION .text:CODE:REORDER(1)  
HASH_RNG_IRQHandler  
        B HASH_RNG_IRQHandler

        PUBWEAK FPU_IRQHandler
        SECTION .text:CODE:REORDER(1)  
FPU_IRQHandler  
        B FPU_IRQHandler

        END
/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
