;/*******************************************************************************
; * SmartFusion startup code for Keil-MDK.
; *
; * This file is based on an ARM provided example.
; *
; * SVN $Revision: 2536 $
; * SVN $Date: 2010-04-08 16:57:12 +0100 (Thu, 08 Apr 2010) $
; */

; *------- <<< Use Configuration Wizard in Context Menu >>> ------------------


; <h> Stack Configuration
;   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>

Stack_Size      EQU     0x00002000

                AREA    STACK, NOINIT, READWRITE, ALIGN=3
Stack_Mem       SPACE   Stack_Size
__initial_sp


; <h> Heap Configuration
;   <o>  Heap Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>

Heap_Size       EQU     0x00000000

                AREA    HEAP, NOINIT, READWRITE, ALIGN=3
__heap_base
Heap_Mem        SPACE   Heap_Size
__heap_limit


                PRESERVE8
                THUMB


;-------------------------------------------------------------------------------
; Vector Table Mapped to Address 0 at Reset
                AREA    RESET, DATA, READONLY
                EXPORT  __Vectors
                EXPORT  __Vectors_End
                EXPORT  __Vectors_Size
				

__Vectors       DCD     __initial_sp               ; Top of Stack
                DCD     Reset_Handler              ; Reset Handler
                DCD     NMI_Handler                ; NMI Handler
                DCD     HardFault_Handler          ; Hard Fault Handler
                DCD     MemManage_Handler          ; MPU Fault Handler
                DCD     BusFault_Handler           ; Bus Fault Handler
                DCD     UsageFault_Handler         ; Usage Fault Handler
                DCD     0                          ; Reserved
                DCD     0                          ; Reserved
                DCD     0                          ; Reserved
                DCD     0                          ; Reserved
                DCD     SVC_Handler                ; SVCall Handler
                DCD     DebugMon_Handler           ; Debug Monitor Handler
                DCD     0                          ; Reserved
                DCD     PendSV_Handler             ; PendSV Handler
                DCD     SysTick_Handler            ; SysTick Handler

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

__Vectors_End

__Vectors_Size 	EQU 	__Vectors_End - __Vectors

                AREA    |.text|, CODE, READONLY



;-------------------------------------------------------------------------------
; Reset Handler
;
Reset_Handler   PROC
                EXPORT  Reset_Handler             [WEAK]
                IMPORT  SystemInit
                IMPORT  __main
                LDR     R0, =SystemInit
                BLX     R0
                LDR     R0, =__main
                BX      R0
                ENDP

;-------------------------------------------------------------------------------
; Dummy Exception Handlers (infinite loops which can be modified)                

NMI_Handler     PROC
                EXPORT  NMI_Handler                [WEAK]
                B       .
                ENDP
HardFault_Handler\
                PROC
                EXPORT  HardFault_Handler          [WEAK]
                B       .
                ENDP
MemManage_Handler\
                PROC
                EXPORT  MemManage_Handler          [WEAK]
                B       .
                ENDP
BusFault_Handler\
                PROC
                EXPORT  BusFault_Handler           [WEAK]
                B       .
                ENDP
UsageFault_Handler\
                PROC
                EXPORT  UsageFault_Handler         [WEAK]
                B       .
                ENDP
SVC_Handler     PROC
                EXPORT  SVC_Handler                [WEAK]
                B       .
                ENDP
DebugMon_Handler\
                PROC
                EXPORT  DebugMon_Handler           [WEAK]
                B       .
                ENDP
PendSV_Handler  PROC
                EXPORT  PendSV_Handler             [WEAK]
                B       .
                ENDP
SysTick_Handler PROC
                EXPORT  SysTick_Handler            [WEAK]
                B       .
                ENDP

Default_Handler PROC

                EXPORT  WdogWakeup_IRQHandler           [WEAK]
                EXPORT  BrownOut_1_5V_IRQHandler        [WEAK]
                EXPORT  BrownOut_3_3V_IRQHandler        [WEAK]
                EXPORT  RTC_Match_IRQHandler            [WEAK]
                EXPORT  RTCIF_Pub_IRQHandler            [WEAK]
                EXPORT  EthernetMAC_IRQHandler          [WEAK]
                EXPORT  IAP_IRQHandler                  [WEAK]
                EXPORT  ENVM0_IRQHandler                [WEAK]
                EXPORT  ENVM1_IRQHandler                [WEAK]
                EXPORT  DMA_IRQHandler                  [WEAK]
                EXPORT  UART0_IRQHandler                [WEAK]
                EXPORT  UART1_IRQHandler                [WEAK]
                EXPORT  SPI0_IRQHandler                 [WEAK]
                EXPORT  SPI1_IRQHandler                 [WEAK]
                EXPORT  I2C0_IRQHandler                 [WEAK]
                EXPORT  I2C0_SMBAlert_IRQHandler        [WEAK]
                EXPORT  I2C0_SMBus_IRQHandler           [WEAK]
                EXPORT  I2C1_IRQHandler                 [WEAK]
                EXPORT  I2C1_SMBAlert_IRQHandler        [WEAK]
                EXPORT  I2C1_SMBus_IRQHandler           [WEAK]
                EXPORT  Timer1_IRQHandler               [WEAK]
                EXPORT  Timer2_IRQHandler               [WEAK]
                EXPORT  PLL_Lock_IRQHandler             [WEAK]
                EXPORT  PLL_LockLost_IRQHandler         [WEAK]
                EXPORT  CommError_IRQHandler            [WEAK]
                EXPORT  Fabric_IRQHandler               [WEAK]
                EXPORT  GPIO0_IRQHandler                [WEAK]
                EXPORT  GPIO1_IRQHandler                [WEAK]
                EXPORT  GPIO2_IRQHandler                [WEAK]
                EXPORT  GPIO3_IRQHandler                [WEAK]
                EXPORT  GPIO4_IRQHandler                [WEAK]
                EXPORT  GPIO5_IRQHandler                [WEAK]
                EXPORT  GPIO6_IRQHandler                [WEAK]
                EXPORT  GPIO7_IRQHandler                [WEAK]
                EXPORT  GPIO8_IRQHandler                [WEAK]
                EXPORT  GPIO9_IRQHandler                [WEAK]
                EXPORT  GPIO10_IRQHandler               [WEAK]
                EXPORT  GPIO11_IRQHandler               [WEAK]
                EXPORT  GPIO12_IRQHandler               [WEAK]
                EXPORT  GPIO13_IRQHandler               [WEAK]
                EXPORT  GPIO14_IRQHandler               [WEAK]
                EXPORT  GPIO15_IRQHandler               [WEAK]
                EXPORT  GPIO16_IRQHandler               [WEAK]
                EXPORT  GPIO17_IRQHandler               [WEAK]
                EXPORT  GPIO18_IRQHandler               [WEAK]
                EXPORT  GPIO19_IRQHandler               [WEAK]
                EXPORT  GPIO20_IRQHandler               [WEAK]
                EXPORT  GPIO21_IRQHandler               [WEAK]
                EXPORT  GPIO22_IRQHandler               [WEAK]
                EXPORT  GPIO23_IRQHandler               [WEAK]
                EXPORT  GPIO24_IRQHandler               [WEAK]
                EXPORT  GPIO25_IRQHandler               [WEAK]
                EXPORT  GPIO26_IRQHandler               [WEAK]
                EXPORT  GPIO27_IRQHandler               [WEAK]
                EXPORT  GPIO28_IRQHandler               [WEAK]
                EXPORT  GPIO29_IRQHandler               [WEAK]
                EXPORT  GPIO30_IRQHandler               [WEAK]
                EXPORT  GPIO31_IRQHandler               [WEAK]
                EXPORT  ACE_PC0_Flag0_IRQHandler        [WEAK]
                EXPORT  ACE_PC0_Flag1_IRQHandler        [WEAK]
                EXPORT  ACE_PC0_Flag2_IRQHandler        [WEAK]
                EXPORT  ACE_PC0_Flag3_IRQHandler        [WEAK]
                EXPORT  ACE_PC1_Flag0_IRQHandler        [WEAK]
                EXPORT  ACE_PC1_Flag1_IRQHandler        [WEAK]
                EXPORT  ACE_PC1_Flag2_IRQHandler        [WEAK]
                EXPORT  ACE_PC1_Flag3_IRQHandler        [WEAK]
                EXPORT  ACE_PC2_Flag0_IRQHandler        [WEAK]
                EXPORT  ACE_PC2_Flag1_IRQHandler        [WEAK]
                EXPORT  ACE_PC2_Flag2_IRQHandler        [WEAK]
                EXPORT  ACE_PC2_Flag3_IRQHandler        [WEAK]
                EXPORT  ACE_ADC0_DataValid_IRQHandler   [WEAK]
                EXPORT  ACE_ADC1_DataValid_IRQHandler   [WEAK]
                EXPORT  ACE_ADC2_DataValid_IRQHandler   [WEAK]
                EXPORT  ACE_ADC0_CalDone_IRQHandler     [WEAK]
                EXPORT  ACE_ADC1_CalDone_IRQHandler     [WEAK]
                EXPORT  ACE_ADC2_CalDone_IRQHandler     [WEAK]
                EXPORT  ACE_ADC0_CalStart_IRQHandler    [WEAK]
                EXPORT  ACE_ADC1_CalStart_IRQHandler    [WEAK]
                EXPORT  ACE_ADC2_CalStart_IRQHandler    [WEAK]
                EXPORT  ACE_Comp0_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp1_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp2_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp3_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp4_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp5_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp6_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp7_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp8_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp9_Fall_IRQHandler       [WEAK]
                EXPORT  ACE_Comp10_Fall_IRQHandler      [WEAK]
                EXPORT  ACE_Comp11_Fall_IRQHandler      [WEAK]
                EXPORT  ACE_Comp0_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp1_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp2_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp3_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp4_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp5_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp6_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp7_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp8_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp9_Rise_IRQHandler       [WEAK]
                EXPORT  ACE_Comp10_Rise_IRQHandler      [WEAK]
                EXPORT  ACE_Comp11_Rise_IRQHandler      [WEAK]
                EXPORT  ACE_ADC0_FifoFull_IRQHandler    [WEAK]
                EXPORT  ACE_ADC0_FifoAFull_IRQHandler   [WEAK]
                EXPORT  ACE_ADC0_FifoEmpty_IRQHandler   [WEAK]
                EXPORT  ACE_ADC1_FifoFull_IRQHandler    [WEAK]
                EXPORT  ACE_ADC1_FifoAFull_IRQHandler   [WEAK]
                EXPORT  ACE_ADC1_FifoEmpty_IRQHandler   [WEAK]
                EXPORT  ACE_ADC2_FifoFull_IRQHandler    [WEAK]
                EXPORT  ACE_ADC2_FifoAFull_IRQHandler   [WEAK]
                EXPORT  ACE_ADC2_FifoEmpty_IRQHandler   [WEAK]
                EXPORT  ACE_PPE_Flag0_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag1_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag2_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag3_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag4_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag5_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag6_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag7_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag8_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag9_IRQHandler        [WEAK]
                EXPORT  ACE_PPE_Flag10_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag11_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag12_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag13_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag14_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag15_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag16_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag17_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag18_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag19_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag20_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag21_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag22_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag23_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag24_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag25_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag26_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag27_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag28_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag29_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag30_IRQHandler       [WEAK]
                EXPORT  ACE_PPE_Flag31_IRQHandler       [WEAK]


WdogWakeup_IRQHandler
BrownOut_1_5V_IRQHandler
BrownOut_3_3V_IRQHandler
RTC_Match_IRQHandler
RTCIF_Pub_IRQHandler
EthernetMAC_IRQHandler
IAP_IRQHandler
ENVM0_IRQHandler
ENVM1_IRQHandler
DMA_IRQHandler
UART0_IRQHandler
UART1_IRQHandler
SPI0_IRQHandler
SPI1_IRQHandler
I2C0_IRQHandler
I2C0_SMBAlert_IRQHandler
I2C0_SMBus_IRQHandler
I2C1_IRQHandler
I2C1_SMBAlert_IRQHandler
I2C1_SMBus_IRQHandler
Timer1_IRQHandler
Timer2_IRQHandler
PLL_Lock_IRQHandler
PLL_LockLost_IRQHandler
CommError_IRQHandler
Fabric_IRQHandler
GPIO0_IRQHandler
GPIO1_IRQHandler
GPIO2_IRQHandler
GPIO3_IRQHandler
GPIO4_IRQHandler
GPIO5_IRQHandler
GPIO6_IRQHandler
GPIO7_IRQHandler
GPIO8_IRQHandler
GPIO9_IRQHandler
GPIO10_IRQHandler
GPIO11_IRQHandler
GPIO12_IRQHandler
GPIO13_IRQHandler
GPIO14_IRQHandler
GPIO15_IRQHandler
GPIO16_IRQHandler
GPIO17_IRQHandler
GPIO18_IRQHandler
GPIO19_IRQHandler
GPIO20_IRQHandler
GPIO21_IRQHandler
GPIO22_IRQHandler
GPIO23_IRQHandler
GPIO24_IRQHandler
GPIO25_IRQHandler
GPIO26_IRQHandler
GPIO27_IRQHandler
GPIO28_IRQHandler
GPIO29_IRQHandler
GPIO30_IRQHandler
GPIO31_IRQHandler
ACE_PC0_Flag0_IRQHandler
ACE_PC0_Flag1_IRQHandler
ACE_PC0_Flag2_IRQHandler
ACE_PC0_Flag3_IRQHandler
ACE_PC1_Flag0_IRQHandler
ACE_PC1_Flag1_IRQHandler
ACE_PC1_Flag2_IRQHandler
ACE_PC1_Flag3_IRQHandler
ACE_PC2_Flag0_IRQHandler
ACE_PC2_Flag1_IRQHandler
ACE_PC2_Flag2_IRQHandler
ACE_PC2_Flag3_IRQHandler
ACE_ADC0_DataValid_IRQHandler
ACE_ADC1_DataValid_IRQHandler
ACE_ADC2_DataValid_IRQHandler
ACE_ADC0_CalDone_IRQHandler
ACE_ADC1_CalDone_IRQHandler
ACE_ADC2_CalDone_IRQHandler
ACE_ADC0_CalStart_IRQHandler
ACE_ADC1_CalStart_IRQHandler
ACE_ADC2_CalStart_IRQHandler
ACE_Comp0_Fall_IRQHandler
ACE_Comp1_Fall_IRQHandler
ACE_Comp2_Fall_IRQHandler
ACE_Comp3_Fall_IRQHandler
ACE_Comp4_Fall_IRQHandler
ACE_Comp5_Fall_IRQHandler
ACE_Comp6_Fall_IRQHandler
ACE_Comp7_Fall_IRQHandler
ACE_Comp8_Fall_IRQHandler
ACE_Comp9_Fall_IRQHandler
ACE_Comp10_Fall_IRQHandler
ACE_Comp11_Fall_IRQHandler
ACE_Comp0_Rise_IRQHandler
ACE_Comp1_Rise_IRQHandler
ACE_Comp2_Rise_IRQHandler
ACE_Comp3_Rise_IRQHandler
ACE_Comp4_Rise_IRQHandler
ACE_Comp5_Rise_IRQHandler
ACE_Comp6_Rise_IRQHandler
ACE_Comp7_Rise_IRQHandler
ACE_Comp8_Rise_IRQHandler
ACE_Comp9_Rise_IRQHandler
ACE_Comp10_Rise_IRQHandler
ACE_Comp11_Rise_IRQHandler
ACE_ADC0_FifoFull_IRQHandler
ACE_ADC0_FifoAFull_IRQHandler
ACE_ADC0_FifoEmpty_IRQHandler
ACE_ADC1_FifoFull_IRQHandler
ACE_ADC1_FifoAFull_IRQHandler
ACE_ADC1_FifoEmpty_IRQHandler
ACE_ADC2_FifoFull_IRQHandler
ACE_ADC2_FifoAFull_IRQHandler
ACE_ADC2_FifoEmpty_IRQHandler
ACE_PPE_Flag0_IRQHandler
ACE_PPE_Flag1_IRQHandler
ACE_PPE_Flag2_IRQHandler
ACE_PPE_Flag3_IRQHandler
ACE_PPE_Flag4_IRQHandler
ACE_PPE_Flag5_IRQHandler
ACE_PPE_Flag6_IRQHandler
ACE_PPE_Flag7_IRQHandler
ACE_PPE_Flag8_IRQHandler
ACE_PPE_Flag9_IRQHandler
ACE_PPE_Flag10_IRQHandler
ACE_PPE_Flag11_IRQHandler
ACE_PPE_Flag12_IRQHandler
ACE_PPE_Flag13_IRQHandler
ACE_PPE_Flag14_IRQHandler
ACE_PPE_Flag15_IRQHandler
ACE_PPE_Flag16_IRQHandler
ACE_PPE_Flag17_IRQHandler
ACE_PPE_Flag18_IRQHandler
ACE_PPE_Flag19_IRQHandler
ACE_PPE_Flag20_IRQHandler
ACE_PPE_Flag21_IRQHandler
ACE_PPE_Flag22_IRQHandler
ACE_PPE_Flag23_IRQHandler
ACE_PPE_Flag24_IRQHandler
ACE_PPE_Flag25_IRQHandler
ACE_PPE_Flag26_IRQHandler
ACE_PPE_Flag27_IRQHandler
ACE_PPE_Flag28_IRQHandler
ACE_PPE_Flag29_IRQHandler
ACE_PPE_Flag30_IRQHandler
ACE_PPE_Flag31_IRQHandler

                B       .

                ENDP


                ALIGN


;-------------------------------------------------------------------------------
; User Initial Stack & Heap

                IF      :DEF:__MICROLIB
                
                EXPORT  __initial_sp
                EXPORT  __heap_base
                EXPORT  __heap_limit
                
                ELSE
                
                IMPORT  __use_two_region_memory
                EXPORT  __user_initial_stackheap
__user_initial_stackheap

                LDR     R0, =  Heap_Mem
                LDR     R1, =(Stack_Mem + Stack_Size)
                LDR     R2, = (Heap_Mem +  Heap_Size)
                LDR     R3, = Stack_Mem
                BX      LR

                ALIGN

                ENDIF


                END
