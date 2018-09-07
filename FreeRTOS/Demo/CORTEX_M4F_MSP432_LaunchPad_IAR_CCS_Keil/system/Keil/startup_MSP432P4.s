;//-------- <<< Use Configuration Wizard in Context Menu >>> ------------------
;*/


; <h> Stack Configuration
;   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>

Stack_Size      EQU     0x00000200

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


; Vector Table Mapped to Address 0 at Reset

                AREA    RESET, DATA, READONLY
                EXPORT  __Vectors
                EXPORT  __Vectors_End
                EXPORT  __Vectors_Size
				IMPORT	vUART_Handler
				IMPORT	vT32_0_Handler
				IMPORT	vT32_1_Handler

__Vectors       DCD     __initial_sp              ; Top of Stack
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
                DCD     PSS_IRQHandler            ;  0:  PSS Interrupt
                DCD     CS_IRQHandler             ;  1:  CS Interrupt
                DCD     PCM_IRQHandler            ;  2:  PCM Interrupt
                DCD     WDT_A_IRQHandler          ;  3:  WDT_A Interrupt
                DCD     FPU_IRQHandler            ;  4:  FPU Interrupt
                DCD     FLCTL_IRQHandler          ;  5:  FLCTL Interrupt
                DCD     COMP_E0_IRQHandler        ;  6:  COMP_E0 Interrupt
                DCD     COMP_E1_IRQHandler        ;  7:  COMP_E1 Interrupt
                DCD     TA0_0_IRQHandler          ;  8:  TA0_0 Interrupt
                DCD     TA0_N_IRQHandler          ;  9:  TA0_N Interrupt
                DCD     TA1_0_IRQHandler          ; 10:  TA1_0 Interrupt
                DCD     TA1_N_IRQHandler          ; 11:  TA1_N Interrupt
                DCD     TA2_0_IRQHandler          ; 12:  TA2_0 Interrupt
                DCD     TA2_N_IRQHandler          ; 13:  TA2_N Interrupt
                DCD     TA3_0_IRQHandler          ; 14:  TA3_0 Interrupt
                DCD     TA3_N_IRQHandler          ; 15:  TA3_N Interrupt
                DCD     vUART_Handler             ; EUSCIA0 ISR
                DCD     EUSCIA1_IRQHandler        ; 17:  EUSCIA1 Interrupt
                DCD     EUSCIA2_IRQHandler        ; 18:  EUSCIA2 Interrupt
                DCD     EUSCIA3_IRQHandler        ; 19:  EUSCIA3 Interrupt
                DCD     EUSCIB0_IRQHandler        ; 20:  EUSCIB0 Interrupt
                DCD     EUSCIB1_IRQHandler        ; 21:  EUSCIB1 Interrupt
                DCD     EUSCIB2_IRQHandler        ; 22:  EUSCIB2 Interrupt
                DCD     EUSCIB3_IRQHandler        ; 23:  EUSCIB3 Interrupt
                DCD     ADC14_IRQHandler          ; 24:  ADC14 Interrupt
                DCD     vT32_0_Handler            ; T32_INT1 ISR
                DCD     vT32_1_Handler            ; T32_INT2 ISR
                DCD     T32_INTC_IRQHandler       ; 27:  T32_INTC Interrupt
                DCD     AES256_IRQHandler         ; 28:  AES256 Interrupt
                DCD     RTC_C_IRQHandler          ; 29:  RTC_C Interrupt
                DCD     DMA_ERR_IRQHandler        ; 30:  DMA_ERR Interrupt
                DCD     DMA_INT3_IRQHandler       ; 31:  DMA_INT3 Interrupt
                DCD     DMA_INT2_IRQHandler       ; 32:  DMA_INT2 Interrupt
                DCD     DMA_INT1_IRQHandler       ; 33:  DMA_INT1 Interrupt
                DCD     DMA_INT0_IRQHandler       ; 34:  DMA_INT0 Interrupt
                DCD     PORT1_IRQHandler          ; 35:  PORT1 Interrupt
                DCD     PORT2_IRQHandler          ; 36:  PORT2 Interrupt
                DCD     PORT3_IRQHandler          ; 37:  PORT3 Interrupt
                DCD     PORT4_IRQHandler          ; 38:  PORT4 Interrupt
                DCD     PORT5_IRQHandler          ; 39:  PORT5 Interrupt
                DCD     PORT6_IRQHandler          ; 40:  PORT6 Interrupt
                DCD     0                         ; 41:  Reserved
                DCD     0                         ; 42:  Reserved
                DCD     0                         ; 43:  Reserved
                DCD     0                         ; 44:  Reserved
                DCD     0                         ; 45:  Reserved
                DCD     0                         ; 46:  Reserved
                DCD     0                         ; 47:  Reserved
                DCD     0                         ; 48:  Reserved
                DCD     0                         ; 49:  Reserved
                DCD     0                         ; 50:  Reserved
                DCD     0                         ; 51:  Reserved
                DCD     0                         ; 52:  Reserved
                DCD     0                         ; 53:  Reserved
                DCD     0                         ; 54:  Reserved
                DCD     0                         ; 55:  Reserved
                DCD     0                         ; 56:  Reserved
                DCD     0                         ; 57:  Reserved
                DCD     0                         ; 58:  Reserved
                DCD     0                         ; 59:  Reserved
                DCD     0                         ; 60:  Reserved
                DCD     0                         ; 61:  Reserved
                DCD     0                         ; 62:  Reserved
                DCD     0                         ; 63:  Reserved
                DCD     0                         ; 64:  Reserved
__Vectors_End

__Vectors_Size  EQU     __Vectors_End - __Vectors

                AREA    |.text|, CODE, READONLY


; Reset Handler

Reset_Handler   PROC
                EXPORT  Reset_Handler             [WEAK]
                IMPORT  SystemInit
                IMPORT  __main
                LDR     R0, =SystemInit
                BLX     R0
                LDR     R0, =__main
                BX      R0
                ENDP


; Dummy Exception Handlers (infinite loops which can be modified)

NMI_Handler     PROC
                EXPORT  NMI_Handler               [WEAK]
                B       .
                ENDP
HardFault_Handler\
                PROC
                EXPORT  HardFault_Handler         [WEAK]
                B       .
                ENDP
MemManage_Handler\
                PROC
                EXPORT  MemManage_Handler         [WEAK]
                B       .
                ENDP
BusFault_Handler\
                PROC
                EXPORT  BusFault_Handler          [WEAK]
                B       .
                ENDP
UsageFault_Handler\
                PROC
                EXPORT  UsageFault_Handler        [WEAK]
                B       .
                ENDP
SVC_Handler     PROC
                EXPORT  SVC_Handler               [WEAK]
                B       .
                ENDP
DebugMon_Handler\
                PROC
                EXPORT  DebugMon_Handler          [WEAK]
                B       .
                ENDP
PendSV_Handler  PROC
                EXPORT  PendSV_Handler            [WEAK]
                B       .
                ENDP
SysTick_Handler PROC
                EXPORT  SysTick_Handler           [WEAK]
                B       .
                ENDP

Default_Handler PROC
                EXPORT  PSS_IRQHandler            [WEAK]
                EXPORT  CS_IRQHandler             [WEAK]
                EXPORT  PCM_IRQHandler            [WEAK]
                EXPORT  WDT_A_IRQHandler          [WEAK]
                EXPORT  FPU_IRQHandler            [WEAK]
                EXPORT  FLCTL_IRQHandler          [WEAK]
                EXPORT  COMP_E0_IRQHandler        [WEAK]
                EXPORT  COMP_E1_IRQHandler        [WEAK]
                EXPORT  TA0_0_IRQHandler          [WEAK]
                EXPORT  TA0_N_IRQHandler          [WEAK]
                EXPORT  TA1_0_IRQHandler          [WEAK]
                EXPORT  TA1_N_IRQHandler          [WEAK]
                EXPORT  TA2_0_IRQHandler          [WEAK]
                EXPORT  TA2_N_IRQHandler          [WEAK]
                EXPORT  TA3_0_IRQHandler          [WEAK]
                EXPORT  TA3_N_IRQHandler          [WEAK]
                EXPORT  EUSCIA0_IRQHandler        [WEAK]
                EXPORT  EUSCIA1_IRQHandler        [WEAK]
                EXPORT  EUSCIA2_IRQHandler        [WEAK]
                EXPORT  EUSCIA3_IRQHandler        [WEAK]
                EXPORT  EUSCIB0_IRQHandler        [WEAK]
                EXPORT  EUSCIB1_IRQHandler        [WEAK]
                EXPORT  EUSCIB2_IRQHandler        [WEAK]
                EXPORT  EUSCIB3_IRQHandler        [WEAK]
                EXPORT  ADC14_IRQHandler          [WEAK]
                EXPORT  T32_INT1_IRQHandler       [WEAK]
                EXPORT  T32_INT2_IRQHandler       [WEAK]
                EXPORT  T32_INTC_IRQHandler       [WEAK]
                EXPORT  AES256_IRQHandler         [WEAK]
                EXPORT  RTC_C_IRQHandler          [WEAK]
                EXPORT  DMA_ERR_IRQHandler        [WEAK]
                EXPORT  DMA_INT3_IRQHandler       [WEAK]
                EXPORT  DMA_INT2_IRQHandler       [WEAK]
                EXPORT  DMA_INT1_IRQHandler       [WEAK]
                EXPORT  DMA_INT0_IRQHandler       [WEAK]
                EXPORT  PORT1_IRQHandler          [WEAK]
                EXPORT  PORT2_IRQHandler          [WEAK]
                EXPORT  PORT3_IRQHandler          [WEAK]
                EXPORT  PORT4_IRQHandler          [WEAK]
                EXPORT  PORT5_IRQHandler          [WEAK]
                EXPORT  PORT6_IRQHandler          [WEAK]

PSS_IRQHandler
CS_IRQHandler
PCM_IRQHandler
WDT_A_IRQHandler
FPU_IRQHandler
FLCTL_IRQHandler
COMP_E0_IRQHandler
COMP_E1_IRQHandler
TA0_0_IRQHandler
TA0_N_IRQHandler
TA1_0_IRQHandler
TA1_N_IRQHandler
TA2_0_IRQHandler
TA2_N_IRQHandler
TA3_0_IRQHandler
TA3_N_IRQHandler
EUSCIA0_IRQHandler
EUSCIA1_IRQHandler
EUSCIA2_IRQHandler
EUSCIA3_IRQHandler
EUSCIB0_IRQHandler
EUSCIB1_IRQHandler
EUSCIB2_IRQHandler
EUSCIB3_IRQHandler
ADC14_IRQHandler
T32_INT1_IRQHandler
T32_INT2_IRQHandler
T32_INTC_IRQHandler
AES256_IRQHandler
RTC_C_IRQHandler
DMA_ERR_IRQHandler
DMA_INT3_IRQHandler
DMA_INT2_IRQHandler
DMA_INT1_IRQHandler
DMA_INT0_IRQHandler
PORT1_IRQHandler
PORT2_IRQHandler
PORT3_IRQHandler
PORT4_IRQHandler
PORT5_IRQHandler
PORT6_IRQHandler
                B       .
                ENDP

                ALIGN


; User Initial Stack & Heap

                IF      :DEF:__MICROLIB

                EXPORT  __initial_sp
                EXPORT  __heap_base
                EXPORT  __heap_limit

                ELSE

                IMPORT  __use_two_region_memory
                EXPORT  __user_initial_stackheap

__user_initial_stackheap PROC
                LDR     R0, =  Heap_Mem
                LDR     R1, =(Stack_Mem + Stack_Size)
                LDR     R2, = (Heap_Mem +  Heap_Size)
                LDR     R3, = Stack_Mem
                BX      LR
                ENDP

                ALIGN

                ENDIF


                END
