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
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     SVC_Handler               ; SVCall Handler
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     PendSV_Handler            ; PendSV Handler
                DCD     SysTick_Handler           ; SysTick Handler

                ; External Interrupts
                DCD     IntDefault_Handler        ; PSS ISR
                DCD     IntDefault_Handler        ; CS ISR 
                DCD     IntDefault_Handler        ; PCM ISR
                DCD     IntDefault_Handler        ; WDT ISR
                DCD     IntDefault_Handler        ; FPU ISR
                DCD     IntDefault_Handler        ; FLCTL ISR
                DCD     IntDefault_Handler        ; COMP0 ISR
                DCD     IntDefault_Handler        ; COMP1 ISR
                DCD     IntDefault_Handler        ; TA0_0 ISR 
                DCD     IntDefault_Handler        ; TA0_N ISR
                DCD     IntDefault_Handler        ; TA1_0 ISR
                DCD     IntDefault_Handler        ; TA1_N ISR
                DCD     IntDefault_Handler        ; TA2_0 ISR
                DCD     IntDefault_Handler        ; TA2_N ISR
                DCD     IntDefault_Handler        ; TA3_0 ISR
                DCD     IntDefault_Handler        ; TA3_N ISR
                DCD     vUART_Handler             ; EUSCIA0 ISR
                DCD     IntDefault_Handler        ; EUSCIA1 ISR
                DCD     IntDefault_Handler        ; EUSCIA2 ISR
                DCD     IntDefault_Handler        ; EUSCIA3 ISR
                DCD     IntDefault_Handler        ; EUSCIB0 ISR
                DCD     IntDefault_Handler        ; EUSCIB1 ISR
                DCD     IntDefault_Handler        ; EUSCIB2 ISR
                DCD     IntDefault_Handler        ; EUSCIB3 ISR
                DCD     IntDefault_Handler        ; ADC12 ISR
                DCD     vT32_0_Handler            ; T32_INT1 ISR
                DCD     vT32_1_Handler            ; T32_INT2 ISR
                DCD     IntDefault_Handler        ; T32_INTC ISR
                DCD     IntDefault_Handler        ; AES ISR
                DCD     IntDefault_Handler        ; RTC ISR
                DCD     IntDefault_Handler        ; DMA_ERR ISR
                DCD     IntDefault_Handler        ; DMA_INT3 ISR
                DCD     IntDefault_Handler        ; DMA_INT2 ISR
                DCD     IntDefault_Handler        ; DMA_INT1 ISR
                DCD     IntDefault_Handler        ; DMA_INT0 ISR
                DCD     IntDefault_Handler        ; PORT1 ISR
                DCD     IntDefault_Handler        ; PORT2 ISR
                DCD     IntDefault_Handler        ; PORT3 ISR
                DCD     IntDefault_Handler        ; PORT4 ISR
                DCD     IntDefault_Handler        ; PORT5 ISR
                DCD     IntDefault_Handler        ; PORT6 ISR
                DCD     IntDefault_Handler        ; Reserved 41
                DCD     IntDefault_Handler        ; Reserved 42
                DCD     IntDefault_Handler        ; Reserved 43
                DCD     IntDefault_Handler        ; Reserved 44
                DCD     IntDefault_Handler        ; Reserved 45
                DCD     IntDefault_Handler        ; Reserved 46
                DCD     IntDefault_Handler        ; Reserved 47
                DCD     IntDefault_Handler        ; Reserved 48
                DCD     IntDefault_Handler        ; Reserved 49
                DCD     IntDefault_Handler        ; Reserved 50
                DCD     IntDefault_Handler        ; Reserved 51
                DCD     IntDefault_Handler        ; Reserved 52
                DCD     IntDefault_Handler        ; Reserved 53
                DCD     IntDefault_Handler        ; Reserved 54
                DCD     IntDefault_Handler        ; Reserved 55
                DCD     IntDefault_Handler        ; Reserved 56
                DCD     IntDefault_Handler        ; Reserved 57
                DCD     IntDefault_Handler        ; Reserved 58
                DCD     IntDefault_Handler        ; Reserved 59
                DCD     IntDefault_Handler        ; Reserved 60
                DCD     IntDefault_Handler        ; Reserved 61
                DCD     IntDefault_Handler        ; Reserved 62
                DCD     IntDefault_Handler        ; Reserved 63
                DCD     IntDefault_Handler        ; Reserved 64
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
SVC_Handler     PROC
                EXPORT  SVC_Handler               [WEAK]
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
IntDefault_Handler PROC
                EXPORT  IntDefault_Handler        [WEAK]
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
__user_initial_stackheap

                LDR     R0, =  Heap_Mem
                LDR     R1, =(Stack_Mem + Stack_Size)
                LDR     R2, = (Heap_Mem +  Heap_Size)
                LDR     R3, = Stack_Mem
                BX      LR

                ALIGN

                ENDIF


                END
