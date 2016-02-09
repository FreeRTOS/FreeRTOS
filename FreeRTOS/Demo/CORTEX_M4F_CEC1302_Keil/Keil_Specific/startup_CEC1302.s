;/*
;******************************************************************************
;* © 2013 Microchip Technology Inc. and its subsidiaries.
;* You may use this software and any derivatives exclusively with
;* Microchip products.
;* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
;* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
;* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
;* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
;* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
;* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
;* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
;* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
;* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
;* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
;* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
;* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
;* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
;* OF THESE TERMS.
;******************************************************************************
; */
;/** @file startup_MEC1322.s
; *MEC1322 API Test: startup and vector table
; */
;/** @defgroup startup_MEC1322
; *  @{
; */

        IMPORT  __main
        IMPORT  |Image$$RW_IRAM1$$Base|
        IMPORT  |Image$$RW_IRAM1$$Limit|
        IMPORT  |Image$$RW_IRAM1$$Length|
        IMPORT  |Image$$RW_IRAM1$$ZI$$Base|
        IMPORT  |Image$$RW_IRAM1$$ZI$$Limit|
        IMPORT  |Image$$ER_IROM1$$Base|
        IMPORT  |Image$$ER_IROM1$$Limit|
        IMPORT  main
        IMPORT  system_set_ec_clock

		EXPORT	Reset_Handler

; <h> Stack Configuration
;   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>

Stack_Size      EQU     0x00000800

                AREA    STACK, NOINIT, READWRITE, ALIGN=3
                EXPORT __stack_bottom
__stack_bottom
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
                EXPORT  __tx_vectors
__tx_vectors
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

                ; MEC1322 External Interrupts
                DCD     NVIC_Handler_I2C0           ; 40h: 0, I2C/SMBus 0
                DCD     NVIC_Handler_I2C1           ; 44h: 1, I2C/SMBus 1
                DCD     NVIC_Handler_I2C2           ; 48h: 2, I2C/SMBus 2
                DCD     NVIC_Handler_I2C3           ; 4Ch: 3, I2C/SMBus 3
                DCD     NVIC_Handler_DMA0           ; 50h: 4, DMA Channel 0
                DCD     NVIC_Handler_DMA1           ; 54h: 5, DMA Channel 1
                DCD     NVIC_Handler_DMA2           ; 58h: 6, DMA Channel 2
                DCD     NVIC_Handler_DMA3           ; 5Ch: 7, DMA Channel 3
                DCD     NVIC_Handler_DMA4           ; 60h: 8, DMA Channel 4
                DCD     NVIC_Handler_DMA5           ; 64h: 9, DMA Channel 5
                DCD     NVIC_Handler_DMA6           ; 68h: 10, DMA Channel 6
                DCD     NVIC_Handler_DMA7           ; 6Ch: 11, DMA Channel 7
                DCD     NVIC_Handler_LPCBERR        ; 70h: 12, LPC Bus Error
                DCD     NVIC_Handler_UART0          ; 74h: 13, UART0
                DCD     NVIC_Handler_IMAP0          ; 78h: 14, IMAP0
                DCD     NVIC_Handler_EC0_IBF        ; 7Ch: 15, ACPI_EC0_IBF
                DCD     NVIC_Handler_EC0_OBF        ; 80h: 16, ACPI_EC0_OBF
                DCD     NVIC_Handler_EC1_IBF        ; 84h: 17, ACPI_EC1_IBF
                DCD     NVIC_Handler_EC1_OBF        ; 88h: 18, ACPI_EC1_OBF
                DCD     NVIC_Handler_PM1_CTL        ; 8Ch: 19, ACPI_PM1_CTL
                DCD     NVIC_Handler_PM1_EN         ; 90h: 20, ACPI_PM1_EN
                DCD     NVIC_Handler_PM1_STS        ; 94h: 21, ACPI_PM1_STS
                DCD     NVIC_Handler_MIF8042_OBF    ; 98h: 22, MIF8042_OBF
                DCD     NVIC_Handler_MIF8042_IBF    ; 9Ch: 23, MIF8042_IBF
                DCD     NVIC_Handler_MAILBOX        ; A0h: 24, Mailbox
                DCD     NVIC_Handler_PECI           ; A4h: 25, PECI
                DCD     NVIC_Handler_TACH0          ; A8h: 26, TACH0
                DCD     NVIC_Handler_TACH1          ; ACh: 27, TACH1
                DCD     NVIC_Handler_ADC_SNGL       ; B0h: 28, ADC_SNGL
                DCD     NVIC_Handler_ADC_RPT        ; B4h: 29, ADC_RPT
                DCD     NVIC_Handler_V2P_INT0       ; B8h: 30, V2P_INT0
                DCD     NVIC_Handler_V2P_INT1       ; BCh: 31, V2P_INT1
                DCD     NVIC_Handler_PS2_CH0        ; C0h: 32, PS2_0
                DCD     NVIC_Handler_PS2_CH1        ; C4h: 33, PS2_1
                DCD     NVIC_Handler_PS2_CH2        ; C8h: 34, PS2_2
                DCD     NVIC_Handler_PS2_CH3        ; CCh: 35, PS2_3
                DCD     NVIC_Handler_SPI0_TX        ; D0h: 36, SPI0_TX
                DCD     NVIC_Handler_SPI0_RX        ; D4h: 37, SPI0_RX
                DCD     NVIC_Handler_HIB_TMR        ; D8h: 38, HIB_TMR
                DCD     NVIC_Handler_KEY_INT        ; DCh: 39, KEY_INT
                DCD     NVIC_Handler_KEY_WAKE       ; E0h: 40, KEY_WAKE
                DCD     NVIC_Handler_RPM_STALL      ; E4h: 41, RPM_STALL
                DCD     NVIC_Handler_RPM_SPIN       ; E8h: 42, RPM_SPIN
                DCD     NVIC_Handler_VBAT           ; ECh: 43, VBAT
                DCD     NVIC_Handler_LED0           ; F0h: 44, LED0
                DCD     NVIC_Handler_LED1           ; F4h: 45, LED1
                DCD     NVIC_Handler_LED2           ; F8h: 46, LED2
                DCD     NVIC_Handler_MBC_ERR        ; FCh: 47, MBC_ERR
                DCD     NVIC_Handler_MBC_BUSY       ; 100h: 48, MBC_BUSY
                DCD     NVIC_Handler_TMR0           ; 104h: 49, TMR0
                DCD     NVIC_Handler_TMR1           ; 108h: 50, TMR1
                DCD     NVIC_Handler_TMR2           ; 10Ch: 51, TMR2
                DCD     NVIC_Handler_TMR3           ; 110h: 52, TMR3
                DCD     NVIC_Handler_TMR4           ; 114h: 53, TMR4
                DCD     NVIC_Handler_TMR5           ; 118h: 54, TMR5
                DCD     NVIC_Handler_SPI1_TX        ; 11Ch: 55, SPI1_TX
                DCD     NVIC_Handler_SPI1_RX        ; 120h: 56, SPI1_RX
                DCD     NVIC_Handler_GIRQ08         ; 124h: 57, GIRQ08
                DCD     NVIC_Handler_GIRQ09         ; 128h: 58, GIRQ09
                DCD     NVIC_Handler_GIRQ10         ; 12Ch: 59, GIRQ10
                DCD     NVIC_Handler_GIRQ11         ; 130h: 60, GIRQ11
                DCD     NVIC_Handler_GIRQ12        ; 134h: 61, GIRQ12
                DCD     NVIC_Handler_GIRQ13         ; 138h: 62, GIRQ13
				DCD     NVIC_Handler_GIRQ14         ; 13Ch: 63, GIRQ14
                DCD     NVIC_Handler_GIRQ15         ; 140h: 64, GIRQ15
                DCD     NVIC_Handler_GIRQ16         ; 144h: 65, GIRQ16
                DCD     NVIC_Handler_GIRQ17         ; 148h: 66, GIRQ17
                DCD     NVIC_Handler_GIRQ18         ; 14Ch: 67, GIRQ18
                DCD     NVIC_Handler_GIRQ19         ; 150h: 68, GIRQ19
                DCD     NVIC_Handler_GIRQ20         ; 154h: 69, GIRQ20
                DCD     NVIC_Handler_GIRQ21         ; 158h: 70, GIRQ21
                DCD     NVIC_Handler_GIRQ22         ; 15Ch: 71, GIRQ22
                DCD     NVIC_Handler_GIRQ23         ; 160h: 72, GIRQ23
                DCD     NVIC_Handler_073            ; 164h: 73, unknown
                DCD     NVIC_Handler_074            ; 168h: 74, unknown
                DCD     NVIC_Handler_075            ; 16Ch: 75, unknown
                DCD     NVIC_Handler_076            ; 170h: 76, unknown
                DCD     NVIC_Handler_077            ; 174h: 77, unknown
                DCD     NVIC_Handler_078            ; 178h: 78, unknown
                DCD     NVIC_Handler_079            ; 17Ch: 79, unknown
                DCD     NVIC_Handler_080            ; 180h: 80, unknown
                DCD     NVIC_Handler_DMA8           ; 184h: 81, DMA CH8
                DCD     NVIC_Handler_DMA9           ; 188h: 82, DMA CH9
                DCD     NVIC_Handler_DMA10          ; 18Ch: 83, DMA CH10
                DCD     NVIC_Handler_DMA11          ; 190h: 84, DMA CH11
                DCD     NVIC_Handler_LED3           ; 194h: 85, LED3
                DCD     NVIC_Handler_PKE_ERR        ; 198h: 86, PKE Error
                DCD     NVIC_Handler_PKE_END        ; 19Ch: 87, PKE End
                DCD     NVIC_Handler_TRNG           ; 1A0h: 88, TRandom Num Gen
                DCD     NVIC_Handler_AES            ; 1A4h: 89, AES 
                DCD     NVIC_Handler_HASH           ; 1A8h: 90, HASH
                

                AREA    ROMTABLE, CODE, READONLY
                THUMB
; ---------- ROM API ----------
; Jump table to ROM API C functions
;
;
; ---------- ROM API End ------
; Reset Handler

                AREA    |.text|, CODE, READONLY
                THUMB

Reset_Handler   PROC
                EXPORT  Reset_Handler             [WEAK]

                CPSID    i
                
 				; support code is loaded from ROM loader
        		LDR 	SP, =__initial_sp
				; configure CPU speed 
                LDR     R0, =system_set_ec_clock
                BLX     R0

                LDR     SP, =__initial_sp

 				; support FPU
                IF      {CPU} = "Cortex-M4.fp"
                LDR     R0, =0xE000ED88           ; Enable CP10,CP11
                LDR     R1,[R0]
                ORR     R1,R1,#(0xF << 20)
                STR     R1,[R0]
                ENDIF

                ; Enter Keil startup code which calls our main
                LDR     R0, =__main
                BX      R0
                ENDP

; Dummy Exception Handlers (infinite loops which can be modified)

NMI_Handler     PROC
                EXPORT  NMI_Handler               [WEAK]
                MOV R7,#1
                B       .
                ENDP
HardFault_Handler\
                PROC
                EXPORT  HardFault_Handler         [WEAK]
                MOV R7,#2
                B       .
                ENDP
MemManage_Handler\
                PROC
                EXPORT  MemManage_Handler         [WEAK]
                MOV R7,#3
                B       .
                ENDP
BusFault_Handler\
                PROC
                EXPORT  BusFault_Handler          [WEAK]
                MOV R7,#4
                B       .
                ENDP
UsageFault_Handler\
                PROC
                EXPORT  UsageFault_Handler        [WEAK]
                MOV R7,#5
                B       .
                ENDP
SVC_Handler     PROC
                EXPORT  SVC_Handler               [WEAK]
                MOV R7,#6
                B       .
                ENDP
DebugMon_Handler\
                PROC
                EXPORT  DebugMon_Handler          [WEAK]
                MOV R7,#7
                B       .
                ENDP
PendSV_Handler  PROC
                EXPORT  PendSV_Handler            [WEAK]
                MOV R7,#8
                B       .
                ENDP
SysTick_Handler PROC
                EXPORT  SysTick_Handler           [WEAK]
                MOV R7,#9
                B       .
                ENDP

Default_Handler PROC

        ; External MEC1322 NVIC Interrupt Inputs
        EXPORT  NVIC_Handler_I2C0               [WEAK]
        EXPORT  NVIC_Handler_I2C1               [WEAK]
        EXPORT  NVIC_Handler_I2C2               [WEAK]
        EXPORT  NVIC_Handler_I2C3               [WEAK]
        EXPORT  NVIC_Handler_DMA0               [WEAK]
        EXPORT  NVIC_Handler_DMA1               [WEAK]
        EXPORT  NVIC_Handler_DMA2               [WEAK]
        EXPORT  NVIC_Handler_DMA3               [WEAK]
        EXPORT  NVIC_Handler_DMA4               [WEAK]
        EXPORT  NVIC_Handler_DMA5               [WEAK]
        EXPORT  NVIC_Handler_DMA6               [WEAK]
        EXPORT  NVIC_Handler_DMA7               [WEAK]
        EXPORT  NVIC_Handler_LPCBERR            [WEAK]
        EXPORT  NVIC_Handler_UART0              [WEAK]
        EXPORT  NVIC_Handler_IMAP0              [WEAK]
        EXPORT  NVIC_Handler_EC0_IBF            [WEAK]
        EXPORT  NVIC_Handler_EC0_OBF            [WEAK]
        EXPORT  NVIC_Handler_EC1_IBF            [WEAK]
        EXPORT  NVIC_Handler_EC1_OBF            [WEAK]
        EXPORT  NVIC_Handler_PM1_CTL            [WEAK]
        EXPORT  NVIC_Handler_PM1_EN             [WEAK]
        EXPORT  NVIC_Handler_PM1_STS            [WEAK]
        EXPORT  NVIC_Handler_MIF8042_OBF        [WEAK]
        EXPORT  NVIC_Handler_MIF8042_IBF        [WEAK]
        EXPORT  NVIC_Handler_MAILBOX            [WEAK]
        EXPORT  NVIC_Handler_PECI               [WEAK]
        EXPORT  NVIC_Handler_TACH0              [WEAK]
        EXPORT  NVIC_Handler_TACH1              [WEAK]
        EXPORT  NVIC_Handler_ADC_SNGL           [WEAK]
        EXPORT  NVIC_Handler_ADC_RPT            [WEAK]
        EXPORT  NVIC_Handler_V2P_INT0           [WEAK]
        EXPORT  NVIC_Handler_V2P_INT1           [WEAK]
        EXPORT  NVIC_Handler_PS2_CH0            [WEAK]
        EXPORT  NVIC_Handler_PS2_CH1            [WEAK]
        EXPORT  NVIC_Handler_PS2_CH2            [WEAK]
        EXPORT  NVIC_Handler_PS2_CH3            [WEAK]
        EXPORT  NVIC_Handler_SPI0_TX            [WEAK]
        EXPORT  NVIC_Handler_SPI0_RX            [WEAK]
        EXPORT  NVIC_Handler_HIB_TMR            [WEAK]
        EXPORT  NVIC_Handler_KEY_INT            [WEAK]
        EXPORT  NVIC_Handler_KEY_WAKE           [WEAK]
        EXPORT  NVIC_Handler_RPM_STALL          [WEAK]
        EXPORT  NVIC_Handler_RPM_SPIN           [WEAK]
        EXPORT  NVIC_Handler_VBAT               [WEAK]
        EXPORT  NVIC_Handler_LED0               [WEAK]
        EXPORT  NVIC_Handler_LED1               [WEAK]
        EXPORT  NVIC_Handler_LED2               [WEAK]
        EXPORT  NVIC_Handler_MBC_ERR            [WEAK]
        EXPORT  NVIC_Handler_MBC_BUSY           [WEAK]
        EXPORT  NVIC_Handler_TMR0               [WEAK]
        EXPORT  NVIC_Handler_TMR1               [WEAK]
        EXPORT  NVIC_Handler_TMR2               [WEAK]
        EXPORT  NVIC_Handler_TMR3               [WEAK]
        EXPORT  NVIC_Handler_TMR4               [WEAK]
        EXPORT  NVIC_Handler_TMR5               [WEAK]
        EXPORT  NVIC_Handler_SPI1_TX            [WEAK]
        EXPORT  NVIC_Handler_SPI1_RX            [WEAK]
        EXPORT  NVIC_Handler_GIRQ08             [WEAK]
        EXPORT  NVIC_Handler_GIRQ09             [WEAK]
        EXPORT  NVIC_Handler_GIRQ10             [WEAK]
        EXPORT  NVIC_Handler_GIRQ11             [WEAK]
        EXPORT  NVIC_Handler_GIRQ12             [WEAK]
        EXPORT  NVIC_Handler_GIRQ13             [WEAK]
        EXPORT  NVIC_Handler_GIRQ14             [WEAK]
        EXPORT  NVIC_Handler_GIRQ15             [WEAK]
        EXPORT  NVIC_Handler_GIRQ16             [WEAK]
        EXPORT  NVIC_Handler_GIRQ17             [WEAK]
        EXPORT  NVIC_Handler_GIRQ18             [WEAK]
        EXPORT  NVIC_Handler_GIRQ19             [WEAK]
        EXPORT  NVIC_Handler_GIRQ20             [WEAK]
        EXPORT  NVIC_Handler_GIRQ21             [WEAK]
        EXPORT  NVIC_Handler_GIRQ22             [WEAK]
        EXPORT  NVIC_Handler_GIRQ23             [WEAK]
        EXPORT  NVIC_Handler_073                [WEAK]
        EXPORT  NVIC_Handler_074                [WEAK]
        EXPORT  NVIC_Handler_075                [WEAK]
        EXPORT  NVIC_Handler_076                [WEAK]
        EXPORT  NVIC_Handler_077                [WEAK]
        EXPORT  NVIC_Handler_078                [WEAK]
        EXPORT  NVIC_Handler_079                [WEAK]
        EXPORT  NVIC_Handler_080                [WEAK]
        EXPORT  NVIC_Handler_DMA8               [WEAK]
        EXPORT  NVIC_Handler_DMA9               [WEAK]
        EXPORT  NVIC_Handler_DMA10              [WEAK]
        EXPORT  NVIC_Handler_DMA11              [WEAK]
        EXPORT  NVIC_Handler_LED3               [WEAK]
        EXPORT  NVIC_Handler_PKE_ERR            [WEAK]
        EXPORT  NVIC_Handler_PKE_END            [WEAK]
        EXPORT  NVIC_Handler_TRNG               [WEAK]
        EXPORT  NVIC_Handler_AES                [WEAK]
        EXPORT  NVIC_Handler_HASH               [WEAK]

NVIC_Handler_I2C0
NVIC_Handler_I2C1
NVIC_Handler_I2C2
NVIC_Handler_I2C3
NVIC_Handler_DMA0
NVIC_Handler_DMA1
NVIC_Handler_DMA2
NVIC_Handler_DMA3
NVIC_Handler_DMA4
NVIC_Handler_DMA5
NVIC_Handler_DMA6
NVIC_Handler_DMA7
NVIC_Handler_LPCBERR
NVIC_Handler_UART0
NVIC_Handler_IMAP0
NVIC_Handler_EC0_IBF
NVIC_Handler_EC0_OBF
NVIC_Handler_EC1_IBF
NVIC_Handler_EC1_OBF
NVIC_Handler_PM1_CTL
NVIC_Handler_PM1_EN
NVIC_Handler_PM1_STS
NVIC_Handler_MIF8042_OBF
NVIC_Handler_MIF8042_IBF
NVIC_Handler_MAILBOX
NVIC_Handler_PECI
NVIC_Handler_TACH0
NVIC_Handler_TACH1
NVIC_Handler_ADC_SNGL
NVIC_Handler_ADC_RPT
NVIC_Handler_V2P_INT0
NVIC_Handler_V2P_INT1
NVIC_Handler_PS2_CH0
NVIC_Handler_PS2_CH1
NVIC_Handler_PS2_CH2
NVIC_Handler_PS2_CH3
NVIC_Handler_SPI0_TX
NVIC_Handler_SPI0_RX
NVIC_Handler_HIB_TMR
NVIC_Handler_KEY_INT
NVIC_Handler_KEY_WAKE
NVIC_Handler_RPM_STALL
NVIC_Handler_RPM_SPIN
NVIC_Handler_VBAT
NVIC_Handler_LED0
NVIC_Handler_LED1
NVIC_Handler_LED2
NVIC_Handler_MBC_ERR
NVIC_Handler_MBC_BUSY
NVIC_Handler_TMR0
NVIC_Handler_TMR1
NVIC_Handler_TMR2
NVIC_Handler_TMR3
NVIC_Handler_TMR4
NVIC_Handler_TMR5
NVIC_Handler_SPI1_TX
NVIC_Handler_SPI1_RX
NVIC_Handler_GIRQ08
NVIC_Handler_GIRQ09
NVIC_Handler_GIRQ10
NVIC_Handler_GIRQ11
NVIC_Handler_GIRQ12
NVIC_Handler_GIRQ13
NVIC_Handler_GIRQ14
NVIC_Handler_GIRQ15
NVIC_Handler_GIRQ16
NVIC_Handler_GIRQ17
NVIC_Handler_GIRQ18
NVIC_Handler_GIRQ19
NVIC_Handler_GIRQ20
NVIC_Handler_GIRQ21
NVIC_Handler_GIRQ22
NVIC_Handler_GIRQ23
NVIC_Handler_073
NVIC_Handler_074
NVIC_Handler_075
NVIC_Handler_076
NVIC_Handler_077
NVIC_Handler_078
NVIC_Handler_079
NVIC_Handler_080
NVIC_Handler_DMA8
NVIC_Handler_DMA9
NVIC_Handler_DMA10
NVIC_Handler_DMA11
NVIC_Handler_LED3
NVIC_Handler_PKE_ERR
NVIC_Handler_PKE_END
NVIC_Handler_TRNG
NVIC_Handler_AES
NVIC_Handler_HASH
                B       .

                ENDP

                ALIGN

; User Initial Stack & Heap

                IF      :DEF:__MICROLIB
                
                EXPORT  __initial_sp
                EXPORT  __heap_base
                EXPORT  __heap_limit
                EXPORT  __stack_bottom

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

;/**   @}
; */
