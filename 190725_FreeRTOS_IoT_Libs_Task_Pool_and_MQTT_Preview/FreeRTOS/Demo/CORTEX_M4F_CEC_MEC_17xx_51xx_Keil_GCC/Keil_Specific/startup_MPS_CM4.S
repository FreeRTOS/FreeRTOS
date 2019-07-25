;/*****************************************************************************
; * @file:    startup_MPS_CM4.s
; * @purpose: CMSIS Cortex-M4 Core Device Startup File
; *           for the ARM 'Microcontroller Prototyping System'
; * @version: V1.00
; * @date:    1. Jun. 2010
; *------- <<< Use Configuration Wizard in Context Menu >>> ------------------
; *
; * Copyright (C) 2008-2010 ARM Limited. All rights reserved.
; * ARM Limited (ARM) is supplying this software for use with Cortex-M4
; * processor based microcontrollers.  This file can be freely distributed
; * within development tools that are supporting such ARM based processors.
; *
; * THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
; * OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
; * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
; * ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
; * CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
; *
; ****************************************************************************/


; <h> Stack Configuration
;   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>
Stack_Size      EQU     0x00000800

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
    DCD    NVIC_Handler_GIRQ08         ;     40h: 0, GIRQ08
    DCD    NVIC_Handler_GIRQ09         ;     44h: 1, GIRQ09
    DCD    NVIC_Handler_GIRQ10         ;     48h: 2, GIRQ10
    DCD    NVIC_Handler_GIRQ11         ;     4Ch: 3, GIRQ11
    DCD    NVIC_Handler_GIRQ12         ;     50h: 4, GIRQ12
    DCD    NVIC_Handler_GIRQ13         ;     54h: 5, GIRQ13
    DCD    NVIC_Handler_GIRQ14         ;     58h: 6, GIRQ14
    DCD    NVIC_Handler_GIRQ15         ;     5Ch: 7, GIRQ15
    DCD    NVIC_Handler_GIRQ16         ;     60h: 8, GIRQ16
    DCD    NVIC_Handler_GIRQ17         ;     64h: 9, GIRQ17
    DCD    NVIC_Handler_GIRQ18         ;     68h: 10, GIRQ18
    DCD    NVIC_Handler_GIRQ19         ;     6Ch: 11, GIRQ19
    DCD    NVIC_Handler_GIRQ20         ;     70h: 12, GIRQ20
    DCD    NVIC_Handler_GIRQ21         ;     74h: 13, GIRQ21
    DCD    NVIC_Handler_GIRQ23         ;     78h: 14, GIRQ23
    DCD    NVIC_Handler_GIRQ24         ;     7Ch: 15, GIRQ24
    DCD    NVIC_Handler_GIRQ25         ;     80h: 16, GIRQ25
    DCD    NVIC_Handler_GIRQ26         ;     84h: 17, GIRQ26
    DCD    0                           ;     88h: 18, RSVD
    DCD    0                           ;     8Ch: 19, RSVD
    DCD    NVIC_Handler_I2C0           ;     90h: 20, I2C/SMBus 0
    DCD    NVIC_Handler_I2C1           ;     94h: 21, I2C/SMBus 1
    DCD    NVIC_Handler_I2C2           ;     98h: 22, I2C/SMBus 2
    DCD    NVIC_Handler_I2C3           ;     9Ch: 23, I2C/SMBus 3
    DCD    NVIC_Handler_DMA0           ;     A0h: 24, DMA Channel 0
    DCD    NVIC_Handler_DMA1           ;     A4h: 25, DMA Channel 1
    DCD    NVIC_Handler_DMA2           ;     A8h: 26, DMA Channel 2
    DCD    NVIC_Handler_DMA3           ;     ACh: 27, DMA Channel 3
    DCD    NVIC_Handler_DMA4           ;     B0h: 28, DMA Channel 4
    DCD    NVIC_Handler_DMA5           ;     B4h: 29, DMA Channel 5
    DCD    NVIC_Handler_DMA6           ;     B8h: 30, DMA Channel 6
    DCD    NVIC_Handler_DMA7           ;     BCh: 31, DMA Channel 7
    DCD    NVIC_Handler_DMA8           ;     C0h: 32, DMA Channel 8
    DCD    NVIC_Handler_DMA9           ;     C4h: 33, DMA Channel 9
    DCD    NVIC_Handler_DMA10          ;     C8h: 34, DMA Channel 10
    DCD    NVIC_Handler_DMA11          ;     CCh: 35, DMA Channel 11
    DCD    NVIC_Handler_DMA12          ;     D0h: 36, DMA Channel 12
    DCD    NVIC_Handler_DMA13          ;     D4h: 37, DMA Channel 13
    DCD    0                           ;     D8h: 38, Unused
    DCD    0                           ;     DCh: 39, Unused
    DCD    NVIC_Handler_UART0          ;     E0h:  40, UART0
    DCD    NVIC_Handler_UART1          ;     E4h:  41, UART1
    DCD    NVIC_Handler_EMI0           ;     E8h:  42, EMI0
    DCD    NVIC_Handler_EMI1           ;     ECh:  43, EMI0
    DCD    NVIC_Handler_EMI2           ;     F0h:  44, EMI0
    DCD    NVIC_Handler_ACPI_EC0_IBF   ;     F4h:  45, ACPI_EC0_IBF
    DCD    NVIC_Handler_ACPI_EC0_OBF   ;     F8h:  46, ACPI_EC0_OBF
    DCD    NVIC_Handler_ACPI_EC1_IBF   ;     FCh:  47, ACPI_EC1_IBF
    DCD    NVIC_Handler_ACPI_EC1_OBF   ;     100h: 48, ACPI_EC1_OBF
    DCD    NVIC_Handler_ACPI_EC2_IBF   ;     104h: 49, ACPI_EC0_IBF
    DCD    NVIC_Handler_ACPI_EC2_OBF   ;     108h: 50, ACPI_EC0_OBF
    DCD    NVIC_Handler_ACPI_EC3_IBF   ;     10Ch: 51, ACPI_EC1_IBF
    DCD    NVIC_Handler_ACPI_EC3_OBF   ;     110h: 52, ACPI_EC1_OBF
    DCD    NVIC_Handler_ACPI_EC4_IBF   ;     114h: 53, ACPI_EC0_IBF
    DCD    NVIC_Handler_ACPI_EC4_OBF   ;     118h: 54, ACPI_EC0_OBF
    DCD    NVIC_Handler_PM1_CTL        ;     11Ch: 55, ACPI_PM1_CTL
    DCD    NVIC_Handler_PM1_EN         ;     120h: 56, ACPI_PM1_EN
    DCD    NVIC_Handler_PM1_STS        ;     124h: 57, ACPI_PM1_STS
    DCD    NVIC_Handler_MIF8042_OBF    ;     128h: 58, MIF8042_OBF
    DCD    NVIC_Handler_MIF8042_IBF    ;     12Ch: 59, MIF8042_IBF
    DCD    NVIC_Handler_MB_H2EC        ;     130h: 60, Mailbox Host to EC
    DCD    NVIC_Handler_MB_DATA        ;     134h: 61, Mailbox Host Data
    DCD    NVIC_Handler_P80A           ;     138h: 62, Port 80h A
    DCD    NVIC_Handler_P80B           ;     13Ch: 63, Port 80h B
    DCD    0                           ;     140h: 64, Reserved
    DCD    NVIC_Handler_PKE_ERR        ;     144h: 65, PKE Error
    DCD    NVIC_Handler_PKE_END        ;     148h: 66, PKE End
    DCD    NVIC_Handler_TRNG           ;     14Ch: 67, Random Num Gen
    DCD    NVIC_Handler_AES            ;     150h: 68, AES
    DCD    NVIC_Handler_HASH           ;     154h: 69, HASH
    DCD    NVIC_Handler_PECI           ;     158h: 70, PECI
    DCD    NVIC_Handler_TACH0          ;     15Ch: 71, TACH0
    DCD    NVIC_Handler_TACH1          ;     160h: 72, TACH1
    DCD    NVIC_Handler_TACH2          ;     164h: 73, TACH2
    DCD    NVIC_Handler_R2P0_FAIL      ;     168h: 74, RPM2PWM 0 Fan Fail
    DCD    NVIC_Handler_R2P0_STALL     ;     16Ch: 75, RPM2PWM 0 Fan Stall
    DCD    NVIC_Handler_R2P1_FAIL      ;     170h: 76, RPM2PWM 1 Fan Fail
    DCD    NVIC_Handler_R2P1_STALL     ;     174h: 77, RPM2PWM 1 Fan Stall
    DCD    NVIC_Handler_ADC_SNGL       ;     178h: 78, ADC_SNGL
    DCD    NVIC_Handler_ADC_RPT        ;     17Ch: 79, ADC_RPT
    DCD    NVIC_Handler_RCID0          ;     180h: 80, RCID 0
    DCD    NVIC_Handler_RCID1          ;     184h: 81, RCID 1
    DCD    NVIC_Handler_RCID2          ;     188h: 82, RCID 2
    DCD    NVIC_Handler_LED0           ;     18Ch: 83, LED0
    DCD    NVIC_Handler_LED1           ;     190h: 84, LED1
    DCD    NVIC_Handler_LED2           ;     194h: 85, LED2
    DCD    NVIC_Handler_LED3           ;     198h: 86, LED2
    DCD    NVIC_Handler_PHOT           ;     19Ch: 87, ProcHot Monitor
    DCD    NVIC_Handler_PWRGD0         ;     1A0h: 88, PowerGuard 0 Status
    DCD    NVIC_Handler_PWRGD1         ;     1A4h: 89, PowerGuard 1 Status
    DCD    NVIC_Handler_LPCBERR        ;     1A8h: 90, LPC Bus Error
    DCD    NVIC_Handler_QMSPI0         ;     1ACh: 91, QMSPI 0
    DCD    NVIC_Handler_GPSPI0_TX      ;     1B0h: 92, GP-SPI0 TX
    DCD    NVIC_Handler_GPSPI0_RX      ;     1B4h: 93, GP-SPI0 RX
    DCD    NVIC_Handler_GPSPI1_TX      ;     1B8h: 94, GP-SPI1 TX
    DCD    NVIC_Handler_GPSPI1_RX      ;     1BCh: 95, GP-SPI1 RX
    DCD    NVIC_Handler_BC0_BUSY       ;     1C0h: 96, BC-Link0 Busy-Clear
    DCD    NVIC_Handler_BC0_ERR        ;     1C4h: 97, BC-Link0 Error
    DCD    NVIC_Handler_BC1_BUSY       ;     1C8h: 98, BC-Link1 Busy-Clear
    DCD    NVIC_Handler_BC1_ERR        ;     1CCh: 99, BC-Link1 Error
    DCD    NVIC_Handler_PS2_0          ;     1D0h: 100, PS2_0
    DCD    NVIC_Handler_PS2_1          ;     1D4h: 101, PS2_1
    DCD    NVIC_Handler_PS2_2          ;     1D8h: 102, PS2_2
    DCD    NVIC_Handler_ESPI_PC        ;     1DCh: 103, eSPI Periph Chan
    DCD    NVIC_Handler_ESPI_BM1       ;     1E0h: 104, eSPI Bus Master 1
    DCD    NVIC_Handler_ESPI_BM2       ;     1E4h: 105, eSPI Bus Master 2
    DCD    NVIC_Handler_ESPI_LTR       ;     1E8h: 106, eSPI LTR
    DCD    NVIC_Handler_ESPI_OOB_UP    ;     1ECh: 107, eSPI Bus Master 1
    DCD    NVIC_Handler_ESPI_OOB_DN    ;     1F0h: 108, eSPI Bus Master 2
    DCD    NVIC_Handler_ESPI_FLASH     ;     1F4h: 109, eSPI Flash Chan
    DCD    NVIC_Handler_ESPI_RESET     ;     1F8h: 110, eSPI Reset
    DCD    NVIC_Handler_RTMR           ;     1FCh: 111, RTOS Timer
    DCD    NVIC_Handler_HTMR0          ;     200h: 112, Hibernation Timer 0
    DCD    NVIC_Handler_HTMR1          ;     204h: 113, Hibernation Timer 1
    DCD    NVIC_Handler_WK             ;     208h: 114, Week Alarm
    DCD    NVIC_Handler_WKSUB          ;     20Ch: 115, Week Alarm, sub week
    DCD    NVIC_Handler_WKSEC          ;     210h: 116, Week Alarm, one sec
    DCD    NVIC_Handler_WKSUBSEC       ;     214h: 117, Week Alarm, sub sec
    DCD    NVIC_Handler_SYSPWR         ;     218h: 118, System Power Present pin
    DCD    NVIC_Handler_RTC            ;     21Ch: 119, RTC
    DCD    NVIC_Handler_RTC_ALARM      ;     220h: 120, RTC_ALARM
    DCD    NVIC_Handler_VCI_OVRD_IN    ;     224h: 121, VCI Override Input
    DCD    NVIC_Handler_VCI_IN0        ;     228h: 122, VCI Input 0
    DCD    NVIC_Handler_VCI_IN1        ;     22Ch: 123, VCI Input 1
    DCD    NVIC_Handler_VCI_IN2        ;     230h: 124, VCI Input 2
    DCD    NVIC_Handler_VCI_IN3        ;     234h: 125, VCI Input 3
    DCD    NVIC_Handler_VCI_IN4        ;     238h: 126, VCI Input 4
    DCD    NVIC_Handler_VCI_IN5        ;     23Ch: 127, VCI Input 5
    DCD    NVIC_Handler_VCI_IN6        ;     240h: 128, VCI Input 6
    DCD    NVIC_Handler_PS20A_WAKE     ;     244h: 129, PS2 Port 0A Wake
    DCD    NVIC_Handler_PS20B_WAKE     ;     248h: 130, PS2 Port 0B Wake
    DCD    NVIC_Handler_PS21A_WAKE     ;     24Ch: 131, PS2 Port 1A Wake
    DCD    NVIC_Handler_PS21B_WAKE     ;     250h: 132, PS2 Port 1B Wake
    DCD    NVIC_Handler_PS21_WAKE      ;     254h: 133, PS2 Port 1 Wake
    DCD    NVIC_Handler_ENVMON         ;     258h: 134, Thernal Monitor
    DCD    NVIC_Handler_KEYSCAN        ;     25Ch: 135, Key Scan
    DCD    NVIC_Handler_BTMR16_0       ;     260h: 136, 16-bit Basic Timer 0
    DCD    NVIC_Handler_BTMR16_1       ;     264h: 137, 16-bit Basic Timer 1
    DCD    NVIC_Handler_BTMR16_2       ;     268h: 138, 16-bit Basic Timer 2
    DCD    NVIC_Handler_BTMR16_3       ;     26Ch: 139, 16-bit Basic Timer 3
    DCD    NVIC_Handler_BTMR32_0       ;     270h: 140, 32-bit Basic Timer 0
    DCD    NVIC_Handler_BTMR32_1       ;     274h: 141, 32-bit Basic Timer 1
    DCD    NVIC_Handler_EVTMR0         ;     278h: 142, Event Counter/Timer 0
    DCD    NVIC_Handler_EVTMR1         ;     27Ch: 143, Event Counter/Timer 1
    DCD    NVIC_Handler_EVTMR2         ;     280h: 144, Event Counter/Timer 2
    DCD    NVIC_Handler_EVTMR3         ;     284h: 145, Event Counter/Timer 3
    DCD    NVIC_Handler_CAPTMR         ;     288h: 146, Capture Timer
    DCD    NVIC_Handler_CAP0           ;     28Ch: 147, Capture 0 Event
    DCD    NVIC_Handler_CAP1           ;     290h: 148, Capture 1 Event
    DCD    NVIC_Handler_CAP2           ;     294h: 149, Capture 2 Event
    DCD    NVIC_Handler_CAP3           ;     298h: 150, Capture 3 Event
    DCD    NVIC_Handler_CAP4           ;     29Ch: 151, Capture 4 Event
    DCD    NVIC_Handler_CAP5           ;     2A0h: 152, Capture 5 Event
    DCD    NVIC_Handler_CMP0           ;     2A4h: 153, Compare 0 Event
    DCD    NVIC_Handler_CMP1           ;     2A8h: 154, Compare 1 Event
    ; Project build information

                AREA    |.text|, CODE, READONLY
;                AREA    RESET, CODE, READONLY

; Reset Handler

Reset_Handler   PROC
                EXPORT  Reset_Handler             [WEAK]
                IMPORT  __main
                IMPORT  SystemInit

                ; Remap vector table
                LDR     R0, =__Vectors
                LDR     R1, =0xE000ED08
                STR     R0,  [r1]
                NOP

                IF      {CPU} = "Cortex-M4.fp"
                LDR     R0, =0xE000ED88           ; Enable CP10,CP11
                LDR     R1,[R0]
                ORR     R1,R1,#(0xF << 20)
                STR     R1,[R0]
                ENDIF

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

    EXPORT    NVIC_Handler_GIRQ08               [WEAK]
    EXPORT    NVIC_Handler_GIRQ09               [WEAK]
    EXPORT    NVIC_Handler_GIRQ10               [WEAK]
    EXPORT    NVIC_Handler_GIRQ11               [WEAK]
    EXPORT    NVIC_Handler_GIRQ12               [WEAK]
    EXPORT    NVIC_Handler_GIRQ13               [WEAK]
    EXPORT    NVIC_Handler_GIRQ14               [WEAK]
    EXPORT    NVIC_Handler_GIRQ15               [WEAK]
    EXPORT    NVIC_Handler_GIRQ16               [WEAK]
    EXPORT    NVIC_Handler_GIRQ17               [WEAK]
    EXPORT    NVIC_Handler_GIRQ18               [WEAK]
    EXPORT    NVIC_Handler_GIRQ19               [WEAK]
    EXPORT    NVIC_Handler_GIRQ20               [WEAK]
    EXPORT    NVIC_Handler_GIRQ21               [WEAK]
    EXPORT    NVIC_Handler_GIRQ23               [WEAK]
    EXPORT    NVIC_Handler_GIRQ24               [WEAK]
    EXPORT    NVIC_Handler_GIRQ25               [WEAK]
    EXPORT    NVIC_Handler_GIRQ26               [WEAK]

    EXPORT    NVIC_Handler_I2C0                 [WEAK]
    EXPORT    NVIC_Handler_I2C1                 [WEAK]
    EXPORT    NVIC_Handler_I2C2                 [WEAK]
    EXPORT    NVIC_Handler_I2C3                 [WEAK]
    EXPORT    NVIC_Handler_DMA0                 [WEAK]
    EXPORT    NVIC_Handler_DMA1                 [WEAK]
    EXPORT    NVIC_Handler_DMA2                 [WEAK]
    EXPORT    NVIC_Handler_DMA3                 [WEAK]
    EXPORT    NVIC_Handler_DMA4                 [WEAK]
    EXPORT    NVIC_Handler_DMA5                 [WEAK]
    EXPORT    NVIC_Handler_DMA6                 [WEAK]
    EXPORT    NVIC_Handler_DMA7                 [WEAK]
    EXPORT    NVIC_Handler_DMA8                 [WEAK]
    EXPORT    NVIC_Handler_DMA9                 [WEAK]
    EXPORT    NVIC_Handler_DMA10                [WEAK]
    EXPORT    NVIC_Handler_DMA11                [WEAK]
    EXPORT    NVIC_Handler_DMA12                [WEAK]
    EXPORT    NVIC_Handler_DMA13                [WEAK]

    EXPORT    NVIC_Handler_UART0                [WEAK]
    EXPORT    NVIC_Handler_UART1                [WEAK]
    EXPORT    NVIC_Handler_EMI0                 [WEAK]
    EXPORT    NVIC_Handler_EMI1                 [WEAK]
    EXPORT    NVIC_Handler_EMI2                 [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC0_IBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC0_OBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC1_IBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC1_OBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC2_IBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC2_OBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC3_IBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC3_OBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC4_IBF         [WEAK]
    EXPORT    NVIC_Handler_ACPI_EC4_OBF         [WEAK]
    EXPORT    NVIC_Handler_PM1_CTL              [WEAK]
    EXPORT    NVIC_Handler_PM1_EN               [WEAK]
    EXPORT    NVIC_Handler_PM1_STS              [WEAK]
    EXPORT    NVIC_Handler_MIF8042_OBF          [WEAK]
    EXPORT    NVIC_Handler_MIF8042_IBF          [WEAK]
    EXPORT    NVIC_Handler_MB_H2EC              [WEAK]
    EXPORT    NVIC_Handler_MB_DATA              [WEAK]
    EXPORT    NVIC_Handler_P80A                 [WEAK]
    EXPORT    NVIC_Handler_P80B                 [WEAK]

    EXPORT    NVIC_Handler_PKE_ERR              [WEAK]
    EXPORT    NVIC_Handler_PKE_END              [WEAK]
    EXPORT    NVIC_Handler_TRNG                 [WEAK]
    EXPORT    NVIC_Handler_AES                  [WEAK]
    EXPORT    NVIC_Handler_HASH                 [WEAK]
    EXPORT    NVIC_Handler_PECI                 [WEAK]
    EXPORT    NVIC_Handler_TACH0                [WEAK]
    EXPORT    NVIC_Handler_TACH1                [WEAK]
    EXPORT    NVIC_Handler_TACH2                [WEAK]
    EXPORT    NVIC_Handler_R2P0_FAIL            [WEAK]
    EXPORT    NVIC_Handler_R2P0_STALL           [WEAK]
    EXPORT    NVIC_Handler_R2P1_FAIL            [WEAK]
    EXPORT    NVIC_Handler_R2P1_STALL           [WEAK]
    EXPORT    NVIC_Handler_ADC_SNGL             [WEAK]
    EXPORT    NVIC_Handler_ADC_RPT              [WEAK]
    EXPORT    NVIC_Handler_RCID0                [WEAK]
    EXPORT    NVIC_Handler_RCID1                [WEAK]
    EXPORT    NVIC_Handler_RCID2                [WEAK]
    EXPORT    NVIC_Handler_LED0                 [WEAK]
    EXPORT    NVIC_Handler_LED1                 [WEAK]
    EXPORT    NVIC_Handler_LED2                 [WEAK]
    EXPORT    NVIC_Handler_LED3                 [WEAK]
    EXPORT    NVIC_Handler_PHOT                 [WEAK]
    EXPORT    NVIC_Handler_PWRGD0               [WEAK]
    EXPORT    NVIC_Handler_PWRGD1               [WEAK]
    EXPORT    NVIC_Handler_LPCBERR              [WEAK]
    EXPORT    NVIC_Handler_QMSPI0               [WEAK]
    EXPORT    NVIC_Handler_GPSPI0_TX            [WEAK]
    EXPORT    NVIC_Handler_GPSPI0_RX            [WEAK]
    EXPORT    NVIC_Handler_GPSPI1_TX            [WEAK]
    EXPORT    NVIC_Handler_GPSPI1_RX            [WEAK]
    EXPORT    NVIC_Handler_BC0_BUSY             [WEAK]
    EXPORT    NVIC_Handler_BC0_ERR              [WEAK]
    EXPORT    NVIC_Handler_BC1_BUSY             [WEAK]
    EXPORT    NVIC_Handler_BC1_ERR              [WEAK]
    EXPORT    NVIC_Handler_PS2_0                [WEAK]
    EXPORT    NVIC_Handler_PS2_1                [WEAK]
    EXPORT    NVIC_Handler_PS2_2                [WEAK]
    EXPORT    NVIC_Handler_ESPI_PC              [WEAK]
    EXPORT    NVIC_Handler_ESPI_BM1             [WEAK]
    EXPORT    NVIC_Handler_ESPI_BM2             [WEAK]
    EXPORT    NVIC_Handler_ESPI_LTR             [WEAK]
    EXPORT    NVIC_Handler_ESPI_OOB_UP          [WEAK]
    EXPORT    NVIC_Handler_ESPI_OOB_DN          [WEAK]
    EXPORT    NVIC_Handler_ESPI_FLASH           [WEAK]
    EXPORT    NVIC_Handler_ESPI_RESET           [WEAK]
    EXPORT    NVIC_Handler_RTMR                 [WEAK]
    EXPORT    NVIC_Handler_HTMR0                [WEAK]
    EXPORT    NVIC_Handler_HTMR1                [WEAK]
    EXPORT    NVIC_Handler_WK                   [WEAK]
    EXPORT    NVIC_Handler_WKSUB                [WEAK]
    EXPORT    NVIC_Handler_WKSEC                [WEAK]
    EXPORT    NVIC_Handler_WKSUBSEC             [WEAK]
    EXPORT    NVIC_Handler_SYSPWR               [WEAK]
    EXPORT    NVIC_Handler_RTC                  [WEAK]
    EXPORT    NVIC_Handler_RTC_ALARM            [WEAK]
    EXPORT    NVIC_Handler_VCI_OVRD_IN          [WEAK]
    EXPORT    NVIC_Handler_VCI_IN0              [WEAK]
    EXPORT    NVIC_Handler_VCI_IN1              [WEAK]
    EXPORT    NVIC_Handler_VCI_IN2              [WEAK]
    EXPORT    NVIC_Handler_VCI_IN3              [WEAK]
    EXPORT    NVIC_Handler_VCI_IN4              [WEAK]
    EXPORT    NVIC_Handler_VCI_IN5              [WEAK]
    EXPORT    NVIC_Handler_VCI_IN6              [WEAK]
    EXPORT    NVIC_Handler_PS20A_WAKE           [WEAK]
    EXPORT    NVIC_Handler_PS20B_WAKE           [WEAK]
    EXPORT    NVIC_Handler_PS21A_WAKE           [WEAK]
    EXPORT    NVIC_Handler_PS21B_WAKE           [WEAK]
    EXPORT    NVIC_Handler_PS21_WAKE            [WEAK]
    EXPORT    NVIC_Handler_ENVMON               [WEAK]
    EXPORT    NVIC_Handler_KEYSCAN              [WEAK]
    EXPORT    NVIC_Handler_BTMR16_0             [WEAK]
    EXPORT    NVIC_Handler_BTMR16_1             [WEAK]
    EXPORT    NVIC_Handler_BTMR16_2             [WEAK]
    EXPORT    NVIC_Handler_BTMR16_3             [WEAK]
    EXPORT    NVIC_Handler_BTMR32_0             [WEAK]
    EXPORT    NVIC_Handler_BTMR32_1             [WEAK]
    EXPORT    NVIC_Handler_EVTMR0               [WEAK]
    EXPORT    NVIC_Handler_EVTMR1               [WEAK]
    EXPORT    NVIC_Handler_EVTMR2               [WEAK]
    EXPORT    NVIC_Handler_EVTMR3               [WEAK]
    EXPORT    NVIC_Handler_CAPTMR               [WEAK]
    EXPORT    NVIC_Handler_CAP0                 [WEAK]
    EXPORT    NVIC_Handler_CAP1                 [WEAK]
    EXPORT    NVIC_Handler_CAP2                 [WEAK]
    EXPORT    NVIC_Handler_CAP3                 [WEAK]
    EXPORT    NVIC_Handler_CAP4                 [WEAK]
    EXPORT    NVIC_Handler_CAP5                 [WEAK]
    EXPORT    NVIC_Handler_CMP0                 [WEAK]
    EXPORT    NVIC_Handler_CMP1                 [WEAK]

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
NVIC_Handler_GIRQ23
NVIC_Handler_GIRQ24
NVIC_Handler_GIRQ25
NVIC_Handler_GIRQ26

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
NVIC_Handler_DMA8
NVIC_Handler_DMA9
NVIC_Handler_DMA10
NVIC_Handler_DMA11
NVIC_Handler_DMA12
NVIC_Handler_DMA13

NVIC_Handler_UART0
NVIC_Handler_UART1
NVIC_Handler_EMI0
NVIC_Handler_EMI1
NVIC_Handler_EMI2
NVIC_Handler_ACPI_EC0_IBF
NVIC_Handler_ACPI_EC0_OBF
NVIC_Handler_ACPI_EC1_IBF
NVIC_Handler_ACPI_EC1_OBF
NVIC_Handler_ACPI_EC2_IBF
NVIC_Handler_ACPI_EC2_OBF
NVIC_Handler_ACPI_EC3_IBF
NVIC_Handler_ACPI_EC3_OBF
NVIC_Handler_ACPI_EC4_IBF
NVIC_Handler_ACPI_EC4_OBF
NVIC_Handler_PM1_CTL
NVIC_Handler_PM1_EN
NVIC_Handler_PM1_STS
NVIC_Handler_MIF8042_OBF
NVIC_Handler_MIF8042_IBF
NVIC_Handler_MB_H2EC
NVIC_Handler_MB_DATA
NVIC_Handler_P80A
NVIC_Handler_P80B

NVIC_Handler_PKE_ERR
NVIC_Handler_PKE_END
NVIC_Handler_TRNG
NVIC_Handler_AES
NVIC_Handler_HASH
NVIC_Handler_PECI
NVIC_Handler_TACH0
NVIC_Handler_TACH1
NVIC_Handler_TACH2
NVIC_Handler_R2P0_FAIL
NVIC_Handler_R2P0_STALL
NVIC_Handler_R2P1_FAIL
NVIC_Handler_R2P1_STALL
NVIC_Handler_ADC_SNGL
NVIC_Handler_ADC_RPT
NVIC_Handler_RCID0
NVIC_Handler_RCID1
NVIC_Handler_RCID2
NVIC_Handler_LED0
NVIC_Handler_LED1
NVIC_Handler_LED2
NVIC_Handler_LED3
NVIC_Handler_PHOT
NVIC_Handler_PWRGD0
NVIC_Handler_PWRGD1
NVIC_Handler_LPCBERR
NVIC_Handler_QMSPI0
NVIC_Handler_GPSPI0_TX
NVIC_Handler_GPSPI0_RX
NVIC_Handler_GPSPI1_TX
NVIC_Handler_GPSPI1_RX
NVIC_Handler_BC0_BUSY
NVIC_Handler_BC0_ERR
NVIC_Handler_BC1_BUSY
NVIC_Handler_BC1_ERR
NVIC_Handler_PS2_0
NVIC_Handler_PS2_1
NVIC_Handler_PS2_2
NVIC_Handler_ESPI_PC
NVIC_Handler_ESPI_BM1
NVIC_Handler_ESPI_BM2
NVIC_Handler_ESPI_LTR
NVIC_Handler_ESPI_OOB_UP
NVIC_Handler_ESPI_OOB_DN
NVIC_Handler_ESPI_FLASH
NVIC_Handler_ESPI_RESET
NVIC_Handler_RTMR
NVIC_Handler_HTMR0
NVIC_Handler_HTMR1
NVIC_Handler_WK
NVIC_Handler_WKSUB
NVIC_Handler_WKSEC
NVIC_Handler_WKSUBSEC
NVIC_Handler_SYSPWR
NVIC_Handler_RTC
NVIC_Handler_RTC_ALARM
NVIC_Handler_VCI_OVRD_IN
NVIC_Handler_VCI_IN0
NVIC_Handler_VCI_IN1
NVIC_Handler_VCI_IN2
NVIC_Handler_VCI_IN3
NVIC_Handler_VCI_IN4
NVIC_Handler_VCI_IN5
NVIC_Handler_VCI_IN6
NVIC_Handler_PS20A_WAKE
NVIC_Handler_PS20B_WAKE
NVIC_Handler_PS21A_WAKE
NVIC_Handler_PS21B_WAKE
NVIC_Handler_PS21_WAKE
NVIC_Handler_ENVMON
NVIC_Handler_KEYSCAN
NVIC_Handler_BTMR16_0
NVIC_Handler_BTMR16_1
NVIC_Handler_BTMR16_2
NVIC_Handler_BTMR16_3
NVIC_Handler_BTMR32_0
NVIC_Handler_BTMR32_1
NVIC_Handler_EVTMR0
NVIC_Handler_EVTMR1
NVIC_Handler_EVTMR2
NVIC_Handler_EVTMR3
NVIC_Handler_CAPTMR
NVIC_Handler_CAP0
NVIC_Handler_CAP1
NVIC_Handler_CAP2
NVIC_Handler_CAP3
NVIC_Handler_CAP4
NVIC_Handler_CAP5
NVIC_Handler_CMP0
NVIC_Handler_CMP1
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
