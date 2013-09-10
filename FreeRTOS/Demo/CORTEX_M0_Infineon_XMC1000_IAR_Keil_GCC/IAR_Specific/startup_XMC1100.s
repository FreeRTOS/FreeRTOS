;**********************************************************************************
;*
;* Part one of the system initialization code, contains low-level
;* initialization, plain thumb variant.
;*
;* Copyright 2013 IAR Systems. All rights reserved.
;*
;* $Revision: 64600 $
;*
;******************* Version History **********************************************   
;  V5, Feb, 6, 2013 TYS:a) Add DAVE3_CE defination, 
;                       b) Remove Math,ADC,CCU8,POSIF,LEDTS,BCCU0 interrupt
;                       c) Change AllowPLLInitByStartup to AllowClkInitByStartup 
;  V6, May, 16,2013 TYS:a) Add XMC1100_SCU.inc 
;     
;**********************************************************************************
;
; The modules in this file are included in the libraries, and may be replaced
; by any user-defined modules that define the PUBLIC symbol _program_start or
; a user defined start symbol.
; To override the cstartup defined in the library, simply add your modified
; version to the workbench project.
;
; Cortex-M version
;

        MODULE  ?cstartup

#ifdef DAVE_CE
#include "XMC1100_SCU.inc"
#include "Device_Data.h"
#else
#define CLKVAL1_SSW 0x00000100
#define CLKVAL2_SSW 0x00000000
#endif 

        ;; Forward declaration of sections.
        SECTION CSTACK:DATA:NOROOT(3)
        SECTION .intvec:CODE:NOROOT(2)

        EXTERN  __iar_program_start
        PUBLIC  __vector_table

        DATA
__vector_table
        DCD     sfe(CSTACK)
        DCD     Reset_Handler             ; Reset Handler
        DCD     0                         ; 0x8
        DCD     0                         ; 0xC
        DCD     CLKVAL1_SSW               ; 0x10 CLK_VAL1 - (CLKCR default)
        DCD     CLKVAL2_SSW               ; 0x14 CLK_VAL2 - (CGATCLR0 default)

        SECTION .vect_table:CODE:ROOT(2)
        THUMB
        LDR     R0,=HardFault_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=SVC_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=Undef_Handler
        BX      R0
        LDR     R0,=PendSV_Handler
        BX      R0
        LDR     R0,=SysTick_Handler
        BX      R0

        ; External Interrupts
        LDR     R0,=SCU_0_IRQHandler      ; Handler name for SR SCU_0
        BX      R0
        LDR     R0,=SCU_1_IRQHandler      ; Handler name for SR SCU_1
        BX      R0
        LDR     R0,=SCU_2_IRQHandler      ; Handler name for SR SCU_2
        BX      R0
        LDR     R0,=ERU0_0_IRQHandler     ; Handler name for SR ERU0_0
        BX      R0
        LDR     R0,=ERU0_1_IRQHandler     ; Handler name for SR ERU0_1
        BX      R0
        LDR     R0,=ERU0_2_IRQHandler     ; Handler name for SR ERU0_2
        BX      R0
        LDR     R0,=ERU0_3_IRQHandler     ; Handler name for SR ERU0_3
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=USIC0_0_IRQHandler    ; Handler name for SR USIC0_0
        BX      R0
        LDR     R0,=USIC0_1_IRQHandler    ; Handler name for SR USIC0_1
        BX      R0
        LDR     R0,=USIC0_2_IRQHandler    ; Handler name for SR USIC0_2
        BX      R0
        LDR     R0,=USIC0_3_IRQHandler    ; Handler name for SR USIC0_3
        BX      R0
        LDR     R0,=USIC0_4_IRQHandler    ; Handler name for SR USIC0_4
        BX      R0
        LDR     R0,=USIC0_5_IRQHandler    ; Handler name for SR USIC0_5
        BX      R0
        LDR     R0,=VADC0_C0_0_IRQHandler ; Handler name for SR VADC0_C0_0
        BX      R0
        LDR     R0,=VADC0_C0_1_IRQHandler ; Handler name for SR VADC0_C0_1
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=CCU40_0_IRQHandler    ; Handler name for SR CCU40_0
        BX      R0
        LDR     R0,=CCU40_1_IRQHandler    ; Handler name for SR CCU40_1
        BX      R0
        LDR     R0,=CCU40_2_IRQHandler    ; Handler name for SR CCU40_2
        BX      R0
        LDR     R0,=CCU40_3_IRQHandler    ; Handler name for SR CCU40_3
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0
        LDR     R0,=Undef_Handler         ; Not Available
        BX      R0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Default interrupt handlers.
;;
        EXTERN  SystemInit
        SECTION .text:CODE:NOROOT(2)

        THUMB

        PUBWEAK Reset_Handler
        SECTION .text:CODE:REORDER(2)
Reset_Handler
        LDR     R0, =SystemInit
        BLX     R0
        LDR     R0, =SystemInit_DAVE3
        BLX     R0
        LDR     R0, =__iar_program_start
        BX      R0

        PUBWEAK Undef_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
Undef_Handler
        B Undef_Handler


        PUBWEAK HardFault_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
HardFault_Handler
        B HardFault_Handler


        PUBWEAK SVC_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
SVC_Handler
        B SVC_Handler


        PUBWEAK PendSV_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
PendSV_Handler
        B PendSV_Handler


        PUBWEAK SysTick_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
SysTick_Handler
        B SysTick_Handler


        PUBWEAK SCU_0_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
SCU_0_IRQHandler
        B SCU_0_IRQHandler

        PUBWEAK SCU_1_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
SCU_1_IRQHandler
        B SCU_1_IRQHandler


        PUBWEAK SCU_2_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
SCU_2_IRQHandler
        B SCU_2_IRQHandler


        PUBWEAK ERU0_0_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
ERU0_0_IRQHandler
        B ERU0_0_IRQHandler


        PUBWEAK ERU0_1_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
ERU0_1_IRQHandler
        B ERU0_1_IRQHandler


        PUBWEAK ERU0_2_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
ERU0_2_IRQHandler
        B ERU0_2_IRQHandler


        PUBWEAK ERU0_3_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
ERU0_3_IRQHandler
        B ERU0_3_IRQHandler


        PUBWEAK USIC0_0_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
USIC0_0_IRQHandler
        B USIC0_0_IRQHandler


        PUBWEAK USIC0_1_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
USIC0_1_IRQHandler
        B USIC0_1_IRQHandler


        PUBWEAK USIC0_2_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
USIC0_2_IRQHandler
        B USIC0_2_IRQHandler


        PUBWEAK USIC0_3_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
USIC0_3_IRQHandler
        B USIC0_3_IRQHandler


        PUBWEAK USIC0_4_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
USIC0_4_IRQHandler
        B USIC0_4_IRQHandler


        PUBWEAK USIC0_5_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
USIC0_5_IRQHandler
        B USIC0_5_IRQHandler


        PUBWEAK VADC0_C0_0_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
VADC0_C0_0_IRQHandler
        B VADC0_C0_0_IRQHandler


        PUBWEAK VADC0_C0_1_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
VADC0_C0_1_IRQHandler
        B VADC0_C0_1_IRQHandler


        PUBWEAK CCU40_0_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
CCU40_0_IRQHandler
        B CCU40_0_IRQHandler


        PUBWEAK CCU40_1_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
CCU40_1_IRQHandler
        B CCU40_1_IRQHandler


        PUBWEAK CCU40_2_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
CCU40_2_IRQHandler
        B CCU40_2_IRQHandler


        PUBWEAK CCU40_3_IRQHandler
        SECTION .text:CODE:REORDER:NOROOT(1)
CCU40_3_IRQHandler
        B CCU40_3_IRQHandler


; Definition of the default weak SystemInit_DAVE3 function
;If DAVE3 requires an extended SystemInit it will create its own version of
;SystemInit_DAVE3 which overrides this weak definition. Example includes
;setting up of external memory interfaces.

        PUBWEAK SystemInit_DAVE3
        SECTION .text:CODE:REORDER:NOROOT(2)
SystemInit_DAVE3
        NOP
        BX LR

;Decision function queried by CMSIS startup for Clock tree setup ======== */
;In the absence of DAVE code engine, CMSIS SystemInit() must perform clock tree setup.
;This decision routine defined here will always return TRUE.
;When overridden by a definition defined in DAVE code engine, this routine
;returns FALSE indicating that the code engine has performed the clock setup

        PUBWEAK AllowClkInitByStartup
        SECTION .text:CODE:REORDER:NOROOT(2)
AllowClkInitByStartup
        MOVS  R0,#1
        BX    LR

        END
