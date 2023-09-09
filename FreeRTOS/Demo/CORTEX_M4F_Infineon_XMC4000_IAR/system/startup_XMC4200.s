/*****************************************************************************/
/* Startup_XMC4200.s: Startup file for XMC4200 device series for EWARM                */
/*****************************************************************************/
/*
* @file     Startup_XMC4200.s
*           XMC4000 Device Series
* @version  V1.1
* @date     Augsut 2013
*
* Copyright (C) 2012 IAR Systems. All rights reserved.
* Copyright (C) 2012 Infineon Technologies AG. All rights reserved.
*
*
* @par
* Infineon Technologies AG (Infineon) is supplying this software for use with 
* Infineon's microcontrollers.  This file can be freely distributed
* within development tools that are supporting such microcontrollers.
*
* @par
* THIS SOFTWARE IS PROVIDED AS IS.  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
* ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
* CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
*
******************************************************************************/
/* ********************* Version History *********************************** */
/* ***************************************************************************
V1.0 January, 30 2013:  In ths version a workoraound for the erratum PMU_CM.001
is implmented (patch for the Exception and interrupt handlers)
V1.1 Augsut, 17 2013:  Fix the bug of preprocessor due to workoraound for 
the erratum PMU_CM.001, and the bug of stack pointer alignment to a 8 byte boundary

**************************************************************************** */

        MODULE  ?vector_table

        AAPCS INTERWORK, VFP_COMPATIBLE, RWPI_COMPATIBLE
        PRESERVE8


        ;; Forward declaration of sections.
        SECTION CSTACK:DATA:NOROOT(3)

        SECTION .intvec:CODE:NOROOT(2)

        EXTERN  __iar_program_start
        EXTERN  SystemInit
        PUBLIC  __vector_table

        DATA

__iar_init$$done:               ; The vector table is not needed
                                ; until after copy initialization is done

;/* ===========START : MACRO DEFINITION MACRO DEFINITION ================== */
;/*
; * STEP_AB and below have the prefetch functional deviation (Errata id: PMU_CM.001).
; * A veneer defined below will first be executed which in turn branches to the final 
; * exception handler.
; *
; * In addition to defining the veneers, the vector table must for these buggy
; * devices contain the veneers.
; */

;set WORKAROUND_PMU_CM001 under Options for target
;define WORKAROUND_PMU_CM001 as TRUE
#define WORKAROUND_PMU_CM001 1

;/* A macro to setup a vector table entry based on STEP ID */
#ifdef WORKAROUND_PMU_CM001
ExcpVector  macro
            DCD \1_Veneer
            endm
#else
ExcpVector  macro
            DCD \1
            endm           
#endif

;/* A macro to ease definition of the various handlers based on STEP ID */
#ifdef WORKAROUND_PMU_CM001
;/* First define the final exception handler */
ProxyHandler  macro
              PUBWEAK \1
              SECTION .text:CODE:REORDER:NOROOT(1)
\1
              B \1
;/* And then define a veneer that will branch to the final excp handler */              
              PUBWEAK \1_Veneer
              SECTION .text:CODE:REORDER:NOROOT(2)
\1_Veneer:
              LDR   R0, =\1
              PUSH	{LR}  /* Breaks AAPCS */
              SUB SP,#4       /* Restores AAPCS */
              BLX   R0
              ADD SP,#4
              POP   {PC}
              endm
 ;/* No prefetch bug, hence define only the final exception handler */              
#else
ProxyHandler  macro
              PUBWEAK \1
              SECTION .text:CODE:REORDER:NOROOT(1)
\1
              B \1
              endm
#endif

;/* ============= END OF MACRO DEFINITION MACRO DEFINITION ================== */

__vector_table
    DCD   sfe(CSTACK)
    DCD   Reset_Handler          	    ; Reset Handler  
              
    ExcpVector   NMI_Handler                 ; NMI Handler                  
    ExcpVector   HardFault_Handler           ; Hard Fault Handler           
    ExcpVector   MemManage_Handler           ; MPU Fault Handler            
    ExcpVector   BusFault_Handler            ; Bus Fault Handler            
    ExcpVector   UsageFault_Handler          ; Usage Fault Handler          
    DCD   0                           ; Reserved                     
    DCD   0                           ; Reserved                     
    DCD   0                           ; Reserved                     
    DCD   0                           ; Reserved                     
    ExcpVector   SVC_Handler                 ; SVCall Handler               
    ExcpVector   DebugMon_Handler            ; Debug Monitor Handler        
    DCD   0                           ; Reserved                     
    ExcpVector   PendSV_Handler              ; PendSV Handler               
    ExcpVector   SysTick_Handler             ; SysTick Handler              

    ; Interrupt Handlers for Service Requests (SR) from XMC4200 Peripherals
    ExcpVector   SCU_0_IRQHandler            ; Handler name for SR SCU_0     
    ExcpVector   ERU0_0_IRQHandler           ; Handler name for SR ERU0_0    
    ExcpVector   ERU0_1_IRQHandler           ; Handler name for SR ERU0_1    
    ExcpVector   ERU0_2_IRQHandler           ; Handler name for SR ERU0_2    
    ExcpVector   ERU0_3_IRQHandler           ; Handler name for SR ERU0_3     
    ExcpVector   ERU1_0_IRQHandler           ; Handler name for SR ERU1_0    
    ExcpVector   ERU1_1_IRQHandler           ; Handler name for SR ERU1_1    
    ExcpVector   ERU1_2_IRQHandler           ; Handler name for SR ERU1_2    
    ExcpVector   ERU1_3_IRQHandler           ; Handler name for SR ERU1_3    
    DCD   0                           ; Not Available                 
    DCD   0                           ; Not Available                 
    DCD   0                           ; Not Available                 
    ExcpVector   PMU0_0_IRQHandler           ; Handler name for SR PMU0_0    
    DCD   0                           ; Not Available                 
    ExcpVector   VADC0_C0_0_IRQHandler       ; Handler name for SR VADC0_C0_0  
    ExcpVector   VADC0_C0_1_IRQHandler       ; Handler name for SR VADC0_C0_1  
    ExcpVector   VADC0_C0_2_IRQHandler       ; Handler name for SR VADC0_C0_1  
    ExcpVector   VADC0_C0_3_IRQHandler       ; Handler name for SR VADC0_C0_3  
    ExcpVector   VADC0_G0_0_IRQHandler       ; Handler name for SR VADC0_G0_0  
    ExcpVector   VADC0_G0_1_IRQHandler       ; Handler name for SR VADC0_G0_1  
    ExcpVector   VADC0_G0_2_IRQHandler       ; Handler name for SR VADC0_G0_2  
    ExcpVector   VADC0_G0_3_IRQHandler       ; Handler name for SR VADC0_G0_3  
    ExcpVector   VADC0_G1_0_IRQHandler       ; Handler name for SR VADC0_G1_0  
    ExcpVector   VADC0_G1_1_IRQHandler       ; Handler name for SR VADC0_G1_1  
    ExcpVector   VADC0_G1_2_IRQHandler       ; Handler name for SR VADC0_G1_2  
    ExcpVector   VADC0_G1_3_IRQHandler       ; Handler name for SR VADC0_G1_3  
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    ExcpVector   DAC0_0_IRQHandler           ; Handler name for SR DAC0_0   
    ExcpVector   DAC0_1_IRQHandler           ; Handler name for SR DAC0_1   
    ExcpVector   CCU40_0_IRQHandler          ; Handler name for SR CCU40_0  
    ExcpVector   CCU40_1_IRQHandler          ; Handler name for SR CCU40_1  
    ExcpVector   CCU40_2_IRQHandler          ; Handler name for SR CCU40_2  
    ExcpVector   CCU40_3_IRQHandler          ; Handler name for SR CCU40_3  
    ExcpVector   CCU41_0_IRQHandler          ; Handler name for SR CCU41_0  
    ExcpVector   CCU41_1_IRQHandler          ; Handler name for SR CCU41_1  
    ExcpVector   CCU41_2_IRQHandler          ; Handler name for SR CCU41_2  
    ExcpVector   CCU41_3_IRQHandler          ; Handler name for SR CCU41_3  
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    ExcpVector   CCU80_0_IRQHandler          ; Handler name for SR CCU80_0  
    ExcpVector   CCU80_1_IRQHandler          ; Handler name for SR CCU80_1  
    ExcpVector   CCU80_2_IRQHandler          ; Handler name for SR CCU80_2  
    ExcpVector   CCU80_3_IRQHandler          ; Handler name for SR CCU80_3  
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    ExcpVector   POSIF0_0_IRQHandler         ; Handler name for SR POSIF0_0 
    ExcpVector   POSIF0_1_IRQHandler         ; Handler name for SR POSIF0_1 
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    ExcpVector   HRPWM_0_IRQHandler          ; Handler name for SR HRPWM_0  
    ExcpVector   HRPWM_1_IRQHandler          ; Handler name for SR HRPWM_1  
    ExcpVector   HRPWM_2_IRQHandler          ; Handler name for SR HRPWM_2  
    ExcpVector   HRPWM_3_IRQHandler          ; Handler name for SR HRPWM_3  
    ExcpVector   CAN0_0_IRQHandler           ; Handler name for SR CAN0_0   
    ExcpVector   CAN0_1_IRQHandler           ; Handler name for SR CAN0_1   
    ExcpVector   CAN0_2_IRQHandler           ; Handler name for SR CAN0_2   
    ExcpVector   CAN0_3_IRQHandler           ; Handler name for SR CAN0_3   
    ExcpVector   CAN0_4_IRQHandler           ; Handler name for SR CAN0_4   
    ExcpVector   CAN0_5_IRQHandler           ; Handler name for SR CAN0_5   
    ExcpVector   CAN0_6_IRQHandler           ; Handler name for SR CAN0_6   
    ExcpVector   CAN0_7_IRQHandler           ; Handler name for SR CAN0_7   
    ExcpVector   USIC0_0_IRQHandler          ; Handler name for SR USIC0_0  
    ExcpVector   USIC0_1_IRQHandler          ; Handler name for SR USIC0_1  
    ExcpVector   USIC0_2_IRQHandler          ; Handler name for SR USIC0_2  
    ExcpVector   USIC0_3_IRQHandler          ; Handler name for SR USIC0_3  
    ExcpVector   USIC0_4_IRQHandler          ; Handler name for SR USIC0_4  
    ExcpVector   USIC0_5_IRQHandler          ; Handler name for SR USIC0_5  
    ExcpVector   USIC1_0_IRQHandler          ; Handler name for SR USIC1_0  
    ExcpVector   USIC1_1_IRQHandler          ; Handler name for SR USIC1_1  
    ExcpVector   USIC1_2_IRQHandler          ; Handler name for SR USIC1_2  
    ExcpVector   USIC1_3_IRQHandler          ; Handler name for SR USIC1_3  
    ExcpVector   USIC1_4_IRQHandler          ; Handler name for SR USIC1_4  
    ExcpVector   USIC1_5_IRQHandler          ; Handler name for SR USIC1_5  
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    ExcpVector   LEDTS0_0_IRQHandler         ; Handler name for SR LEDTS0_0 
    DCD   0                           ; Not Available                
    ExcpVector   FCE0_0_IRQHandler           ; Handler name for SR FCE0_0   
    ExcpVector   GPDMA0_0_IRQHandler         ; Handler name for SR GPDMA0_0 
    DCD   0                           ; Not Available                
    ExcpVector   USB0_0_IRQHandler           ; Handler name for SR USB0_0   
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                
    DCD   0                           ; Not Available                


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
        LDR     R0, =SystemInit_DAVE3
        BLX     R0  
        LDR     R0, =__iar_program_start
        BX      R0
        

        ProxyHandler NMI_Handler
        ProxyHandler HardFault_Handler
        ProxyHandler MemManage_Handler
        ProxyHandler BusFault_Handler
        ProxyHandler UsageFault_Handler
        ProxyHandler SVC_Handler
        ProxyHandler DebugMon_Handler
        ProxyHandler PendSV_Handler
        ProxyHandler SysTick_Handler

        ProxyHandler SCU_0_IRQHandler         
        ProxyHandler ERU0_0_IRQHandler        
        ProxyHandler ERU0_1_IRQHandler        
        ProxyHandler ERU0_2_IRQHandler        
        ProxyHandler ERU0_3_IRQHandler        
        ProxyHandler ERU1_0_IRQHandler        
        ProxyHandler ERU1_1_IRQHandler        
        ProxyHandler ERU1_2_IRQHandler        
        ProxyHandler ERU1_3_IRQHandler        
        ProxyHandler PMU0_0_IRQHandler        
        ProxyHandler VADC0_C0_0_IRQHandler    
        ProxyHandler VADC0_C0_1_IRQHandler    
        ProxyHandler VADC0_C0_2_IRQHandler    
        ProxyHandler VADC0_C0_3_IRQHandler    
        ProxyHandler VADC0_G0_0_IRQHandler    
        ProxyHandler VADC0_G0_1_IRQHandler    
        ProxyHandler VADC0_G0_2_IRQHandler    
        ProxyHandler VADC0_G0_3_IRQHandler    
        ProxyHandler VADC0_G1_0_IRQHandler    
        ProxyHandler VADC0_G1_1_IRQHandler    
        ProxyHandler VADC0_G1_2_IRQHandler    
        ProxyHandler VADC0_G1_3_IRQHandler          
        ProxyHandler DAC0_0_IRQHandler        
        ProxyHandler DAC0_1_IRQHandler        
        ProxyHandler CCU40_0_IRQHandler       
        ProxyHandler CCU40_1_IRQHandler       
        ProxyHandler CCU40_2_IRQHandler       
        ProxyHandler CCU40_3_IRQHandler       
        ProxyHandler CCU41_0_IRQHandler       
        ProxyHandler CCU41_1_IRQHandler       
        ProxyHandler CCU41_2_IRQHandler       
        ProxyHandler CCU41_3_IRQHandler             
        ProxyHandler CCU80_0_IRQHandler       
        ProxyHandler CCU80_1_IRQHandler       
        ProxyHandler CCU80_2_IRQHandler       
        ProxyHandler CCU80_3_IRQHandler            
        ProxyHandler POSIF0_0_IRQHandler      
        ProxyHandler POSIF0_1_IRQHandler           
        ProxyHandler HRPWM_0_IRQHandler       
        ProxyHandler HRPWM_1_IRQHandler       
        ProxyHandler HRPWM_2_IRQHandler       
        ProxyHandler HRPWM_3_IRQHandler       
        ProxyHandler CAN0_0_IRQHandler        
        ProxyHandler CAN0_1_IRQHandler        
        ProxyHandler CAN0_2_IRQHandler        
        ProxyHandler CAN0_3_IRQHandler        
        ProxyHandler CAN0_4_IRQHandler        
        ProxyHandler CAN0_5_IRQHandler        
        ProxyHandler CAN0_6_IRQHandler        
        ProxyHandler CAN0_7_IRQHandler        
        ProxyHandler USIC0_0_IRQHandler       
        ProxyHandler USIC0_1_IRQHandler       
        ProxyHandler USIC0_2_IRQHandler       
        ProxyHandler USIC0_3_IRQHandler       
        ProxyHandler USIC0_4_IRQHandler       
        ProxyHandler USIC0_5_IRQHandler       
        ProxyHandler USIC1_0_IRQHandler       
        ProxyHandler USIC1_1_IRQHandler       
        ProxyHandler USIC1_2_IRQHandler       
        ProxyHandler USIC1_3_IRQHandler       
        ProxyHandler USIC1_4_IRQHandler       
        ProxyHandler USIC1_5_IRQHandler       
        ProxyHandler LEDTS0_0_IRQHandler      
        ProxyHandler FCE0_0_IRQHandler        
        ProxyHandler GPDMA0_0_IRQHandler      
        ProxyHandler USB0_0_IRQHandler              

; Definition of the default weak SystemInit_DAVE3 function for DAVE3 system init.
        PUBWEAK SystemInit_DAVE3
        SECTION .text:CODE:REORDER:NOROOT(2)
SystemInit_DAVE3
        NOP 
        BX LR
 
; Definition of the default weak DAVE3 function for clock App usage.
; AllowPLLInitByStartup Handler
        PUBWEAK AllowPLLInitByStartup
        SECTION .text:CODE:REORDER:NOROOT(2)
AllowPLLInitByStartup       
        MOV R0,#1
        BX LR   

PREF_PCON       EQU 0x58004000
SCU_GCU_PEEN    EQU 0x5000413C
SCU_GCU_PEFLAG  EQU 0x50004150

        
        END
