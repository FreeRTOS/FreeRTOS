;*******************************************************************************
; DISCLAIMER
; This software is supplied by Renesas Electronics Corporation and is only
; intended for use with Renesas products. No other uses are authorized. This
; software is owned by Renesas Electronics Corporation and is protected under
; all applicable laws, including copyright laws.
; THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
; THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
; LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
; AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
; TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
; ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
; FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
; ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
; BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
; Renesas reserves the right, without notice, to make changes to this software
; and to discontinue the availability of this software. By using this software,
; you agree to the additional terms and conditions found by accessing the
; following link:
; http://www.renesas.com/disclaimer
;
; Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
;******************************************************************************
;*******************************************************************************
; System Name  : RZ/T1 Init program
; File Name    : loader_init.asm
; Version      : 0.1
; Device       : R7S9100xx
; Abstract     : Loader program 1
; Tool-Chain   : IAR Embedded Workbench Ver.7.20
; OS           : not use
; H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
; Description  : Description interrupt service routine of RZ/T1
; Limitation   : none
;******************************************************************************
;*******************************************************************************
; History      : DD.MM.YYYY Version  Description
;              :                     First Release
;******************************************************************************

    SECTION IRQ_STACK:DATA:NOROOT(3)
    SECTION FIQ_STACK:DATA:NOROOT(3)
    SECTION SVC_STACK:DATA:NOROOT(3)
    SECTION ABT_STACK:DATA:NOROOT(3)
    SECTION UND_STACK:DATA:NOROOT(3)
    SECTION CSTACK:DATA:NOROOT(3)
  
    SECTION LDR_DATA_RBLOCK:DATA:ROOT(2)
    SECTION LDR_DATA_WBLOCK:DATA:ROOT(2)

    SECTION M3_PRG_RBLOCK:DATA:ROOT(2)
    SECTION M3_PRG_WBLOCK:DATA:ROOT(2)

; This program is allocated to section "d_ldr_prg" 
    SECTION d_ldr_prg:CODE:ROOT(2)
    
    ARM
    
    PUBLIC loader_init1
    PUBLIC set_low_vec
    PUBLIC cache_init
    PUBLIC mpu_init
    IMPORT loader_init2

 
;***********************************************************************
; Function Name : loader_init1
; Description   : Initialize sysytem by loader program
; Arguments     : none
; Return Value  : none
;***********************************************************************
loader_init1:
 
stack_init:
    ; Stack setting  
    cps  #17  ; FIQ mode
    ldr  sp, =SFE(FIQ_STACK)
    cps  #18  ; IRQ mode
    ldr  sp, =SFE(IRQ_STACK)
    cps  #23  ; Abort mode
    ldr  sp, =SFE(ABT_STACK)
    cps  #27  ; Undef mode
    ldr  sp, =SFE(UND_STACK)
    cps  #31  ; System mode
    ldr  sp, =SFE(CSTACK)
    cps  #19  ; SVC mode
    ldr  sp, =SFE(SVC_STACK)
 
vfp_init:  
    ; Initialize VFP setting
    mrc  p15, #0, r0, c1, c0, #2  ; Enables cp10 and cp11 accessing
    orr  r0, r0, #0xF00000
    mcr  p15, #0, r0, c1, c0, #2
    isb                           ; Ensuring Context-changing
    
    mov  r0, #0x40000000  ; Enables VFP operation
    vmsr  fpexc, r0
     
data_init:   
    ; Initialize variables has initialized value of loader_init2.
    ; Variables has no initialized value already be initialized to zero 
    ; in boot sequence(Clear ATCM and BTCM).
    ldr  r0, =SFB(LDR_DATA_RBLOCK)
    ldr  r1, =SFB(LDR_DATA_WBLOCK)
    ldr  r2, =SIZEOF(LDR_DATA_WBLOCK)
    cmp  r2, #0
#ifdef DUAL_CORE
    beq  m3_init
#else
    beq  jump_loader_init2
#endif
   
copy_to_LDR_DATA:
    ldrb  r3, [r0], #1
    strb  r3, [r1], #1
    subs  r2, r2, #1
    bne   copy_to_LDR_DATA    
    dsb                     ; Ensuring data-changing

#ifdef DUAL_CORE

m3_init:
    ; Initialize image for Cortex-M3 core
    ldr  r0, =SFB(M3_PRG_RBLOCK)
    ldr  r1, =SFB(M3_PRG_WBLOCK)
    ldr  r2, =SIZEOF(M3_PRG_WBLOCK)
    cmp  r2, #0
    beq  jump_loader_init2
   
copy_to_M3_PRG:
    ldrb  r3, [r0], #1
    strb  r3, [r1], #1
    subs  r2, r2, #1
    bne   copy_to_M3_PRG    
    dsb                     ; Ensuring data-changing

#endif

    ; Jump to loader_init2
jump_loader_init2:
    ldr  r0, =loader_init2
    bx  r0

;***********************************************************************
; Function Name : cache_init
; Description   : Initialize I1, D1 cache and MPU settings
; Arguments     : none
; Return Value  : none
;***********************************************************************

;*******************************************************************************
; Macro definitions
;*******************************************************************************

SCTLR_BR:  dcd  0x00020000
SCTLR_M:   dcd  0x00000001
SCTLR_I_C: dcd  0x00001004
 
DRBAR_REGION_0: dcd  0x04000000  ; Base address = 0400_0000h
DRACR_REGION_0: dcd  0x0000030C  ; R/W(full), Normal, Non-cache, share
DRSR_REGION_0:  dcd  0x00000025  ; Size 512KB, MPU enable

DRBAR_REGION_1: dcd  0x10000000  ; Base address = 1000_0000h 
DRACR_REGION_1: dcd  0x0000030C  ; R/W(full), Normal, Non-cache, share
DRSR_REGION_1:  dcd  0x00000033  ; Size 64MB, MPU enable 

DRBAR_REGION_2: dcd  0x20000000  ; Base address = 2000_0000h 
DRACR_REGION_2: dcd  0x0000030C  ; R/W(full), Normal, Non-cache, share
DRSR_REGION_2:  dcd  0x00000025  ; Size 512KB, MPU enable

DRBAR_REGION_3: dcd  0x22000000  ; Base address = 2200_0000h 
DRACR_REGION_3: dcd  0x00000307  ; R/W(full), Normal, Write-back no allocate, share
DRSR_REGION_3:  dcd  0x00000033  ; Size 64MB, MPU enable 

DRBAR_REGION_4: dcd  0x30000000  ; Base address = 3000_0000h 
DRACR_REGION_4: dcd  0x0000030F  ; R/W(full), Normal, Write-back write allocate, share 
DRSR_REGION_4:  dcd  0x00000033  ; Size 64MB, MPU enable  

DRBAR_REGION_5: dcd  0x40000000  ; Base address = 4000_0000h 
DRACR_REGION_5: dcd  0x0000030F  ; R/W(full), Normal, Write-back write allocate, share 
DRSR_REGION_5:  dcd  0x00000035  ; Size 128MB, MPU enable  
 
DRBAR_REGION_6: dcd  0x48000000  ; Base address = 4800_0000h 
DRACR_REGION_6: dcd  0x0000030F  ; R/W(full), Normal, Write-back write allocate, share 
DRSR_REGION_6:  dcd  0x00000035  ; Size 128MB, MPU enable  

DRBAR_REGION_7: dcd  0x50000000  ; Base address = 5000_0000h 
DRACR_REGION_7: dcd  0x00001305  ; R/W(full), XN, Device, share 
DRSR_REGION_7:  dcd  0x00000035  ; Size 128MB, MPU enable  

DRBAR_REGION_8: dcd  0x60000000  ; Base address = 6000_0000h
DRACR_REGION_8: dcd  0x0000030C  ; R/W(full), Normal, Non-cache, share 
DRSR_REGION_8:  dcd  0x00000035  ; Size 128MB, MPU enable  

DRBAR_REGION_9: dcd  0x68000000  ; Base address = 6800_0000h 
DRACR_REGION_9: dcd  0x0000030C  ; R/W(full), Normal, Non-cache, share 
DRSR_REGION_9:  dcd  0x00000035  ; Size 128MB, MPU enable  
 
DRBAR_REGION_10: dcd  0x70000000 ; Base address = 7000_0000h 
DRACR_REGION_10: dcd  0x00001305 ; R/W(full), XN, Device, share 
DRSR_REGION_10:  dcd  0x00000035 ; Size 128MB, MPU enable  

DRBAR_REGION_11: dcd  0x80000000 ; Base address = 8000_0000h 
DRACR_REGION_11: dcd  0x00001305 ; R/W(full), XN, Device, share 
DRSR_REGION_11:  dcd  0x0000003D ; Size 2GB, MPU enable  

cache_init:
    push  {lr}

cache_invalidate:
    ; Invalidate the I1, D1 cache 
    mov  r0, #0
    mcr  p15, #0, r0, c7, c5, #0   ; Invalidate all Instruction Caches (Write-value is Ignored)
    isb                            ; Ensuring Context-changing
    mcr  p15, #0, r0, c15, c5, #0  ; Invalidate all Data Caches (Write-value is Ignored)
    isb                            ; Ensuring Context-changing
  
    ; Adopt default memory map as background map.
    ldr  r0, SCTLR_BR           ; Set SCTLR.BR bit to 1
    mrc  p15, 0, r1, c1, c0, 0  
    orr  r1, r1, r0
    dsb
    mcr  p15, 0, r1, c1, c0, 0  
    isb                         ; Ensuring Context-changing
    
    ; Initialize MPU settings (region 0 to 11)
    ; Define region 0
    mov  r0,  #0
    ldr  r1, DRBAR_REGION_0
    ldr  r2, DRACR_REGION_0
    ldr  r3, DRSR_REGION_0
    bl  mpu_init

    ; Define region 1
    mov  r0,  #1
    ldr  r1, DRBAR_REGION_1
    ldr  r2, DRACR_REGION_1
    ldr  r3, DRSR_REGION_1
    bl  mpu_init

    ; Define region 2
    mov  r0,  #2
    ldr  r1, DRBAR_REGION_2
    ldr  r2, DRACR_REGION_2
    ldr  r3, DRSR_REGION_2
    bl  mpu_init

    ; Define region 3
    mov  r0,  #3
    ldr  r1, DRBAR_REGION_3
    ldr  r2, DRACR_REGION_3
    ldr  r3, DRSR_REGION_3
    bl  mpu_init

    ; Define region 4
    mov  r0,  #4
    ldr  r1, DRBAR_REGION_4
    ldr  r2, DRACR_REGION_4
    ldr  r3, DRSR_REGION_4
    bl  mpu_init

    ; Define region 5
    mov  r0,  #5
    ldr  r1, DRBAR_REGION_5
    ldr  r2, DRACR_REGION_5
    ldr  r3, DRSR_REGION_5
    bl  mpu_init

    ; Define region 6
    mov  r0,  #6
    ldr  r1, DRBAR_REGION_6
    ldr  r2, DRACR_REGION_6
    ldr  r3, DRSR_REGION_6
    bl  mpu_init

    ; Define region 7
    mov  r0,  #7
    ldr  r1, DRBAR_REGION_7
    ldr  r2, DRACR_REGION_7
    ldr  r3, DRSR_REGION_7
    bl  mpu_init

    ; Define region 8
    mov  r0,  #8
    ldr  r1, DRBAR_REGION_8
    ldr  r2, DRACR_REGION_8
    ldr  r3, DRSR_REGION_8
    bl  mpu_init

    ; Define region 9
    mov  r0,  #9
    ldr  r1, DRBAR_REGION_9
    ldr  r2, DRACR_REGION_9
    ldr  r3, DRSR_REGION_9
    bl  mpu_init

    ; Define region 10
    mov  r0,  #10
    ldr  r1, DRBAR_REGION_10
    ldr  r2, DRACR_REGION_10
    ldr  r3, DRSR_REGION_10
    bl  mpu_init

    ; Define region 11
    mov  r0,  #11
    ldr  r1, DRBAR_REGION_11
    ldr  r2, DRACR_REGION_11
    ldr  r3, DRSR_REGION_11
    bl  mpu_init
    
    ; Enables MPU operation
    ldr  r0, SCTLR_M            ; Set SCTLR.M bit to 1
    mrc  p15, 0, r1, c1, c0, 0  
    orr  r1, r1, r0
    dsb
    mcr  p15, 0, r1, c1, c0, 0  
    isb                         ; Ensuring Context-changing
    
    ; Enables I1,D1 cache operation
    ldr  r0, SCTLR_I_C          ; Set SCTLR.I and C bit to 1
    mrc  p15, 0, r1, c1, c0, 0  
    orr  r1, r1, r0
    dsb
    mcr  p15, 0, r1, c1, c0, 0  
    isb                         ; Ensuring Context-changing

    pop  {pc}
    bx  lr

;***********************************************************************
; Function Name : mpu_init
; Description   : Initialize MPU settings
; Arguments     : none
; Return Value  : none
;***********************************************************************
mpu_init:
    ; RGNR(MPU Memory Region Number Register)
    mcr p15, #0, r0, c6, c2, #0
    isb                             ; Ensuring Context-changing
    
    ; DRBAR(Data Region Base Address Register)
    mcr  p15, #0, r1, c6, c1, #0
    isb                             ; Ensuring Context-changing

    ; DRACR(Data Region Access Control Register)
    mcr p15, #0, r2, c6, c1, #4
    isb                             ; Ensuring Context-changing

    ; DRSR(Data Region Size and Enable Register)
    mcr p15, #0, r3, c6, c1, #2
    isb                             ; Ensuring Context-changing
    
    bx      lr


;***********************************************************************
; Function Name : set_low_vec
; Description   : Initialize sysytem by loader program
; Arguments     : none
; Return Value  : none
;***********************************************************************
set_low_vec:
    mrc  p15, 0, r0, c1, c0, 0  ; Set SCTLR.V bit to 1 (low-vector)
    and  r0, r0, #0xFFFFDFFF
    mcr  p15, 0, r0, c1, c0, 0
    isb                         ; Ensuring Context-changing
    
    bx  lr  

    END   
; End of File 
