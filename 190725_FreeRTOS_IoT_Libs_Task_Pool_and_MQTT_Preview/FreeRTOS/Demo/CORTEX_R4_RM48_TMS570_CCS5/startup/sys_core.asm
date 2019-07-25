;-------------------------------------------------------------------------------
; sys_core.asm
;
; (c) Texas Instruments 2009, All rights reserved.
;

    	.text
    	.arm

;-------------------------------------------------------------------------------
; Initialize CPU Registers

    	.def     _coreInitRegisters

_coreInitRegisters:
        mov   r0,         lr
        mov   r1,         #0x0000
        mov   r2,         #0x0000
        mov   r3,         #0x0000
        mov   r4,         #0x0000
        mov   r5,         #0x0000
        mov   r6,         #0x0000
        mov   r7,         #0x0000
        mov   r8,         #0x0000
        mov   r9,         #0x0000
        mov   r10,        #0x0000
        mov   r11,        #0x0000
        mov   r12,        #0x0000
        mov   r13,        #0x0000
        cps   #0x11  
        mov   lr,         r0
        mov   r8,         #0x0000
        mov   r9,         #0x0000
        mov   r10,        #0x0000
        mov   r11,        #0x0000
        mov   r12,        #0x0000
        mov   r13,        #0x0000
        cps   #0x12  
        mov   r13,        #0x0000
        mov   lr,         r0
        cps   #0x17
        mov   r13,        #0x0000
        mov   lr,         r0
        cps   #0x1B
        mov   r13,        #0x0000
        mov   lr,         r0
        cps   #0x13
        mov   r13,        #0x0000

	.if (__TI_VFPV3D16_SUPPORT__)
        fmdrr d0,        r1,     r1
        fmdrr d1,        r1,     r1
        fmdrr d2,        r1,     r1
        fmdrr d3,        r1,     r1
        fmdrr d4,        r1,     r1
        fmdrr d5,        r1,     r1
        fmdrr d6,        r1,     r1
        fmdrr d7,        r1,     r1
        fmdrr d8,        r1,     r1
        fmdrr d9,        r1,     r1
        fmdrr d10,       r1,     r1
        fmdrr d11,       r1,     r1
        fmdrr d12,       r1,     r1
        fmdrr d13,       r1,     r1
        fmdrr d14,       r1,     r1
        fmdrr d15,       r1,     r1
    .endif

        bl    $+4
        bl    $+4
        bl    $+4
        bl    $+4
        bx    r0


;-------------------------------------------------------------------------------
; Initialize Stack Pointers

    	.def     _coreInitStackPointer

_coreInitStackPointer:
        msr   cpsr_c,   #0xD1
        ldr   sp,       fiqSp
        msr   cpsr_c,   #0xD2
        ldr   sp,       irqSp
        msr   cpsr_c,   #0xD7
        ldr   sp,       abortSp
        msr   cpsr_c,   #0xDB
        ldr   sp,       undefSp
        msr   cpsr_c,   #0xDF
        ldr   sp,       userSp
        msr   cpsr_c,   #0xD3
        ldr   sp,       svcSp
        bx    lr

userSp  .word 0x00000000+0x00000000
svcSp   .word 0x08000000+0x00000100
fiqSp   .word 0x00000000+0x00000000
irqSp   .word 0x08000100+0x00000100
abortSp .word 0x00000000+0x00000000
undefSp .word 0x00000000+0x00000000


;-------------------------------------------------------------------------------
; Enable VFP Unit

    	.def     _coreEnableVfp

_coreEnableVfp:
	.if (__TI_VFPV3D16_SUPPORT__)
        mrc   p15, #0x00, r0, c1, c0, #0x02
        orr   r0, r0, #0xF00000
        mcr   p15, #0x00, r0, c1, c0, #0x02
        mov   r0, #0x40000000
        fmxr  fpexc, r0
	.endif
        bx    lr


;-------------------------------------------------------------------------------
; Enable Event Bus Export

    	.def  _coreEnableEventBusExport

_coreEnableEventBusExport:
        mrc   p15, #0x00, r0, c9, c12, #0x00
        orr   r0,  r0, #0x10
        mcr   p15, #0x00, r0, c9, c12, #0x00
        bx    lr

;-------------------------------------------------------------------------------
; Enable RAM ECC Support

    	.def  _coreEnableRamEcc

_coreEnableRamEcc:
        mrc   p15, #0x00, r0, c1, c0,  #0x01
        orr   r0,  r0, #0x0C000000
        mcr   p15, #0x00, r0, c1, c0,  #0x01
        bx    lr

;-------------------------------------------------------------------------------
; Enable Flash ECC Support

    	.def  _coreEnableFlashEcc

_coreEnableFlashEcc:
        mrc   p15, #0x00, r0, c1, c0,  #0x01
        orr   r0,  r0, #0x02000000
        mcr   p15, #0x00, r0, c1, c0,  #0x01
        bx    lr

;-------------------------------------------------------------------------------
; Enable Offset via Vic controller

    	.def  _coreEnableIrqVicOffset

_coreEnableIrqVicOffset:
        mrc   p15, #0, r0, c1, c0,  #0
        orr   r0,  r0, #0x01000000
        mcr   p15, #0, r0, c1, c0,  #0
        bx    lr
    
;-------------------------------------------------------------------------------

