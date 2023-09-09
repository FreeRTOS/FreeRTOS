;-------------------------------------------------------------------------------
; sys_intvecs.asm
;
; (c) Texas Instruments 2009-2010, All rights reserved.
;

        .sect ".intvecs"

;-------------------------------------------------------------------------------
; import reference for interrupt routines

        .ref _c_int00
        .ref vPortYieldProcessor

;-------------------------------------------------------------------------------
; interrupt vectors

        b   _c_int00				; reset
        b   #-8						; undefined instruction
        b   vPortYieldProcessor		; software interrupt
        b   #-8						; Abort (prefetch)
        b   #-8						; Abort (data)
        b   #-8						; Reserved
        ldr pc,[pc,#-0x1b0]			; IRQ
        ldr pc,[pc,#-0x1b0]			; FIQ


;-------------------------------------------------------------------------------
