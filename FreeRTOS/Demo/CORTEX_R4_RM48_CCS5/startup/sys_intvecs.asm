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

        b   _c_int00
        b   #-8
        b   vPortYieldProcessor
        b   #-8
        b   #-8
        b   #-8
        ldr pc,[pc,#-0x1b0]
        ldr pc,[pc,#-0x1b0]


;-------------------------------------------------------------------------------
