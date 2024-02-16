;-------------------------------------------------------------------------------
;   This file contains an Interrupt Vector Table used by the
;   IAR C/C++ Compiler for RL78 version 3.xx or later.
;
;   Modified for use with Amazon FreeRTOS.
;    
;   IAR Source License
;    
;   The following license agreement applies to linker command files, 
;   example projects (unless another license is explicitly stated), the 
;   cstartup code, low_level_init.c, and some other low-level runtime 
;   library files. 
;
;   Copyright 2016-2022 IAR Systems AB.
;
;   This source code is the property of IAR Systems. The source code may only
;   be used together with the IAR Embedded Workbench. Redistribution and use 
;   in source and binary forms, with or without modification, is permitted 
;   provided that the following conditions are met:
;
;   - Redistributions of source code, in whole or in part, must retain the 
;   above copyright notice, this list of conditions and the disclaimer below.
;
;   - IAR Systems name may not be used to endorse or promote products
;   derived from this software without specific prior written permission.
;
;   THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
;   WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
;   MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
;   ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
;   WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
;   ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
;   OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
;-------------------------------------------------------------------------------

    NAME   _interrupt_vector_table

#if !defined(__IASMRL78__) || (__VER__ < 310)
    #error "This demo requires the IAR Assembler for RL78 version 3.10 or later."
#endif

;   The portmacro.h header provides the portSAVE_CONTEXT() and
;   portRESTORE_context() macros.
#include "portmacro.h"

;   Hardware includes.
#include "demo_specific_io.h"

;   The interrupt handler for the _vPortTickISR is installed according to the
;   address of INTIT_vect interrupt, defined in the `<ior5f1nnn.h>` header.
    EXTERN _vPortTickISR

;   The interrupt handler for the _vPortYield is always installed in the address
;   of the BRK_I_vect interrupt, also defined in the `<ior5f1nnn.h>` header.
    EXTERN _vPortYield


;-------------------------------------------------------------------------------
;   This demo does not include a functional ISR other the ones required by
;   FreeRTOS.
;
;   ISRs that do not cause a context switch have no special requirements and
;   can be written as per compiler documentation.
;
;   The Assembly wrapper uses a callback function named _vAnExampleISR_C_Handler
;   which is implemented in `main.c`. See the documentation page for this demo
;   on the FreeRTOS.prg website for full instructions.
;
;   NOTE: vAnExampleISR_ASM_Wrapper needs to be installed into the relevant
;   vector in the Interrupt Vector Table below. For this example, it is
;   installed into the interrupt vector table under the address 0x3A.
;-------------------------------------------------------------------------------
    PUBLIC _vAnExampleISR_ASM_Wrapper
    EXTERN _vAnExampleISR_C_Handler

    SECTION `.text`:CODE
_vAnExampleISR_ASM_Wrapper:
    portSAVE_CONTEXT                    ; The wrapped ISR must start with the portSAVE_CONTEXT() macro.

    CALL    _vAnExampleISR_C_Handler    ; Once the context has been saved the C handler can be called.

    portRESTORE_CONTEXT                 ; The wrapped ISR must end with the to portRESTORE_CONTEXT() macro.

    RETI                                ; Returns from the interrupt to whichever task task is now the task selected
                                        ; to run (which might differ from the task that was running before the ISR.
;-------------------------------------------------------------------------------

    PUBLIC _interrupt_vector_table

    EXTERN ___interrupt_0x00
    PUBLIC ___interrupt_tab_0x00
    EXTERN ___interrupt_0x04
    PUBLIC ___interrupt_tab_0x04
    EXTERN ___interrupt_0x06
    PUBLIC ___interrupt_tab_0x06
    EXTERN ___interrupt_0x08
    PUBLIC ___interrupt_tab_0x08
    EXTERN ___interrupt_0x0A
    PUBLIC ___interrupt_tab_0x0A
    EXTERN ___interrupt_0x0C
    PUBLIC ___interrupt_tab_0x0C
    EXTERN ___interrupt_0x0E
    PUBLIC ___interrupt_tab_0x0E
    EXTERN ___interrupt_0x10
    PUBLIC ___interrupt_tab_0x10
    EXTERN ___interrupt_0x12
    PUBLIC ___interrupt_tab_0x12
    EXTERN ___interrupt_0x14
    PUBLIC ___interrupt_tab_0x14
    EXTERN ___interrupt_0x16
    PUBLIC ___interrupt_tab_0x16
    EXTERN ___interrupt_0x18
    PUBLIC ___interrupt_tab_0x18
    EXTERN ___interrupt_0x1A
    PUBLIC ___interrupt_tab_0x1A
    EXTERN ___interrupt_0x1C
    PUBLIC ___interrupt_tab_0x1C
    EXTERN ___interrupt_0x1E
    PUBLIC ___interrupt_tab_0x1E
    EXTERN ___interrupt_0x20
    PUBLIC ___interrupt_tab_0x20
    EXTERN ___interrupt_0x22
    PUBLIC ___interrupt_tab_0x22
    EXTERN ___interrupt_0x24
    PUBLIC ___interrupt_tab_0x24
    EXTERN ___interrupt_0x26
    PUBLIC ___interrupt_tab_0x26
    EXTERN ___interrupt_0x28
    PUBLIC ___interrupt_tab_0x28
    EXTERN ___interrupt_0x2A
    PUBLIC ___interrupt_tab_0x2A
    EXTERN ___interrupt_0x2C
    PUBLIC ___interrupt_tab_0x2C
    EXTERN ___interrupt_0x2E
    PUBLIC ___interrupt_tab_0x2E
    EXTERN ___interrupt_0x30
    PUBLIC ___interrupt_tab_0x30
    EXTERN ___interrupt_0x32
    PUBLIC ___interrupt_tab_0x32
    EXTERN ___interrupt_0x34
    PUBLIC ___interrupt_tab_0x34
    EXTERN ___interrupt_0x36
    PUBLIC ___interrupt_tab_0x36
    EXTERN ___interrupt_0x38
    PUBLIC ___interrupt_tab_0x38
    EXTERN ___interrupt_0x3A
    PUBLIC ___interrupt_tab_0x3A
    EXTERN ___interrupt_0x3C
    PUBLIC ___interrupt_tab_0x3C
    EXTERN ___interrupt_0x3E
    PUBLIC ___interrupt_tab_0x3E
    EXTERN ___interrupt_0x40
    PUBLIC ___interrupt_tab_0x40
    EXTERN ___interrupt_0x42
    PUBLIC ___interrupt_tab_0x42
    EXTERN ___interrupt_0x44
    PUBLIC ___interrupt_tab_0x44
    EXTERN ___interrupt_0x46
    PUBLIC ___interrupt_tab_0x46
    EXTERN ___interrupt_0x48
    PUBLIC ___interrupt_tab_0x48
    EXTERN ___interrupt_0x4A
    PUBLIC ___interrupt_tab_0x4A
    EXTERN ___interrupt_0x4C
    PUBLIC ___interrupt_tab_0x4C
    EXTERN ___interrupt_0x4E
    PUBLIC ___interrupt_tab_0x4E
    EXTERN ___interrupt_0x50
    PUBLIC ___interrupt_tab_0x50
    EXTERN ___interrupt_0x52
    PUBLIC ___interrupt_tab_0x52
    EXTERN ___interrupt_0x54
    PUBLIC ___interrupt_tab_0x54
    EXTERN ___interrupt_0x56
    PUBLIC ___interrupt_tab_0x56
    EXTERN ___interrupt_0x58
    PUBLIC ___interrupt_tab_0x58
    EXTERN ___interrupt_0x5A
    PUBLIC ___interrupt_tab_0x5A
    EXTERN ___interrupt_0x5C
    PUBLIC ___interrupt_tab_0x5C
    EXTERN ___interrupt_0x5E
    PUBLIC ___interrupt_tab_0x5E
    EXTERN ___interrupt_0x60
    PUBLIC ___interrupt_tab_0x60
    EXTERN ___interrupt_0x62
    PUBLIC ___interrupt_tab_0x62
    EXTERN ___interrupt_0x64
    PUBLIC ___interrupt_tab_0x64
    EXTERN ___interrupt_0x66
    PUBLIC ___interrupt_tab_0x66
    EXTERN ___interrupt_0x68
    PUBLIC ___interrupt_tab_0x68
    EXTERN ___interrupt_0x6A
    PUBLIC ___interrupt_tab_0x6A
    EXTERN ___interrupt_0x6C
    PUBLIC ___interrupt_tab_0x6C
    EXTERN ___interrupt_0x6E
    PUBLIC ___interrupt_tab_0x6E
    EXTERN ___interrupt_0x70
    PUBLIC ___interrupt_tab_0x70
    EXTERN ___interrupt_0x72
    PUBLIC ___interrupt_tab_0x72
    EXTERN ___interrupt_0x74
    PUBLIC ___interrupt_tab_0x74
    EXTERN ___interrupt_0x76
    PUBLIC ___interrupt_tab_0x76
    EXTERN ___interrupt_0x78
    PUBLIC ___interrupt_tab_0x78
    EXTERN ___interrupt_0x7A
    PUBLIC ___interrupt_tab_0x7A
    EXTERN ___interrupt_0x7C
    PUBLIC ___interrupt_tab_0x7C
    EXTERN ___interrupt_0x7E
    PUBLIC ___interrupt_tab_0x7E

;-------------------------------------------------------------------------------
;   Reset Vector
;   The reset vector is placed in the `.reset` section.
;-------------------------------------------------------------------------------
    SECTION `.reset`:CONST:ROOT(1)
_interrupt_vector_table:
___interrupt_tab_0x00:
    DATA16
    DC16      ___interrupt_0x00
;-------------------------------------------------------------------------------



;-------------------------------------------------------------------------------
;   Interrupt Vector Table
;   The table is placed in the `.intvec` section.
;-------------------------------------------------------------------------------
    SECTION `.intvec`:CONST:ROOT(1)
___interrupt_tab_0x04:
    DATA16
    DC16      ___interrupt_0x04

___interrupt_tab_0x06:
    DATA16
    DC16      ___interrupt_0x06

___interrupt_tab_0x08:
    DATA16
    DC16      ___interrupt_0x08

___interrupt_tab_0x0A:
    DATA16
    DC16      ___interrupt_0x0A

___interrupt_tab_0x0C:
    DATA16
    DC16      ___interrupt_0x0C

___interrupt_tab_0x0E:
    DATA16
    DC16      ___interrupt_0x0E

___interrupt_tab_0x10:
    DATA16
    DC16      ___interrupt_0x10

___interrupt_tab_0x12:
    DATA16
    DC16      ___interrupt_0x12

___interrupt_tab_0x14:
    DATA16
    DC16      ___interrupt_0x14

___interrupt_tab_0x16:
    DATA16
    DC16      ___interrupt_0x16

___interrupt_tab_0x18:
    DATA16
    DC16      ___interrupt_0x18

___interrupt_tab_0x1A:
    DATA16
    DC16      ___interrupt_0x1A

___interrupt_tab_0x1C:
    DATA16
    DC16      ___interrupt_0x1C

___interrupt_tab_0x1E:
    DATA16
    DC16      ___interrupt_0x1E

___interrupt_tab_0x20:
    DATA16
    DC16      ___interrupt_0x20

___interrupt_tab_0x22:
    DATA16
    DC16      ___interrupt_0x22

___interrupt_tab_0x24:
    DATA16
    DC16      ___interrupt_0x24

___interrupt_tab_0x26:
    DATA16
    DC16      ___interrupt_0x26

___interrupt_tab_0x28:
    DATA16
    DC16      ___interrupt_0x28

___interrupt_tab_0x2A:
    DATA16
    DC16      ___interrupt_0x2A

___interrupt_tab_0x2C:
    DATA16
    DC16      ___interrupt_0x2C

___interrupt_tab_0x2E:
    DATA16
    DC16      ___interrupt_0x2E

___interrupt_tab_0x30:
    DATA16
    DC16      ___interrupt_0x30

___interrupt_tab_0x32:
    DATA16
    DC16      ___interrupt_0x32

___interrupt_tab_0x34:
    DATA16
    DC16      ___interrupt_0x34

___interrupt_tab_0x36:
    DATA16
    DC16      ___interrupt_0x36
;-------------------------------------------------------------------------------
;   Install the _vPortTickISR handler for the RL78 devices where INTIT_vect==56.
;   Otherwise, installs the C Runtime Library default.
;-------------------------------------------------------------------------------
___interrupt_tab_0x38:
    DATA16
#if (0x38 == INTIT_vect)
    DC16      _vPortTickISR
#else
    DC16      ___interrupt_0x38
#endif
;-------------------------------------------------------------------------------


;-------------------------------------------------------------------------------
;   Place a pointer to the _vAnExampleISR_ASM_Wrapper at the correct index into
;   the interrupt vector table. This is an example for a ISR which needs context
;   switch.
;
;   NOTE: 0x3A is used is purely as an example.  The correct vector index for
;   the interrupt being installed must be used.
;-------------------------------------------------------------------------------
___interrupt_tab_0x3A:
    DATA16
    DC16      _vAnExampleISR_ASM_Wrapper
;-------------------------------------------------------------------------------


;-------------------------------------------------------------------------------
;   Install the _vPortTickISR handler for the RL78 devices where INTIT_vect==60.
;   Otherwise, installs the C Runtime Library default.
;-------------------------------------------------------------------------------
___interrupt_tab_0x3C:                 ; --- INTIT_vect(?)
    DATA16
#if (0x3C == INTIT_vect)
    DC16      _vPortTickISR
#else
    DC16      ___interrupt_0x3C
#endif
;-------------------------------------------------------------------------------

___interrupt_tab_0x3E:
    DATA16
    DC16      ___interrupt_0x3E

___interrupt_tab_0x40:
    DATA16
    DC16      ___interrupt_0x40

___interrupt_tab_0x42:
    DATA16
    DC16      ___interrupt_0x42

___interrupt_tab_0x44:
    DATA16
    DC16      ___interrupt_0x44

___interrupt_tab_0x46:
    DATA16
    DC16      ___interrupt_0x46

___interrupt_tab_0x48:
    DATA16
    DC16      ___interrupt_0x48

___interrupt_tab_0x4A:
    DATA16
    DC16      ___interrupt_0x4A

___interrupt_tab_0x4C:
    DATA16
    DC16      ___interrupt_0x4C

___interrupt_tab_0x4E:
    DATA16
    DC16      ___interrupt_0x4E

___interrupt_tab_0x50:
    DATA16
    DC16      ___interrupt_0x50

___interrupt_tab_0x52:
    DATA16
    DC16      ___interrupt_0x52

___interrupt_tab_0x54:
    DATA16
    DC16      ___interrupt_0x54

___interrupt_tab_0x56:
    DATA16
    DC16      ___interrupt_0x56

___interrupt_tab_0x58:
    DATA16
    DC16      ___interrupt_0x58

___interrupt_tab_0x5A:
    DATA16
    DC16      ___interrupt_0x5A

___interrupt_tab_0x5C:
    DATA16
    DC16      ___interrupt_0x5C

___interrupt_tab_0x5E:
    DATA16
    DC16      ___interrupt_0x5E

___interrupt_tab_0x60:
    DATA16
    DC16      ___interrupt_0x60

___interrupt_tab_0x62:
    DATA16
    DC16      ___interrupt_0x62

___interrupt_tab_0x64:
    DATA16
    DC16      ___interrupt_0x64

___interrupt_tab_0x66:
    DATA16
    DC16      ___interrupt_0x66

___interrupt_tab_0x68:
    DATA16
    DC16      ___interrupt_0x68

___interrupt_tab_0x6A:
    DATA16
    DC16      ___interrupt_0x6A

___interrupt_tab_0x6C:
    DATA16
    DC16      ___interrupt_0x6C

___interrupt_tab_0x6E:
    DATA16
    DC16      ___interrupt_0x6E

___interrupt_tab_0x70:
    DATA16
    DC16      ___interrupt_0x70

___interrupt_tab_0x72:
    DATA16
    DC16      ___interrupt_0x72

___interrupt_tab_0x74:
    DATA16
    DC16      ___interrupt_0x74

___interrupt_tab_0x76:
    DATA16
    DC16      ___interrupt_0x76

___interrupt_tab_0x78:
    DATA16
    DC16      ___interrupt_0x78

___interrupt_tab_0x7A:
    DATA16
    DC16      ___interrupt_0x7A

___interrupt_tab_0x7C:
    DATA16
    DC16      ___interrupt_0x7C
;-------------------------------------------------------------------------------
;   The BRK_I_vect (0x7E) is used by the RTOS context switch.
;-------------------------------------------------------------------------------
___interrupt_tab_0x7E:
    DATA16
    DC16      _vPortYield
;-------------------------------------------------------------------------------

    END
;-------------------------------------------------------------------------------
