// Rowley C Compiler, runtime support.
//
// Copyright (c) 2001, 2002, 2003 Rowley Associates Limited.
//
// This file may be distributed under the terms of the License Agreement
// provided with this software.
//
// THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE
// WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.

; Create sections
        .data
        .bss

; Go to code section.
        .code

; Executed upon reset
__reset proc

; Turn off watchdog.  You can enable it in main() if required.
        mov.w   #0x5a80, &0x120

; Set up stack.
        mov.w   #RAM_Start_Address+RAM_Size, sp

; Copy from initialised data section to data section.
        mov.w   #SFB(IDATA0), r15
        mov.w   #data_init_begin, r14
        mov.w   #data_init_end-data_init_begin, r13
        call    #_memcpy

; Zero the bss.  Ensure the stack is not allocated in the bss!
        mov.w   #SFB(UDATA0), r15
        mov.w   #0, r14
        mov.w   #SFE(UDATA0)-SFB(UDATA0), r13
        call    #_memset

; Call user entry point void main(void).
        call    #_main

; If main() returns, kick off again.
        jmp     __reset
        endproc

; Heap data structures; removed by the linker if the heap isn't used.
        .break   
        .data
        align   WORD
___heap_start__::
        DW      0
        DW      heap_size
        DS      heap_size-4    

; Reset vector
        .vectors
        .keep
        org     0x1e
        dw      __reset

; Initialise the IDATA0 section by duplicating the contents into the
; CONST section and copying them on startup.
        .const
data_init_begin:
        .init  "IDATA0"
data_init_end:
