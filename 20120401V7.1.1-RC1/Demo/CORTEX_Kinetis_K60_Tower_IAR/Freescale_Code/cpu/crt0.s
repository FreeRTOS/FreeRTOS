/*
 * File:	crt0.s
 * Purpose:	Lowest level routines for Kinetis.
 *
 * Notes:	
 *
 */

;         AREA   Crt0, CODE, READONLY      ; name this block of code



  	SECTION .noinit : CODE
  	EXPORT  __startup
__startup

    MOV     r0,#0                   ; Initialize the GPRs
	MOV     r1,#0
	MOV     r2,#0
	MOV     r3,#0
	MOV     r4,#0
	MOV     r5,#0
	MOV     r6,#0
	MOV     r7,#0
	MOV     r8,#0
	MOV     r9,#0
	MOV     r10,#0
	MOV     r11,#0
	MOV     r12,#0
        import start
        BL      start                  ; call the C code
__done
        B       __done


        END
