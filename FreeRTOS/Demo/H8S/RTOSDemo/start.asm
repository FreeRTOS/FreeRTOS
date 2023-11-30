;/****************************************************************
;KPIT Cummins Infosystems Ltd, Pune, India. - 4th September 2003.
;
;This program is distributed in the hope that it will be useful,
;but WITHOUT ANY WARRANTY; without even the implied warranty of
;MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE
;
;*****************************************************************/


;*********************************************************************
; File: start.asm
;
;
; desc:
; 
;  System initialisation routine - entry point for the application.
;  The stack pointer is initialised, then the hardware initialisation
;  routine called.  The static data areas are then initialised, before
;  the main function is executed.  A simple exit funtion is also
;  supplied
;
;*********************************************************************

#ifdef __H8300H__  

#ifdef __NORMAL_MODE__
	.h8300hn
#else
	.h8300h
#endif

#endif	/*_H8300H_ */

#ifdef __H8300S__

#ifdef __NORMAL_MODE__
	.h8300sn
#else
	.h8300s
#endif

#endif /* __H8300S__ */
	
	.section .text
	.global _start
#if DEBUG	
	.extern _exit
#endif

	.extern _hw_initialise
	.extern _main

	.extern _data
	.extern _mdata
	.extern _edata
	.extern _bss
	.extern _ebss
	.extern _stack

_start:
	; initialise the SP for non-vectored code
    mov.l   #_stack,er7
	; call the hardware initialiser
	jsr     @_hw_initialise
#ifdef ROMSTART	
	; get the boundaries for the .data section initialisation
    mov.l   #_data,er0
    mov.l   #_edata,er1
    mov.l   #_mdata,er2
    cmp.l   er0,er1
	beq     start_1
start_l:
    mov.b   @er2,r3l  ;get from src
    mov.b   r3l,@er0  ;place in dest
    inc.l   #1,er2    ;inc src
    inc.l   #1,er0    ;inc dest
    cmp.l   er0,er1   ;dest == edata?
	bne     start_l
start_1:
#endif		//ROMSTART
	; zero out bss
    mov.l   #_bss,er0
    mov.l   #_ebss,er1
    cmp.l   er0,er1         
	beq     start_3
	sub.b   r2l,r2l
start_2:
    mov.b   r2l,@er0
    inc.l   #1,er0
    cmp.l   er0,er1
	bne     start_2
start_3:
#ifdef CPPAPP	
	;Initialize global constructor	
	jsr	@___main
#endif
	
	; call the mainline     
	jsr     @_main

	
    mov.l   er0,er4
    
    ;call to exit
#if DEBUG
    jsr     @_exit
#endif
#if RELEASE
 exit:
	bra 	exit
#endif

	

