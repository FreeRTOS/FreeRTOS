/*
	FreeRTOS.org V5.1.2 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

	EXTERN pxCurrentTCB
	EXTERN usCriticalNesting

#include "FreeRTOSConfig.h"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Context save and restore macro definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

portSAVE_CONTEXT MACRO

    add     -0x0C,sp			; prepare stack to save necessary values
    st.w    lp,8[sp]			; store LP to stack
    stsr    0,r31
    st.w    lp,4[sp]			; store EIPC to stack
    stsr    1,lp
    st.w    lp,0[sp]			; store EIPSW to stack
#if configDATA_MODE == 1                                        ; Using the Tiny data model
    prepare {r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30},76,sp ; save general purpose registers
    sst.w   r19,72[ep]
    sst.w   r18,68[ep]
    sst.w   r17,64[ep]
    sst.w   r16,60[ep]
    sst.w   r15,56[ep]
    sst.w   r14,52[ep]
    sst.w   r13,48[ep]
    sst.w   r12,44[ep]
    sst.w   r11,40[ep]
    sst.w   r10,36[ep]
    sst.w   r9,32[ep]
    sst.w   r8,28[ep]
    sst.w   r7,24[ep]
    sst.w   r6,20[ep]
    sst.w   r5,16[ep]
    sst.w   r4,12[ep]
#else                                                           ; Using the Small/Large data model
    prepare {r20,r21,r22,r23,r24,r26,r27,r28,r29,r30},72,sp     ; save general purpose registers
    sst.w   r19,68[ep]
    sst.w   r18,64[ep]
    sst.w   r17,60[ep]
    sst.w   r16,56[ep]
    sst.w   r15,52[ep]
    sst.w   r14,48[ep]
    sst.w   r13,44[ep]
    sst.w   r12,40[ep]
    sst.w   r11,36[ep]
    sst.w   r10,32[ep]
    sst.w   r9,28[ep]
    sst.w   r8,24[ep]
    sst.w   r7,20[ep]
    sst.w   r6,16[ep]
    sst.w   r5,12[ep]
#endif /* configDATA_MODE */
    sst.w   r2,8[ep]
    sst.w   r1,4[ep]
    MOVHI   hi1(usCriticalNesting),r0,r1	; save usCriticalNesting value to stack
    ld.w    lw1(usCriticalNesting)[r1],r2
    sst.w   r2,0[ep]
    MOVHI   hi1(pxCurrentTCB),r0,r1			; save SP to top of current TCB
    ld.w    lw1(pxCurrentTCB)[r1],r2
    st.w    sp,0[r2]
    ENDM


portRESTORE_CONTEXT MACRO

    MOVHI   hi1(pxCurrentTCB),r0,r1			; get Stackpointer address
    ld.w    lw1(pxCurrentTCB)[r1],sp
    MOV     sp,r1
    ld.w    0[r1],sp						; load stackpointer
    MOV     sp,ep							; set stack pointer to element pointer
    sld.w   0[ep],r1						; load usCriticalNesting value from stack
    MOVHI   hi1(usCriticalNesting),r0,r2
    st.w    r1,lw1(usCriticalNesting)[r2]
    sld.w   4[ep],r1						; restore general purpose registers
    sld.w   8[ep],r2
#if configDATA_MODE == 1					; Using Tiny data model
    sld.w   12[ep],r4
    sld.w   16[ep],r5
    sld.w   20[ep],r6
    sld.w   24[ep],r7
    sld.w   28[ep],r8
    sld.w   32[ep],r9
    sld.w   36[ep],r10
    sld.w   40[ep],r11
    sld.w   44[ep],r12
    sld.w   48[ep],r13
    sld.w   52[ep],r14
    sld.w   56[ep],r15
    sld.w   60[ep],r16
    sld.w   64[ep],r17
    sld.w   68[ep],r18
    sld.w   72[ep],r19
    dispose 76,{r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30}
#else										; Using Small/Large data model
    sld.w   12[ep],r5
    sld.w   16[ep],r6
    sld.w   20[ep],r7
    sld.w   24[ep],r8
    sld.w   28[ep],r9
    sld.w   32[ep],r10
    sld.w   36[ep],r11
    sld.w   40[ep],r12
    sld.w   44[ep],r13
    sld.w   48[ep],r14
    sld.w   52[ep],r15
    sld.w   56[ep],r16
    sld.w   60[ep],r17
    sld.w   64[ep],r18
    sld.w   68[ep],r19
    dispose 72,{r20,r21,r22,r23,r24,r26,r27,r28,r29,r30}
#endif /* configDATA_MODE */
    ld.w    0[sp],lp						; restore EIPSW from stack
    ldsr    lp,1
    ld.w    4[sp],lp						; restore EIPC from stack
    ldsr    lp,0
    ld.w    8[sp],lp						; restore LP from stack
    add     0x0C,sp							; set SP to right position

    RETI

    ENDM
