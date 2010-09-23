	.macro portSAVE_CONTEXT

	; Save r0 to r14 and pr.
	movml.l r15, @-r15
	
	; Save mac1, mach and gbr
	sts.l	macl, @-r15
	sts.l	mach, @-r15
	stc.l	gbr, @-r15
	
	; Get the address of pxCurrentTCB
	mov.l	#_pxCurrentTCB, r0
	
	; Get the address of pxTopOfStack from the TCB.
	mov.l	@r0, r0
	
	; Save the stack pointer in pxTopOfStack.
	mov.l	r15, @r0

	.endm

;-----------------------------------------------------------

	.macro portRESTORE_CONTEXT

	; Get the address of the pxCurrentTCB variable.
	mov.l	#_pxCurrentTCB, r0

	; Get the address of the task stack from pxCurrentTCB.
	mov.l	@r0, r0

	; Get the task stack itself into the stack pointer. 
	mov.l	@r0, r15		

	; Restore system registers.
	ldc.l	@r15+, gbr
	lds.l	@r15+, mach
	lds.l	@r15+, macl

	; Restore r0 to r14 and PR
	movml.l	@r15+, r15
	
	; Pop the SR and PC to jump to the start of the task.
	rte
	nop

	.endm
;-----------------------------------------------------------