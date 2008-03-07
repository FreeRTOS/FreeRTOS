#include "xreg405.h"

	.extern pxCurrentTCB
	.extern vTaskSwitchContext
	.extern vTaskIncrementTick
	.extern vPortISRHandler

	.global vPortStartFirstTask
	.global vPortYield
	.global vPortTickISR
	.global vPortISRWrapper

.set	BChainField, 0
.set	NextLRField, BChainField + 4
.set	MSRField,    NextLRField + 4
.set	PCField,     MSRField    + 4
.set	LRField,     PCField     + 4
.set	CTRField,    LRField     + 4
.set	XERField,    CTRField    + 4
.set	CRField,     XERField    + 4
.set	USPRG0Field, CRField     + 4
.set	r0Field,     USPRG0Field + 4
.set	r2Field,     r0Field     + 4
.set	r3r31Field,  r2Field     + 4
.set	IFrameSize,  r3r31Field  + ( ( 31 - 3 ) + 1 ) * 4


.macro portSAVE_STACK_POINTER_AND_LR

	# Get the address of the TCB.				
	xor		R0, R0, R0
	addis	R2, R0, pxCurrentTCB@ha
	lwz		R2,	pxCurrentTCB@l( R2 )

	# Store the stack pointer into the TCB
	stw		SP,	0( R2 )

	# Save the link register
	stwu	R1, -24( R1 )
	mflr	R0
	stw		R31, 20( R1 )
	stw		R0, 28( R1 )
	mr		R31, r1

.endm

.macro portRESTORE_STACK_POINTER_AND_LR

	# Restore the link register
	lwz		R11, 0( R1 )
	lwz		R0, 4( R11 )
	mtlr	R0
	lwz		R31, -4( R11 )
	mr		R1, R11

	# Get the address of the TCB.
	xor		R0, R0, R0
	addis   SP, R0, pxCurrentTCB@ha
	lwz		SP,	pxCurrentTCB@l( R1 )

	# Get the task stack pointer from the TCB.
	lwz		SP, 0( SP )

.endm


vPortStartFirstTask:

	# Get the address of the TCB.
	xor		R0, R0, R0
    addis   SP, R0, pxCurrentTCB@ha
    lwz		SP,	pxCurrentTCB@l( SP )

	# Get the task stack pointer from the TCB.
	lwz		SP, 0( SP )
	
	# Restore MSR register to SRR1.
	lwz		R0, MSRField(R1)
	mtsrr1	R0
	
	# Restore current PC location to SRR0.
	lwz		R0, PCField(R1)
	mtsrr0	R0

	# Save  USPRG0 register
	lwz		R0, USPRG0Field(R1)
	mtspr	0x100,R0
	
	# Restore Condition register
	lwz		R0, CRField(R1)
	mtcr	R0
	
	# Restore Fixed Point Exception register
	lwz		R0, XERField(R1)
	mtxer	R0
	
	# Restore Counter register
	lwz		R0, CTRField(R1)
	mtctr	R0
	
	# Restore Link register
	lwz		R0, LRField(R1)
	mtlr	R0
	
	# Restore remaining GPR registers.
	lmw	R3,r3r31Field(R1)
	
	# Restore r0 and r2.
	lwz		R0, r0Field(R1)
	lwz		R2, r2Field(R1)
	
	# Remove frame from stack
	addi	R1,R1,IFrameSize

	# Return into the first task
	rfi



vPortYield:

	portSAVE_STACK_POINTER_AND_LR
	bl vTaskSwitchContext
	portRESTORE_STACK_POINTER_AND_LR
	blr

vPortTickISR:

	portSAVE_STACK_POINTER_AND_LR
	bl vTaskIncrementTick
	#if configUSE_PREEMPTION == 1
		bl vTaskSwitchContext
	#endif

	# Clear the interrupt
	lis		R0, 2048
	mttsr	R0

	portRESTORE_STACK_POINTER_AND_LR
	blr

vPortISRWrapper:

	portSAVE_STACK_POINTER_AND_LR
	bl vPortISRHandler
	portRESTORE_STACK_POINTER_AND_LR
	blr
