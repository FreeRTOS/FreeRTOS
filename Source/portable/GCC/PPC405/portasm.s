#include "xreg405.h"

	.extern pxCurrentTCB
	.extern vTaskSwitchContext

	.global vStartFirstTask
	.global vPortYield

.set portCONTEXT_SIZE, 156
.set portR0_OFFSET, 152
.set portGPR_OFFSET, 32
.set portCR_OFFSET, 28
.set portXER_OFFSET, 24
.set portLR_OFFSET, 16
.set portCTR_OFFSET, 16
.set portUSPRG0_OFFSET, 12
.set portSRR0_OFFSET, 8
.set portSRR1_OFFSET, 4


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


.macro portRESTORE_CONTEXT

	# Get the address of the TCB.
	xor		R0, R0, R0
    addis   SP, R0, pxCurrentTCB@ha
    lwz		SP,	pxCurrentTCB@l( SP )

	# Get the task stack pointer from the TCB.
	lwz		SP, 0( SP )

	# Pop the special purpose registers
	lwz		R0, portSRR1_OFFSET( SP )
	mtspr   SRR1, R0
	lwz		R0, portSRR0_OFFSET( SP )
	mtspr   SRR0, R0
	lwz		R0, portUSPRG0_OFFSET( SP )
	mtspr   256, R0 #USPRG0
	lwz		R0, portCTR_OFFSET( SP )
	mtspr   CTR, R0
	lwz		R0, portLR_OFFSET( SP )
	mtspr   LR, R0
	lwz		R0, portXER_OFFSET( SP )
	mtspr   XER, R0
	lwz		R0, portCR_OFFSET( SP )
	mtcr	R0

	# Pop GPRs
	lmw		R2, portGPR_OFFSET( SP )

	# Finally pop R0 and correct the stack pointer
	lwz		R0, portR0_OFFSET( SP )
	addi	R1, R1, portCONTEXT_SIZE

	# Start the task running
	rfi

	.endm

.macro portSAVE_CONTEXT

	# Make room on the stack.
	subi	R1, R1, portCONTEXT_SIZE

	# Push R0, then the GPRs
	stw		R0, portR0_OFFSET( SP )
	stm		R2, portGPR_OFFSET( SP )

	# Push the SFRs
	mfcr	R0
	stw		R0, portCR_OFFSET( SP )
	mfspr	R0, XER
	stw		R0, portXER_OFFSET( SP )
	mfspr	R0, LR
	stw		R0, portLR_OFFSET( SP )
	mfspr	R0, CTR
	stw		R0, portCTR_OFFSET( SP )
	mfspr	R0, 256 #USPRG0
	stw		R0, portUSPRG0_OFFSET( SP )
	mfspr	R0, SRR0
	stw		R0, portSRR0_OFFSET( SP )
	mfspr	R0, SRR1
	stw		R0, portSRR1_OFFSET( SP )

	# Get the address of the TCB.
	xor		R0, R0, R0
	addis	R2, R0, pxCurrentTCB@ha
	lwz		R2,	pxCurrentTCB@l( R2 )

	# Store the stack pointer into the TCB
	stw		SP,	0( R2 )

	.endm


.macro int_epilogue

	# Get the address of the TCB.
	xor		R0, R0, R0
    addis   SP, R0, pxCurrentTCB@ha
    lwz		SP,	pxCurrentTCB@l( SP )

	# Get the task stack pointer from the TCB.
	lwz		SP, 0( SP )
	
	# Restore MSR register to SRR1.
	lwz	R0,MSRField(R1)
	mtsrr1	R0
	
	# Restore current PC location to SRR0.
	lwz	R0,PCField(R1)
	mtsrr0	R0

	# Save USPRG0 register
	lwz	R0,USPRG0Field(R1)
	mtspr	0x100,R0
	
	# Restore Condition register
	lwz	R0,CRField(R1)
	mtcr	R0
	
	# Restore Fixed Point Exception register
	lwz	R0,XERField(R1)
	mtxer	R0
	
	# Restore Counter register
	lwz	R0,CTRField(R1)
	mtctr	R0
	
	# Restore Link register
	lwz	R0,LRField(R1)
	mtlr	R0
	
	# Restore remaining GPR registers.
	lmw	R3,r3r31Field(R1)
	
	# Restore r0 and r2.
	lwz	R0,r0Field(R1)
	lwz	R2,r2Field(R1)
	
	# Remove frame from stack
	addi	R1,R1,IFrameSize
	
.endm

.macro portENTER_SWITCHING_ISR

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

.macro portEXIT_SWITCHING_ISR

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


vStartFirstTask:

	int_epilogue
	rfi

#vStartFirstTask:
#	portRESTORE_CONTEXT
#	rfi



vPortYield:

	portENTER_SWITCHING_ISR
	bl vTaskSwitchContext
	portEXIT_SWITCHING_ISR
	blr

	NOP
	NOP
