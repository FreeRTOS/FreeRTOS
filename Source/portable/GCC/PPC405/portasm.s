	.extern pxCurrentTCB
	.extern vTaskSwitchContext

	.global vStartFirstTask
	.global vPortYield

.set portCONTEXT_SIZE, 156
.set portR0_OFFSET, 152
.set portGPR_OFFSET, 32
.set portCR_OFFSET, 28
.set portXER_OFFSET, 24
.set portLR_OFFSET, 20
.set portCTR_OFFSET, 16
.set portUSPRG0_OFFSET, 12
.set portSRR0_OFFSET, 8
.set portSRR1_OFFSET, 4

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

vStartFirstTask:
	portRESTORE_CONTEXT
	rfi



vPortYield:

	portSAVE_CONTEXT
	bl vTaskSwitchContext
	portRESTORE_CONTEXT

	NOP
	NOP
