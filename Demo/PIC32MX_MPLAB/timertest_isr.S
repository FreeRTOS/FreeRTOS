#include <p32xxxx.h>
#include <sys/asm.h>
#include "ISR_Support.h"

	.set	nomips16
 	.set 	noreorder
 	
 	.extern vT2InterruptHandler
	.extern xISRStackTop
 	.global	vT2InterruptWrapper

	.set		noreorder
	.set 		noat
	.ent		vT2InterruptWrapper

vT2InterruptWrapper:

	portSAVE_CONTEXT
	jal vT2InterruptHandler
	nop
	portRESTORE_CONTEXT

	.end		vT2InterruptWrapper

