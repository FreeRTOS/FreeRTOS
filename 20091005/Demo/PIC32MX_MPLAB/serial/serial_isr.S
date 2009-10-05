#include <p32xxxx.h>
#include <sys/asm.h>
#include "ISR_Support.h"

	.set	nomips16
 	.set 	noreorder
 	
 	.extern vU2InterruptHandler
	.extern xISRStackTop
 	.global	vU2InterruptWrapper

	.set		noreorder
	.set 		noat
	.ent		vU2InterruptWrapper

vU2InterruptWrapper:

	portSAVE_CONTEXT
	jal vU2InterruptHandler
	nop
	portRESTORE_CONTEXT

	.end		vU2InterruptWrapper

