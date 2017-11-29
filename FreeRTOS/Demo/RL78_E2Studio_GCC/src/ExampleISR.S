/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/*
 * This file defines the assembler wrapper for the example interrupt that is
 * defined in main.c.  The wrapper is the interrupt entry point.
 */

/* ISR_Support.h contains the definitions of portSAVE_CONTEXT() and
portRESTORE_CONTEXT(). */
#include "ISR_Support.h"

	.global	_vANExampleISR_ASM_Wrapper
	.extern _vAnExampleISR_C_Handler

	.text

	/*
	 * This demo does not include a functional interrupt service routine - so
	 * this dummy handler (which is not actually installed) is provided as an
	 * example of how an ISR that needs to cause a context switch needs to be
	 * implemented.  ISRs that do not cause a context switch have no special
	 * requirements and can be written as per the compiler documentation.
	 *
	 * This assembly wrapper function calls the main handler, which is called
	 * vAnExampleISR_C_Handler(), and is implemented in main.c.  See the
	 * documentation page for this demo on the FreeRTOS.org website for full
	 * instructions.
	 *
	 * NOTE:  vANExampleISR_ASM_Wrapper needs to be installed into the relevant
	 * vector within vector_table.c.
	 */

	 vANExampleISR_ASM_Wrapper:

	 	/* portSAVE_CONTEXT() must be the first thing called in the ASM
	 	wrapper. */
	 	portSAVE_CONTEXT

	 	/* Once the context has been saved the C handler can be called. */
	 	call !!_vAnExampleISR_C_Handler

	 	/* Finally the ISR must end with a call to portRESTORE_CONTEXT()
	 	followed by a reti instruction to return from the interrupt to whichever
	 	task is now the task selected to run (which may be different to the task
	 	that was running before the interrupt started). */
	    portRESTORE_CONTEXT
	    reti

	.end

