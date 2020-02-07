/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
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

	SECTION .text:CODE:NOROOT(2)
	THUMB

	PUBLIC SecureContext_LoadContextAsm
	PUBLIC SecureContext_SaveContextAsm

#if ( configENABLE_FPU == 1 )
	#error Cortex-M23 does not have a Floating Point Unit (FPU) and therefore configENABLE_FPU must be set to 0.
#endif
/*-----------------------------------------------------------*/

SecureContext_LoadContextAsm:
	/* xSecureContextHandle value is in r0. */
	mrs r1, ipsr							/* r1 = IPSR. */
	cbz r1, load_ctx_therad_mode			/* Do nothing if the processor is running in the Thread Mode. */
	ldmia r0!, {r1, r2}						/* r1 = xSecureContextHandle->pucCurrentStackPointer, r2 = xSecureContextHandle->pucStackLimit. */
#if ( configENABLE_MPU == 1 )
	ldmia r1!, {r3}							/* Read CONTROL register value from task's stack. r3 = CONTROL. */
	msr control, r3							/* CONTROL = r3. */
#endif /* configENABLE_MPU */
	msr psplim, r2							/* PSPLIM = r2. */
	msr psp, r1								/* PSP = r1. */

	load_ctx_therad_mode:
		bx lr
/*-----------------------------------------------------------*/

SecureContext_SaveContextAsm:
	/* xSecureContextHandle value is in r0. */
	mrs r1, ipsr							/* r1 = IPSR. */
	cbz r1, save_ctx_therad_mode			/* Do nothing if the processor is running in the Thread Mode. */
	mrs r1, psp								/* r1 = PSP. */
#if ( configENABLE_MPU == 1 )
	mrs r2, control							/* r2 = CONTROL. */
	subs r1, r1, #4							/* Make space for the CONTROL value on the stack. */
	str r1, [r0]							/* Save the top of stack in context. xSecureContextHandle->pucCurrentStackPointer = r1. */
	stmia r1!, {r2}							/* Store CONTROL value on the stack. */
#else /* configENABLE_MPU */
	str r1, [r0]							/* Save the top of stack in context. xSecureContextHandle->pucCurrentStackPointer = r1. */
#endif /* configENABLE_MPU */
	movs r1, #0								/* r1 = securecontextNO_STACK. */
	msr psplim, r1							/* PSPLIM = securecontextNO_STACK. */
	msr psp, r1								/* PSP = securecontextNO_STACK i.e. No stack for thread mode until next task's context is loaded. */

	save_ctx_therad_mode:
		bx lr
/*-----------------------------------------------------------*/

	END
