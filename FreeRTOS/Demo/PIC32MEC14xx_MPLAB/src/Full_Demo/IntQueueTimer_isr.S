/*
 * FreeRTOS V202012.00
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

#include <xc.h>
#include <sys/asm.h>
#include "ISR_Support.h"

#define portEXC_CODE_MASK ( 0x1f << 2 )


 	.extern vT0InterruptHandler
 	.extern vT1InterruptHandler

	.global vT0InterruptWrapper
	.global vT1InterruptWrapper


/******************************************************************/

	.set	micromips
	.set	noreorder
	.set 	noat
	.ent	vT0InterruptWrapper
	.global girq23_b0

girq23_b0:
vT0InterruptWrapper:

	portSAVE_CONTEXT

	jal		vT0InterruptHandler
	nop

	portRESTORE_CONTEXT

	.end vT0InterruptWrapper

/******************************************************************/

	.set	micromips
 	.set	noreorder
	.set 	noat
 	.ent	vT1InterruptWrapper
	.global girq23_b1

girq23_b1:
vT1InterruptWrapper:

	portSAVE_CONTEXT

	jal 	vT1InterruptHandler
	nop

	portRESTORE_CONTEXT

	.end vT1InterruptWrapper

