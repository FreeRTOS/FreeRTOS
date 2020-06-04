;/*
; * FreeRTOS Kernel V10.3.0
; * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
; *
; * Permission is hereby granted, free of charge, to any person obtaining a copy of
; * this software and associated documentation files (the "Software"), to deal in
; * the Software without restriction, including without limitation the rights to
; * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
; * the Software, and to permit persons to whom the Software is furnished to do so,
; * subject to the following conditions:
; *
; * The above copyright notice and this permission notice shall be included in all
; * copies or substantial portions of the Software.
; *
; * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
; * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
; * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
; * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
; * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
; *
; * http://www.FreeRTOS.org
; * http://aws.amazon.com/freertos
; *
; * 1 tab == 4 spaces!
; */

	INCLUDE portmacro.inc

	;The UART interrupt entry point is defined within an assembly wrapper
	;within this file.  This takes care of the task context saving before it
	;calls the main handler (vUART_ISRHandler()) which is written in C within
	;serial.c.  The execution of the handler can unblock tasks that were blocked
	;waiting for UART events.  Once the handler completes the asm wrapper
	;finishes off by	restoring the context of whichever task is now selected to
	;enter the RUNNING state (which might now be a different task to that which
	;was originally interrupted.
	IMPORT vUART_ISRHandler
	EXPORT vUART_ISREntry

	;/* Interrupt entry must always be in ARM mode. */
	ARM
	AREA	|.text|, CODE, READONLY


vUART_ISREntry

	PRESERVE8

	; Save the context of the interrupted task.
	portSAVE_CONTEXT

	; Call the C handler function - defined within serial.c.
	LDR R0, =vUART_ISRHandler
	MOV LR, PC
	BX R0

	; Finish off by restoring the context of the task that has been chosen to
	; run next - which might be a different task to that which was originally
	; interrupted.
	portRESTORE_CONTEXT

	END
