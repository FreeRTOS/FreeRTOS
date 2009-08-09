/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

        .global _vPortYield
		.extern _vTaskSwitchContext
		.extern uxCriticalNesting

_vPortYield:

		PUSH	SR						/* Save the SR used by the task.... */
		PUSH	W0						/* ....then disable interrupts. */
		MOV		#32, W0
		MOV		W0, SR
		PUSH	W1						/* Save registers to the stack. */
		PUSH.D	W2
		PUSH.D	W4
		PUSH.D	W6
		PUSH.D 	W8
		PUSH.D 	W10
		PUSH.D	W12
		PUSH	W14
		PUSH	RCOUNT
		PUSH	TBLPAG
																						
		PUSH	CORCON
		PUSH	PSVPAG
		MOV		_uxCriticalNesting, W0		/* Save the critical nesting counter for the task. */
		PUSH	W0
		MOV		_pxCurrentTCB, W0			/* Save the new top of stack into the TCB. */
		MOV		W15, [W0]

		call 	_vTaskSwitchContext

		MOV		_pxCurrentTCB, W0			/* Restore the stack pointer for the task. */
		MOV		[W0], W15
		POP		W0							/* Restore the critical nesting counter for the task. */
		MOV		W0, _uxCriticalNesting
		POP		PSVPAG
		POP		CORCON
		POP		TBLPAG
		POP		RCOUNT						/* Restore the registers from the stack. */
		POP		W14
		POP.D	W12
		POP.D	W10
		POP.D	W8
		POP.D	W6
		POP.D	W4
		POP.D	W2
		POP.D	W0
		POP		SR

        return

        .end
