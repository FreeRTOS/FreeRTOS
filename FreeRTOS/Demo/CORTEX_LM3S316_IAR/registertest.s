	RSEG ICODE:CODE

	EXTERN vSetErrorLED

	PUBLIC vSetAndCheckRegisters

vSetAndCheckRegisters:
	/* Fill the general purpose registers with known values. */
	mov r11, #10
	add r0, r11, #1
	add r1, r11, #2
	add r2, r11, #3
	add r3, r11, #4
	add r4, r11, #5
	add r5, r11, #6
	add r6, r11, #7
	add r7, r11, #8
	add r8, r11, #9
	add r9, r11, #10
	add r10, r11, #11
	add r12, r11, #12

	/* Check the values are as expected. */
	cmp r11, #10
	bne set_error_led
	cmp r0, #11
	bne set_error_led
	cmp r1, #12
	bne set_error_led
	cmp r2, #13
	bne set_error_led
	cmp r3, #14
	bne set_error_led
	cmp r4, #15
	bne set_error_led
	cmp r5, #16
	bne set_error_led
	cmp r6, #17
	bne set_error_led
	cmp r7, #18
	bne set_error_led
	cmp r8, #19
	bne set_error_led
	cmp r9, #20
	bne set_error_led
	cmp r10, #21
	bne set_error_led
	cmp r12, #22
	bne set_error_led
	bx lr

set_error_led:
	push {r14}
	ldr r1, =vSetErrorLED
	blx r1
	pop {r14}
	bx lr

	END
	
