	MODULE  ?mutex

	//// Forward declaration of sections.
	SECTION IRQ_STACK:DATA:NOROOT(2)
	SECTION CSTACK:DATA:NOROOT(3)

#define LOCKED  0x1
#define FREE    0x0
#define SUCCESS 0x1
#define FAILURE 0x0

/* try to lock mutex */
	SECTION .mutex_try_lock:CODE:NOROOT(2)
	PUBLIC  mutex_try_lock
mutex_try_lock:
	push    {r1,r2,r3}
	mov     r1, #LOCKED
	mov     r3, #SUCCESS

	ldrex   r2, [r0]
	cmp     r2, r1        /* Test if mutex is locked or unlocked */
	moveq   r3, #FAILURE  /* If locked */
	beq     lbl1          /* return failure */
	strexne r2, r1, [r0]  /* Not locked, attempt to lock it */
	cmp     r2, #LOCKED   /* Check if Store-Exclusive failed */
	movne   r3, #FAILURE  /* If failed - return failure */
lbl1:
	dmb                   /* Required before accessing protected resource */
	mov     r0, r3
	pop     {r1,r2,r3}
	bx      lr


/* free mutex */
	SECTION .mutex_free:CODE:NOROOT(2)
	PUBLIC mutex_free
mutex_free:
	push    {r1}
	mov     r1, #FREE
	dmb                   /* Required before releasing protected resource */
	str     r1, [r0]      /* Unlock mutex */
	pop     {r1}
	bx      lr

/* Check if mutex is locked or not */
	SECTION .mutex_is_locked:CODE:NOROOT(2)
	PUBLIC mutex_is_locked
mutex_is_locked:
	push    {r1, r2}
	mov     r1, #LOCKED

	ldrex   r2, [r0]
	cmp     r2, r1        /* Test if mutex is locked or unlocked */
	moveq   r0, #SUCCESS
	movne   r0, #FAILURE
	pop     {r1, r2}
	bx      lr

	END
