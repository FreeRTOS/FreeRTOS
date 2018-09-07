#define LOCKED  0x1
#define FREE    0x0
#define SUCCESS 0x1
#define FAILURE 0x0


/* try to lock mutex */
	.global mutex_try_lock
	.section .text.mutex_try_lock
mutex_try_lock:
	push    {r1,r2,r3}
	mov     r1, #LOCKED
	mov     r3, #SUCCESS
1:
	ldrex   r2, [r0]
	cmp     r2, r1        /* Test if mutex is locked or unlocked */
	moveq   r3, #FAILURE  /* If locked */
	beq     2f            /* return failure */
	strexne r2, r1, [r0]  /* Not locked, attempt to lock it */
	cmp     r2, #LOCKED   /* Check if Store-Exclusive failed */
	movne   r3, #FAILURE  /* If failed - return failure */
2:
	dmb                   /* Required before accessing protected resource */
	mov     r0, r3
	pop     {r1,r2,r3}
	bx      lr


/* free mutex */
	.global mutex_free
	.section .text.mutex_free
mutex_free:
	push    {r1}
	mov     r1, #FREE
	dmb                   /* Required before releasing protected resource */
	str     r1, [r0]      /* Unlock mutex */
	pop     {r1}
	bx      lr

/* Check if mutex is locked or not */
	.global mutex_is_locked
	.section .text.mutex_is_locked
mutex_is_locked:
	push    {r1, r2}
	mov     r1, #LOCKED

	ldrex   r2, [r0]
	cmp     r2, r1        /* Test if mutex is locked or unlocked */
	moveq   r0, #SUCCESS
	movne   r0, #FAILURE
	pop     {r1, r2}
	bx      lr
