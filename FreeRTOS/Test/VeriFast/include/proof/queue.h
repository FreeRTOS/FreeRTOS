/*
 * FreeRTOS VeriFast Proofs
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

#ifndef QUEUE_H
#define QUEUE_H

#define VERIFAST
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <threading.h>
/*@#include "common.gh"@*/

typedef size_t TickType_t;
typedef size_t UBaseType_t;
typedef ssize_t BaseType_t;

/* Empty/no-op macros */
/* Tracing */
#define traceBLOCKING_ON_QUEUE_PEEK(x)
#define traceBLOCKING_ON_QUEUE_RECEIVE(x)
#define traceBLOCKING_ON_QUEUE_SEND(x)
#define traceQUEUE_CREATE(x)
#define traceQUEUE_CREATE_FAILED(x)
#define traceQUEUE_DELETE(x)
#define traceQUEUE_PEEK(x)
#define traceQUEUE_PEEK_FAILED(x)
#define traceQUEUE_PEEK_FROM_ISR(x)
#define traceQUEUE_PEEK_FROM_ISR_FAILED(x)
#define traceQUEUE_RECEIVE(x)
#define traceQUEUE_RECEIVE_FAILED(x)
#define traceQUEUE_RECEIVE_FROM_ISR(x)
#define traceQUEUE_RECEIVE_FROM_ISR_FAILED(x)
#define traceQUEUE_SEND(x)
#define traceQUEUE_SEND_FAILED(x)
#define traceQUEUE_SEND_FROM_ISR(x)
#define traceQUEUE_SEND_FROM_ISR_FAILED(x)
/* Coverage */
#define mtCOVERAGE_TEST_MARKER()
/* Asserts */
#define configASSERT(x)
#define portASSERT_IF_INTERRUPT_PRIORITY_INVALID()

/* Map portable memory management functions */
#define pvPortMalloc malloc
#define vPortFree free

#define queueSEND_TO_BACK	0
#define queueSEND_TO_FRONT	1
#define queueOVERWRITE		2

#define pdTRUE	1
#define pdFALSE	0

#define pdPASS pdTRUE
#define pdFAIL pdFALSE
#define errQUEUE_FULL	0
#define errQUEUE_EMPTY	0

#define queueUNLOCKED					( ( int8_t ) -1 )
#define queueLOCKED_UNMODIFIED			( ( int8_t ) 0 )
#define queueINT8_MAX					( ( int8_t ) 127 )

typedef struct QueuePointers
{
	int8_t *pcTail;					/*< Points to the byte at the end of the queue storage area.  Once more byte is allocated than necessary to store the queue items, this is used as a marker. */
	int8_t *pcReadFrom;				/*< Points to the last place that a queued item was read from when the structure is used as a queue. */
} QueuePointers_t;

typedef struct SemaphoreData
{
#ifdef VERIFAST /*< do not model xMutexHolder */
	void *xMutexHolder;
#else
	TaskHandle_t xMutexHolder;		 /*< The handle of the task that holds the mutex. */
#endif
	UBaseType_t uxRecursiveCallCount;/*< Maintains a count of the number of times a recursive mutex has been recursively 'taken' when the structure is used as a mutex. */
} SemaphoreData_t;

/* VeriFast does not support unions so we replace with a struct */
struct fake_union_t {
	QueuePointers_t xQueue;
	SemaphoreData_t xSemaphore;
};

typedef struct xLIST {
	UBaseType_t uxNumberOfItems;
#ifndef VERIFAST /*< do not model pxIndex and xListEnd of xLIST struct */
	struct xLIST_ITEM *pxIndex;
	MiniListItem_t xListEnd;
#endif
} List_t;

typedef struct QueueDefinition 		/* The old naming convention is used to prevent breaking kernel aware debuggers. */ {
	int8_t *pcHead;					/*< Points to the beginning of the queue storage area. */
	int8_t *pcWriteTo;				/*< Points to the free next place in the storage area. */

#ifdef VERIFAST /*< VeriFast does not model unions */
	struct fake_union_t u;
#else
	union
	{
		QueuePointers_t xQueue;		/*< Data required exclusively when this structure is used as a queue. */
		SemaphoreData_t xSemaphore; /*< Data required exclusively when this structure is used as a semaphore. */
	} u;
#endif

	List_t xTasksWaitingToSend;		/*< List of tasks that are blocked waiting to post onto this queue.  Stored in priority order. */
	List_t xTasksWaitingToReceive;	/*< List of tasks that are blocked waiting to read from this queue.  Stored in priority order. */

	volatile UBaseType_t uxMessagesWaiting;/*< The number of items currently in the queue. */
	UBaseType_t uxLength;			/*< The length of the queue defined as the number of items it will hold, not the number of bytes. */
	UBaseType_t uxItemSize;			/*< The size of each items that the queue will hold. */

	volatile int8_t cRxLock;		/*< Stores the number of items received from the queue (removed from the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */
	volatile int8_t cTxLock;		/*< Stores the number of items transmitted to the queue (added to the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */

	/*@struct mutex *irqMask;@*/		/*< Ghost mutex simulates the effect of irq masking */
	/*@struct mutex *schedulerSuspend;@*/	/*< Ghost mutex simulates the effect of scheduler suspension */
	/*@struct mutex *locked;@*/		/*< Ghost mutex simulates the effect of queue locking */
} xQUEUE;

typedef xQUEUE Queue_t;

typedef struct QueueDefinition * QueueHandle_t;

/*@
#define QUEUE_SHAPE(q, Storage, N, M, K)					\
	malloc_block_QueueDefinition(q) &*&						\
	q->pcHead |-> Storage &*&								\
	q->pcWriteTo |-> ?WPtr &*&								\
	q->u.xQueue.pcTail |-> ?End &*&							\
	q->u.xQueue.pcReadFrom |-> ?RPtr &*&					\
	q->uxItemSize |-> M &*&									\
	q->uxLength |-> N &*&									\
	q->uxMessagesWaiting |-> K &*&							\
	q->cRxLock |-> ?rxLock &*&								\
	q->cTxLock |-> ?txLock &*&								\
	struct_QueuePointers_padding(&q->u.xQueue) &*&			\
	struct_SemaphoreData_padding(&q->u.xSemaphore) &*&		\
	struct_fake_union_t_padding(&q->u) &*&					\
	struct_xLIST_padding(&q->xTasksWaitingToSend) &*&		\
	struct_xLIST_padding(&q->xTasksWaitingToReceive) &*&	\
	q->u.xSemaphore.xMutexHolder |-> _ &*&					\
	q->u.xSemaphore.uxRecursiveCallCount |-> _ &*&			\
	true

predicate queue(QueueHandle_t q, int8_t *Storage, size_t N, size_t M, size_t W, size_t R, size_t K, bool is_locked; list<list<char> >abs) =
	QUEUE_SHAPE(q, Storage, N, M, K) &*&
	0 < N &*&
	0 < M &*&
	0 <= W &*& W < N &*&
	0 <= R &*& R < N &*&
	0 <= K &*& K <= N &*&
	W == (R + 1 + K) % N &*&
	(-1) <= rxLock &*&
	(-1) <= txLock &*&
	(is_locked ? 0 <= rxLock : (-1) == rxLock) &*&
	(is_locked ? 0 <= txLock : (-1) == txLock) &*&
	WPtr == Storage + (W*M) &*&
	RPtr == Storage + (R*M) &*&
	End == Storage + (N*M) &*&
	buffer(Storage, N, M, ?contents) &*&
	length(contents) == N &*&
	abs == take(K, rotate_left((R+1)%N, contents)) &*&
	malloc_block(Storage, N*M) &*&
	true
	;

predicate buffer(char *buffer, size_t N, size_t M; list<list<char> > elements) =
	N == 0
		? elements == nil
		: chars(buffer, M, ?x) &*& buffer(buffer + M, N - 1, M, ?xs) &*& elements == cons(x, xs);

// TODO: buffer_from_chars proof
lemma void buffer_from_chars(char *buffer, size_t N, size_t M);
requires chars(buffer, N*M, _);
ensures exists<list<list<char> > >(?elements) &*& buffer(buffer, N, M, elements) &*& length(elements) == N;

// TODO: split_element proof
lemma void split_element<t>(char *buffer, size_t N, size_t M, size_t i);
requires buffer(buffer, N, M, ?elements) &*& i < N;
ensures
	buffer(buffer, i, M, take(i, elements)) &*&
	chars(buffer + i * M, M, nth(i, elements)) &*&
	buffer(buffer + (i + 1) * M, (N-1-i), M, drop(i+1, elements));

// TODO: join_element proof
lemma void join_element(char *buffer, size_t N, size_t M, size_t i);
requires
	buffer(buffer, i, M, ?prefix) &*&
	chars(buffer + i * M, M, ?element) &*&
	buffer(buffer + (i + 1) * M, (N-1-i), M, ?suffix);
ensures buffer(buffer, N, M, append(prefix, cons(element, suffix)));

predicate list(List_t *l;) =
	l->uxNumberOfItems |-> _;

predicate queuelists(QueueHandle_t q;) =
	list(&q->xTasksWaitingToSend) &*&
	list(&q->xTasksWaitingToReceive);
@*/

/* Because prvCopyDataFromQueue does *not* decrement uxMessagesWaiting (K) the
queue predicate above does not hold as a postcondition. If the caller
subsequently decrements K then the queue predicate can be reinstated. */
/*@
predicate queue_after_prvCopyDataFromQueue(QueueHandle_t q, int8_t *Storage, size_t N, size_t M, size_t W, size_t R, size_t K, bool is_locked; list<list<char> >abs) =
	QUEUE_SHAPE(q, Storage, N, M, K) &*&
	0 < N &*&
	0 < M &*&
	0 <= W &*& W < N &*&
	0 <= R &*& R < N &*&
	0 <= K &*& K <= N &*&
	W == (R + K) % N &*& //< Differs from queue predicate
	(-1) <= rxLock &*&
	(-1) <= txLock &*&
	(is_locked ? 0 <= rxLock : (-1) == rxLock) &*&
	(is_locked ? 0 <= txLock : (-1) == txLock) &*&
	WPtr == Storage + (W*M) &*&
	RPtr == Storage + (R*M) &*&
	End == Storage + (N*M) &*&
	buffer(Storage, N, M, ?contents) &*&
	length(contents) == N &*&
	abs == take(K, rotate_left(R, contents)) &*& //< Differs from queue predicate
	malloc_block(Storage, N*M) &*&
	true
	;
@*/

/* Can't be called `mutex` as this clashes with VeriFast's predicate */
/*@
predicate freertos_mutex(QueueHandle_t q, int8_t *Storage, size_t N, size_t K;) =
	QUEUE_SHAPE(q, Storage, N, 0, K) &*&
	queuelists(q) &*&
	0 < N &*&
	0 <= K &*& K <= N &*&
	(-1) <= rxLock &*&
	(-1) <= txLock &*&
	WPtr == Storage &*&
	RPtr == Storage &*&
	End == Storage &*&
	malloc_block(Storage, 0) &*&
	chars(Storage, 0, _) &*&
	true
	;
@*/

/* A queuehandle can be shared between tasks and ISRs. Acquiring the ghost
`irqMask` gives access to the core queue resources. The permissions granted
after masking interrupts depends on the caller:
- A task has access to the queue and the queuelists
- An ISR has access to the queue and, if the queue is unlocked, the queuelists */
/*@
predicate queuehandle(QueueHandle_t q, size_t N, size_t M, bool is_isr;) =
	q->irqMask |-> ?m &*& mutex(m, irqs_masked_invariant(q, N, M, is_isr));

predicate_ctor irqs_masked_invariant(QueueHandle_t queue, size_t N, size_t M, bool is_isr)() =
	queue(queue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
	(is_isr && is_locked ? true : queuelists(queue));
@*/

/* A queuesuspend can be shared between tasks. Acquiring the ghost `schedulerSuspend` gives access to the `locked` mutex. */
/*@
predicate_ctor scheduler_suspended_invariant(QueueHandle_t queue)() =
	queue->locked |-> ?m &*&
	mutex(m, queue_locked_invariant(queue));

predicate queuesuspend(QueueHandle_t q;) =
	q->schedulerSuspend |-> ?m &*&
	mutex(m, scheduler_suspended_invariant(q));
@*/

/* A queuelock is exclusively acquired by a task. Acquiring the ghost `queuelock` gives access to the queue list resources. */
/*@
predicate queuelock(QueueHandle_t q;) =
	q->locked |-> ?m &*&
	mutex(m, queue_locked_invariant(q));

predicate_ctor queue_locked_invariant(QueueHandle_t queue)() =
	queuelists(queue);
@*/

BaseType_t vListInitialise(List_t *list);
/*@requires list(list);@*/
/*@ensures list(list);@*/

BaseType_t listLIST_IS_EMPTY(List_t *list);
/*@requires list->uxNumberOfItems |-> ?len;@*/
/*@ensures list->uxNumberOfItems |-> len &*& result == (len == 0 ? pdTRUE : pdFALSE);@*/

typedef struct xTIME_OUT
{
	BaseType_t xOverflowCount;
	TickType_t xTimeOnEntering;
} TimeOut_t;

/*@
predicate xTIME_OUT(struct xTIME_OUT *to;) =
	to->xOverflowCount |-> _ &*&
	to->xTimeOnEntering |-> _ &*&
	struct_xTIME_OUT_padding(to);
@*/

void vTaskInternalSetTimeOutState( TimeOut_t * x);
/*@requires xTIME_OUT(x);@*/
/*@ensures xTIME_OUT(x);@*/

BaseType_t xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut, TickType_t * const pxTicksToWait );
/*@requires xTIME_OUT(pxTimeOut) &*& u_integer(pxTicksToWait, _);@*/
/*@ensures xTIME_OUT(pxTimeOut) &*& u_integer(pxTicksToWait, _);@*/

BaseType_t xTaskRemoveFromEventList(List_t *list);
/*@requires list(list);@*/
/*@ensures list(list);@*/

void vTaskPlaceOnEventList( List_t * const pxEventList, const TickType_t xTicksToWait );
/*@requires list(pxEventList);@*/
/*@ensures list(pxEventList);@*/

void vTaskMissedYield();
/*@requires true;@*/
/*@ensures true;@*/

void vTaskSuspendAll();
/*@requires exists<QueueHandle_t>(?xQueue) &*&
	[1/2]xQueue->schedulerSuspend |-> ?m &*&
	[1/2]mutex(m, scheduler_suspended_invariant(xQueue));@*/
/*@ensures [1/2]xQueue->schedulerSuspend |-> m &*&
	mutex_held(m, scheduler_suspended_invariant(xQueue), currentThread, 1/2) &*&
	xQueue->locked |-> ?m2 &*&
	mutex(m2, queue_locked_invariant(xQueue));@*/

BaseType_t xTaskResumeAll( void );
/*@requires exists<QueueHandle_t>(?xQueue) &*&
	[1/2]xQueue->schedulerSuspend |-> ?m &*&
	mutex_held(m, scheduler_suspended_invariant(xQueue), currentThread, 1/2) &*&
	xQueue->locked |-> ?m2 &*&
	mutex(m2, queue_locked_invariant(xQueue));@*/
/*@ensures [1/2]xQueue->schedulerSuspend |-> m &*&
	[1/2]mutex(m, scheduler_suspended_invariant(xQueue));@*/

void prvLockQueue( QueueHandle_t xQueue );
/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false &*&
	[1/2]queuelock(xQueue); @*/
/*@ensures [1/2]queuehandle(xQueue, N, M, is_isr) &*&
	[1/2]xQueue->locked |-> ?m &*&
	mutex_held(m, queue_locked_invariant(xQueue), currentThread, 1/2) &*&
	queue_locked_invariant(xQueue)();@*/

void prvUnlockQueue( QueueHandle_t xQueue );
/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false &*&
	[1/2]xQueue->locked |-> ?m &*&
	mutex_held(m, queue_locked_invariant(xQueue), currentThread, 1/2) &*&
	queue_locked_invariant(xQueue)();@*/
/*@ensures [1/2]queuehandle(xQueue, N, M, is_isr) &*&
	[1/2]queuelock(xQueue);@*/

void setInterruptMask(QueueHandle_t xQueue)
/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false;@*/
/*@ensures [1/2]xQueue->irqMask |-> ?m &*&
	mutex_held(m, irqs_masked_invariant(xQueue, N, M, is_isr), currentThread, 1/2) &*&
	queue(xQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
	queuelists(xQueue);@*/
{
	/*@open queuehandle(xQueue, N, M, is_isr);@*/
	mutex_acquire(xQueue->irqMask);
	/*@open irqs_masked_invariant(xQueue, N, M, is_isr)();@*/
}

void clearInterruptMask(QueueHandle_t xQueue)
/*@requires queue(xQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
	[1/2]xQueue->irqMask |-> ?m &*&
	mutex_held(m, irqs_masked_invariant(xQueue, N, M, false), currentThread, 1/2) &*&
	queuelists(xQueue);@*/
/*@ensures [1/2]queuehandle(xQueue, N, M, false);@*/
{
	/*@close irqs_masked_invariant(xQueue, N, M, false)();@*/
	mutex_release(xQueue->irqMask);
	/*@close [1/2]queuehandle(xQueue, N, M, false);@*/
}

#define taskENTER_CRITICAL() setInterruptMask(xQueue)
#define taskEXIT_CRITICAL() clearInterruptMask(xQueue)
#define portYIELD_WITHIN_API()
#define queueYIELD_IF_USING_PREEMPTION()

UBaseType_t setInterruptMaskFromISR(QueueHandle_t xQueue)
/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == true;@*/
/*@ensures [1/2]xQueue->irqMask |-> ?m &*&
	mutex_held(m, irqs_masked_invariant(xQueue, N, M, is_isr), currentThread, 1/2) &*&
	queue(xQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
	(is_locked ? true : queuelists(xQueue));@*/
{
	/*@open queuehandle(xQueue, N, M, is_isr);@*/
	mutex_acquire(xQueue->irqMask);
	/*@open irqs_masked_invariant(xQueue, N, M, is_isr)();@*/
	return 0;
}

void clearInterruptMaskFromISR(QueueHandle_t xQueue, UBaseType_t uxSavedInterruptStatus)
/*@requires queue(xQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
	[1/2]xQueue->irqMask |-> ?m &*&
	mutex_held(m, irqs_masked_invariant(xQueue, N, M, true), currentThread, 1/2) &*&
	(is_locked ? true : queuelists(xQueue));@*/
/*@ensures [1/2]queuehandle(xQueue, N, M, true);@*/
{
	/*@close irqs_masked_invariant(xQueue, N, M, true)();@*/
	mutex_release(xQueue->irqMask);
	/*@close [1/2]queuehandle(xQueue, N, M, true);@*/
}

#define portSET_INTERRUPT_MASK_FROM_ISR() setInterruptMaskFromISR(xQueue)
#define portCLEAR_INTERRUPT_MASK_FROM_ISR(uxSavedInterruptStatus) clearInterruptMaskFromISR(xQueue, uxSavedInterruptStatus)

#endif /* QUEUE_H */
