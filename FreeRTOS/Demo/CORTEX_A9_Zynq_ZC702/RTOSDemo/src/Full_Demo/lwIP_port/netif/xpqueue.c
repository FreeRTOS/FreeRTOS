/*
 * Copyright (c) 2007-13 Xilinx, Inc.  All rights reserved.
 *
 * Xilinx, Inc.
 * XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A
 * COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
 * ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR
 * STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION
 * IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE
 * FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION.
 * XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO
 * THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO
 * ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
 * FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 */

#include <stdlib.h>

#include "netif/xpqueue.h"

#define NUM_QUEUES	2

pq_queue_t pq_queue[NUM_QUEUES];

pq_queue_t *
pq_create_queue()
{
	static int i;
	pq_queue_t *q = NULL;

	if (i >= NUM_QUEUES) {
		xil_printf("ERR: Max Queues allocated\n\r");
		return q;
	}

	q = &pq_queue[i++];

	if (!q)
		return q;

	q->head = q->tail = q->len = 0;

	return q;
}

int 
pq_enqueue(pq_queue_t *q, void *p)
{
	if (q->len == PQ_QUEUE_SIZE)
		return -1;

	q->data[q->head] = p;
	q->head = (q->head + 1)%PQ_QUEUE_SIZE;
	q->len++;

	return 0;
}

void*
pq_dequeue(pq_queue_t *q)
{
	int ptail;

	if (q->len == 0)
		return NULL;

	ptail = q->tail;
	q->tail = (q->tail + 1)%PQ_QUEUE_SIZE;
	q->len--;

	return q->data[ptail];
}

int 
pq_qlength(pq_queue_t *q)
{
	return q->len;
}
