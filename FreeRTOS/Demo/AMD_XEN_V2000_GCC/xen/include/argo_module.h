/* argo_module
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *
 */

#include <hypervisor.h>
#include <argo.h>
#include <events.h>
#include <xenbus.h>

/*
 * Utilities for ARGO
 */

#define PAGESIZE        	4096
#define ROUNDUP(x, y)   	( ( ( x ) + ( y ) - 1 ) & ~( ( y ) - 1 ) )
#define RINGPAGESIZE    	( ROUNDUP( ( PAGESIZE - sizeof( xen_argo_ring_t ) ) , XEN_ARGO_MSG_SLOT_SIZE ) )
#define MAX_RINGS		5

#define ARGO_SHF_SYN     (1 << 0)
#define ARGO_SHF_ACK     (1 << 1)
#define ARGO_SHF_RST     (1 << 2)

#define ARGO_PROTO_DGRAM     0x6447724d
#define ARGO_PROTO_STREAM    0x3574526d

#define CONNID  3224526688

typedef enum
{
	ARGO_PTYPE_DGRAM = 1,
	ARGO_PTYPE_STREAM,
} argo_ptype;

typedef struct argo_handle
{
	xen_argo_addr_t src;
	xen_argo_addr_t dest;

	uint8_t *argo_ring;
	xen_argo_gfn_t gfn;

	uint32_t conid;
	uint32_t rx_ptr;
} argo_handle_t;

typedef void (*recv_handler)(domid_t dom, xen_argo_port_t aport, char msg[], size_t len);
typedef struct argo_ring
{
        int inuse;
	argo_handle_t handle;
	recv_handler recv_cb;

} argo_ring_t;

typedef struct argo_stream_header
{
	uint32_t flags;
	uint32_t conid;
} argo_stream_header;


/*
 * ARGO Functions
 */

int argo_ring_register(domid_t partner_id, xen_argo_port_t aport, recv_handler recv_cb);
int argo_ring_unregister(domid_t partner_id, xen_argo_port_t aport);
int sendv(domid_t partner_id, xen_argo_port_t aport, char *msg, int connect);
int argo_init(void);
int argo_fini(void);
