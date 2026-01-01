/* argo 
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


#include <argo_module.h>
#include "stdlib.h"
#include "string.h"

extern uint8_t argo_ring;
evtchn_port_t argo_evtchn;
int ring_used;
argo_ring_t ring_handle[MAX_RINGS];

/*
 * Helper Functions
 */

static inline size_t argo_ring_has_data(size_t rx, size_t tx)
{
        if (rx > tx)
                return RINGPAGESIZE - (rx - tx);

        return tx - rx;
}


static inline domid_t str_to_domid_t(const char *str)
{
        char *endptr = NULL;
        domid_t val = (domid_t)strtoul(str, &endptr, 10);
        return val;
}

int search_ring_handle (domid_t partner_id, xen_argo_port_t aport)
{
	int ring_idx;
	int found = 0;

	for (ring_idx = 0; ring_idx < MAX_RINGS; ring_idx++)
		if (ring_handle[ring_idx].handle.dest.domain_id == partner_id && ring_handle[ring_idx].handle.dest.aport == aport) {
			found = 1;
			break;
		}

	if (found == 0)
		return -1;
	
	return ring_idx;
}

int remove_ring (domid_t partner_id, xen_argo_port_t aport)
{
	int ring_idx;

	ring_idx = search_ring_handle(partner_id, aport);
	if (ring_idx == -1)
		return ring_idx;

	ring_handle[ring_idx].handle.src.aport = 0;
        ring_handle[ring_idx].handle.src.domain_id = 0;
        ring_handle[ring_idx].handle.src.pad = 0;
        ring_handle[ring_idx].handle.dest.aport = 0;
        ring_handle[ring_idx].handle.dest.domain_id = 0;
        ring_handle[ring_idx].handle.dest.pad = 0;
        ring_handle[ring_idx].handle.argo_ring = NULL;
        ring_handle[ring_idx].handle.gfn = 0;
        ring_handle[ring_idx].handle.rx_ptr = 0;

	ring_handle[ring_idx].recv_cb = NULL;

        ring_handle[ring_idx].inuse = 0;
        ring_used--;

        return 0;
}

int allocate_ring (domid_t partner_id, xen_argo_port_t aport, recv_handler recv_cb)
{
	int ring_idx;

	if (ring_used == MAX_RINGS)
		return -1;

	for (ring_idx = 0; ring_idx < MAX_RINGS; ring_idx++)
		if (ring_handle[ring_idx].inuse == 0)
			break;

	ring_handle[ring_idx].handle.src.aport = aport;
#if defined(__x86_64__)
        ring_handle[ring_idx].handle.src.domain_id = xenbus_get_self_id();
#else
        char *domid_self;
        xenbus_read(XBT_NIL, "domid", &domid_self);
        ring_handle[ring_idx].handle.src.domain_id = str_to_domid_t(domid_self);
#endif
	ring_handle[ring_idx].handle.src.pad = 0;
	ring_handle[ring_idx].handle.dest.aport = aport;
	ring_handle[ring_idx].handle.dest.domain_id = partner_id;
	ring_handle[ring_idx].handle.dest.pad = 0;
	ring_handle[ring_idx].handle.argo_ring = &argo_ring + (ring_idx * 4096);
	ring_handle[ring_idx].handle.gfn = ((uint64_t)ring_handle[ring_idx].handle.argo_ring) >> 12;
	ring_handle[ring_idx].handle.rx_ptr = 0;

	ring_handle[ring_idx].recv_cb = recv_cb;

	ring_handle[ring_idx].inuse = 1;
	ring_used++;

	return ring_idx;
}

/*
 * ARGO Hypercalls wrappers.
 */

int argo_ring_register(domid_t partner_id, xen_argo_port_t aport, recv_handler recv_cb)
{
	int ring_idx = allocate_ring(partner_id, aport, recv_cb);
	if (ring_idx == -1)
		return -11;

        xen_argo_register_ring_t reg = {
                .aport = ring_handle[ring_idx].handle.dest.aport,
                .partner_id = ring_handle[ring_idx].handle.dest.domain_id,
                .pad = 0,
                .len = RINGPAGESIZE,
        };

	memset(ring_handle[ring_idx].handle.argo_ring, 0, sizeof(uint8_t)*4096);

	xen_argo_gfn_t gfn = ring_handle[ring_idx].handle.gfn;

        int rc = HYPERVISOR_argo_op(XEN_ARGO_OP_register_ring, (unsigned long)&reg, (unsigned long)&gfn, 1, 0);

	return rc;
}

int argo_ring_unregister(domid_t partner_id, xen_argo_port_t aport)
{
	int ring_idx = remove_ring(partner_id, aport);
	if (ring_idx == -1)
		return -11;

        xen_argo_unregister_ring_t unreg = {
                .aport = aport,
                .partner_id = partner_id,
                .pad = 0,
        };

        int rc = HYPERVISOR_argo_op(XEN_ARGO_OP_unregister_ring, (unsigned long)&unreg, NULL, 0, 0);
	if (rc)
                printk("Failed to unregister argo ring for dom%u:%u (%d).\n", unreg.partner_id, unreg.aport, rc);
        else
                printk("Ring for dom%u:%u unregistered.\n", unreg.partner_id, unreg.aport);

	return rc;
}

int sendv(domid_t partner_id, xen_argo_port_t aport, char msg[], int connect)
{
	int ring_idx;
        int ret;
	int niovs;
	argo_stream_header sh;

	ring_idx = search_ring_handle(partner_id, aport);
	if (ring_idx == -1)
		return -11;

	xen_argo_send_addr_t msg_header = {
            .src.aport = ring_handle[ring_idx].handle.src.aport,
            .src.domain_id = ring_handle[ring_idx].handle.src.domain_id,
            .src.pad = 0,
            .dst.aport = ring_handle[ring_idx].handle.dest.aport,
            .dst.domain_id = ring_handle[ring_idx].handle.dest.domain_id,
            .dst.pad = 0,
	};

	if (connect == 1) {
		niovs = 1;

		sh.flags = ARGO_SHF_SYN;
		sh.conid = CONNID;
	}
	else {
		niovs = 2;

		sh.flags = 0;
                sh.conid = CONNID;
	}

	xen_argo_iov_t iov[niovs];

	iov[0].iov_hnd = (unsigned long)&sh;
	iov[0].iov_len = sizeof(sh);
	iov[0].pad = 0;

	if (niovs > 1) {
		char buf[strlen(msg)];
		strncpy(buf, msg, strlen(msg));
		iov[1].iov_hnd = (unsigned long)&buf;
		iov[1].iov_len = strlen(msg);
		iov[1].pad = 0;
	}

        ret = HYPERVISOR_argo_op(XEN_ARGO_OP_sendv, &msg_header, &iov, niovs, ARGO_PROTO_STREAM);

        return ret;
}


/*
 * Event handlers for ARGO VIRQ & Receiver handler.
 */

void recv_payload (int ring_idx)
{
	size_t rx = ring_handle[ring_idx].handle.rx_ptr;
        xen_argo_ring_t *temp = (xen_argo_ring_t *)(((uint8_t *)ring_handle[ring_idx].handle.argo_ring) + rx);
	struct xen_argo_ring_message_header *mh;
        argo_stream_header *sh;

	if (argo_ring_has_data(rx, temp->tx_ptr) >= sizeof(struct xen_argo_ring_message_header)) {
                mh = (struct xen_argo_ring_message_header *)((uint8_t *)temp + sizeof(xen_argo_ring_t));
                if (mh->len == sizeof(struct xen_argo_ring_message_header) + sizeof(argo_stream_header)) {
                        sh = (argo_stream_header *)mh->data;
                        ring_handle[ring_idx].handle.conid = sh->conid;
                }
                else if (mh->len > sizeof(argo_stream_header)) {
                        char buff[255];
                        char *msg = (char *)((uint8_t *)mh->data + sizeof(argo_stream_header));
                        size_t length = mh->len - (sizeof(struct xen_argo_ring_message_header) + sizeof(argo_stream_header));
                        memcpy(buff, msg, length);
                        ring_handle[ring_idx].recv_cb(mh->source.domain_id, mh->source.aport, buff, length);
                }
        }
        rx = ROUNDUP((ROUNDUP((rx + mh->len), XEN_ARGO_MSG_SLOT_SIZE) % RINGPAGESIZE), XEN_ARGO_MSG_SLOT_SIZE);
        ring_handle[ring_idx].handle.rx_ptr = rx;
}

void ARGO_handler(evtchn_port_t ev, void *regs, void *ign)
{
	for (int ring_idx = 0; ring_idx < MAX_RINGS; ring_idx++) {
		if (ring_handle[ring_idx].inuse == 1) {
			size_t rx = ring_handle[ring_idx].handle.rx_ptr;
			xen_argo_ring_t *temp = (xen_argo_ring_t *)(((uint8_t *)ring_handle[ring_idx].handle.argo_ring) + rx);
			if (argo_ring_has_data(rx, temp->tx_ptr) >= sizeof(struct xen_argo_ring_message_header))
				recv_payload(ring_idx);
		}
	}
}

/*
 * Init & Fini functions to be called when main is called.
 */

int argo_init(void)
{
        evtchn_port_t port;

        port = bind_virq(VIRQ_ARGO, &ARGO_handler, NULL);
        if (port == (evtchn_port_t)-1) {
		return -1;
        }
        unmask_evtchn(port);

        argo_evtchn = port;

	ring_used = 0;

	for (int i = 0; i < MAX_RINGS; i++)
		ring_handle[i].inuse = 0;

	return 0;
}

int argo_fini(void)
{
        if (argo_evtchn == (evtchn_port_t)-1) {
		return -1;
        }
        unbind_evtchn(argo_evtchn);

	return 0;
}
