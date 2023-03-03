/*
 * FreeRTOS V202212.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 * For captures on Linux cooked sockets, we construct a fake header
 * that includes:
 *
 *	a 2-byte "packet type" which is one of:
 *
 *		LINUX_SLL_HOST		packet was sent to us
 *		LINUX_SLL_BROADCAST	packet was broadcast
 *		LINUX_SLL_MULTICAST	packet was multicast
 *		LINUX_SLL_OTHERHOST	packet was sent to somebody else
 *		LINUX_SLL_OUTGOING	packet was sent *by* us;
 *
 *	a 2-byte Ethernet protocol field;
 *
 *	a 2-byte link-layer type;
 *
 *	a 2-byte link-layer address length;
 *
 *	an 8-byte source link-layer address, whose actual length is
 *	specified by the previous value.
 *
 * All fields except for the link-layer address are in network byte order.
 *
 * DO NOT change the layout of this structure, or change any of the
 * LINUX_SLL_ values below.  If you must change the link-layer header
 * for a "cooked" Linux capture, introduce a new DLT_ type (ask
 * "tcpdump-workers@lists.tcpdump.org" for one, so that you don't give it
 * a value that collides with a value already being used), and use the
 * new header in captures of that type, so that programs that can
 * handle DLT_LINUX_SLL captures will continue to handle them correctly
 * without any change, and so that capture files with different headers
 * can be told apart and programs that read them can dissect the
 * packets in them.
 */

#ifndef lib_pcap_sll_h
#define lib_pcap_sll_h

/*
 * A DLT_LINUX_SLL fake link-layer header.
 */
#define SLL_HDR_LEN	16		/* total header length */
#define SLL_ADDRLEN	8		/* length of address field */

struct sll_header {
	u_int16_t sll_pkttype;		/* packet type */
	u_int16_t sll_hatype;		/* link-layer address type */
	u_int16_t sll_halen;		/* link-layer address length */
	u_int8_t sll_addr[SLL_ADDRLEN];	/* link-layer address */
	u_int16_t sll_protocol;		/* protocol */
};

/*
 * The LINUX_SLL_ values for "sll_pkttype"; these correspond to the
 * PACKET_ values on Linux, but are defined here so that they're
 * available even on systems other than Linux, and so that they
 * don't change even if the PACKET_ values change.
 */
#define LINUX_SLL_HOST		0
#define LINUX_SLL_BROADCAST	1
#define LINUX_SLL_MULTICAST	2
#define LINUX_SLL_OTHERHOST	3
#define LINUX_SLL_OUTGOING	4

/*
 * The LINUX_SLL_ values for "sll_protocol"; these correspond to the
 * ETH_P_ values on Linux, but are defined here so that they're
 * available even on systems other than Linux.  We assume, for now,
 * that the ETH_P_ values won't change in Linux; if they do, then:
 *
 *	if we don't translate them in "pcap-linux.c", capture files
 *	won't necessarily be readable if captured on a system that
 *	defines ETH_P_ values that don't match these values;
 *
 *	if we do translate them in "pcap-linux.c", that makes life
 *	unpleasant for the BPF code generator, as the values you test
 *	for in the kernel aren't the values that you test for when
 *	reading a capture file, so the fixup code run on BPF programs
 *	handed to the kernel ends up having to do more work.
 *
 * Add other values here as necessary, for handling packet types that
 * might show up on non-Ethernet, non-802.x networks.  (Not all the ones
 * in the Linux "if_ether.h" will, I suspect, actually show up in
 * captures.)
 */
#define LINUX_SLL_P_802_3	0x0001	/* Novell 802.3 frames without 802.2 LLC header */
#define LINUX_SLL_P_802_2	0x0004	/* 802.2 frames (not D/I/X Ethernet) */

#endif
