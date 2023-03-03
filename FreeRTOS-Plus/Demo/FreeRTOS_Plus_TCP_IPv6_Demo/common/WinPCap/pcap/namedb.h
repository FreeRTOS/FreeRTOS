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

#ifndef lib_pcap_namedb_h
#define lib_pcap_namedb_h

#ifdef __cplusplus
extern "C" {
#endif

/*
 * As returned by the pcap_next_etherent()
 * XXX this stuff doesn't belong in this interface, but this
 * library already must do name to address translation, so
 * on systems that don't have support for /etc/ethers, we
 * export these hooks since they'll
 */
struct pcap_etherent {
	u_char addr[6];
	char name[122];
};
#ifndef PCAP_ETHERS_FILE
#define PCAP_ETHERS_FILE "/etc/ethers"
#endif
struct	pcap_etherent *pcap_next_etherent(FILE *);
u_char *pcap_ether_hostton(const char*);
u_char *pcap_ether_aton(const char *);

bpf_u_int32 **pcap_nametoaddr(const char *);
#ifdef INET6
struct addrinfo *pcap_nametoaddrinfo(const char *);
#endif
bpf_u_int32 pcap_nametonetaddr(const char *);

int	pcap_nametoport(const char *, int *, int *);
int	pcap_nametoportrange(const char *, int *, int *, int *);
int	pcap_nametoproto(const char *);
int	pcap_nametoeproto(const char *);
int	pcap_nametollc(const char *);
/*
 * If a protocol is unknown, PROTO_UNDEF is returned.
 * Also, pcap_nametoport() returns the protocol along with the port number.
 * If there are ambiguous entried in /etc/services (i.e. domain
 * can be either tcp or udp) PROTO_UNDEF is returned.
 */
#define PROTO_UNDEF		-1

/* XXX move these to pcap-int.h? */
int __pcap_atodn(const char *, bpf_u_int32 *);
int __pcap_atoin(const char *, bpf_u_int32 *);
u_short	__pcap_nametodnaddr(const char *);

#ifdef __cplusplus
}
#endif

#endif
