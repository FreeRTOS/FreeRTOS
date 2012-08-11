/* snifftest.c
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#ifdef _WIN32
    #define CYASSL_SNIFFER
#endif

#ifndef CYASSL_SNIFFER

/* blank build */
#include <stdio.h>
#include <stdlib.h>
int main()
{
    printf("do ./configure --enable-sniffer to enable build support\n");
    return EXIT_SUCCESS;
}

#else
/* do a full build */

#ifdef _MSC_VER
	/* builds on *nix too, for scanf device and port */
	#define _CRT_SECURE_NO_WARNINGS
#endif

#include <pcap/pcap.h>     /* pcap stuff */
#include <stdio.h>         /* printf */
#include <stdlib.h>        /* EXIT_SUCCESS */
#include <signal.h>        /* signal */

#include <cyassl/sniffer.h>


#ifndef _WIN32
    #include <arpa/inet.h>
#endif

typedef unsigned char byte;

enum {
    ETHER_IF_FRAME_LEN = 14,   /* ethernet interface frame length */
    LOCAL_IF_FRAME_LEN =  4,   /* localhost interface frame length  */
};


pcap_t* pcap = 0;
pcap_if_t *alldevs;

static void sig_handler(const int sig) 
{
    printf("SIGINT handled.\n");
    if (pcap)
        pcap_close(pcap);
	pcap_freealldevs(alldevs);
#ifndef _WIN32
    ssl_FreeSniffer();
#endif
    exit(EXIT_SUCCESS);
}


void err_sys(const char* msg)
{
	fprintf(stderr, "%s\n", msg);
	exit(EXIT_FAILURE);
}


#ifdef _WIN32
	#define SNPRINTF _snprintf
#else
	#define SNPRINTF snprintf
#endif


char* iptos(unsigned int addr)
{
	static char    output[32];
	byte *p = (byte*)&addr;

	SNPRINTF(output, sizeof(output), "%d.%d.%d.%d", p[0], p[1], p[2], p[3]);

	return output;
}


int main(int argc, char** argv)
{
    int          ret;
	int		     inum;
	int		     port;
	int		     i = 0;
    char         err[PCAP_ERRBUF_SIZE];
	char         filter[32];
	char         loopback = 0;
	char        *server = NULL;
	struct       bpf_program fp;
	pcap_if_t   *d;
	pcap_addr_t *a;

    signal(SIGINT, sig_handler);

#ifndef _WIN32
    ssl_InitSniffer();
#endif
    ssl_Trace("./tracefile.txt", err);

	if (pcap_findalldevs(&alldevs, err) == -1)
		err_sys("Error in pcap_findalldevs");

	for (d = alldevs; d; d=d->next) {
		printf("%d. %s", ++i, d->name);
		if (d->description)
			printf(" (%s)\n", d->description);
		else
			printf(" (No description available)\n");
	}

	if (i == 0)
		err_sys("No interfaces found! Make sure pcap or WinPcap is installed "
                "correctly and you have sufficient permissions");

	printf("Enter the interface number (1-%d): ", i);
	scanf("%d", &inum);

	if (inum < 1 || inum > i)
		err_sys("Interface number out of range");

	/* Jump to the selected adapter */
	for (d = alldevs, i = 0; i < inum - 1; d = d->next, i++);

	pcap = pcap_create(d->name, err);

    if (pcap == NULL) printf("pcap_create failed %s\n", err);

	if (d->flags & PCAP_IF_LOOPBACK)
		loopback = 1;

	/* get an IPv4 address */
	for (a = d->addresses; a; a = a->next) {
		switch(a->addr->sa_family)
		{
			case AF_INET:
				server =iptos(((struct sockaddr_in *)a->addr)->sin_addr.s_addr);
				printf("server = %s\n", server);
				break;
		}
	}
	if (server == NULL)
		err_sys("Unable to get device IPv4 address");

    ret = pcap_set_snaplen(pcap, 65536);
    if (ret != 0) printf("pcap_set_snaplen failed %s\n", pcap_geterr(pcap));

    ret = pcap_set_timeout(pcap, 1000); 
    if (ret != 0) printf("pcap_set_timeout failed %s\n", pcap_geterr(pcap));

    ret = pcap_set_buffer_size(pcap, 1000000); 
    if (ret != 0)
		printf("pcap_set_buffer_size failed %s\n", pcap_geterr(pcap));

    ret = pcap_set_promisc(pcap, 1); 
    if (ret != 0) printf("pcap_set_promisc failed %s\n", pcap_geterr(pcap));


    ret = pcap_activate(pcap);
    if (ret != 0) printf("pcap_activate failed %s\n", pcap_geterr(pcap));

	printf("Enter the port to scan: ");
	scanf("%d", &port);

	SNPRINTF(filter, sizeof(filter), "tcp and port %d", port);

	ret = pcap_compile(pcap, &fp, filter, 0, 0);
    if (ret != 0) printf("pcap_compile failed %s\n", pcap_geterr(pcap));

    ret = pcap_setfilter(pcap, &fp);
    if (ret != 0) printf("pcap_setfilter failed %s\n", pcap_geterr(pcap));

    ret = ssl_SetPrivateKey(server, port, "../../certs/server-key.pem",
                            FILETYPE_PEM, NULL, err);
    if (ret != 0)
        err_sys(err);

    while (1) {
        struct pcap_pkthdr header;
        const unsigned char* packet = pcap_next(pcap, &header);
        if (packet) {

            byte data[65535];

            if (header.caplen > 40)  { /* min ip(20) + min tcp(20) */
				int frame = ETHER_IF_FRAME_LEN;
				if (loopback)
					frame = LOCAL_IF_FRAME_LEN;
				packet        += frame;
				header.caplen -= frame;					
            }
            else
                continue;

            ret = ssl_DecodePacket(packet, header.caplen, data, err);
            if (ret < 0)
                printf("ssl_Decode ret = %d, %s\n", ret, err);
            if (ret > 0) {
                data[ret] = 0;
				printf("SSL App Data:%s\n", data);
            }
        }
    }

    return EXIT_SUCCESS;
}

#endif /* full build */
