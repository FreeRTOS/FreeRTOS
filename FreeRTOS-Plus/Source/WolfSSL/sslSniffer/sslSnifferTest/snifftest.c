/* snifftest.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFSSL_SNIFFER_STORE_DATA_CB
    #include <wolfssl/wolfcrypt/memory.h>
#endif

#ifdef _WIN32
    #define WOLFSSL_SNIFFER
#endif

#ifndef WOLFSSL_SNIFFER

/* blank build */
#include <stdio.h>
#include <stdlib.h>
int main(void)
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
#include <string.h>        /* strcmp */
#include <signal.h>        /* signal */
#include <ctype.h>         /* isprint */

#include <cyassl/sniffer.h>


#ifndef _WIN32
    #include <sys/socket.h>    /* AF_INET */
    #include <arpa/inet.h>
    #include <netinet/in.h>
#endif

typedef unsigned char byte;

enum {
    ETHER_IF_FRAME_LEN = 14,   /* ethernet interface frame length */
    NULL_IF_FRAME_LEN =   4,   /* no link interface frame length  */
};


/* A TLS record can be 16k and change. The chain is broken up into 2K chunks.
 * This covers the TLS record, plus a chunk for TCP/IP headers. */
#ifndef CHAIN_INPUT_CHUNK_SIZE
    #define CHAIN_INPUT_CHUNK_SIZE 2048
#elif (CHAIN_INPUT_CHUNK_SIZE < 256)
    #undef CHAIN_INPUT_CHUNK_SIZE
    #define CHAIN_INPUT_CHUNK_SIZE 256
#elif (CHAIN_INPUT_CHUNK_SIZE > 16384)
    #undef CHAIN_INPUT_CHUNK_SIZE
    #define CHAIN_INPUT_CHUNK_SIZE 16384
#endif
#define CHAIN_INPUT_COUNT ((16384 / CHAIN_INPUT_CHUNK_SIZE) + 1)


#ifndef STORE_DATA_BLOCK_SZ
    #define STORE_DATA_BLOCK_SZ 1024
#endif


pcap_t* pcap = NULL;
pcap_if_t* alldevs = NULL;


static void FreeAll(void)
{
    if (pcap)
        pcap_close(pcap);
    if (alldevs)
        pcap_freealldevs(alldevs);
#ifndef _WIN32
    ssl_FreeSniffer();
#endif
}


#ifdef WOLFSSL_SNIFFER_STATS

static void DumpStats(void)
{
    SSLStats sslStats;
    ssl_ReadStatistics(&sslStats);

    printf("SSL Stats (sslStandardConns):%lu\n",
            sslStats.sslStandardConns);
    printf("SSL Stats (sslClientAuthConns):%lu\n",
            sslStats.sslClientAuthConns);
    printf("SSL Stats (sslResumedConns):%lu\n",
            sslStats.sslResumedConns);
    printf("SSL Stats (sslEphemeralMisses):%lu\n",
            sslStats.sslEphemeralMisses);
    printf("SSL Stats (sslResumeMisses):%lu\n",
            sslStats.sslResumeMisses);
    printf("SSL Stats (sslCiphersUnsupported):%lu\n",
            sslStats.sslCiphersUnsupported);
    printf("SSL Stats (sslKeysUnmatched):%lu\n",
            sslStats.sslKeysUnmatched);
    printf("SSL Stats (sslKeyFails):%lu\n",
            sslStats.sslKeyFails);
    printf("SSL Stats (sslDecodeFails):%lu\n",
            sslStats.sslDecodeFails);
    printf("SSL Stats (sslAlerts):%lu\n",
            sslStats.sslAlerts);
    printf("SSL Stats (sslDecryptedBytes):%lu\n",
            sslStats.sslDecryptedBytes);
    printf("SSL Stats (sslEncryptedBytes):%lu\n",
            sslStats.sslEncryptedBytes);
    printf("SSL Stats (sslEncryptedPackets):%lu\n",
            sslStats.sslEncryptedPackets);
    printf("SSL Stats (sslDecryptedPackets):%lu\n",
            sslStats.sslDecryptedPackets);
    printf("SSL Stats (sslKeyMatches):%lu\n",
            sslStats.sslKeyMatches);
    printf("SSL Stats (sslEncryptedConns):%lu\n",
            sslStats.sslEncryptedConns);
}

#endif


static void sig_handler(const int sig)
{
    printf("SIGINT handled = %d.\n", sig);
    FreeAll();
#ifdef WOLFSSL_SNIFFER_STATS
    DumpStats();
#endif
    if (sig)
        exit(EXIT_SUCCESS);
}


static void err_sys(const char* msg)
{
	fprintf(stderr, "%s\n", msg);
    if (msg)
	    exit(EXIT_FAILURE);
}


#ifdef _WIN32
	#define SNPRINTF _snprintf
#else
	#define SNPRINTF snprintf
#endif


static char* iptos(const struct in_addr* addr)
{
	static char    output[32];
	byte *p = (byte*)&addr->s_addr;

	snprintf(output, sizeof(output), "%d.%d.%d.%d", p[0], p[1], p[2], p[3]);

	return output;
}


static const char* ip6tos(const struct in6_addr* addr)
{
	static char    output[42];
	return inet_ntop(AF_INET6, addr, output, 42);
}


#if defined(WOLFSSL_SNIFFER_STORE_DATA_CB) || defined(WOLFSSL_SNIFFER_CHAIN_INPUT)

static inline unsigned int min(unsigned int a, unsigned int b)
{
    return a > b ? b : a;
}

#endif


#ifdef WOLFSSL_SNIFFER_WATCH

const byte rsaHash[] = {
    0xD1, 0xB6, 0x12, 0xAD, 0xB6, 0x50, 0x7B, 0x59,
    0x97, 0x83, 0x6B, 0xCB, 0x35, 0xF5, 0xB8, 0x67,
    0xEB, 0x83, 0x75, 0x40, 0x1B, 0x42, 0x61, 0xF1,
    0x03, 0x72, 0xDC, 0x09, 0x0D, 0x60, 0x83, 0x15
};

const byte eccHash[] = {
    0xDA, 0x08, 0x6D, 0xB5, 0x0B, 0xC4, 0x9F, 0x8A,
    0x9E, 0x61, 0x9E, 0x87, 0x57, 0x5F, 0x00, 0xAA,
    0x76, 0xE5, 0x1C, 0x9C, 0x74, 0x2A, 0x19, 0xBE,
    0x22, 0xAE, 0x25, 0x3F, 0xA8, 0xAF, 0x8E, 0x7F
};


static int myWatchCb(void* vSniffer,
        const unsigned char* certHash, unsigned int certHashSz,
        const unsigned char* certChain, unsigned int certChainSz,
        void* ctx, char* error)
{
    const char* certName = NULL;

    (void)certChain;
    (void)certChainSz;
    (void)ctx;

    if (certHashSz == sizeof(rsaHash) &&
            memcmp(certHash, rsaHash, certHashSz) == 0)
        certName = "../../certs/server-key.pem";
    if (certHashSz == sizeof(eccHash) &&
            memcmp(certHash, eccHash, certHashSz) == 0)
        certName = "../../certs/ecc-key.pem";

    if (certName == NULL)
        return -1;

    return ssl_SetWatchKey_file(vSniffer, certName, FILETYPE_PEM, NULL, error);
}

#endif


#ifdef WOLFSSL_SNIFFER_STORE_DATA_CB

static int myStoreDataCb(const unsigned char* decryptBuf,
        unsigned int decryptBufSz, unsigned int decryptBufOffset, void* ctx)
{
    byte** data = (byte**)ctx;
    unsigned int qty;

    if (data == NULL)
        return -1;

    if (decryptBufSz < decryptBufOffset)
        return -1;

    qty = min(decryptBufSz - decryptBufOffset, STORE_DATA_BLOCK_SZ);

    if (*data == NULL) {
        byte* tmpData;
        tmpData = (byte*)XREALLOC(*data, decryptBufSz + 1,
                NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (tmpData == NULL) {
            XFREE(*data, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            *data = NULL;
            return -1;
        }
        *data = tmpData;
    }

    memcpy(*data + decryptBufOffset, decryptBuf + decryptBufOffset, qty);

    return qty;
}

#endif


int main(int argc, char** argv)
{
    int          ret = 0;
    int          hadBadPacket = 0;
	int		     inum;
	int		     port;
    int          saveFile = 0;
	int		     i = 0;
    int          frame = ETHER_IF_FRAME_LEN;
    char         err[PCAP_ERRBUF_SIZE];
	char         filter[32];
	const char  *server = NULL;
	struct       bpf_program fp;
	pcap_if_t   *d;
	pcap_addr_t *a;
#ifdef WOLFSSL_SNIFFER_CHAIN_INPUT
    struct iovec chain[CHAIN_INPUT_COUNT];
    int          chainSz;
#endif

    signal(SIGINT, sig_handler);

#ifndef _WIN32
    ssl_InitSniffer();   /* dll load on Windows */
#endif
    ssl_Trace("./tracefile.txt", err);
    ssl_EnableRecovery(1, -1, err);
#ifdef WOLFSSL_SNIFFER_WATCH
    ssl_SetWatchKeyCallback(myWatchCb, err);
#endif
#ifdef WOLFSSL_SNIFFER_STORE_DATA_CB
    ssl_SetStoreDataCallback(myStoreDataCb);
#endif

    if (argc == 1) {
        /* normal case, user chooses device and port */

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
		    err_sys("No interfaces found! Make sure pcap or WinPcap is"
                    " installed correctly and you have sufficient permissions");

	    printf("Enter the interface number (1-%d): ", i);
	    ret = scanf("%d", &inum);
        if (ret != 1) {
            printf("scanf port failed\n");
        }

	    if (inum < 1 || inum > i)
		    err_sys("Interface number out of range");

	    /* Jump to the selected adapter */
	    for (d = alldevs, i = 0; i < inum - 1; d = d->next, i++);

	    pcap = pcap_create(d->name, err);

        if (pcap == NULL) printf("pcap_create failed %s\n", err);

        /* print out addresses for selected interface */
	    for (a = d->addresses; a; a = a->next) {
            if (a->addr->sa_family == AF_INET) {
				server =
                    iptos(&((struct sockaddr_in *)a->addr)->sin_addr);
		        printf("server = %s\n", server);
            }
            else if (a->addr->sa_family == AF_INET6) {
                server =
                    ip6tos(&((struct sockaddr_in6 *)a->addr)->sin6_addr);
		        printf("server = %s\n", server);
            }
	    }
	    if (server == NULL)
		    err_sys("Unable to get device IPv4 or IPv6 address");

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
	    ret = scanf("%d", &port);
        if (ret != 1)
            printf("scanf port failed\n");

	    SNPRINTF(filter, sizeof(filter), "tcp and port %d", port);

	    ret = pcap_compile(pcap, &fp, filter, 0, 0);
        if (ret != 0) printf("pcap_compile failed %s\n", pcap_geterr(pcap));

        ret = pcap_setfilter(pcap, &fp);
        if (ret != 0) printf("pcap_setfilter failed %s\n", pcap_geterr(pcap));

	    /* get IPv4 or IPv6 addresses for selected interface */
	    for (a = d->addresses; a; a = a->next) {
            server = NULL;
            if (a->addr->sa_family == AF_INET) {
				server =
                    iptos(&((struct sockaddr_in *)a->addr)->sin_addr);
            }
            else if (a->addr->sa_family == AF_INET6) {
                server =
                    ip6tos(&((struct sockaddr_in6 *)a->addr)->sin6_addr);
            }

            if (server) {
            #ifndef WOLFSSL_SNIFFER_WATCH
                ret = ssl_SetPrivateKey(server, port,
                        "../../certs/server-key.pem",
                        FILETYPE_PEM, NULL, err);
                if (ret != 0) {
                    printf("Please run directly from sslSniffer/sslSnifferTest"
                           "dir\n");
                }
            #ifdef HAVE_SNI
                {
                    char altName[128];

                    printf("Enter alternate SNI: ");
                    ret = scanf("%s", altName);

                    if (strnlen(altName, 128) > 0) {
                        ret = ssl_SetNamedPrivateKey(altName,
                                server, port, "../../certs/server-key.pem",
                                FILETYPE_PEM, NULL, err);
                        if (ret != 0) {
                            printf("Please run directly from "
                                   "sslSniffer/sslSnifferTest dir\n");
                        }
                    }
                }
            #endif
            #endif
            }
	    }
    }
    else if (argc >= 3) {
        saveFile = 1;
        pcap = pcap_open_offline(argv[1], err);
        if (pcap == NULL) {
            printf("pcap_open_offline failed %s\n", err);
            ret = -1;
        }
        else {
            const char* passwd = NULL;
            /* defaults for server and port */
            port = 443;
            server = "127.0.0.1";

            if (argc >= 4)
                server = argv[3];

            if (argc >= 5)
                port = atoi(argv[4]);

            if (argc >= 6)
                passwd = argv[5];

            ret = ssl_SetPrivateKey(server, port, argv[2],
                                    FILETYPE_PEM, passwd, err);
        }
    }
    else {
        /* usage error */
        printf( "usage: ./snifftest or ./snifftest dump pemKey"
                " [server] [port] [password]\n");
        exit(EXIT_FAILURE);
    }

    if (ret != 0)
        err_sys(err);

    if (pcap_datalink(pcap) == DLT_NULL)
        frame = NULL_IF_FRAME_LEN;

    while (1) {
        static int packetNumber = 0;
        struct pcap_pkthdr header;
        const unsigned char* packet = pcap_next(pcap, &header);
        SSLInfo sslInfo;
        packetNumber++;
        if (packet) {

            byte* data = NULL;

            if (header.caplen > 40)  { /* min ip(20) + min tcp(20) */
				packet        += frame;
				header.caplen -= frame;
            }
            else
                continue;
#ifdef WOLFSSL_SNIFFER_CHAIN_INPUT
            {
                unsigned int j = 0;
                unsigned int remainder = header.caplen;

                chainSz = 0;
                do {
                    unsigned int chunkSz;

                    chunkSz = min(remainder, CHAIN_INPUT_CHUNK_SIZE);
                    chain[chainSz].iov_base = (void*)(packet + j);
                    chain[chainSz].iov_len = chunkSz;
                    j += chunkSz;
                    remainder -= chunkSz;
                    chainSz++;
                } while (j < header.caplen);
            }
#endif

#if defined(WOLFSSL_SNIFFER_CHAIN_INPUT) && \
    defined(WOLFSSL_SNIFFER_STORE_DATA_CB)
            ret = ssl_DecodePacketWithChainSessionInfoStoreData(chain, chainSz,
                    &data, &sslInfo, err);
#elif defined(WOLFSSL_SNIFFER_CHAIN_INPUT)
            (void)sslInfo;
            ret = ssl_DecodePacketWithChain(chain, chainSz, &data, err);
#elif defined(WOLFSSL_SNIFFER_STORE_DATA_CB)
            ret = ssl_DecodePacketWithSessionInfoStoreData(packet,
                    header.caplen, &data, &sslInfo, err);
#else
            ret = ssl_DecodePacketWithSessionInfo(packet, header.caplen, &data,
                                                  &sslInfo, err);
#endif
            if (ret < 0) {
                printf("ssl_Decode ret = %d, %s\n", ret, err);
                hadBadPacket = 1;
            }
            if (ret > 0) {
                int j;
                /* Convert non-printable data to periods. */
                for (j = 0; j < ret; j++) {
                    if (isprint(data[j]) || isspace(data[j])) continue;
                    data[j] = '.';
                }
                data[ret] = 0;
                printf("SSL App Data(%d:%d):%s\n", packetNumber, ret, data);
                ssl_FreeZeroDecodeBuffer(&data, ret, err);
            }
        }
        else if (saveFile)
            break;      /* we're done reading file */
    }
    FreeAll();

    return hadBadPacket ? EXIT_FAILURE : EXIT_SUCCESS;
}

#endif /* full build */
