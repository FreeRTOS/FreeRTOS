/* client.c
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

#include <wolfssl/ssl.h>

#if defined(WOLFSSL_MDK_ARM) || defined(WOLFSSL_KEIL_TCP_NET)
        #include <stdio.h>
        #include <string.h>
        #include "rl_fs.h"
        #include "rl_net.h"
#endif

#include <wolfssl/test.h>

#include <examples/client/client.h>
#include <wolfssl/error-ssl.h>

#ifndef NO_WOLFSSL_CLIENT

#ifdef USE_FAST_MATH
    /* included to inspect the size of FP_MAX_BITS */
    /* need integer.h header to make sure right math version used */
    #include <wolfssl/wolfcrypt/integer.h>
#endif
#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    static int devId = INVALID_DEVID;
#endif

#define DEFAULT_TIMEOUT_SEC 2
#ifndef MAX_NON_BLOCK_SEC
#define MAX_NON_BLOCK_SEC   10
#endif

#define OCSP_STAPLING 1
#define OCSP_STAPLINGV2 2
#define OCSP_STAPLINGV2_MULTI 3
#define OCSP_STAPLING_OPT_MAX OCSP_STAPLINGV2_MULTI

/* Note on using port 0: the client standalone example doesn't utilize the
 * port 0 port sharing; that is used by (1) the server in external control
 * test mode and (2) the testsuite which uses this code and sets up the correct
 * port numbers when the internal thread using the server code using port 0. */

static int lng_index = 0;
#ifdef WOLFSSL_CALLBACKS
    WOLFSSL_TIMEVAL timeoutConnect;
    static int handShakeCB(HandShakeInfo* info)
    {
        (void)info;
        return 0;
    }

    static int timeoutCB(TimeoutInfo* info)
    {
        (void)info;
        return 0;
    }

#endif

#ifdef HAVE_SESSION_TICKET
    static int sessionTicketCB(WOLFSSL* ssl,
                        const unsigned char* ticket, int ticketSz,
                        void* ctx)
    {
        (void)ssl;
        (void)ticket;
        printf("Session Ticket CB: ticketSz = %d, ctx = %s\n",
               ticketSz, (char*)ctx);
        return 0;
    }
#endif

static int NonBlockingSSL_Connect(WOLFSSL* ssl)
{
    int ret;
    int error;
    SOCKET_T sockfd;
    int select_ret = 0;
    int elapsedSec = 0;

#ifndef WOLFSSL_CALLBACKS
    ret = wolfSSL_connect(ssl);
#else
    ret = wolfSSL_connect_ex(ssl, handShakeCB, timeoutCB, timeoutConnect);
#endif
    error = wolfSSL_get_error(ssl, 0);
    sockfd = (SOCKET_T)wolfSSL_get_fd(ssl);

    while (ret != WOLFSSL_SUCCESS &&
        (error == WOLFSSL_ERROR_WANT_READ || error == WOLFSSL_ERROR_WANT_WRITE
        #ifdef WOLFSSL_ASYNC_CRYPT
            || error == WC_PENDING_E
        #endif
        #ifdef WOLFSSL_NONBLOCK_OCSP
            || error == OCSP_WANT_READ
        #endif
    )) {
        int currTimeout = 1;

        if (error == WOLFSSL_ERROR_WANT_READ)
            printf("... client would read block\n");
        else if (error == WOLFSSL_ERROR_WANT_WRITE)
            printf("... client would write block\n");

#ifdef WOLFSSL_ASYNC_CRYPT
        if (error == WC_PENDING_E) {
            ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
            if (ret < 0) break;
        }
        else
#endif
        {
            if (error != WOLFSSL_ERROR_WANT_WRITE) {
            #ifdef WOLFSSL_DTLS
                currTimeout = wolfSSL_dtls_get_current_timeout(ssl);
            #endif
                select_ret = tcp_select(sockfd, currTimeout);
            }
        }

        if ((select_ret == TEST_RECV_READY) || (select_ret == TEST_SEND_READY)
            || (select_ret == TEST_ERROR_READY)
        #ifdef WOLFSSL_ASYNC_CRYPT
            || error == WC_PENDING_E
        #endif
        ) {
        #ifndef WOLFSSL_CALLBACKS
            ret = wolfSSL_connect(ssl);
        #else
            ret = wolfSSL_connect_ex(ssl, handShakeCB, timeoutCB,
                                                                timeoutConnect);
        #endif
            error = wolfSSL_get_error(ssl, 0);
            elapsedSec = 0; /* reset elapsed */
            if (error == WOLFSSL_ERROR_WANT_WRITE) {
                /* Do a send select here. */
                select_ret = tcp_select_tx(sockfd, 1);
                if (select_ret == TEST_TIMEOUT) {
                    error = WOLFSSL_FATAL_ERROR;
                }
            }
        }
        else if (select_ret == TEST_TIMEOUT && !wolfSSL_dtls(ssl)) {
            error = WOLFSSL_ERROR_WANT_READ;

            elapsedSec += currTimeout;
            if (elapsedSec > MAX_NON_BLOCK_SEC) {
                printf("Nonblocking connect timeout\n");
                error = WOLFSSL_FATAL_ERROR;
            }
        }
#ifdef WOLFSSL_DTLS
        else if (select_ret == TEST_TIMEOUT && wolfSSL_dtls(ssl) &&
                                        wolfSSL_dtls_got_timeout(ssl) >= 0) {
            error = WOLFSSL_ERROR_WANT_READ;
        }
#endif
        else {
            error = WOLFSSL_FATAL_ERROR;
        }
    }

    return ret;
}


static void ShowCiphers(void)
{
    static char ciphers[WOLFSSL_CIPHER_LIST_MAX_SIZE];

    int ret = wolfSSL_get_ciphers(ciphers, (int)sizeof(ciphers));

    if (ret == WOLFSSL_SUCCESS)
        printf("%s\n", ciphers);
}

/* Shows which versions are valid */
static void ShowVersions(void)
{
#ifndef NO_OLD_TLS
    #ifdef WOLFSSL_ALLOW_SSLV3
        printf("0:");
    #endif
    #ifdef WOLFSSL_ALLOW_TLSV10
        printf("1:");
    #endif
    printf("2:");
#endif /* NO_OLD_TLS */
#ifndef WOLFSSL_NO_TLS12
    printf("3:");
#endif
#ifdef WOLFSSL_TLS13
    printf("4:");
#endif
    printf("d(downgrade):");
#if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EITHER_SIDE)
    printf("e(either):");
#endif
    printf("\n");
}

#ifdef WOLFSSL_TLS13
static void SetKeyShare(WOLFSSL* ssl, int onlyKeyShare, int useX25519,
                        int useX448)
{
    int groups[3] = {0};
    int count = 0;

    (void)useX25519;
    (void)useX448;

    WOLFSSL_START(WC_FUNC_CLIENT_KEY_EXCHANGE_SEND);
    if (onlyKeyShare == 0 || onlyKeyShare == 2) {
    #ifdef HAVE_CURVE25519
        if (useX25519) {
            groups[count++] = WOLFSSL_ECC_X25519;
            if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X25519) != WOLFSSL_SUCCESS)
                err_sys("unable to use curve x25519");
        }
        else
    #endif
    #ifdef HAVE_CURVE448
        if (useX448) {
            groups[count++] = WOLFSSL_ECC_X448;
            if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X448) != WOLFSSL_SUCCESS)
                err_sys("unable to use curve x448");
        }
        else
    #endif
        {
    #ifdef HAVE_ECC
        #if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
            groups[count++] = WOLFSSL_ECC_SECP256R1;
            if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_SECP256R1)
                                                           != WOLFSSL_SUCCESS) {
                err_sys("unable to use curve secp256r1");
            }
        #endif
    #endif
        }
    }
    if (onlyKeyShare == 0 || onlyKeyShare == 1) {
    #ifdef HAVE_FFDHE_2048
        groups[count++] = WOLFSSL_FFDHE_2048;
        if (wolfSSL_UseKeyShare(ssl, WOLFSSL_FFDHE_2048) != WOLFSSL_SUCCESS)
            err_sys("unable to use DH 2048-bit parameters");
    #endif
    }

    if (wolfSSL_set_groups(ssl, groups, count) != WOLFSSL_SUCCESS)
        err_sys("unable to set groups");
    WOLFSSL_END(WC_FUNC_CLIENT_KEY_EXCHANGE_SEND);
}
#endif

#ifdef WOLFSSL_EARLY_DATA
static void EarlyData(WOLFSSL_CTX* ctx, WOLFSSL* ssl, const char* msg,
                      int msgSz, char* buffer)
{
    int err;
    int ret;

    do {
        err = 0; /* reset error */
        ret = wolfSSL_write_early_data(ssl, msg, msgSz, &msgSz);
        if (ret <= 0) {
            err = wolfSSL_get_error(ssl, 0);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
        #endif
        }
    } while (err == WC_PENDING_E);
    if (ret != msgSz) {
        printf("SSL_write_early_data msg error %d, %s\n", err,
                                         wolfSSL_ERR_error_string(err, buffer));
        wolfSSL_free(ssl); ssl = NULL;
        wolfSSL_CTX_free(ctx); ctx = NULL;
        err_sys("SSL_write_early_data failed");
    }
    do {
        err = 0; /* reset error */
        ret = wolfSSL_write_early_data(ssl, msg, msgSz, &msgSz);
        if (ret <= 0) {
            err = wolfSSL_get_error(ssl, 0);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
        #endif
        }
    } while (err == WC_PENDING_E);
    if (ret != msgSz) {
        printf("SSL_write_early_data msg error %d, %s\n", err,
                                         wolfSSL_ERR_error_string(err, buffer));
        wolfSSL_free(ssl);
        wolfSSL_CTX_free(ctx);
        err_sys("SSL_write_early_data failed");
    }
}
#endif

/* Measures average time to create, connect and disconnect a connection (TPS).
Benchmark = number of connections. */
static const char* client_bench_conmsg[][5] = {
    /* English */
    {
        "wolfSSL_resume  avg took:", "milliseconds\n",
        "wolfSSL_connect avg took:", "milliseconds\n",
        NULL
    },
    #ifndef NO_MULTIBYTE_PRINT
    /* Japanese */
    {
        "wolfSSL_resume  平均時間:", "ミリ秒\n",
        "wolfSSL_connect 平均時間:", "ミリ秒\n",
    }
    #endif
};

static int ClientBenchmarkConnections(WOLFSSL_CTX* ctx, char* host, word16 port,
    int dtlsUDP, int dtlsSCTP, int benchmark, int resumeSession, int useX25519,
    int useX448, int helloRetry, int onlyKeyShare, int version, int earlyData)
{
    /* time passed in number of connects give average */
    int times = benchmark, skip = times * 0.1;
    int loops = resumeSession ? 2 : 1;
    int i = 0, err, ret;
#ifndef NO_SESSION_CACHE
    WOLFSSL_SESSION* benchSession = NULL;
#endif
#ifdef WOLFSSL_TLS13
    byte* reply[80];
    static const char msg[] = "GET /index.html HTTP/1.0\r\n\r\n";
#ifdef WOLFSSL_EARLY_DATA
    static const char earlyMsg[] = "A drop of info";
#endif
#endif
    const char** words = client_bench_conmsg[lng_index];

    (void)resumeSession;
    (void)useX25519;
    (void)useX448;
    (void)helloRetry;
    (void)onlyKeyShare;
    (void)version;
    (void)earlyData;

    while (loops--) {
    #ifndef NO_SESSION_CACHE
        int benchResume = resumeSession && loops == 0;
    #endif
        double start = current_time(1), avg;

        for (i = 0; i < times; i++) {
            SOCKET_T sockfd;
            WOLFSSL* ssl;

            if (i == skip)
                start = current_time(1);

            ssl = wolfSSL_new(ctx);
            if (ssl == NULL)
                err_sys("unable to get SSL object");

        #ifndef NO_SESSION_CACHE
            if (benchResume)
                wolfSSL_set_session(ssl, benchSession);
        #endif
        #ifdef WOLFSSL_TLS13
            else if (version >= 4) {
                if (!helloRetry)
                    SetKeyShare(ssl, onlyKeyShare, useX25519, useX448);
                else
                    wolfSSL_NoKeyShares(ssl);
            }
        #endif

            tcp_connect(&sockfd, host, port, dtlsUDP, dtlsSCTP, ssl);

            if (wolfSSL_set_fd(ssl, sockfd) != WOLFSSL_SUCCESS) {
                err_sys("error in setting fd");
            }

    #if defined(WOLFSSL_TLS13) && !defined(NO_SESSION_CACHE) && \
                                                     defined(WOLFSSL_EARLY_DATA)
            if (version >= 4 && benchResume && earlyData) {
                char buffer[WOLFSSL_MAX_ERROR_SZ];
                EarlyData(ctx, ssl, earlyMsg, sizeof(earlyMsg)-1, buffer);
            }
    #endif
            do {
                err = 0; /* reset error */
                ret = wolfSSL_connect(ssl);
                if (ret != WOLFSSL_SUCCESS) {
                    err = wolfSSL_get_error(ssl, 0);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (err == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                        if (ret < 0) break;
                    }
                #endif
                }
            } while (err == WC_PENDING_E);
            if (ret != WOLFSSL_SUCCESS) {
                err_sys("SSL_connect failed");
            }

    #ifdef WOLFSSL_TLS13
        #ifndef NO_SESSION_CACHE
            if (version >= 4 && resumeSession && !benchResume)
        #else
            if (version >= 4 && resumeSession)
        #endif
            {
                if (wolfSSL_write(ssl, msg, sizeof(msg)-1) <= 0)
                    err_sys("SSL_write failed");

                if (wolfSSL_read(ssl, reply, sizeof(reply)-1) <= 0)
                    err_sys("SSL_read failed");
            }
    #endif


            wolfSSL_shutdown(ssl);
    #ifndef NO_SESSION_CACHE
            if (i == (times-1) && resumeSession) {
                benchSession = wolfSSL_get_session(ssl);
            }
    #endif
            wolfSSL_free(ssl); ssl = NULL;
            CloseSocket(sockfd);
        }
        avg = current_time(0) - start;
        avg /= (times - skip);
        avg *= 1000;   /* milliseconds */
    #ifndef NO_SESSION_CACHE
        if (benchResume)
            printf("%s %8.3f %s\n", words[0],avg, words[1]);
        else
    #endif
            printf("%s %8.3f %s\n", words[2],avg, words[3]);

        WOLFSSL_TIME(times);
    }

    return EXIT_SUCCESS;
}

/* Measures throughput in kbps. Throughput = number of bytes */
static int ClientBenchmarkThroughput(WOLFSSL_CTX* ctx, char* host, word16 port,
    int dtlsUDP, int dtlsSCTP, int block, size_t throughput, int useX25519,
    int useX448)
{
    double start, conn_time = 0, tx_time = 0, rx_time = 0;
    SOCKET_T sockfd;
    WOLFSSL* ssl;
    int ret = 0, err = 0;

    start = current_time(1);
    ssl = wolfSSL_new(ctx);
    if (ssl == NULL)
        err_sys("unable to get SSL object");

    tcp_connect(&sockfd, host, port, dtlsUDP, dtlsSCTP, ssl);
    if (wolfSSL_set_fd(ssl, sockfd) != WOLFSSL_SUCCESS) {
        err_sys("error in setting fd");
    }

    (void)useX25519;
    (void)useX448;
    #ifdef WOLFSSL_TLS13
        #ifdef HAVE_CURVE25519
            if (useX25519) {
                if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X25519)
                        != WOLFSSL_SUCCESS) {
                    err_sys("unable to use curve x25519");
                }
            }
        #endif
        #ifdef HAVE_CURVE448
            if (useX448) {
                if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X448)
                        != WOLFSSL_SUCCESS) {
                    err_sys("unable to use curve x448");
                }
            }
        #endif
    #endif

    do {
        err = 0; /* reset error */
        ret = wolfSSL_connect(ssl);
        if (ret != WOLFSSL_SUCCESS) {
            err = wolfSSL_get_error(ssl, 0);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
        #endif
        }
    } while (err == WC_PENDING_E);
    if (ret == WOLFSSL_SUCCESS) {
        /* Perform throughput test */
        char *tx_buffer, *rx_buffer;

        /* Record connection time */
        conn_time = current_time(0) - start;

        /* Allocate TX/RX buffers */
        tx_buffer = (char*)XMALLOC(block, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        rx_buffer = (char*)XMALLOC(block, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (tx_buffer && rx_buffer) {
            WC_RNG rng;

            /* Startup the RNG */
        #if !defined(HAVE_FIPS) && defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_InitRng_ex(&rng, NULL, devId);
        #else
            ret = wc_InitRng(&rng);
        #endif
            if (ret == 0) {
                size_t xfer_bytes;

                /* Generate random data to send */
                ret = wc_RNG_GenerateBlock(&rng, (byte*)tx_buffer, block);
                wc_FreeRng(&rng);
                if(ret != 0) {
                    err_sys("wc_RNG_GenerateBlock failed");
                }

                /* Perform TX and RX of bytes */
                xfer_bytes = 0;
                while (throughput > xfer_bytes) {
                    int len, rx_pos, select_ret;

                    /* Determine packet size */
                    len = min(block, (int)(throughput - xfer_bytes));

                    /* Perform TX */
                    start = current_time(1);
                    do {
                        err = 0; /* reset error */
                        ret = wolfSSL_write(ssl, tx_buffer, len);
                        if (ret <= 0) {
                            err = wolfSSL_get_error(ssl, 0);
                        #ifdef WOLFSSL_ASYNC_CRYPT
                            if (err == WC_PENDING_E) {
                                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                                if (ret < 0) break;
                            }
                        #endif
                        }
                    } while (err == WC_PENDING_E);
                    if (ret != len) {
                        printf("SSL_write bench error %d!\n", err);
                        err_sys("SSL_write failed");
                    }
                    tx_time += current_time(0) - start;

                    /* Perform RX */
                    select_ret = tcp_select(sockfd, DEFAULT_TIMEOUT_SEC);
                    if (select_ret == TEST_RECV_READY) {
                        start = current_time(1);
                        rx_pos = 0;
                        while (rx_pos < len) {
                            ret = wolfSSL_read(ssl, &rx_buffer[rx_pos],
                                                                len - rx_pos);
                            if (ret <= 0) {
                                err = wolfSSL_get_error(ssl, 0);
                            #ifdef WOLFSSL_ASYNC_CRYPT
                                if (err == WC_PENDING_E) {
                                    ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                                    if (ret < 0) break;
                                }
                                else
                            #endif
                                if (err != WOLFSSL_ERROR_WANT_READ) {
                                    printf("SSL_read bench error %d\n", err);
                                    err_sys("SSL_read failed");
                                }
                            }
                            else {
                                rx_pos += ret;
                            }
                        }
                        rx_time += current_time(0) - start;
                    }

                    /* Compare TX and RX buffers */
                    if (XMEMCMP(tx_buffer, rx_buffer, len) != 0) {
                        free(tx_buffer);
                        tx_buffer = NULL;
                        free(rx_buffer);
                        rx_buffer = NULL;
                        err_sys("Compare TX and RX buffers failed");
                    }

                    /* Update overall position */
                    xfer_bytes += len;
                }
            }
            else {
                err_sys("wc_InitRng failed");
            }
            (void)rng; /* for WC_NO_RNG case */
        }
        else {
            err_sys("Client buffer malloc failed");
        }
        if(tx_buffer) XFREE(tx_buffer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if(rx_buffer) XFREE(rx_buffer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
    else {
        err_sys("wolfSSL_connect failed");
    }

    wolfSSL_shutdown(ssl);
    wolfSSL_free(ssl); ssl = NULL;
    CloseSocket(sockfd);

#if !defined(__MINGW32__)
    printf("wolfSSL Client Benchmark %zu bytes\n"
#else
    printf("wolfSSL Client Benchmark %d bytes\n"
#endif
        "\tConnect %8.3f ms\n"
        "\tTX      %8.3f ms (%8.3f MBps)\n"
        "\tRX      %8.3f ms (%8.3f MBps)\n",
#if !defined(__MINGW32__)
        throughput,
#else
        (int)throughput,
#endif
        conn_time * 1000,
        tx_time * 1000, throughput / tx_time / 1024 / 1024,
        rx_time * 1000, throughput / rx_time / 1024 / 1024
    );

    return EXIT_SUCCESS;
}

const char* starttlsCmd[6] = {
    "220",
    "EHLO mail.example.com\r\n",
    "250",
    "STARTTLS\r\n",
    "220",
    "QUIT\r\n",
};

/* Initiates the STARTTLS command sequence over TCP */
static int StartTLS_Init(SOCKET_T* sockfd)
{
    char tmpBuf[256];

    if (sockfd == NULL)
        return BAD_FUNC_ARG;

    /* S: 220 <host> SMTP service ready */
    XMEMSET(tmpBuf, 0, sizeof(tmpBuf));
    if (recv(*sockfd, tmpBuf, sizeof(tmpBuf)-1, 0) < 0)
        err_sys("failed to read STARTTLS command\n");

    if (!XSTRNCMP(tmpBuf, starttlsCmd[0], XSTRLEN(starttlsCmd[0]))) {
        printf("%s\n", tmpBuf);
    } else {
        err_sys("incorrect STARTTLS command received");
    }

    /* C: EHLO mail.example.com */
    if (send(*sockfd, starttlsCmd[1], (int)XSTRLEN(starttlsCmd[1]), 0) !=
              (int)XSTRLEN(starttlsCmd[1]))
        err_sys("failed to send STARTTLS EHLO command\n");

    /* S: 250 <host> offers a warm hug of welcome */
    XMEMSET(tmpBuf, 0, sizeof(tmpBuf));
    if (recv(*sockfd, tmpBuf, sizeof(tmpBuf)-1, 0) < 0)
        err_sys("failed to read STARTTLS command\n");

    if (!XSTRNCMP(tmpBuf, starttlsCmd[2], XSTRLEN(starttlsCmd[2]))) {
        printf("%s\n", tmpBuf);
    } else {
        err_sys("incorrect STARTTLS command received");
    }

    /* C: STARTTLS */
    if (send(*sockfd, starttlsCmd[3], (int)XSTRLEN(starttlsCmd[3]), 0) !=
              (int)XSTRLEN(starttlsCmd[3])) {
        err_sys("failed to send STARTTLS command\n");
    }

    /* S: 220 Go ahead */
    XMEMSET(tmpBuf, 0, sizeof(tmpBuf));
    if (recv(*sockfd, tmpBuf, sizeof(tmpBuf)-1, 0) < 0)
        err_sys("failed to read STARTTLS command\n");

    if (!XSTRNCMP(tmpBuf, starttlsCmd[4], XSTRLEN(starttlsCmd[4]))) {
        printf("%s\n", tmpBuf);
    } else {
        err_sys("incorrect STARTTLS command received, expected 220");
    }

    return WOLFSSL_SUCCESS;
}

/* Closes down the SMTP connection */
static int SMTP_Shutdown(WOLFSSL* ssl, int wc_shutdown)
{
    int ret, err = 0;
    char tmpBuf[256];

    if (ssl == NULL)
        return BAD_FUNC_ARG;

    printf("\nwolfSSL client shutting down SMTP connection\n");

    XMEMSET(tmpBuf, 0, sizeof(tmpBuf));

    /* C: QUIT */
    do {
        ret = wolfSSL_write(ssl, starttlsCmd[5], (int)XSTRLEN(starttlsCmd[5]));
        if (ret < 0) {
            err = wolfSSL_get_error(ssl, 0);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
        #endif
        }
    } while (err == WC_PENDING_E);
    if (ret != (int)XSTRLEN(starttlsCmd[5])) {
        err_sys("failed to send SMTP QUIT command\n");
    }

    /* S: 221 2.0.0 Service closing transmission channel */
    do {
        ret = wolfSSL_read(ssl, tmpBuf, sizeof(tmpBuf));
        if (ret < 0) {
            err = wolfSSL_get_error(ssl, 0);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
        #endif
        }
    } while (err == WC_PENDING_E);
    if (ret < 0) {
        err_sys("failed to read SMTP closing down response\n");
    }

    printf("%s\n", tmpBuf);

    ret = wolfSSL_shutdown(ssl);
    if (wc_shutdown && ret == WOLFSSL_SHUTDOWN_NOT_DONE) {
        if (tcp_select(wolfSSL_get_fd(ssl), DEFAULT_TIMEOUT_SEC) ==
                TEST_RECV_READY) {
            ret = wolfSSL_shutdown(ssl);    /* bidirectional shutdown */
            if (ret == WOLFSSL_SUCCESS)
                printf("Bidirectional shutdown complete\n");
        }
        if (ret != WOLFSSL_SUCCESS)
            printf("Bidirectional shutdown failed\n");
    }

    return WOLFSSL_SUCCESS;
}

static void ClientWrite(WOLFSSL* ssl, char* msg, int msgSz, const char* str)
{
    int ret, err;
    char buffer[WOLFSSL_MAX_ERROR_SZ];

    do {
        err = 0; /* reset error */
        ret = wolfSSL_write(ssl, msg, msgSz);
        if (ret <= 0) {
            err = wolfSSL_get_error(ssl, 0);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
        #endif
        }
    } while (err == WOLFSSL_ERROR_WANT_WRITE
    #ifdef WOLFSSL_ASYNC_CRYPT
        || err == WC_PENDING_E
    #endif
    );
    if (ret != msgSz) {
        printf("SSL_write%s msg error %d, %s\n", str, err,
                                        wolfSSL_ERR_error_string(err, buffer));
        err_sys("SSL_write failed");
    }
}

static void ClientRead(WOLFSSL* ssl, char* reply, int replyLen, int mustRead,
                       const char* str)
{
    int ret, err;
    char buffer[WOLFSSL_MAX_ERROR_SZ];
    double start = current_time(1), elapsed;

    do {
        err = 0; /* reset error */
        ret = wolfSSL_read(ssl, reply, replyLen);
        if (ret <= 0) {
            err = wolfSSL_get_error(ssl, 0);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
            else
        #endif
            if (err != WOLFSSL_ERROR_WANT_READ) {
                printf("SSL_read reply error %d, %s\n", err,
                                         wolfSSL_ERR_error_string(err, buffer));
                err_sys("SSL_read failed");
            }
        }

        if (mustRead && err == WOLFSSL_ERROR_WANT_READ) {
            elapsed = current_time(0) - start;
            if (elapsed > MAX_NON_BLOCK_SEC) {
                printf("Nonblocking read timeout\n");
                ret = WOLFSSL_FATAL_ERROR;
                break;
            }
        }
    } while ((mustRead && err == WOLFSSL_ERROR_WANT_READ)
    #ifdef WOLFSSL_ASYNC_CRYPT
        || err == WC_PENDING_E
    #endif
    );
    if (ret > 0) {
        reply[ret] = 0;
        printf("%s%s\n", str, reply);
    }
}


/* when adding new option, please follow the steps below: */
/*  1. add new option message in English section          */
/*  2. increase the number of the second column           */
/*  3. add the same message into Japanese section         */
/*     (will be translated later)                         */
/*  4. add printf() into suitable position of Usage()     */
static const char* client_usage_msg[][59] = {
    /* English */
    {
        " NOTE: All files relative to wolfSSL home dir\n",          /* 0 */
        "Max RSA key size in bits for build is set at : ",          /* 1 */
#ifdef NO_RSA
        "RSA not supported\n",                                      /* 2 */
#elif defined(WOLFSSL_SP_MATH) /* case of SP math only */
#ifndef WOLFSSL_SP_NO_3072
        "3072\n",                                                   /* 2 */
#elif !defined(WOLFSSL_SP_NO_2048)
        "2048\n",                                                   /* 2 */
#else
        "0\n",                                                      /* 2 */
#endif
#elif defined(USE_FAST_MATH)
#else
        "INFINITE\n",                                               /* 2 */
#endif
        "-? <num>    Help, print this usage\n"
        "            0: English, 1: Japanese\n",                    /* 3 */
        "-h <host>   Host to connect to, default",                  /* 4 */
        "-p <num>    Port to connect on, not 0, default",           /* 5 */

#ifndef WOLFSSL_TLS13
        "-v <num>    SSL version [0-3], SSLv3(0) - TLS1.2(3)), default", /* 6 */
        "-V          Prints valid ssl version numbers"
                                             ", SSLv3(0) - TLS1.2(3)\n", /* 7 */
#else
        "-v <num>    SSL version [0-4], SSLv3(0) - TLS1.3(4)), default", /* 6 */
        "-V          Prints valid ssl version numbers,"
                                            " SSLv3(0) - TLS1.3(4)\n",   /* 7 */
#endif
        "-l <str>    Cipher suite list (: delimited)\n",                /* 8 */
        "-c <file>   Certificate file,           default",              /* 9 */
        "-k <file>   Key file,                   default",              /* 10 */
        "-A <file>   Certificate Authority file, default",              /* 11 */
#ifndef NO_DH
        "-Z <num>    Minimum DH key bits,        default",              /* 12 */
#endif
        "-b <num>    Benchmark <num> connections and print stats\n",    /* 13 */
#ifdef HAVE_ALPN
        "-L <str>    Application-Layer Protocol"
                                      " Negotiation ({C,F}:<list>)\n",  /* 14 */
#endif
        "-B <num>    Benchmark throughput"
                                " using <num> bytes and print stats\n", /* 15 */
        "-s          Use pre Shared keys\n",                            /* 16 */
        "-d          Disable peer checks\n",                            /* 17 */
        "-D          Override Date Errors example\n",                   /* 18 */
        "-e          List Every cipher suite available, \n",            /* 19 */
        "-g          Send server HTTP GET\n",                           /* 20 */
        "-u          Use UDP DTLS,"
                 " add -v 2 for DTLSv1, -v 3 for DTLSv1.2 (default)\n", /* 21 */
#ifdef WOLFSSL_SCTP
        "-G          Use SCTP DTLS,"
                " add -v 2 for DTLSv1, -v 3 for DTLSv1.2 (default)\n",  /* 22 */
#endif
        "-m          Match domain name in cert\n",                      /* 23 */
        "-N          Use Non-blocking sockets\n",                       /* 24 */
#ifndef NO_SESSION_CACHE
        "-r          Resume session\n",                                 /* 25 */
#endif
        "-w          Wait for bidirectional shutdown\n",                /* 26 */
        "-M <prot>   Use STARTTLS, using <prot> protocol (smtp)\n",     /* 27 */
#ifdef HAVE_SECURE_RENEGOTIATION
        "-R          Allow Secure Renegotiation\n",                     /* 28 */
        "-i          Force client Initiated Secure Renegotiation\n",    /* 29 */
#endif
        "-f          Fewer packets/group messages\n",                   /* 30 */
        "-x          Disable client cert/key loading\n",                /* 31 */
        "-X          Driven by eXternal test case\n",                   /* 32 */
        "-j          Use verify callback override\n",                   /* 33 */
#ifdef SHOW_SIZES
        "-z          Print structure sizes\n",                          /* 34 */
#endif
#ifdef HAVE_SNI
        "-S <str>    Use Host Name Indication\n",                       /* 35 */
#endif
#ifdef HAVE_MAX_FRAGMENT
        "-F <num>    Use Maximum Fragment Length [1-6]\n",              /* 36 */
#endif
#ifdef HAVE_TRUNCATED_HMAC
        "-T          Use Truncated HMAC\n",                             /* 37 */
#endif
#ifdef HAVE_EXTENDED_MASTER
        "-n          Disable Extended Master Secret\n",                 /* 38 */
#endif
#ifdef HAVE_OCSP
        "-o          Perform OCSP lookup on peer certificate\n",        /* 39 */
        "-O <url>    Perform OCSP lookup using <url> as responder\n",   /* 40 */
#endif
#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
 || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
        "-W <num>    Use OCSP Stapling (1 v1, 2 v2, 3 v2 multi)\n",     /* 41 */
#endif
#if defined(ATOMIC_USER) && !defined(WOLFSSL_AEAD_ONLY)
        "-U          Atomic User Record Layer Callbacks\n",             /* 42 */
#endif
#ifdef HAVE_PK_CALLBACKS
        "-P          Public Key Callbacks\n",                           /* 43 */
#endif
#ifdef HAVE_ANON
        "-a          Anonymous client\n",                               /* 44 */
#endif
#ifdef HAVE_CRL
        "-C          Disable CRL\n",                                    /* 45 */
#endif
#ifdef WOLFSSL_TRUST_PEER_CERT
        "-E <file>   Path to load trusted peer cert\n",                 /* 46 */
#endif
#ifdef HAVE_WNR
        "-q <file>   Whitewood config file,      defaults\n",           /* 47 */
#endif
        "-H <arg>    Internal tests"
            " [defCipherList, exitWithRet, verifyFail, useSupCurve,\n", /* 48 */
        "                            loadSSL, disallowETM]\n",          /* 49 */
#ifdef WOLFSSL_TLS13
        "-J          Use HelloRetryRequest to choose group for KE\n",   /* 50 */
        "-K          Key Exchange for PSK not using (EC)DHE\n",         /* 51 */
        "-I          Update keys and IVs before sending data\n",        /* 52 */
#ifndef NO_DH
        "-y          Key Share with FFDHE named groups only\n",         /* 53 */
#endif
#ifdef HAVE_ECC
        "-Y          Key Share with ECC named groups only\n",           /* 54 */
#endif
#endif /* WOLFSSL_TLS13 */
#ifdef HAVE_CURVE25519
        "-t          Use X25519 for key exchange\n",                    /* 55 */
#endif
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
        "-Q          Support requesting certificate post-handshake\n",  /* 56 */
#endif
#ifdef WOLFSSL_EARLY_DATA
        "-0          Early data sent to server (0-RTT handshake)\n",    /* 57 */
#endif
#ifdef WOLFSSL_MULTICAST
        "-3 <grpid>  Multicast, grpid < 256\n",                         /* 58 */
#endif
        "-1 <num>    Display a result by specified language.\n"
                               "            0: English, 1: Japanese\n", /* 59 */
#if !defined(NO_DH) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST) && !defined(WOLFSSL_OLD_PRIME_CHECK)
        "-2          Disable DH Prime check\n",                         /* 60 */
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
        "-4          Use resumption for renegotiation\n",               /* 61 */
#endif
#ifdef HAVE_TRUSTED_CA
        "-5          Use Trusted CA Key Indication\n",                  /* 62 */
#endif
#ifdef HAVE_CURVE448
        "-8          Use X448 for key exchange\n",                      /* 65 */
#endif
        NULL,
    },
#ifndef NO_MULTIBYTE_PRINT
    /* Japanese */
        {
        " 注意 : 全てのファイルは wolfSSL ホーム・ディレクトリからの相対です。"
                                                               "\n",     /* 0 */
        "RSAの最大ビットは次のように設定されています: ",                 /* 1 */
#ifdef NO_RSA
        "RSAはサポートされていません。\n",                               /* 2 */
#elif defined(WOLFSSL_SP_MATH) /* case of SP math only */
#ifndef WOLFSSL_SP_NO_3072
        "3072\n",                                                        /* 2 */
#elif !defined(WOLFSSL_SP_NO_2048)
        "2048\n",                                                        /* 2 */
#else
        "0\n",                                                           /* 2 */
#endif
#elif defined(USE_FAST_MATH)
#else
        "無限\n",                                                        /* 2 */
#endif
        "-? <num>    ヘルプ, 使い方を表示\n"
                            "            0: 英語、 1: 日本語\n",         /* 3 */
        "-h <host>   接続先ホスト, 既定値",                              /* 4 */
        "-p <num>    接続先ポート, 0は無効, 既定値",                     /* 5 */

#ifndef WOLFSSL_TLS13
        "-v <num>    SSL バージョン [0-3], SSLv3(0) - TLS1.2(3)),"
                                                              " 既定値", /* 6 */
        "-V          有効な ssl バージョン番号を出力, SSLv3(0) -"
                                                 " TLS1.2(3)\n",         /* 7 */
#else
        "-v <num>    SSL バージョン [0-4], SSLv3(0) - TLS1.3(4)),"
                                                    " 既定値",           /* 6 */
        "-V          有効な ssl バージョン番号を出力, SSLv3(0) -"
                                                 " TLS1.3(4)\n",         /* 7 */
#endif
        "-l <str>    暗号スイートリスト (区切り文字 :)\n",               /* 8 */
        "-c <file>   証明書ファイル,  既定値",                           /* 9 */
        "-k <file>   鍵ファイル,      既定値",                          /* 10 */
        "-A <file>   認証局ファイル,  既定値",                          /* 11 */
#ifndef NO_DH
        "-Z <num>    最小 DH 鍵 ビット, 既定値",                        /* 12 */
#endif
        "-b <num>    ベンチマーク <num> 接続及び結果出力する\n",        /* 13 */
#ifdef HAVE_ALPN
        "-L <str>    アプリケーション層プロトコルネゴシエーションを行う"
                                                 " ({C,F}:<list>)\n",   /* 14 */
#endif
        "-B <num>    <num> バイトを用いてのベンチマーク・スループット測定"
                                                  "と結果を出力する\n", /* 15 */
        "-s          事前共有鍵を使用する\n",                           /* 16 */
        "-d          ピア確認を無効とする\n",                           /* 17 */
        "-D          日付エラー用コールバック例の上書きを行う\n",       /* 18 */
        "-e          利用可能な全ての暗号スイートをリスト, \n",         /* 19 */
        "-g          サーバーへ HTTP GET を送信\n",                     /* 20 */
        "-u          UDP DTLSを使用する。-v 2 を追加指定すると"
               " DTLSv1, -v 3 を追加指定すると DTLSv1.2 (既定値)\n",    /* 21 */
#ifdef WOLFSSL_SCTP
        "-G          SCTP DTLSを使用する。-v 2 を追加指定すると"
                " DTLSv1, -v 3 を追加指定すると DTLSv1.2 (既定値)\n",   /* 22 */
#endif
        "-m          証明書内のドメイン名一致を確認する\n",             /* 23 */
        "-N          ノンブロッキング・ソケットを使用する\n",           /* 24 */
#ifndef NO_SESSION_CACHE
        "-r          セッションを継続する\n",                           /* 25 */
#endif
        "-w          双方向シャットダウンを待つ\n",                     /* 26 */
        "-M <prot>   STARTTLSを使用する, <prot>プロトコル(smtp)を"
                                              "使用する\n",             /* 27 */
#ifdef HAVE_SECURE_RENEGOTIATION
        "-R          セキュアな再ネゴシエーションを許可する\n",         /* 28 */
        "-i          クライアント主導のネゴシエーションを強制する\n",   /* 29 */
#endif
        "-f          より少ないパケット/グループメッセージを使用する\n",/* 30 */
        "-x          クライアントの証明書/鍵のロードを無効する\n",      /* 31 */
        "-X          外部テスト・ケースにより動作する\n",               /* 32 */
        "-j          コールバック・オーバーライドの検証を使用する\n",   /* 33 */
#ifdef SHOW_SIZES
        "-z          構造体のサイズを表示する\n",                       /* 34 */
#endif
#ifdef HAVE_SNI
        "-S <str>    ホスト名表示を使用する\n",                         /* 35 */
#endif
#ifdef HAVE_MAX_FRAGMENT
        "-F <num>    最大フラグメント長[1-6]を設定する\n",              /* 36 */
#endif
#ifdef HAVE_TRUNCATED_HMAC
        "-T          Truncated HMACを使用する\n",                       /* 37 */
#endif
#ifdef HAVE_EXTENDED_MASTER
        "-n          マスターシークレット拡張を無効にする\n",           /* 38 */
#endif
#ifdef HAVE_OCSP
        "-o          OCSPルックアップをピア証明書で実施する\n",         /* 39 */
        "-O <url>    OCSPルックアップを、<url>を使用し"
                                   "応答者として実施する\n",            /* 40 */
#endif
#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
 || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
        "-W <num>    OCSP Staplingを使用する"
                                         " (1 v1, 2 v2, 3 v2 multi)\n", /* 41 */
#endif
#if defined(ATOMIC_USER) && !defined(WOLFSSL_AEAD_ONLY)
        "-U          アトミック・ユーザー記録の"
                                           "コールバックを利用する\n",  /* 42 */
#endif
#ifdef HAVE_PK_CALLBACKS
        "-P          公開鍵コールバック\n",                             /* 43 */
#endif
#ifdef HAVE_ANON
        "-a          匿名クライアント\n",                               /* 44 */
#endif
#ifdef HAVE_CRL
        "-C          CRLを無効\n",                                      /* 45 */
#endif
#ifdef WOLFSSL_TRUST_PEER_CERT
        "-E <file>   信頼出来るピアの証明書ロードの為のパス\n",         /* 46 */
#endif
#ifdef HAVE_WNR
        "-q <file>   Whitewood コンフィグファイル,      既定値\n",      /* 47 */
#endif
        "-H <arg>    内部テスト"
            " [defCipherList, exitWithRet, verifyFail, useSupCurve,\n", /* 48 */
        "                            loadSSL, disallowETM]\n",          /* 49 */
#ifdef WOLFSSL_TLS13
        "-J          HelloRetryRequestをKEのグループ選択に使用する\n",  /* 50 */
        "-K          鍵交換にPSKを使用、(EC)DHEは使用しない\n",         /* 51 */
        "-I          データ送信前に、鍵とIVを更新する\n",               /* 52 */
#ifndef NO_DH
        "-y          FFDHE名前付きグループとの鍵共有のみ\n",            /* 53 */
#endif
#ifdef HAVE_ECC
        "-Y          ECC名前付きグループとの鍵共有のみ\n",              /* 54 */
#endif
#endif /* WOLFSSL_TLS13 */
#ifdef HAVE_CURVE25519
        "-t          X25519を鍵交換に使用する\n",                       /* 55 */
#endif
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
        "-Q          ポストハンドシェークの証明要求をサポートする\n",   /* 56 */
#endif
#ifdef WOLFSSL_EARLY_DATA
        "-0          Early data をサーバーへ送信する"
                            "（0-RTTハンドシェイク）\n",                /* 57 */
#endif
#ifdef WOLFSSL_MULTICAST
        "-3 <grpid>  マルチキャスト, grpid < 256\n",                    /* 58 */
#endif
        "-1 <num>    指定された言語で結果を表示します。\n"
                                   "            0: 英語、 1: 日本語\n", /* 59 */
#if !defined(NO_DH) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST) && !defined(WOLFSSL_OLD_PRIME_CHECK)
        "-2          DHプライム番号チェックを無効にする\n",             /* 60 */
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
        "-4          再交渉に再開を使用\n",                             /* 61 */
#endif
#ifdef HAVE_TRUSTED_CA
        "-5          信頼できる認証局の鍵表示を使用する\n",             /* 62 */
#endif
#ifdef HAVE_CURVE448
        "-8          Use X448 for key exchange\n",                      /* 65 */
#endif
        NULL,
    },
#endif

};

static void Usage(void)
{
    int msgid = 0;
    const char** msg = client_usage_msg[lng_index];

    printf("%s%s%s", "wolfSSL client ",    LIBWOLFSSL_VERSION_STRING,
           msg[msgid]);

    /* print out so that scripts can know what the max supported key size is */
    printf("%s", msg[++msgid]);
#ifdef NO_RSA
    printf("%s", msg[++msgid]);
#elif defined(WOLFSSL_SP_MATH) /* case of SP math only */
    #ifndef WOLFSSL_SP_NO_3072
        printf("%s", msg[++msgid]);
    #elif !defined(WOLFSSL_SP_NO_2048)
        printf("%s", msg[++msgid]);
    #else
        printf("%s", msg[++msgid]);
    #endif
#elif defined(USE_FAST_MATH)
    printf("%d\n", FP_MAX_BITS/2);
#else
    /* normal math has unlimited max size */
    printf("%s", msg[++msgid]);
#endif

    printf("%s", msg[++msgid]); /* ? */
    printf("%s %s\n", msg[++msgid], wolfSSLIP);   /* -h */
    printf("%s %d\n", msg[++msgid], wolfSSLPort); /* -p */
#ifndef WOLFSSL_TLS13
    printf("%s %d\n", msg[++msgid], CLIENT_DEFAULT_VERSION); /* -v */
    printf("%s", msg[++msgid]); /* -V */
#else
    printf("%s %d\n", msg[++msgid], CLIENT_DEFAULT_VERSION); /* -v */
    printf("%s", msg[++msgid]);                              /* -V */
#endif
    printf("%s", msg[++msgid]); /* -l */
    printf("%s %s\n", msg[++msgid], cliCertFile); /* -c */
    printf("%s %s\n", msg[++msgid], cliKeyFile);  /* -k */
    printf("%s %s\n", msg[++msgid], caCertFile);  /* -A */
#ifndef NO_DH
    printf("%s %d\n", msg[++msgid], DEFAULT_MIN_DHKEY_BITS);
#endif
    printf("%s", msg[++msgid]); /* -b */
#ifdef HAVE_ALPN
    printf("%s", msg[++msgid]); /* -L <str> */
#endif
    printf("%s", msg[++msgid]); /* -B <num> */
    printf("%s", msg[++msgid]); /* -s */
    printf("%s", msg[++msgid]); /* -d */
    printf("%s", msg[++msgid]); /* -D */
    printf("%s", msg[++msgid]); /* -e */
    printf("%s", msg[++msgid]); /* -g */
    printf("%s", msg[++msgid]); /* -u */
#ifdef WOLFSSL_SCTP
    printf("%s", msg[++msgid]); /* -G */
#endif
    printf("%s", msg[++msgid]); /* -m */
    printf("%s", msg[++msgid]); /* -N */
#ifndef NO_SESSION_CACHE
    printf("%s", msg[++msgid]); /* -r */
#endif
    printf("%s", msg[++msgid]); /* -w */
    printf("%s", msg[++msgid]); /* -M */
#ifdef HAVE_SECURE_RENEGOTIATION
    printf("%s", msg[++msgid]); /* -R */
    printf("%s", msg[++msgid]); /* -i */
#endif
    printf("%s", msg[++msgid]); /* -f */
    printf("%s", msg[++msgid]); /* -x */
    printf("%s", msg[++msgid]); /* -X */
    printf("%s", msg[++msgid]); /* -j */
#ifdef SHOW_SIZES
    printf("%s", msg[++msgid]); /* -z */
#endif
#ifdef HAVE_SNI
    printf("%s", msg[++msgid]); /* -S */
#endif
#ifdef HAVE_MAX_FRAGMENT
    printf("%s", msg[++msgid]); /* -F */
#endif
#ifdef HAVE_TRUNCATED_HMAC
    printf("%s", msg[++msgid]); /* -T */
#endif
#ifdef HAVE_EXTENDED_MASTER
    printf("%s", msg[++msgid]); /* -n */
#endif
#ifdef HAVE_OCSP
    printf("%s", msg[++msgid]); /* -o */
    printf("%s", msg[++msgid]); /* -O */
#endif
#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
 || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
    printf("%s", msg[++msgid]); /* -W */
#endif
#if defined(ATOMIC_USER) && !defined(WOLFSSL_AEAD_ONLY)
    printf("%s", msg[++msgid]); /* -U */
#endif
#ifdef HAVE_PK_CALLBACKS
    printf("%s", msg[++msgid]); /* -P */
#endif
#ifdef HAVE_ANON
    printf("%s", msg[++msgid]); /* -a */
#endif
#ifdef HAVE_CRL
    printf("%s", msg[++msgid]); /* -C */
#endif
#ifdef WOLFSSL_TRUST_PEER_CERT
    printf("%s", msg[++msgid]); /* -E */
#endif
#ifdef HAVE_WNR
    printf("%s %s\n", msg[++msgid], wnrConfig); /* -q */
#endif
    printf("%s", msg[++msgid]);                /* -H  */
    printf("%s", msg[++msgid]);                /* more -H options  */
#ifdef WOLFSSL_TLS13
    printf("%s", msg[++msgid]); /* -J */
    printf("%s", msg[++msgid]); /* -K */
    printf("%s", msg[++msgid]); /* -I */
#ifndef NO_DH
    printf("%s", msg[++msgid]); /* -y */
#endif
#ifdef HAVE_ECC
    printf("%s", msg[++msgid]); /* -Y */
#endif
#endif /* WOLFSSL_TLS13 */
#ifdef HAVE_CURVE25519
    printf("%s", msg[++msgid]); /* -t */
#endif
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
    printf("%s", msg[++msgid]); /* -Q */
#endif
#ifdef WOLFSSL_EARLY_DATA
    printf("%s", msg[++msgid]); /* -0 */
#endif
#ifdef WOLFSSL_MULTICAST
    printf("%s", msg[++msgid]); /* -3 */
#endif
    printf("%s", msg[++msgid]);  /* -1 */
#if !defined(NO_DH) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST) && !defined(WOLFSSL_OLD_PRIME_CHECK)
    printf("%s", msg[++msgid]);  /* -2 */
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
    printf("%s", msg[++msgid]);  /* -4 */
#endif
#ifdef HAVE_TRUSTED_CA
    printf("%s", msg[++msgid]);  /* -5 */
#endif
#ifdef HAVE_CURVE448
    printf("%s", msg[++msgid]); /* -8 */
#endif
}

THREAD_RETURN WOLFSSL_THREAD client_test(void* args)
{
    SOCKET_T sockfd = WOLFSSL_SOCKET_INVALID;

    wolfSSL_method_func method = NULL;
    WOLFSSL_CTX*     ctx     = 0;
    WOLFSSL*         ssl     = 0;

    WOLFSSL*         sslResume = 0;
    WOLFSSL_SESSION* session = 0;
    byte*            flatSession = NULL;
    int              flatSessionSz = 0;

#ifndef WOLFSSL_ALT_TEST_STRINGS
    char msg[32] = "hello wolfssl!";   /* GET may make bigger */
    char resumeMsg[32] = "resuming wolfssl!";
#else
    char msg[32] = "hello wolfssl!\n";
    char resumeMsg[32] = "resuming wolfssl!\n";
#endif

    char reply[128];
    int  msgSz = (int)XSTRLEN(msg);
    int  resumeSz = (int)XSTRLEN(resumeMsg);

    word16 port   = wolfSSLPort;
    char* host   = (char*)wolfSSLIP;
    const char* domain = "localhost";  /* can't default to www.wolfssl.com
                                          because can't tell if we're really
                                          going there to detect old chacha-poly
                                       */
#ifndef WOLFSSL_VXWORKS
    int    ch;
#endif
    int    version = CLIENT_INVALID_VERSION;
    int    usePsk   = 0;
    int    useAnon  = 0;
    int    sendGET  = 0;
    int    benchmark = 0;
    int    block = TEST_BUFFER_SIZE;
    size_t throughput = 0;
    int    doDTLS    = 0;
    int    dtlsUDP   = 0;
    int    dtlsSCTP  = 0;
    int    doMcast   = 0;
    int    matchName = 0;
    int    doPeerCheck = 1;
    int    nonBlocking = 0;
    int    resumeSession = 0;
    int    wc_shutdown   = 0;
    int    disableCRL    = 0;
    int    externalTest  = 0;
    int    ret;
    int    err           = 0;
    int    scr           = 0;    /* allow secure renegotiation */
    int    forceScr      = 0;    /* force client initiaed scr */
    int    resumeScr     = 0;    /* use resumption for renegotiation */
#ifndef WOLFSSL_NO_CLIENT_AUTH
    int    useClientCert = 1;
#else
    int    useClientCert = 0;
#endif
    int    fewerPackets  = 0;
    int    atomicUser    = 0;
#ifdef HAVE_PK_CALLBACKS
    int    pkCallbacks   = 0;
    PkCbInfo pkCbInfo;
#endif
    int    overrideDateErrors = 0;
    int    minDhKeyBits  = DEFAULT_MIN_DHKEY_BITS;
    char*  alpnList = NULL;
    unsigned char alpn_opt = 0;
    char*  cipherList = NULL;
    int    useDefCipherList = 0;
    const char* verifyCert;
    const char* ourCert;
    const char* ourKey;

    int   doSTARTTLS    = 0;
    char* starttlsProt = NULL;
    int   useVerifyCb = 0;
    int   useSupCurve = 0;

#ifdef WOLFSSL_TRUST_PEER_CERT
    const char* trustCert  = NULL;
#endif

#ifdef HAVE_SNI
    char*  sniHostName = NULL;
#endif
#ifdef HAVE_TRUSTED_CA
    int trustedCaKeyId = 0;
#endif
#ifdef HAVE_MAX_FRAGMENT
    byte maxFragment = 0;
#endif
#ifdef HAVE_TRUNCATED_HMAC
    byte truncatedHMAC = 0;
#endif
#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
 || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
    byte statusRequest = 0;
#endif
#ifdef HAVE_EXTENDED_MASTER
    byte disableExtMasterSecret = 0;
#endif
    int helloRetry = 0;
    int onlyKeyShare = 0;
#ifdef WOLFSSL_TLS13
    int noPskDheKe = 0;
    int postHandAuth = 0;
#endif
    int updateKeysIVs = 0;
    int earlyData = 0;
#ifdef WOLFSSL_MULTICAST
    byte mcastID = 0;
#endif
#if !defined(NO_DH) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST) && !defined(WOLFSSL_OLD_PRIME_CHECK)
    int doDhKeyCheck = 1;
#endif

#ifdef HAVE_OCSP
    int    useOcsp  = 0;
    char*  ocspUrl  = NULL;
#endif
    int useX25519 = 0;
    int useX448 = 0;
    int exitWithRet = 0;
    int loadCertKeyIntoSSLObj = 0;

#ifdef HAVE_ENCRYPT_THEN_MAC
    int disallowETM = 0;
#endif

#ifdef HAVE_WNR
    const char* wnrConfigFile = wnrConfig;
#endif
    char buffer[WOLFSSL_MAX_ERROR_SZ];

    int     argc = ((func_args*)args)->argc;
    char**  argv = ((func_args*)args)->argv;


#ifdef WOLFSSL_STATIC_MEMORY
    #if (defined(HAVE_ECC) && !defined(ALT_ECC_SIZE)) \
        || defined(SESSION_CERTS)
        /* big enough to handle most cases including session certs */
        byte memory[320000];
    #else
        byte memory[80000];
    #endif
    byte memoryIO[34500]; /* max for IO buffer (TLS packet can be 16k) */
    WOLFSSL_MEM_CONN_STATS ssl_stats;
    #ifdef DEBUG_WOLFSSL
        WOLFSSL_MEM_STATS mem_stats;
    #endif
    WOLFSSL_HEAP_HINT *heap = NULL;
#endif

    ((func_args*)args)->return_code = -1; /* error state */

#ifndef NO_RSA
    verifyCert = caCertFile;
    ourCert    = cliCertFile;
    ourKey     = cliKeyFile;
#else
    #ifdef HAVE_ECC
        verifyCert = caEccCertFile;
        ourCert    = cliEccCertFile;
        ourKey     = cliEccKeyFile;
    #elif defined(HAVE_ED25519)
        verifyCert = caEdCertFile;
        ourCert    = cliEdCertFile;
        ourKey     = cliEdKeyFile;
    #elif defined(HAVE_ED448)
        verifyCert = caEd448CertFile;
        ourCert    = cliEd448CertFile;
        ourKey     = cliEd448KeyFile;
    #else
        verifyCert = NULL;
        ourCert    = NULL;
        ourKey     = NULL;
    #endif
#endif

    (void)resumeSz;
    (void)session;
    (void)flatSession;
    (void)flatSessionSz;
    (void)sslResume;
    (void)atomicUser;
    (void)scr;
    (void)forceScr;
    (void)resumeScr;
    (void)ourKey;
    (void)ourCert;
    (void)verifyCert;
    (void)useClientCert;
    (void)overrideDateErrors;
    (void)disableCRL;
    (void)minDhKeyBits;
    (void)alpnList;
    (void)alpn_opt;
    (void)updateKeysIVs;
    (void)earlyData;
    (void)useX25519;
    (void)useX448;
    (void)helloRetry;
    (void)onlyKeyShare;
    (void)useSupCurve;
    (void)loadCertKeyIntoSSLObj;

    StackTrap();

#ifndef WOLFSSL_VXWORKS
    /* Not used: All used */
    while ((ch = mygetopt(argc, argv, "?:"
            "ab:c:defgh:ijk:l:mnop:q:rstuv:wxyz"
            "A:B:CDE:F:GH:IJKL:M:NO:PQRS:TUVW:XYZ:"
            "01:23:458")) != -1) {
        switch (ch) {
            case '?' :
                if(myoptarg!=NULL) {
                    lng_index = atoi(myoptarg);
                    if(lng_index<0||lng_index>1){
                        lng_index = 0;
                    }
                }
                Usage();
                XEXIT_T(EXIT_SUCCESS);

            case 'g' :
                sendGET = 1;
                break;

            case 'd' :
                doPeerCheck = 0;
                break;

            case 'e' :
                ShowCiphers();
                XEXIT_T(EXIT_SUCCESS);

            case 'D' :
                overrideDateErrors = 1;
                break;

            case 'C' :
                #ifdef HAVE_CRL
                    disableCRL = 1;
                #endif
                break;

            case 'u' :
                doDTLS = 1;
                dtlsUDP = 1;
                break;

            case 'G' :
            #ifdef WOLFSSL_SCTP
                doDTLS = 1;
                dtlsSCTP = 1;
            #endif
                break;

            case 's' :
                usePsk = 1;
                break;

            #ifdef WOLFSSL_TRUST_PEER_CERT
            case 'E' :
                trustCert = myoptarg;
                break;
            #endif

            case 'm' :
                matchName = 1;
                break;

            case 'x' :
                useClientCert = 0;
                break;

            case 'X' :
                externalTest = 1;
                break;

            case 'f' :
                fewerPackets = 1;
                break;

            case 'U' :
            #if defined(ATOMIC_USER) && !defined(WOLFSSL_AEAD_ONLY)
                atomicUser = 1;
            #endif
                break;

            case 'P' :
            #ifdef HAVE_PK_CALLBACKS
                pkCallbacks = 1;
            #endif
                break;

            case 'h' :
                host   = myoptarg;
                domain = myoptarg;
                break;

            case 'p' :
                port = (word16)atoi(myoptarg);
                #if !defined(NO_MAIN_DRIVER) || defined(USE_WINDOWS_API)
                    if (port == 0)
                        err_sys("port number cannot be 0");
                #endif
                break;

            case 'v' :
                if (myoptarg[0] == 'd') {
                    version = CLIENT_DOWNGRADE_VERSION;
                    break;
                }
            #if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EITHER_SIDE)
                else if (myoptarg[0] == 'e') {
                    version = EITHER_DOWNGRADE_VERSION;
                #ifndef NO_CERTS
                    loadCertKeyIntoSSLObj = 1;
                #endif
                    break;
                }
            #endif
                version = atoi(myoptarg);
                if (version < 0 || version > 4) {
                    Usage();
                    XEXIT_T(MY_EX_USAGE);
                }
                break;

            case 'V' :
                ShowVersions();
                XEXIT_T(EXIT_SUCCESS);

            case 'l' :
                cipherList = myoptarg;
                break;

            case 'H' :
                if (XSTRNCMP(myoptarg, "defCipherList", 13) == 0) {
                    printf("Using default cipher list for testing\n");
                    useDefCipherList = 1;
                }
                else if (XSTRNCMP(myoptarg, "exitWithRet", 11) == 0) {
                    printf("Skip exit() for testing\n");
                    exitWithRet = 1;
                }
                else if (XSTRNCMP(myoptarg, "verifyFail", 10) == 0) {
                    printf("Verify should fail\n");
                    myVerifyFail = 1;
                }
                else if (XSTRNCMP(myoptarg, "useSupCurve", 11) == 0) {
                    printf("Attempting to test use supported curve\n");
                #if defined(HAVE_ECC) && defined(HAVE_SUPPORTED_CURVES)
                    useSupCurve = 1;
                #else
                    printf("Supported curves not compiled in!\n");
                #endif
                }
                else if (XSTRNCMP(myoptarg, "loadSSL", 7) == 0) {
                    printf("Load cert/key into wolfSSL object\n");
                #ifndef NO_CERTS
                    loadCertKeyIntoSSLObj = 1;
                #else
                    printf("Certs turned off with NO_CERTS!\n");
                #endif
                }
                else if (XSTRNCMP(myoptarg, "disallowETM", 7) == 0) {
                    printf("Disallow Enrypt-Then-MAC\n");
                #ifdef HAVE_ENCRYPT_THEN_MAC
                    disallowETM = 1;
                #endif
                }
                else {
                    Usage();
                    XEXIT_T(MY_EX_USAGE);
                }
                break;

            case 'A' :
                verifyCert = myoptarg;
                break;

            case 'c' :
                ourCert = myoptarg;
                break;

            case 'k' :
                ourKey = myoptarg;
                break;

            case 'Z' :
                #ifndef NO_DH
                    minDhKeyBits = atoi(myoptarg);
                    if (minDhKeyBits <= 0 || minDhKeyBits > 16000) {
                        Usage();
                        XEXIT_T(MY_EX_USAGE);
                    }
                #endif
                break;

            case 'b' :
                benchmark = atoi(myoptarg);
                if (benchmark < 0 || benchmark > 1000000) {
                    Usage();
                    XEXIT_T(MY_EX_USAGE);
                }
                break;

            case 'B' :
                throughput = atol(myoptarg);
                for (; *myoptarg != '\0'; myoptarg++) {
                    if (*myoptarg == ',') {
                        block = atoi(myoptarg + 1);
                        break;
                    }
                }
                if (throughput == 0 || block <= 0) {
                    Usage();
                    XEXIT_T(MY_EX_USAGE);
                }
                break;

            case 'N' :
                nonBlocking = 1;
                break;

            case 'r' :
                resumeSession = 1;
                break;

            case 'w' :
                wc_shutdown = 1;
                break;

            case 'R' :
                #ifdef HAVE_SECURE_RENEGOTIATION
                    scr = 1;
                #endif
                break;

            case 'i' :
                #ifdef HAVE_SECURE_RENEGOTIATION
                    scr      = 1;
                    forceScr = 1;
                #endif
                break;

            case 'z' :
                #ifndef WOLFSSL_LEANPSK
                    wolfSSL_GetObjectSize();
                #endif
                break;

            case 'S' :
                if (XSTRNCMP(myoptarg, "check", 5) == 0) {
                #ifdef HAVE_SNI
                    printf("SNI is: ON\n");
                #else
                    printf("SNI is: OFF\n");
                #endif
                    XEXIT_T(EXIT_SUCCESS);
                }
                #ifdef HAVE_SNI
                    sniHostName = myoptarg;
                #endif
                break;

            case 'F' :
                #ifdef HAVE_MAX_FRAGMENT
                    maxFragment = atoi(myoptarg);
                    if (maxFragment < WOLFSSL_MFL_MIN ||
                                               maxFragment > WOLFSSL_MFL_MAX) {
                        Usage();
                        XEXIT_T(MY_EX_USAGE);
                    }
                #endif
                break;

            case 'T' :
                #ifdef HAVE_TRUNCATED_HMAC
                    truncatedHMAC = 1;
                #endif
                break;

            case 'n' :
                #ifdef HAVE_EXTENDED_MASTER
                    disableExtMasterSecret = 1;
                #endif
                break;

            case 'W' :
                #if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
                 || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
                    statusRequest = atoi(myoptarg);
                    if (statusRequest > OCSP_STAPLING_OPT_MAX) {
                        Usage();
                        XEXIT_T(MY_EX_USAGE);
                    }
                #endif
                break;

            case 'o' :
                #ifdef HAVE_OCSP
                    useOcsp = 1;
                #endif
                break;

            case 'O' :
                #ifdef HAVE_OCSP
                    useOcsp = 1;
                    ocspUrl = myoptarg;
                #endif
                break;

            case 'a' :
                #ifdef HAVE_ANON
                    useAnon = 1;
                #endif
                break;

            case 'L' :
                #ifdef HAVE_ALPN
                    alpnList = myoptarg;

                    if (alpnList[0] == 'C' && alpnList[1] == ':')
                        alpn_opt = WOLFSSL_ALPN_CONTINUE_ON_MISMATCH;
                    else if (alpnList[0] == 'F' && alpnList[1] == ':')
                        alpn_opt = WOLFSSL_ALPN_FAILED_ON_MISMATCH;
                    else {
                        Usage();
                        XEXIT_T(MY_EX_USAGE);
                    }

                    alpnList += 2;

                #endif
                break;

            case 'M' :
                doSTARTTLS = 1;
                starttlsProt = myoptarg;

                if (XSTRNCMP(starttlsProt, "smtp", 4) != 0) {
                    Usage();
                    XEXIT_T(MY_EX_USAGE);
                }

                break;

            case 'q' :
                #ifdef HAVE_WNR
                    wnrConfigFile = myoptarg;
                #endif
                break;

            case 'J' :
                #ifdef WOLFSSL_TLS13
                    helloRetry = 1;
                #endif
                break;

            case 'K' :
                #ifdef WOLFSSL_TLS13
                    noPskDheKe = 1;
                #endif
                break;

            case 'I' :
                #ifdef WOLFSSL_TLS13
                    updateKeysIVs = 1;
                #endif
                break;

            case 'y' :
                #if defined(WOLFSSL_TLS13) && !defined(NO_DH)
                    onlyKeyShare = 1;
                #endif
                break;

            case 'Y' :
                #if defined(WOLFSSL_TLS13) && defined(HAVE_ECC)
                    onlyKeyShare = 2;
                #endif
                break;

            case 'j' :
                useVerifyCb = 1;
                break;

            case 't' :
                #ifdef HAVE_CURVE25519
                    useX25519 = 1;
                    #ifdef HAVE_ECC
                    useSupCurve = 1;
                        #ifdef WOLFSSL_TLS13
                        onlyKeyShare = 2;
                        #endif
                    #endif
                #endif
                break;

            case 'Q' :
                #if defined(WOLFSSL_TLS13) && \
                                            defined(WOLFSSL_POST_HANDSHAKE_AUTH)
                    postHandAuth = 1;
                #endif
                break;

            case '0' :
            #ifdef WOLFSSL_EARLY_DATA
                earlyData = 1;
            #endif
                break;

            case '1' :
                lng_index = atoi(myoptarg);
                if(lng_index<0||lng_index>1){
                      lng_index = 0;
                }
                break;

            case '2' :
               #if !defined(NO_DH) && !defined(HAVE_FIPS) && \
                   !defined(HAVE_SELFTEST) && !defined(WOLFSSL_OLD_PRIME_CHECK)
                    doDhKeyCheck = 0;
                #endif
                break;

            case '3' :
                #ifdef WOLFSSL_MULTICAST
                    doMcast = 1;
                    mcastID = (byte)(atoi(myoptarg) & 0xFF);
                #endif
                break;

            case '4' :
                #ifdef HAVE_SECURE_RENEGOTIATION
                    scr       = 1;
                    forceScr  = 1;
                    resumeScr = 1;
                #endif
                break;

            case '5' :
            #ifdef HAVE_TRUSTED_CA
                trustedCaKeyId = 1;
            #endif /* HAVE_TRUSTED_CA */
                break;

            case '8' :
                #ifdef HAVE_CURVE448
                    useX448 = 1;
                    #ifdef HAVE_ECC
                    useSupCurve = 1;
                        #ifdef WOLFSSL_TLS13
                        onlyKeyShare = 2;
                        #endif
                    #endif
                #endif
                break;

            default:
                Usage();
                XEXIT_T(MY_EX_USAGE);
        }
    }

    myoptind = 0;      /* reset for test cases */
#endif /* !WOLFSSL_VXWORKS */

    if (externalTest) {
        /* detect build cases that wouldn't allow test against wolfssl.com */
        int done = 0;

        #ifdef NO_RSA
            done += 1; /* require RSA for external tests */
        #endif

        if (!XSTRNCMP(domain, "www.globalsign.com", 14)) {
        /* www.globalsign.com does not respond to ipv6 ocsp requests */
        #if defined(TEST_IPV6) && defined(HAVE_OCSP)
            done += 1;
        #endif

        /* www.globalsign.com has limited supported cipher suites */
        #if defined(NO_AES) && defined(HAVE_OCSP)
            done += 1;
        #endif

        /* www.globalsign.com only supports static RSA or ECDHE with AES */
        /* We cannot expect users to have on static RSA so test for ECC only
         * as some users will most likely be on 32-bit systems where ECC
         * is not enabled by default */
        #if defined(HAVE_OCSP) && !defined(HAVE_ECC)
            done += 1;
        #endif
        }

        #ifndef NO_PSK
        if (usePsk) {
            done += 1; /* don't perform exernal tests if PSK is enabled */
        }
        #endif

        #ifdef NO_SHA
            done += 1;  /* external cert chain most likely has SHA */
        #endif

        #if !defined(HAVE_ECC) && !defined(WOLFSSL_STATIC_RSA) \
            || ( defined(HAVE_ECC) && !defined(HAVE_SUPPORTED_CURVES) \
                  && !defined(WOLFSSL_STATIC_RSA) )
            /* google needs ECDHE+Supported Curves or static RSA */
            if (!XSTRNCMP(domain, "www.google.com", 14))
                done += 1;
        #endif

        #if !defined(HAVE_ECC) && !defined(WOLFSSL_STATIC_RSA)
            /* wolfssl needs ECDHE or static RSA */
            if (!XSTRNCMP(domain, "www.wolfssl.com", 15))
                done += 1;
        #endif

        #if !defined(WOLFSSL_SHA384)
            if (!XSTRNCMP(domain, "www.wolfssl.com", 15)) {
                /* wolfssl need sha384 for cert chain verify */
                done += 1;
            }
        #endif

        #if !defined(HAVE_AESGCM) && defined(NO_AES) && \
            !(defined(HAVE_CHACHA) && defined(HAVE_POLY1305))
            /* need at least one of these for external tests */
            done += 1;
        #endif

        #if defined(HAVE_QSH)
            /*currently google server rejects client hello with QSH extension.*/
            done += 1;
        #endif

        /* For the external test, if we disable AES, GoDaddy will reject the
         * connection. They only currently support AES suites, RC4 and 3DES
         * suites. With AES disabled we only offer PolyChacha suites. */
        #if defined(NO_AES) && !defined(HAVE_AESGCM)
            if (!XSTRNCMP(domain, "www.wolfssl.com", 15)) {
                done += 1;
            }
        #endif

        if (done) {
            printf("external test can't be run in this mode\n");

            ((func_args*)args)->return_code = 0;
            XEXIT_T(EXIT_SUCCESS);
        }
    }

    /* sort out DTLS versus TLS versions */
    if (version == CLIENT_INVALID_VERSION) {
        if (doDTLS)
            version = CLIENT_DTLS_DEFAULT_VERSION;
        else
            version = CLIENT_DEFAULT_VERSION;
    }
    else {
        if (doDTLS) {
            if (version == 3)
                version = -2;
        #if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EITHER_SIDE)
            else if (version == EITHER_DOWNGRADE_VERSION)
                version = -3;
        #endif
            else
                version = -1;
        }
    }

#ifdef HAVE_WNR
    if (wc_InitNetRandom(wnrConfigFile, NULL, 5000) != 0)
        err_sys("can't load whitewood net random config file");
#endif

    switch (version) {
#ifndef NO_OLD_TLS
    #ifdef WOLFSSL_ALLOW_SSLV3
        case 0:
            method = wolfSSLv3_client_method_ex;
            break;
    #endif

    #ifndef NO_TLS
        #ifdef WOLFSSL_ALLOW_TLSV10
        case 1:
            method = wolfTLSv1_client_method_ex;
            break;
        #endif

        case 2:
            method = wolfTLSv1_1_client_method_ex;
            break;
    #endif /* !NO_TLS */
#endif /* !NO_OLD_TLS */

#ifndef NO_TLS
    #ifndef WOLFSSL_NO_TLS12
        case 3:
            method = wolfTLSv1_2_client_method_ex;
            break;
    #endif

    #ifdef WOLFSSL_TLS13
        case 4:
            method = wolfTLSv1_3_client_method_ex;
            break;
    #endif

        case CLIENT_DOWNGRADE_VERSION:
            method = wolfSSLv23_client_method_ex;
            break;
    #if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EITHER_SIDE)
        case EITHER_DOWNGRADE_VERSION:
            method = wolfSSLv23_method_ex;
            break;
    #endif
#endif /* NO_TLS */

#ifdef WOLFSSL_DTLS
        #ifndef NO_OLD_TLS
        case -1:
            method = wolfDTLSv1_client_method_ex;
            break;
        #endif

    #ifndef WOLFSSL_NO_TLS12
        case -2:
            method = wolfDTLSv1_2_client_method_ex;
            break;
    #endif
    #if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EITHER_SIDE)
        case -3:
            method = wolfDTLSv1_2_method_ex;
            break;
    #endif
#endif

        default:
            err_sys("Bad SSL version");
            break;
    }

    if (method == NULL)
        err_sys("unable to get method");


#ifdef WOLFSSL_STATIC_MEMORY
    #ifdef DEBUG_WOLFSSL
    /* print off helper buffer sizes for use with static memory
     * printing to stderr in case of debug mode turned on */
    fprintf(stderr, "static memory management size = %d\n",
            wolfSSL_MemoryPaddingSz());
    fprintf(stderr, "calculated optimum general buffer size = %d\n",
            wolfSSL_StaticBufferSz(memory, sizeof(memory), 0));
    fprintf(stderr, "calculated optimum IO buffer size      = %d\n",
            wolfSSL_StaticBufferSz(memoryIO, sizeof(memoryIO),
                                                  WOLFMEM_IO_POOL_FIXED));
    #endif /* DEBUG_WOLFSSL */

    if (wc_LoadStaticMemory(&heap, memory, sizeof(memory), WOLFMEM_GENERAL, 1)
            != 0) {
        err_sys("unable to load static memory");
    }

    ctx = wolfSSL_CTX_new_ex(method(heap), heap);
    if (ctx == NULL)
        err_sys("unable to get ctx");

    if (wolfSSL_CTX_load_static_memory(&ctx, NULL, memoryIO, sizeof(memoryIO),
           WOLFMEM_IO_POOL_FIXED | WOLFMEM_TRACK_STATS, 1) != WOLFSSL_SUCCESS) {
        err_sys("unable to load static memory");
    }
#else
    ctx = wolfSSL_CTX_new(method(NULL));
    if (ctx == NULL)
        err_sys("unable to get ctx");
#endif

#ifdef SINGLE_THREADED
    if (wolfSSL_CTX_new_rng(ctx) != WOLFSSL_SUCCESS) {
        wolfSSL_CTX_free(ctx); ctx = NULL;
        err_sys("Single Threaded new rng at CTX failed");
    }
#endif

    if (cipherList && !useDefCipherList) {
        if (wolfSSL_CTX_set_cipher_list(ctx, cipherList) != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("client can't set cipher list 1");
        }
    }

#ifdef WOLFSSL_LEANPSK
    if (!usePsk) {
        usePsk = 1;
    }
#endif

#if defined(NO_RSA) && !defined(HAVE_ECC) && !defined(HAVE_ED25519) && \
                                                            !defined(HAVE_ED448)
    if (!usePsk) {
        usePsk = 1;
    }
#endif

    if (fewerPackets)
        wolfSSL_CTX_set_group_messages(ctx);

#ifndef NO_DH
    if (wolfSSL_CTX_SetMinDhKey_Sz(ctx, (word16)minDhKeyBits)
            != WOLFSSL_SUCCESS) {
        err_sys("Error setting minimum DH key size");
    }
#endif

    if (usePsk) {
#ifndef NO_PSK
        wolfSSL_CTX_set_psk_client_callback(ctx, my_psk_client_cb);
    #ifdef WOLFSSL_TLS13
        wolfSSL_CTX_set_psk_client_tls13_callback(ctx, my_psk_client_tls13_cb);
    #endif
        if (cipherList == NULL) {
            const char *defaultCipherList;
        #if defined(HAVE_AESGCM) && !defined(NO_DH)
            #ifdef WOLFSSL_TLS13
                defaultCipherList = "DHE-PSK-AES128-GCM-SHA256:"
                                    "TLS13-AES128-GCM-SHA256";
            #else
                defaultCipherList = "DHE-PSK-AES128-GCM-SHA256";
            #endif
        #elif defined(HAVE_NULL_CIPHER)
                defaultCipherList = "PSK-NULL-SHA256";
        #else
                defaultCipherList = "PSK-AES128-CBC-SHA256";
        #endif
            if (wolfSSL_CTX_set_cipher_list(ctx,defaultCipherList)
                                                            !=WOLFSSL_SUCCESS) {
                wolfSSL_CTX_free(ctx); ctx = NULL;
                err_sys("client can't set cipher list 2");
            }
        }
#endif
        if (useClientCert) {
            useClientCert = 0;
        }
    }

    if (useAnon) {
#ifdef HAVE_ANON
        if (cipherList == NULL || (cipherList && useDefCipherList)) {
            const char* defaultCipherList;
            wolfSSL_CTX_allow_anon_cipher(ctx);
            defaultCipherList = "ADH-AES256-GCM-SHA384:"
                                "ADH-AES128-SHA";
            if (wolfSSL_CTX_set_cipher_list(ctx,defaultCipherList)
                                                           != WOLFSSL_SUCCESS) {
                wolfSSL_CTX_free(ctx); ctx = NULL;
                err_sys("client can't set cipher list 4");
            }
        }
#endif
        if (useClientCert) {
            useClientCert = 0;
        }
    }

#ifdef WOLFSSL_SCTP
    if (dtlsSCTP)
        wolfSSL_CTX_dtls_set_sctp(ctx);
#endif

#ifdef WOLFSSL_ENCRYPTED_KEYS
    wolfSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#if defined(WOLFSSL_SNIFFER)
    if (cipherList == NULL) {
        /* don't use EDH, can't sniff tmp keys */
        if (wolfSSL_CTX_set_cipher_list(ctx, "AES128-SHA") != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("client can't set cipher list 3");
        }
    }
#endif

#ifdef HAVE_OCSP
    if (useOcsp) {
    #ifdef HAVE_IO_TIMEOUT
        wolfIO_SetTimeout(DEFAULT_TIMEOUT_SEC);
    #endif

        if (ocspUrl != NULL) {
            wolfSSL_CTX_SetOCSP_OverrideURL(ctx, ocspUrl);
            wolfSSL_CTX_EnableOCSP(ctx, WOLFSSL_OCSP_NO_NONCE
                                                    | WOLFSSL_OCSP_URL_OVERRIDE);
        }
        else {
            wolfSSL_CTX_EnableOCSP(ctx, WOLFSSL_OCSP_CHECKALL);
        }

    #ifdef WOLFSSL_NONBLOCK_OCSP
        wolfSSL_CTX_SetOCSP_Cb(ctx, OCSPIOCb, OCSPRespFreeCb, NULL);
    #endif
    }
#endif

#ifdef USER_CA_CB
    wolfSSL_CTX_SetCACb(ctx, CaCb);
#endif

#ifdef HAVE_EXT_CACHE
    wolfSSL_CTX_sess_set_get_cb(ctx, mySessGetCb);
    wolfSSL_CTX_sess_set_new_cb(ctx, mySessNewCb);
    wolfSSL_CTX_sess_set_remove_cb(ctx, mySessRemCb);
#endif

#ifndef NO_CERTS
    if (useClientCert && !loadCertKeyIntoSSLObj){
    #ifndef TEST_LOAD_BUFFER
        if (wolfSSL_CTX_use_certificate_chain_file(ctx, ourCert)
                                                           != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't load client cert file, check file and run from"
                    " wolfSSL home dir");
        }
    #else
        load_buffer(ctx, ourCert, WOLFSSL_CERT_CHAIN);
    #endif
    }

    #ifdef HAVE_PK_CALLBACKS
        pkCbInfo.ourKey = ourKey;
    #endif
    if (useClientCert && !loadCertKeyIntoSSLObj
    #if defined(HAVE_PK_CALLBACKS) && defined(TEST_PK_PRIVKEY)
        && !pkCallbacks
    #endif
    ) {
    #ifndef TEST_LOAD_BUFFER
        if (wolfSSL_CTX_use_PrivateKey_file(ctx, ourKey, WOLFSSL_FILETYPE_PEM)
                                         != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't load client private key file, check file and run "
                    "from wolfSSL home dir");
        }
    #else
        load_buffer(ctx, ourKey, WOLFSSL_KEY);
    #endif
    }

    if (!usePsk && !useAnon && !useVerifyCb && !myVerifyFail) {
    #ifndef TEST_LOAD_BUFFER
        unsigned int verify_flags = 0;
    #ifdef TEST_BEFORE_DATE
        verify_flags |= WOLFSSL_LOAD_FLAG_DATE_ERR_OKAY;
    #endif
        if (wolfSSL_CTX_load_verify_locations_ex(ctx, verifyCert, 0, verify_flags)
                                                           != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't load ca file, Please run from wolfSSL home dir");
        }
    #else
        load_buffer(ctx, verifyCert, WOLFSSL_CA);
    #endif  /* !NO_FILESYSTEM */

    #ifdef HAVE_ECC
        /* load ecc verify too, echoserver uses it by default w/ ecc */
        #ifndef TEST_LOAD_BUFFER
        if (wolfSSL_CTX_load_verify_locations_ex(ctx, eccCertFile, 0, verify_flags)
                                                           != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't load ecc ca file, Please run from wolfSSL home dir");
        }
        #else
        load_buffer(ctx, eccCertFile, WOLFSSL_CA);
        #endif /* !TEST_LOAD_BUFFER */
    #endif /* HAVE_ECC */
    #if defined(WOLFSSL_TRUST_PEER_CERT) && !defined(NO_FILESYSTEM)
        if (trustCert) {
            if ((ret = wolfSSL_CTX_trust_peer_cert(ctx, trustCert,
                                    WOLFSSL_FILETYPE_PEM)) != WOLFSSL_SUCCESS) {
                wolfSSL_CTX_free(ctx); ctx = NULL;
                err_sys("can't load trusted peer cert file");
            }
        }
    #endif /* WOLFSSL_TRUST_PEER_CERT && !NO_FILESYSTEM */
    }
    if (useVerifyCb || myVerifyFail)
        wolfSSL_CTX_set_verify(ctx, WOLFSSL_VERIFY_PEER, myVerify);
    else if (!usePsk && !useAnon && doPeerCheck == 0)
        wolfSSL_CTX_set_verify(ctx, WOLFSSL_VERIFY_NONE, 0);
    else if (!usePsk && !useAnon && overrideDateErrors == 1)
        wolfSSL_CTX_set_verify(ctx, WOLFSSL_VERIFY_PEER, myDateCb);
#endif /* !NO_CERTS */

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfAsync_DevOpen(&devId);
    if (ret < 0) {
        printf("Async device open failed\nRunning without async\n");
    }
    wolfSSL_CTX_UseAsync(ctx, devId);
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifdef HAVE_SNI
    if (sniHostName) {
        if (wolfSSL_CTX_UseSNI(ctx, 0, sniHostName,
                    (word16) XSTRLEN(sniHostName)) != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("UseSNI failed");
        }
    }
#endif
#ifdef HAVE_MAX_FRAGMENT
    if (maxFragment)
        if (wolfSSL_CTX_UseMaxFragment(ctx, maxFragment) != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("UseMaxFragment failed");
        }
#endif
#ifdef HAVE_TRUNCATED_HMAC
    if (truncatedHMAC)
        if (wolfSSL_CTX_UseTruncatedHMAC(ctx) != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("UseTruncatedHMAC failed");
        }
#endif
#ifdef HAVE_SESSION_TICKET
    if (wolfSSL_CTX_UseSessionTicket(ctx) != WOLFSSL_SUCCESS) {
        wolfSSL_CTX_free(ctx); ctx = NULL;
        err_sys("UseSessionTicket failed");
    }
#endif
#ifdef HAVE_EXTENDED_MASTER
    if (disableExtMasterSecret)
        if (wolfSSL_CTX_DisableExtendedMasterSecret(ctx) != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("DisableExtendedMasterSecret failed");
        }
#endif
#if defined(HAVE_SUPPORTED_CURVES)
    #if defined(HAVE_CURVE25519)
    if (useX25519) {
        if (wolfSSL_CTX_UseSupportedCurve(ctx, WOLFSSL_ECC_X25519)
                                                           != WOLFSSL_SUCCESS) {
            err_sys("unable to support X25519");
        }
    }
    #endif /* HAVE_CURVE25519 */
    #if defined(HAVE_CURVE448)
    if (useX448) {
        if (wolfSSL_CTX_UseSupportedCurve(ctx, WOLFSSL_ECC_X448)
                                                           != WOLFSSL_SUCCESS) {
            err_sys("unable to support X448");
        }
    }
    #endif /* HAVE_CURVE448 */
    #ifdef HAVE_ECC
    if (useSupCurve) {
        #if !defined(NO_ECC_SECP) && \
            (defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES))
        if (wolfSSL_CTX_UseSupportedCurve(ctx, WOLFSSL_ECC_SECP384R1)
                                                           != WOLFSSL_SUCCESS) {
            err_sys("unable to support secp384r1");
        }
        #endif
        #if !defined(NO_ECC_SECP) && \
            (!defined(NO_ECC256) || defined(HAVE_ALL_CURVES))
        if (wolfSSL_CTX_UseSupportedCurve(ctx, WOLFSSL_ECC_SECP256R1)
                                                           != WOLFSSL_SUCCESS) {
            err_sys("unable to support secp256r1");
        }
        #endif
    }
    #endif /* HAVE_ECC */
    #ifdef HAVE_FFDHE_2048
    if (useSupCurve) {
        if (wolfSSL_CTX_UseSupportedCurve(ctx, WOLFSSL_FFDHE_2048)
                                                           != WOLFSSL_SUCCESS) {
            err_sys("unable to support FFDHE 2048");
        }
    }
    #endif
#endif /* HAVE_SUPPORTED_CURVES */

#ifdef WOLFSSL_TLS13
    if (noPskDheKe)
        wolfSSL_CTX_no_dhe_psk(ctx);
#endif
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
    if (postHandAuth)
        wolfSSL_CTX_allow_post_handshake_auth(ctx);
#endif

    if (benchmark) {
        ((func_args*)args)->return_code =
            ClientBenchmarkConnections(ctx, host, port, dtlsUDP, dtlsSCTP,
                                       benchmark, resumeSession, useX25519,
                                       useX448, helloRetry, onlyKeyShare,
                                       version, earlyData);
        wolfSSL_CTX_free(ctx); ctx = NULL;
        XEXIT_T(EXIT_SUCCESS);
    }

    if (throughput) {
        ((func_args*)args)->return_code =
            ClientBenchmarkThroughput(ctx, host, port, dtlsUDP, dtlsSCTP,
                                      block, throughput, useX25519, useX448);
        wolfSSL_CTX_free(ctx); ctx = NULL;
        XEXIT_T(EXIT_SUCCESS);
    }

    #if defined(WOLFSSL_MDK_ARM)
    wolfSSL_CTX_set_verify(ctx, WOLFSSL_VERIFY_NONE, 0);
    #endif

    #if defined(OPENSSL_EXTRA)
    if (wolfSSL_CTX_get_read_ahead(ctx) != 0) {
        wolfSSL_CTX_free(ctx); ctx = NULL;
        err_sys("bad read ahead default value");
    }
    if (wolfSSL_CTX_set_read_ahead(ctx, 1) != WOLFSSL_SUCCESS) {
        wolfSSL_CTX_free(ctx); ctx = NULL;
        err_sys("error setting read ahead value");
    }
    #endif

#if defined(WOLFSSL_STATIC_MEMORY) && defined(DEBUG_WOLFSSL)
        fprintf(stderr, "Before creating SSL\n");
        if (wolfSSL_CTX_is_static_memory(ctx, &mem_stats) != 1)
            err_sys("ctx not using static memory");
        if (wolfSSL_PrintStats(&mem_stats) != 1) /* function in test.h */
            err_sys("error printing out memory stats");
#endif

    if (doMcast) {
#ifdef WOLFSSL_MULTICAST
        wolfSSL_CTX_mcast_set_member_id(ctx, mcastID);
        if (wolfSSL_CTX_set_cipher_list(ctx, "WDM-NULL-SHA256")
                                                           != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("Couldn't set multicast cipher list.");
        }
#endif
    }

#ifdef HAVE_PK_CALLBACKS
    if (pkCallbacks)
        SetupPkCallbacks(ctx);
#endif

    ssl = wolfSSL_new(ctx);
    if (ssl == NULL) {
        wolfSSL_CTX_free(ctx); ctx = NULL;
        err_sys("unable to get SSL object");
    }


#ifndef NO_CERTS
    if (useClientCert && loadCertKeyIntoSSLObj){
    #ifndef TEST_LOAD_BUFFER
        if (wolfSSL_use_certificate_chain_file(ssl, ourCert)
                                                           != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't load client cert file, check file and run from"
                    " wolfSSL home dir");
        }
    #else
        load_ssl_buffer(ssl, ourCert, WOLFSSL_CERT_CHAIN);
    #endif
    }

    if (loadCertKeyIntoSSLObj
    #if defined(HAVE_PK_CALLBACKS) && defined(TEST_PK_PRIVKEY)
        && !pkCallbacks
    #endif
    ) {
    #ifndef TEST_LOAD_BUFFER
        if (wolfSSL_use_PrivateKey_file(ssl, ourKey, WOLFSSL_FILETYPE_PEM)
                                         != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't load client private key file, check file and run "
                    "from wolfSSL home dir");
        }
    #else
        load_ssl_buffer(ssl, ourKey, WOLFSSL_KEY);
    #endif
    }
#endif /* !NO_CERTS */

#ifdef OPENSSL_EXTRA
    wolfSSL_KeepArrays(ssl);
#endif

#if defined(WOLFSSL_STATIC_MEMORY) && defined(DEBUG_WOLFSSL)
    fprintf(stderr, "After creating SSL\n");
    if (wolfSSL_CTX_is_static_memory(ctx, &mem_stats) != 1)
        err_sys("ctx not using static memory");
    if (wolfSSL_PrintStats(&mem_stats) != 1) /* function in test.h */
            err_sys("error printing out memory stats");
#endif

#ifdef WOLFSSL_TLS13
    if (!helloRetry) {
    #if defined(WOLFSSL_TLS13) && (!defined(NO_DH) || defined(HAVE_ECC) || \
                             defined(HAVE_CURVE25519) || defined(HAVE_CURVE448))
        if (onlyKeyShare == 0 || onlyKeyShare == 2) {
        #ifdef HAVE_CURVE25519
            if (useX25519) {
                if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X25519)
                                                           != WOLFSSL_SUCCESS) {
                    err_sys("unable to use curve x25519");
                }
            }
        #endif
        #ifdef HAVE_CURVE448
            if (useX448) {
                if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X448)
                                                           != WOLFSSL_SUCCESS) {
                    err_sys("unable to use curve x448");
                }
            }
        #endif
        #ifdef HAVE_ECC
            #if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
            if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_SECP256R1)
                                                           != WOLFSSL_SUCCESS) {
                err_sys("unable to use curve secp256r1");
            }
            #endif
        #endif
        }
        if (onlyKeyShare == 0 || onlyKeyShare == 1) {
        #ifdef HAVE_FFDHE_2048
            if (wolfSSL_UseKeyShare(ssl, WOLFSSL_FFDHE_2048)
                                                           != WOLFSSL_SUCCESS) {
                err_sys("unable to use DH 2048-bit parameters");
            }
        #endif
        }
    #endif
    }
    else {
        wolfSSL_NoKeyShares(ssl);
    }
#endif

    if (doMcast) {
#ifdef WOLFSSL_MULTICAST
        byte pms[512]; /* pre master secret */
        byte cr[32];   /* client random */
        byte sr[32];   /* server random */
        const byte suite[2] = {0, 0xfe};  /* WDM_WITH_NULL_SHA256 */

        XMEMSET(pms, 0x23, sizeof(pms));
        XMEMSET(cr, 0xA5, sizeof(cr));
        XMEMSET(sr, 0x5A, sizeof(sr));

        if (wolfSSL_set_secret(ssl, 1, pms, sizeof(pms), cr, sr, suite)
                                                           != WOLFSSL_SUCCESS) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("unable to set mcast secret");
        }
#endif
    }

    #ifdef HAVE_SESSION_TICKET
    wolfSSL_set_SessionTicket_cb(ssl, sessionTicketCB, (void*)"initial session");
    #endif

#ifdef HAVE_TRUSTED_CA
    if (trustedCaKeyId) {
        if (wolfSSL_UseTrustedCA(ssl, WOLFSSL_TRUSTED_CA_PRE_AGREED,
                    NULL, 0) != WOLFSSL_SUCCESS) {
            err_sys("UseTrustedCA failed");
        }
    }
#endif
#ifdef HAVE_ALPN
    if (alpnList != NULL) {
       printf("ALPN accepted protocols list : %s\n", alpnList);
       wolfSSL_UseALPN(ssl, alpnList, (word32)XSTRLEN(alpnList), alpn_opt);
    }
#endif

#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) || \
    defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
    if (statusRequest) {
        if (version == 4 &&
            (statusRequest == OCSP_STAPLINGV2 || \
             statusRequest == OCSP_STAPLINGV2_MULTI)) {
            err_sys("Cannot use OCSP Stapling V2 with TLSv1.3");
        }

        if (wolfSSL_CTX_EnableOCSPStapling(ctx) != WOLFSSL_SUCCESS)
            err_sys("can't enable OCSP Stapling Certificate Manager");

        switch (statusRequest) {
        #ifdef HAVE_CERTIFICATE_STATUS_REQUEST
            case OCSP_STAPLING:
                if (wolfSSL_UseOCSPStapling(ssl, WOLFSSL_CSR_OCSP,
                               WOLFSSL_CSR_OCSP_USE_NONCE) != WOLFSSL_SUCCESS) {
                    wolfSSL_free(ssl); ssl = NULL;
                    wolfSSL_CTX_free(ctx); ctx = NULL;
                    err_sys("UseCertificateStatusRequest failed");
                }
            break;
        #endif
        #ifdef HAVE_CERTIFICATE_STATUS_REQUEST_V2
            case OCSP_STAPLINGV2:
                if (wolfSSL_UseOCSPStaplingV2(ssl,
                    WOLFSSL_CSR2_OCSP, WOLFSSL_CSR2_OCSP_USE_NONCE)
                                                           != WOLFSSL_SUCCESS) {
                    wolfSSL_free(ssl); ssl = NULL;
                    wolfSSL_CTX_free(ctx); ctx = NULL;
                    err_sys("UseCertificateStatusRequest failed");
                }
            break;
            case OCSP_STAPLINGV2_MULTI:
                if (wolfSSL_UseOCSPStaplingV2(ssl,
                    WOLFSSL_CSR2_OCSP_MULTI, 0)
                                                           != WOLFSSL_SUCCESS) {
                    wolfSSL_free(ssl); ssl = NULL;
                    wolfSSL_CTX_free(ctx); ctx = NULL;
                    err_sys("UseCertificateStatusRequest failed");
                }
            break;
        #endif
            default:
                err_sys("Invalid OCSP Stapling option");
        }

        wolfSSL_CTX_EnableOCSP(ctx, 0);
    }
#endif

#if !defined(NO_DH) && !defined(WOLFSSL_OLD_PRIME_CHECK) && \
    !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
    if (!doDhKeyCheck)
        wolfSSL_SetEnableDhKeyTest(ssl, 0);
#endif

#ifdef HAVE_ENCRYPT_THEN_MAC
    if (disallowETM)
        wolfSSL_AllowEncryptThenMac(ssl, 0);
#endif


    tcp_connect(&sockfd, host, port, dtlsUDP, dtlsSCTP, ssl);
    if (wolfSSL_set_fd(ssl, sockfd) != WOLFSSL_SUCCESS) {
        wolfSSL_free(ssl); ssl = NULL;
        wolfSSL_CTX_free(ctx); ctx = NULL;
        err_sys("error in setting fd");
    }

    /* STARTTLS */
    if (doSTARTTLS) {
        if (StartTLS_Init(&sockfd) != WOLFSSL_SUCCESS) {
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("error during STARTTLS protocol");
        }
    }

#ifdef HAVE_CRL
    if (disableCRL == 0 && !useVerifyCb) {
    #ifdef HAVE_IO_TIMEOUT
        wolfIO_SetTimeout(DEFAULT_TIMEOUT_SEC);
    #endif

        if (wolfSSL_EnableCRL(ssl, WOLFSSL_CRL_CHECKALL) != WOLFSSL_SUCCESS) {
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't enable crl check");
        }
        if (wolfSSL_LoadCRL(ssl, crlPemDir, WOLFSSL_FILETYPE_PEM, 0)
                                                           != WOLFSSL_SUCCESS) {
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't load crl, check crlfile and date validity");
        }
        if (wolfSSL_SetCRL_Cb(ssl, CRL_CallBack) != WOLFSSL_SUCCESS) {
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't set crl callback");
        }
    }
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
    if (scr) {
        if (wolfSSL_UseSecureRenegotiation(ssl) != WOLFSSL_SUCCESS) {
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("can't enable secure renegotiation");
        }
    }
#endif
#if defined(ATOMIC_USER) && !defined(WOLFSSL_AEAD_ONLY)
    if (atomicUser)
        SetupAtomicUser(ctx, ssl);
#endif
#ifdef HAVE_PK_CALLBACKS
    if (pkCallbacks)
        SetupPkCallbackContexts(ssl, &pkCbInfo);
#endif
    if (matchName && doPeerCheck)
        wolfSSL_check_domain_name(ssl, domain);
#ifndef WOLFSSL_CALLBACKS
    if (nonBlocking) {
#ifdef WOLFSSL_DTLS
        if (doDTLS) {
            wolfSSL_dtls_set_using_nonblock(ssl, 1);
        }
#endif
        tcp_set_nonblocking(&sockfd);
        ret = NonBlockingSSL_Connect(ssl);
    }
    else {
#ifdef WOLFSSL_EARLY_DATA
        if (usePsk && earlyData)
            EarlyData(ctx, ssl, msg, msgSz, buffer);
#endif
        do {
            err = 0; /* reset error */
            ret = wolfSSL_connect(ssl);
            if (ret != WOLFSSL_SUCCESS) {
                err = wolfSSL_get_error(ssl, 0);
            #ifdef WOLFSSL_ASYNC_CRYPT
                if (err == WC_PENDING_E) {
                    ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                    if (ret < 0) break;
                }
            #endif
            }
        } while (err == WC_PENDING_E);
    }
#else
    timeoutConnect.tv_sec  = DEFAULT_TIMEOUT_SEC;
    timeoutConnect.tv_usec = 0;
    ret = NonBlockingSSL_Connect(ssl);  /* will keep retrying on timeout */
#endif
    if (ret != WOLFSSL_SUCCESS) {
        err = wolfSSL_get_error(ssl, 0);
        printf("wolfSSL_connect error %d, %s\n", err,
            wolfSSL_ERR_error_string(err, buffer));

        /* cleanup */
        wolfSSL_free(ssl); ssl = NULL;
        wolfSSL_CTX_free(ctx); ctx = NULL;
        CloseSocket(sockfd);

        if (!exitWithRet)
            err_sys("wolfSSL_connect failed");
        /* see note at top of README */
        /* if you're getting an error here  */

        ((func_args*)args)->return_code = err;
        goto exit;
    }

    showPeerEx(ssl, lng_index);

#ifdef OPENSSL_EXTRA
    printf("Session timeout set to %ld seconds\n", wolfSSL_get_timeout(ssl));
    {
        byte*  rnd;
        byte*  pt;
        size_t size;

        /* get size of buffer then print */
        size = wolfSSL_get_client_random(NULL, NULL, 0);
        if (size == 0) {
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("error getting client random buffer size");
        }

        rnd = (byte*)XMALLOC(size, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (rnd == NULL) {
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("error creating client random buffer");
        }

        size = wolfSSL_get_client_random(ssl, rnd, size);
        if (size == 0) {
            XFREE(rnd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            wolfSSL_free(ssl); ssl = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("error getting client random buffer");
        }

        printf("Client Random : ");
        for (pt = rnd; pt < rnd + size; pt++) printf("%02X", *pt);
        printf("\n");
        XFREE(rnd, NULL, DYNAMIC_TYPE_TMP_BUFFER);

    }

    #if defined(OPENSSL_ALL)
    /* print out session to stdout */
    {
        WOLFSSL_BIO* bio = wolfSSL_BIO_new_fp(stdout, BIO_NOCLOSE);
        if (bio != NULL) {
            if (wolfSSL_SESSION_print(bio, wolfSSL_get_session(ssl)) !=
                    WOLFSSL_SUCCESS) {
                wolfSSL_BIO_printf(bio, "ERROR: Unable to print out session\n");
            }
        }
        wolfSSL_BIO_free(bio);
    }
    #endif
#endif

    if (doSTARTTLS && starttlsProt != NULL) {
        if (XSTRNCMP(starttlsProt, "smtp", 4) == 0) {
            if (SMTP_Shutdown(ssl, wc_shutdown) != WOLFSSL_SUCCESS) {
                wolfSSL_free(ssl); ssl = NULL;
                wolfSSL_CTX_free(ctx); ctx = NULL;
                err_sys("error closing STARTTLS connection");
            }
        }

        wolfSSL_free(ssl); ssl = NULL;
        CloseSocket(sockfd);

        wolfSSL_CTX_free(ctx); ctx = NULL;

        ((func_args*)args)->return_code = 0;
        return 0;
    }

#ifdef HAVE_ALPN
    if (alpnList != NULL) {
        char *protocol_name = NULL;
        word16 protocol_nameSz = 0;

        err = wolfSSL_ALPN_GetProtocol(ssl, &protocol_name, &protocol_nameSz);
        if (err == WOLFSSL_SUCCESS)
            printf("Received ALPN protocol : %s (%d)\n",
                   protocol_name, protocol_nameSz);
        else if (err == WOLFSSL_ALPN_NOT_FOUND)
            printf("No ALPN response received (no match with server)\n");
        else
            printf("Getting ALPN protocol name failed\n");
    }
#endif

#ifdef HAVE_SECURE_RENEGOTIATION
    if (scr && forceScr) {
        if (nonBlocking) {
            printf("not doing secure renegotiation on example with"
                   " nonblocking yet\n");
        } else {
            if (!resumeScr) {
                printf("Beginning secure rengotiation.\n");
                if (wolfSSL_Rehandshake(ssl) != WOLFSSL_SUCCESS) {
                    err = wolfSSL_get_error(ssl, 0);
                    printf("err = %d, %s\n", err,
                                    wolfSSL_ERR_error_string(err, buffer));
                    wolfSSL_free(ssl); ssl = NULL;
                    wolfSSL_CTX_free(ctx); ctx = NULL;
                    err_sys("wolfSSL_Rehandshake failed");
                }
                else {
                    printf("RENEGOTIATION SUCCESSFUL\n");
                }
            }
            else {
                printf("Beginning secure resumption.\n");
                if (wolfSSL_SecureResume(ssl) != WOLFSSL_SUCCESS) {
                    err = wolfSSL_get_error(ssl, 0);
                    printf("err = %d, %s\n", err,
                                    wolfSSL_ERR_error_string(err, buffer));
                    wolfSSL_free(ssl); ssl = NULL;
                    wolfSSL_CTX_free(ctx); ctx = NULL;
                    err_sys("wolfSSL_SecureResume failed");
                }
                else {
                    printf("SECURE RESUMPTION SUCCESSFUL\n");
                }
            }
        }
    }
#endif /* HAVE_SECURE_RENEGOTIATION */

    if (sendGET) {
        printf("SSL connect ok, sending GET...\n");
        msgSz = sizeof("GET /index.html HTTP/1.0\r\n\r\n");
        XSTRNCPY(msg, "GET /index.html HTTP/1.0\r\n\r\n", msgSz);
        msg[msgSz] = '\0';

        resumeSz = msgSz;
        XSTRNCPY(resumeMsg, "GET /index.html HTTP/1.0\r\n\r\n", resumeSz);
        resumeMsg[resumeSz] = '\0';
    }

/* allow some time for exporting the session */
#ifdef WOLFSSL_SESSION_EXPORT_DEBUG
#ifdef USE_WINDOWS_API
    Sleep(500);
#elif defined(WOLFSSL_TIRTOS)
    Task_sleep(1);
#else
    sleep(1);
#endif
#endif /* WOLFSSL_SESSION_EXPORT_DEBUG */

#ifdef WOLFSSL_TLS13
    if (updateKeysIVs)
        wolfSSL_update_keys(ssl);
#endif

    ClientWrite(ssl, msg, msgSz, "");

    ClientRead(ssl, reply, sizeof(reply)-1, 1, "");

#if defined(WOLFSSL_TLS13)
    if (updateKeysIVs || postHandAuth)
        ClientWrite(ssl, msg, msgSz, "");
#endif
    if (sendGET) {  /* get html */
        ClientRead(ssl, reply, sizeof(reply)-1, 0, "");
    }

#ifndef NO_SESSION_CACHE
    if (resumeSession) {
        session   = wolfSSL_get_session(ssl);
    }
#endif

#if defined(OPENSSL_EXTRA) && defined(HAVE_EXT_CACHE)
    if (session != NULL && resumeSession) {
        flatSessionSz = wolfSSL_i2d_SSL_SESSION(session, NULL);
        if (flatSessionSz != 0) {
            int checkSz = wolfSSL_i2d_SSL_SESSION(session, &flatSession);
            if (flatSession == NULL)
                err_sys("error creating flattened session buffer");
            if (checkSz != flatSessionSz) {
                XFREE(flatSession, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                err_sys("flat session size check failure");
            }
        }
    }
#endif

    if (dtlsUDP == 0) {           /* don't send alert after "break" command */
        ret = wolfSSL_shutdown(ssl);
        if (wc_shutdown && ret == WOLFSSL_SHUTDOWN_NOT_DONE) {
            if (tcp_select(sockfd, DEFAULT_TIMEOUT_SEC) == TEST_RECV_READY) {
                ret = wolfSSL_shutdown(ssl); /* bidirectional shutdown */
                if (ret == WOLFSSL_SUCCESS)
                    printf("Bidirectional shutdown complete\n");
            }
            if (ret != WOLFSSL_SUCCESS)
                printf("Bidirectional shutdown failed\n");
        }
    }
#if defined(ATOMIC_USER) && !defined(WOLFSSL_AEAD_ONLY)
    if (atomicUser)
        FreeAtomicUser(ssl);
#endif

    /* display collected statistics */
#ifdef WOLFSSL_STATIC_MEMORY
    if (wolfSSL_is_static_memory(ssl, &ssl_stats) != 1)
        err_sys("static memory was not used with ssl");

    fprintf(stderr, "\nprint off SSL memory stats\n");
    fprintf(stderr, "*** This is memory state before wolfSSL_free is called\n");
    fprintf(stderr, "peak connection memory = %d\n", ssl_stats.peakMem);
    fprintf(stderr, "current memory in use  = %d\n", ssl_stats.curMem);
    fprintf(stderr, "peak connection allocs = %d\n", ssl_stats.peakAlloc);
    fprintf(stderr, "current connection allocs = %d\n", ssl_stats.curAlloc);
    fprintf(stderr, "total connection allocs   = %d\n", ssl_stats.totalAlloc);
    fprintf(stderr, "total connection frees    = %d\n\n", ssl_stats.totalFr);
#endif

    wolfSSL_free(ssl); ssl = NULL;
    CloseSocket(sockfd);

#ifndef NO_SESSION_CACHE
    if (resumeSession) {
        sslResume = wolfSSL_new(ctx);
        if (sslResume == NULL) {
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("unable to get SSL object");
        }

#if !defined(NO_DH) && !defined(WOLFSSL_OLD_PRIME_CHECK) && \
    !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
        if (!doDhKeyCheck)
            wolfSSL_SetEnableDhKeyTest(sslResume, 0);
#endif

        if (dtlsUDP) {
#ifdef USE_WINDOWS_API
            Sleep(500);
#elif defined(WOLFSSL_TIRTOS)
            Task_sleep(1);
#else
            sleep(1);
#endif
        }
        tcp_connect(&sockfd, host, port, dtlsUDP, dtlsSCTP, sslResume);
        if (wolfSSL_set_fd(sslResume, sockfd) != WOLFSSL_SUCCESS) {
            wolfSSL_free(sslResume); sslResume = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("error in setting fd");
        }
#ifdef HAVE_ALPN
        if (alpnList != NULL) {
            printf("ALPN accepted protocols list : %s\n", alpnList);
            wolfSSL_UseALPN(sslResume, alpnList, (word32)XSTRLEN(alpnList),
                            alpn_opt);
        }
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
        if (scr) {
            if (wolfSSL_UseSecureRenegotiation(sslResume) != WOLFSSL_SUCCESS) {
                wolfSSL_free(sslResume); sslResume = NULL;
                wolfSSL_CTX_free(ctx); ctx = NULL;
                err_sys("can't enable secure renegotiation");
            }
        }
#endif

#if defined(OPENSSL_EXTRA) && defined(HAVE_EXT_CACHE)
        if (flatSession) {
            const byte* constFlatSession = flatSession;
            session = wolfSSL_d2i_SSL_SESSION(NULL,
                    &constFlatSession, flatSessionSz);
        }
#endif

        wolfSSL_set_session(sslResume, session);

#if defined(OPENSSL_EXTRA) && defined(HAVE_EXT_CACHE)
        if (flatSession) {
            XFREE(flatSession, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            wolfSSL_SESSION_free(session);
        }
#endif
#ifdef HAVE_SESSION_TICKET
        wolfSSL_set_SessionTicket_cb(sslResume, sessionTicketCB,
                                    (void*)"resumed session");
#endif

#ifndef WOLFSSL_CALLBACKS
        if (nonBlocking) {
#ifdef WOLFSSL_DTLS
            if (doDTLS) {
                wolfSSL_dtls_set_using_nonblock(sslResume, 1);
            }
#endif
            tcp_set_nonblocking(&sockfd);
            ret = NonBlockingSSL_Connect(sslResume);
        }
        else {
    #ifdef WOLFSSL_EARLY_DATA
        #ifndef HAVE_SESSION_TICKET
            if (!usePsk) {
            }
            else
        #endif
            if (earlyData) {
                EarlyData(ctx, sslResume, msg, msgSz, buffer);
            }
    #endif
            do {
                err = 0; /* reset error */
                ret = wolfSSL_connect(sslResume);
                if (ret != WOLFSSL_SUCCESS) {
                    err = wolfSSL_get_error(sslResume, 0);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (err == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPoll(sslResume,
                                                    WOLF_POLL_FLAG_CHECK_HW);
                        if (ret < 0) break;
                    }
                #endif
                }
            } while (err == WC_PENDING_E);
        }
#else
        timeoutConnect.tv_sec  = DEFAULT_TIMEOUT_SEC;
        timeoutConnect.tv_usec = 0;
        ret = NonBlockingSSL_Connect(sslResume);  /* will keep retrying on timeout */
#endif
        if (ret != WOLFSSL_SUCCESS) {
            printf("wolfSSL_connect resume error %d, %s\n", err,
                wolfSSL_ERR_error_string(err, buffer));
            wolfSSL_free(sslResume); sslResume = NULL;
            wolfSSL_CTX_free(ctx); ctx = NULL;
            err_sys("wolfSSL_connect resume failed");
        }

        showPeerEx(sslResume, lng_index);

        if (wolfSSL_session_reused(sslResume))
            printf("reused session id\n");
        else
            printf("didn't reuse session id!!!\n");

#ifdef HAVE_ALPN
        if (alpnList != NULL) {
            char *protocol_name = NULL;
            word16 protocol_nameSz = 0;

            printf("Sending ALPN accepted list : %s\n", alpnList);
            err = wolfSSL_ALPN_GetProtocol(sslResume, &protocol_name,
                                           &protocol_nameSz);
            if (err == WOLFSSL_SUCCESS)
                printf("Received ALPN protocol : %s (%d)\n",
                       protocol_name, protocol_nameSz);
            else if (err == WOLFSSL_ALPN_NOT_FOUND)
                printf("Not received ALPN response (no match with server)\n");
            else
                printf("Getting ALPN protocol name failed\n");
        }
#endif

    /* allow some time for exporting the session */
    #ifdef WOLFSSL_SESSION_EXPORT_DEBUG
        #ifdef USE_WINDOWS_API
            Sleep(500);
        #elif defined(WOLFSSL_TIRTOS)
            Task_sleep(1);
        #else
            sleep(1);
        #endif
    #endif /* WOLFSSL_SESSION_EXPORT_DEBUG */

#ifdef HAVE_SECURE_RENEGOTIATION
    if (scr && forceScr) {
        if (nonBlocking) {
            printf("not doing secure renegotiation on example with"
                   " nonblocking yet\n");
        } else {
            if (!resumeScr) {
                printf("Beginning secure rengotiation.\n");
                if (wolfSSL_Rehandshake(sslResume) != WOLFSSL_SUCCESS) {
                    err = wolfSSL_get_error(sslResume, 0);
                    printf("err = %d, %s\n", err,
                                    wolfSSL_ERR_error_string(err, buffer));
                    wolfSSL_free(sslResume); sslResume = NULL;
                    wolfSSL_CTX_free(ctx); ctx = NULL;
                    err_sys("wolfSSL_Rehandshake failed");
                }
                else {
                    printf("RENEGOTIATION SUCCESSFUL\n");
                }
            }
            else {
                printf("Beginning secure resumption.\n");
                if (wolfSSL_SecureResume(sslResume) != WOLFSSL_SUCCESS) {
                    err = wolfSSL_get_error(sslResume, 0);
                    printf("err = %d, %s\n", err,
                                    wolfSSL_ERR_error_string(err, buffer));
                    wolfSSL_free(sslResume); sslResume = NULL;
                    wolfSSL_CTX_free(ctx); ctx = NULL;
                    err_sys("wolfSSL_SecureResume failed");
                }
                else {
                    printf("SECURE RESUMPTION SUCCESSFUL\n");
                }
            }
        }
    }
#endif /* HAVE_SECURE_RENEGOTIATION */

        ClientWrite(sslResume, resumeMsg, resumeSz, " resume");

        ClientRead(sslResume, reply, sizeof(reply)-1, sendGET,
                   "Server resume: ");
        /* try to send session break */
        ClientWrite(sslResume, msg, msgSz, " resume 2");

        ret = wolfSSL_shutdown(sslResume);
        if (wc_shutdown && ret == WOLFSSL_SHUTDOWN_NOT_DONE)
            wolfSSL_shutdown(sslResume);    /* bidirectional shutdown */

        /* display collected statistics */
    #ifdef WOLFSSL_STATIC_MEMORY
        if (wolfSSL_is_static_memory(sslResume, &ssl_stats) != 1)
            err_sys("static memory was not used with ssl");

        fprintf(stderr, "\nprint off SSLresume memory stats\n");
        fprintf(stderr, "*** This is memory state before wolfSSL_free is called\n");
        fprintf(stderr, "peak connection memory = %d\n", ssl_stats.peakMem);
        fprintf(stderr, "current memory in use  = %d\n", ssl_stats.curMem);
        fprintf(stderr, "peak connection allocs = %d\n", ssl_stats.peakAlloc);
        fprintf(stderr, "current connection allocs = %d\n", ssl_stats.curAlloc);
        fprintf(stderr, "total connection allocs   = %d\n", ssl_stats.totalAlloc);
        fprintf(stderr, "total connection frees    = %d\n\n", ssl_stats.totalFr);
    #endif

        wolfSSL_free(sslResume); sslResume = NULL;
        CloseSocket(sockfd);
    }
#endif /* NO_SESSION_CACHE */

    wolfSSL_CTX_free(ctx); ctx = NULL;

    ((func_args*)args)->return_code = 0;

exit:

#ifdef WOLFSSL_ASYNC_CRYPT
    wolfAsync_DevClose(&devId);
#endif

#if defined(HAVE_ECC) && defined(FP_ECC) && defined(HAVE_THREAD_LS) \
                                         && defined(HAVE_STACK_SIZE)
    wc_ecc_fp_free();  /* free per thread cache */
#endif

    /* There are use cases  when these assignments are not read. To avoid
     * potential confusion those warnings have been handled here.
     */
    (void) overrideDateErrors;
    (void) useClientCert;
    (void) verifyCert;
    (void) ourCert;
    (void) ourKey;
    (void) useVerifyCb;

#if !defined(WOLFSSL_TIRTOS)
    return 0;
#endif
}

#endif /* !NO_WOLFSSL_CLIENT */


/* so overall tests can pull in test function */
#ifndef NO_MAIN_DRIVER

    int main(int argc, char** argv)
    {
        func_args args;


        StartTCP();

        args.argc = argc;
        args.argv = argv;
        args.return_code = 0;

#if defined(DEBUG_WOLFSSL) && !defined(WOLFSSL_MDK_SHELL) && !defined(STACK_TRAP)
        wolfSSL_Debugging_ON();
#endif
        wolfSSL_Init();
        ChangeToWolfRoot();

#ifndef NO_WOLFSSL_CLIENT
#ifdef HAVE_STACK_SIZE
        StackSizeCheck(&args, client_test);
#else
        client_test(&args);
#endif
#else
        printf("Client not compiled in!\n");
#endif
        wolfSSL_Cleanup();

#ifdef HAVE_WNR
    if (wc_FreeNetRandom() < 0)
        err_sys("Failed to free netRandom context");
#endif /* HAVE_WNR */

        return args.return_code;
    }

    int myoptind = 0;
    char* myoptarg = NULL;

#endif /* NO_MAIN_DRIVER */
