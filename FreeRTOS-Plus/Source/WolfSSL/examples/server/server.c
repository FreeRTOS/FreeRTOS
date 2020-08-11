/* server.c
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
#include <wolfssl/ssl.h> /* name change portability layer */

#include <wolfssl/wolfcrypt/settings.h>
#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>   /* wc_ecc_fp_free */
#endif

#if defined(WOLFSSL_MDK_ARM) || defined(WOLFSSL_KEIL_TCP_NET)
        #include <stdio.h>
        #include <string.h>
        #include "rl_fs.h"
        #include "rl_net.h"
#endif

#include <wolfssl/openssl/ssl.h>
#include <wolfssl/test.h>
#ifdef WOLFSSL_DTLS
    #include <wolfssl/error-ssl.h>
#endif

#include "examples/server/server.h"

#ifndef NO_WOLFSSL_SERVER

#ifdef WOLFSSL_ASYNC_CRYPT
    static int devId = INVALID_DEVID;
#endif

#define DEFAULT_TIMEOUT_SEC 2

/* Note on using port 0: if the server uses port 0 to bind an ephemeral port
 * number and is using the ready file for scripted testing, the code in
 * test.h will write the actual port number into the ready file for use
 * by the client. */

static const char webServerMsg[] =
    "HTTP/1.1 200 OK\r\n"
    "Content-Type: text/html\r\n"
    "Connection: close\r\n"
    "Content-Length: 141\r\n"
    "\r\n"
    "<html>\r\n"
    "<head>\r\n"
    "<title>Welcome to wolfSSL!</title>\r\n"
    "</head>\r\n"
    "<body>\r\n"
    "<p>wolfSSL has successfully performed handshake!</p>\r\n"
    "</body>\r\n"
    "</html>\r\n";

int runWithErrors = 0; /* Used with -x flag to run err_sys vs. print errors */
int catastrophic = 0; /* Use with -x flag to still exit when an error is
                      * considered catastrophic EG the servers own cert failing
                      * to load would be catastrophic since there would be no
                      * cert to send to clients attempting to connect. The
                      * server should error out completely in that case
                      */
static int lng_index = 0;

#ifdef WOLFSSL_CALLBACKS
    #if !defined(NO_OLD_TIMEVAL_NAME)
        Timeval srvTo;
    #else
        WOLFSSL_TIMEVAL srvTo;
    #endif
    static int srvHandShakeCB(HandShakeInfo* info)
    {
        (void)info;
        return 0;
    }

    static int srvTimeoutCB(TimeoutInfo* info)
    {
        (void)info;
        return 0;
    }

#endif

#ifndef NO_HANDSHAKE_DONE_CB
    static int myHsDoneCb(WOLFSSL* ssl, void* user_ctx)
    {
        (void)user_ctx;
        (void)ssl;

        /* printf("Notified HandShake done\n"); */

        /* return negative number to end TLS connection now */
        return 0;
    }
#endif


static void err_sys_ex(int out, const char* msg)
{
    if (out == 1) { /* if server is running w/ -x flag, print error w/o exit */
        printf("wolfSSL error: %s\n", msg);
        printf("Continuing server execution...\n\n");
    } else {
        err_sys(msg);
    }
}


#ifdef WOLFSSL_DTLS

/* Translates return codes returned from
 * send() and recv() if need be.
 */
static WC_INLINE int TranslateReturnCode(int old, int sd)
{
    (void)sd;

#if defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)
    if (old == 0) {
        errno = SOCKET_EWOULDBLOCK;
        return -1;  /* convert to BSD style wouldblock as error */
    }

    if (old < 0) {
        errno = RTCS_geterror(sd);
        if (errno == RTCSERR_TCP_CONN_CLOSING)
            return 0;   /* convert to BSD style closing */
        if (errno == RTCSERR_TCP_CONN_RLSD)
            errno = SOCKET_ECONNRESET;
        if (errno == RTCSERR_TCP_TIMED_OUT)
            errno = SOCKET_EAGAIN;
    }
#endif

    return old;
}

static WC_INLINE int wolfSSL_LastError(void)
{
#ifdef USE_WINDOWS_API
    return WSAGetLastError();
#elif defined(EBSNET)
    return xn_getlasterror();
#else
    return errno;
#endif
}

/* wolfSSL Sock Addr */
struct WOLFSSL_TEST_SOCKADDR {
    unsigned int  sz; /* sockaddr size */
    SOCKADDR_IN_T sa; /* pointer to the sockaddr_in or sockaddr_in6 */
};

typedef struct WOLFSSL_TEST_DTLS_CTX {
    struct WOLFSSL_TEST_SOCKADDR peer;
    int rfd;
    int wfd;
    int failOnce;
    word32 blockSeq;
} WOLFSSL_TEST_DTLS_CTX;


static WC_INLINE int PeekSeq(const char* buf, word32* seq)
{
    const char* c = buf + 3;

    if ((c[0] | c[1] | c[2] | c[3]) == 0) {
        *seq = (c[4] << 24) | (c[5] << 16) | (c[6] << 8) | c[7];
        return 1;
    }

    return 0;
}


/* The send embedded callback
 *  return : nb bytes sent, or error
 */
static int TestEmbedSendTo(WOLFSSL* ssl, char *buf, int sz, void *ctx)
{
    WOLFSSL_TEST_DTLS_CTX* dtlsCtx = (WOLFSSL_TEST_DTLS_CTX*)ctx;
    int sd = dtlsCtx->wfd;
    int sent;
    int err;

    (void)ssl;

    WOLFSSL_ENTER("TestEmbedSendTo()");

    if (dtlsCtx->failOnce) {
        word32 seq = 0;

        if (PeekSeq(buf, &seq) && seq == dtlsCtx->blockSeq) {
            dtlsCtx->failOnce = 0;
            WOLFSSL_MSG("Forcing WANT_WRITE");
            return WOLFSSL_CBIO_ERR_WANT_WRITE;
        }
    }

    sent = (int)sendto(sd, buf, sz, 0, (const SOCKADDR*)&dtlsCtx->peer.sa,
                                                             dtlsCtx->peer.sz);

    sent = TranslateReturnCode(sent, sd);

    if (sent < 0) {
        err = wolfSSL_LastError();
        WOLFSSL_MSG("Embed Send To error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            WOLFSSL_MSG("\tWould Block");
            return WOLFSSL_CBIO_ERR_WANT_WRITE;
        }
        else if (err == SOCKET_ECONNRESET) {
            WOLFSSL_MSG("\tConnection reset");
            return WOLFSSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            WOLFSSL_MSG("\tSocket interrupted");
            return WOLFSSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_EPIPE) {
            WOLFSSL_MSG("\tSocket EPIPE");
            return WOLFSSL_CBIO_ERR_CONN_CLOSE;
        }
        else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    return sent;
}

#endif /* WOLFSSL_DTLS */


static int NonBlockingSSL_Accept(SSL* ssl)
{
#ifndef WOLFSSL_CALLBACKS
    int ret = SSL_accept(ssl);
#else
    int ret = wolfSSL_accept_ex(ssl, srvHandShakeCB, srvTimeoutCB, srvTo);
#endif
    int error = SSL_get_error(ssl, 0);
    SOCKET_T sockfd = (SOCKET_T)SSL_get_fd(ssl);
    int select_ret = 0;

    while (ret != WOLFSSL_SUCCESS &&
        (error == WOLFSSL_ERROR_WANT_READ || error == WOLFSSL_ERROR_WANT_WRITE
        #ifdef WOLFSSL_ASYNC_CRYPT
            || error == WC_PENDING_E
        #endif
    )) {
        int currTimeout = 1;

        if (error == WOLFSSL_ERROR_WANT_READ) {
            /* printf("... server would read block\n"); */
        }
        else if (error == WOLFSSL_ERROR_WANT_WRITE) {
            /* printf("... server would write block\n"); */
        }

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
                ret = SSL_accept(ssl);
            #else
                ret = wolfSSL_accept_ex(ssl,
                                    srvHandShakeCB, srvTimeoutCB, srvTo);
            #endif
            error = SSL_get_error(ssl, 0);
            if (error == WOLFSSL_ERROR_WANT_WRITE) {
                /* Do a select here. */
                select_ret = tcp_select_tx(sockfd, 1);
                if (select_ret == TEST_TIMEOUT)
                    error = WOLFSSL_FATAL_ERROR;
            }
        }
        else if (select_ret == TEST_TIMEOUT && !wolfSSL_dtls(ssl)) {
            error = WOLFSSL_ERROR_WANT_READ;
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

/* Echo number of bytes specified by -e arg */
int ServerEchoData(SSL* ssl, int clientfd, int echoData, int block,
                   size_t throughput)
{
    int ret = 0, err;
    double start = 0, rx_time = 0, tx_time = 0;
    int select_ret, len, rx_pos;
    size_t xfer_bytes = 0;
    char* buffer;

    buffer = (char*)malloc(block);
    if (!buffer) {
        err_sys_ex(runWithErrors, "Server buffer malloc failed");
    }

    while ((echoData && throughput == 0) ||
          (!echoData && xfer_bytes < throughput))
    {
        select_ret = tcp_select(clientfd, 1); /* Timeout=1 second */
        if (select_ret == TEST_RECV_READY) {

            len = min(block, (int)(throughput - xfer_bytes));
            rx_pos = 0;

            if (throughput) {
                start = current_time(1);
            }

            /* Read data */
            while (rx_pos < len) {
                ret = SSL_read(ssl, &buffer[rx_pos], len - rx_pos);
                if (ret < 0) {
                    err = SSL_get_error(ssl, 0);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (err == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                        if (ret < 0) break;
                    }
                    else
                #endif
                    if (err != WOLFSSL_ERROR_WANT_READ &&
                                             err != WOLFSSL_ERROR_ZERO_RETURN) {
                        printf("SSL_read echo error %d\n", err);
                        err_sys_ex(runWithErrors, "SSL_read failed");
                        break;
                    }
                }
                else {
                    rx_pos += ret;
                }
            }
            if (throughput) {
                rx_time += current_time(0) - start;
                start = current_time(1);
            }

            /* Write data */
            do {
                err = 0; /* reset error */
                ret = SSL_write(ssl, buffer, len);
                if (ret <= 0) {
                    err = SSL_get_error(ssl, 0);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (err == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                        if (ret < 0) break;
                    }
                #endif
                }
            } while (err == WC_PENDING_E);
            if (ret != len) {
                printf("SSL_write echo error %d\n", err);
                err_sys_ex(runWithErrors, "SSL_write failed");
            }

            if (throughput) {
                tx_time += current_time(0) - start;
            }

            xfer_bytes += len;
        }
    }

    free(buffer);

    if (throughput) {
    #if !defined(__MINGW32__)
        printf("wolfSSL Server Benchmark %zu bytes\n"
    #else
        printf("wolfSSL Server Benchmark %d bytes\n"
    #endif
            "\tRX      %8.3f ms (%8.3f MBps)\n"
            "\tTX      %8.3f ms (%8.3f MBps)\n",
    #if !defined(__MINGW32__)
            throughput,
    #else
            (int)throughput,
    #endif
            tx_time * 1000, throughput / tx_time / 1024 / 1024,
            rx_time * 1000, throughput / rx_time / 1024 / 1024
        );
    }

    return EXIT_SUCCESS;
}

static void ServerRead(WOLFSSL* ssl, char* input, int inputLen)
{
    int ret, err;
    char buffer[WOLFSSL_MAX_ERROR_SZ];

    /* Read data */
    do {
        err = 0; /* reset error */
        ret = SSL_read(ssl, input, inputLen);
        if (ret < 0) {
            err = SSL_get_error(ssl, 0);

        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
            else
        #endif
        #ifdef WOLFSSL_DTLS
            if (wolfSSL_dtls(ssl) && err == DECRYPT_ERROR) {
                printf("Dropped client's message due to a bad MAC\n");
            }
            else
        #endif
            if (err != WOLFSSL_ERROR_WANT_READ) {
                printf("SSL_read input error %d, %s\n", err,
                                                 ERR_error_string(err, buffer));
                err_sys_ex(runWithErrors, "SSL_read failed");
            }
        }
        else if (SSL_get_error(ssl, 0) == 0 &&
                            tcp_select(SSL_get_fd(ssl), 0) == TEST_RECV_READY) {
                err = WOLFSSL_ERROR_WANT_READ;
        }
    } while (err == WC_PENDING_E || err == WOLFSSL_ERROR_WANT_READ);
    if (ret > 0) {
        input[ret] = 0; /* null terminate message */
        printf("Client message: %s\n", input);
    }
}

static void ServerWrite(WOLFSSL* ssl, const char* output, int outputLen)
{
    int ret, err;
    char buffer[WOLFSSL_MAX_ERROR_SZ];
    int len;

#ifdef OPENSSL_ALL
    /* Fuzz testing expects reply split over two msgs when TLSv1.0 or below */
    if (wolfSSL_GetVersion(ssl) <= WOLFSSL_TLSV1)
         len = outputLen / 2;
    else
#endif
        len = outputLen;

    do {
        err = 0; /* reset error */
        ret = SSL_write(ssl, output, len);
        if (ret <= 0) {
            err = SSL_get_error(ssl, 0);

        #ifdef WOLFSSL_ASYNC_CRYPT
            if (err == WC_PENDING_E) {
                ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                if (ret < 0) break;
            }
        #endif
        }
        else if (ret != outputLen) {
            output += ret;
            len = (outputLen -= ret);
            err = WOLFSSL_ERROR_WANT_WRITE;
        }
    } while (err == WC_PENDING_E || err == WOLFSSL_ERROR_WANT_WRITE);
    if (ret != outputLen) {
        printf("SSL_write msg error %d, %s\n", err,
                                                 ERR_error_string(err, buffer));
        err_sys_ex(runWithErrors, "SSL_write failed");
    }
}
/* when adding new option, please follow the steps below: */
/*  1. add new option message in English section          */
/*  2. increase the number of the second column           */
/*  3. add the same message into Japanese section         */
/*     (will be translated later)                         */
/*  4. add printf() into suitable position of Usage()     */
static const char* server_usage_msg[][49] = {
    /* English */
    {
        " NOTE: All files relative to wolfSSL home dir\n",               /* 0 */
        "-? <num>    Help, print this usage\n"
        "            0: English, 1: Japanese\n",                         /* 1 */
        "-p <num>    Port to listen on, not 0, default",                 /* 2 */
#ifndef WOLFSSL_TLS13
        "-v <num>    SSL version [0-3], SSLv3(0) - TLS1.2(3)), default", /* 3 */
#else
        "-v <num>    SSL version [0-4], SSLv3(0) - TLS1.3(4)), default", /* 3 */
#endif
        "-l <str>    Cipher suite list (: delimited)\n",                 /* 4 */
        "-c <file>   Certificate file,           default",               /* 5 */
        "-k <file>   Key file,                   default",               /* 6 */
        "-A <file>   Certificate Authority file, default",               /* 7 */
        "-R <file>   Create Ready file for external monitor"
                                                     " default none\n",  /* 8 */
#ifndef NO_DH
        "-D <file>   Diffie-Hellman Params file, default",               /* 9 */
        "-Z <num>    Minimum DH key bits,        default",              /* 10 */
#endif
#ifdef HAVE_ALPN
        "-L <str>    Application-Layer Protocol Negotiation"
                                                  " ({C,F}:<list>)\n",  /* 11 */
#endif
        "-d          Disable client cert check\n",                      /* 12 */
        "-b          Bind to any interface instead of localhost only\n",/* 13 */
        "-s          Use pre Shared keys\n",                            /* 14 */
        "-u          Use UDP DTLS,"
           " add -v 2 for DTLSv1, -v 3 for DTLSv1.2 (default)\n",       /* 15 */
#ifdef WOLFSSL_SCTP
        "-G          Use SCTP DTLS,"
           " add -v 2 for DTLSv1, -v 3 for DTLSv1.2 (default)\n",       /* 16 */
#endif
        "-f          Fewer packets/group messages\n",                   /* 17 */
        "-r          Allow one client Resumption\n",                    /* 18 */
        "-N          Use Non-blocking sockets\n",                       /* 19 */
        "-S <str>    Use Host Name Indication\n",                       /* 20 */
        "-w          Wait for bidirectional shutdown\n",                /* 21 */
#ifdef HAVE_OCSP
        "-o          Perform OCSP lookup on peer certificate\n",        /* 22 */
        "-O <url>    Perform OCSP lookup using <url> as responder\n",   /* 23 */
#endif
#ifdef HAVE_PK_CALLBACKS
        "-P          Public Key Callbacks\n",                           /* 24 */
#endif
#ifdef HAVE_ANON
        "-a          Anonymous server\n",                               /* 25 */
#endif
#ifndef NO_PSK
        "-I          Do not send PSK identity hint\n",                  /* 26 */
#endif
        "-x          Print server errors but do not close connection\n",/* 27 */
        "-i          Loop indefinitely (allow repeated connections)\n", /* 28 */
        "-e          Echo data mode (return raw bytes received)\n",     /* 29 */
#ifdef HAVE_NTRU
        "-n          Use NTRU key (needed for NTRU suites)\n",          /* 30 */
#endif
        "-B <num>    Benchmark throughput"
                            " using <num> bytes and print stats\n",     /* 31 */
#ifdef HAVE_CRL
        "-V          Disable CRL\n",                                    /* 32 */
#endif
#ifdef WOLFSSL_TRUST_PEER_CERT
        "-E <file>   Path to load trusted peer cert\n",                 /* 33 */
#endif
#ifdef HAVE_WNR
        "-q <file>   Whitewood config file,      default",              /* 34 */
#endif
        "-g          Return basic HTML web page\n",                     /* 35 */
        "-C <num>    The number of connections to accept, default: 1\n",/* 36 */
        "-H <arg>    Internal tests"
            " [defCipherList, exitWithRet, verifyFail, useSupCurve,\n", /* 37 */
        "                            loadSSL, disallowETM]\n",          /* 38 */
#ifdef WOLFSSL_TLS13
        "-U          Update keys and IVs before sending\n",             /* 39 */
        "-K          Key Exchange for PSK not using (EC)DHE\n",         /* 40 */
#ifndef NO_DH
        "-y          Pre-generate Key Share using FFDHE_2048 only\n",   /* 41 */
#endif
#ifdef HAVE_ECC
        "-Y          Pre-generate Key Share using P-256 only \n",       /* 42 */
#endif
#ifdef HAVE_CURVE25519
        "-t          Pre-generate Key share using Curve25519 only\n",   /* 43 */
#endif
#ifdef HAVE_SESSION_TICKET
        "-T          Do not generate session ticket\n",                 /* 44 */
#endif
        "-F          Send alert if no mutual authentication\n",         /* 45 */
#ifdef WOLFSSL_POST_HANDSHAKE_AUTH
        "-Q          Request certificate from client post-handshake\n", /* 46 */
#endif
#ifdef WOLFSSL_SEND_HRR_COOKIE
        "-J          Server sends Cookie Extension containing state\n", /* 47 */
#endif
#endif /* WOLFSSL_TLS13 */
#ifdef WOLFSSL_EARLY_DATA
        "-0          Early data read from client (0-RTT handshake)\n",  /* 48 */
#endif
#ifdef WOLFSSL_MULTICAST
        "-3 <grpid>  Multicast, grpid < 256\n",                         /* 49 */
#endif
        "-1 <num>    Display a result by specified language."
                             "\n            0: English, 1: Japanese\n", /* 50 */
#ifdef HAVE_TRUSTED_CA
        "-5          Use Trusted CA Key Indication\n",                  /* 53 */
#endif
#ifdef HAVE_CURVE448
        "-8          Pre-generate Key share using Curve448 only\n",     /* 55 */
#endif
        NULL,
    },
#ifndef NO_MULTIBYTE_PRINT
    /* Japanese */
    {
        " 注意 : 全てのファイルは"
        " wolfSSL ホーム・ディレクトリからの相対です。\n",               /* 0 */
        "-? <num>    ヘルプ, 使い方を表示\n"
        "            0: 英語、 1: 日本語\n",                             /* 1 */
        "-p <num>    接続先ポート, 0は無効, 既定値",                     /* 2 */
#ifndef WOLFSSL_TLS13
        "-v <num>    SSL バージョン [0-3], SSLv3(0) - TLS1.2(3)),"
                                                            " 既定値",   /* 3 */
#else
        "-v <num>    SSL バージョン [0-4], SSLv3(0) - TLS1.3(4)),"
                                                            " 既定値",   /* 3 */
#endif
        "-l <str>    暗号スイートリスト (区切り文字 :)\n",               /* 4 */
        "-c <file>   証明書ファイル,  既定値",                           /* 5 */
        "-k <file>   鍵ファイル,      既定値",                           /* 6 */
        "-A <file>   認証局ファイル,  既定値",                           /* 7 */
        "-R <file>   外部モニタ用の準備完了ファイルを作成する。"
                                                      "既定値  なし\n",  /* 8 */
#ifndef NO_DH
        "-D <file>   ディフィー・ヘルマンのパラメータファイル,"
                                                     " 既定値",          /* 9 */
        "-Z <num>    最小 DH 鍵 ビット, 既定値",                        /* 10 */
#endif
#ifdef HAVE_ALPN
        "-L <str>    アプリケーション層プロトコルネゴシエーションを行う"
                                                  " ({C,F}:<list>)\n",  /* 11 */
#endif
        "-d          クライアント認証を無効とする\n",                   /* 12 */
        "-b          ローカルホスト以外のインターフェースへも"
                                                "バインドする\n",       /* 13 */
        "-s          事前共有鍵を使用する\n",                           /* 14 */
        "-u          UDP DTLSを使用する。-v 2 を追加指定すると"
             " DTLSv1, -v 3 を追加指定すると DTLSv1.2 (既定値)\n",      /* 15 */
#ifdef WOLFSSL_SCTP
        "-G          SCTP DTLSを使用する。-v 2 を追加指定すると"
              " DTLSv1, -v 3 を追加指定すると DTLSv1.2 (既定値)\n",     /* 16 */
#endif
        "-f          より少ないパケット/グループメッセージを使用する\n",/* 17 */
        "-r          クライアントの再開を許可する\n",                   /* 18 */
        "-N          ノンブロッキング・ソケットを使用する\n",           /* 19 */
        "-S <str>    ホスト名表示を使用する\n",                         /* 20 */
        "-w          双方向シャットダウンを待つ\n",                     /* 21 */
#ifdef HAVE_OCSP
        "-o          OCSPルックアップをピア証明書で実施する\n",         /* 22 */
        "-O <url>    OCSPルックアップを、"
                        "<url>を使用し応答者として実施する\n",          /* 23 */
#endif
#ifdef HAVE_PK_CALLBACKS
        "-P          公開鍵コールバック\n",                             /* 24 */
#endif
#ifdef HAVE_ANON
        "-a          匿名サーバー\n",                                   /* 25 */
#endif
#ifndef NO_PSK
        "-I          PSKアイデンティティのヒントを送信しない\n",        /* 26 */
#endif
        "-x          サーバーエラーを出力するが接続を切断しない\n",     /* 27 */
        "-i          無期限にループする(繰り返し接続を許可)\n",         /* 28 */
        "-e          エコー・データモード"
                                   "(受け取ったバイトデータを返す)\n",  /* 29 */
#ifdef HAVE_NTRU
        "-n          NTRU鍵を使用する(NTRUスイートに必要)\n",           /* 30 */
#endif
        "-B <num>    <num> バイトを用いてのベンチマーク・スループット"
                                          "測定と結果を出力する\n",     /* 31 */
#ifdef HAVE_CRL
        "-V          CRLを無効とする\n",                                /* 32 */
#endif
#ifdef WOLFSSL_TRUST_PEER_CERT
        "-E <file>   信頼出来るピアの証明書ロードの為のパス\n\n",       /* 33 */
#endif
#ifdef HAVE_WNR
        "-q <file>   Whitewood コンフィグファイル,      既定値",        /* 34 */
#endif
        "-g          基本的な Web ページを返す\n",                      /* 35 */
        "-C <num>    アクセプト可能な接続数を指定する。既定値: 1\n",    /* 36 */
        "-H <arg>    内部テスト"
            " [defCipherList, exitWithRet, verifyFail, useSupCurve,\n", /* 37 */
        "                            loadSSL, disallowETM]\n",          /* 38 */
#ifdef WOLFSSL_TLS13
        "-U          データ送信前に、鍵とIVを更新する\n",               /* 39 */
        "-K          鍵交換にPSKを使用、(EC)DHEは使用しない\n",         /* 40 */
#ifndef NO_DH
        "-y          FFDHE_2048のみを使用して鍵共有を事前生成する\n",   /* 41 */
#endif
#ifdef HAVE_ECC
        "-Y          P-256のみを使用したキー共有の事前生成\n",          /* 42 */
#endif
#ifdef HAVE_CURVE25519
        "-t          Curve25519のみを使用して鍵共有を事前生成する\n",   /* 43 */
#endif
#ifdef HAVE_SESSION_TICKET
        "-T         セッションチケットを生成しない\n",                  /* 44 */
#endif
        "-F          Send alert if no mutual authentication\n",         /* 45 */
#ifdef WOLFSSL_POST_HANDSHAKE_AUTH
        "-Q          クライアントのポストハンドシェイクから"
                                              "証明書を要求する\n",     /* 46 */
#endif
#ifdef WOLFSSL_SEND_HRR_COOKIE
        "-J          サーバーの状態を含むTLS Cookie 拡張を送信する\n",  /* 47 */
#endif
#endif /* WOLFSSL_TLS13 */
#ifdef WOLFSSL_EARLY_DATA
        "-0          クライアントからの Early Data 読み取り"
                                      "（0-RTTハンドシェイク）\n",      /* 48 */
#endif
#ifdef WOLFSSL_MULTICAST
        "-3 <grpid>  マルチキャスト, grpid < 256\n",                    /* 49 */
#endif
        "-1 <num>    指定された言語で結果を表示します。"
                                 "\n            0: 英語、 1: 日本語\n", /* 50 */
#ifdef HAVE_TRUSTED_CA
        "-5          信頼できる認証局の鍵表示を使用する\n",             /* 53 */
#endif
#ifdef HAVE_CURVE448
        "-8          Pre-generate Key share using Curve448 only\n",     /* 55 */
#endif
        NULL,
    },
#endif
};

static void Usage(void)
{
    int msgId = 0;
    const char** msg = server_usage_msg[lng_index];

    printf("%s%s%s", "server ", LIBWOLFSSL_VERSION_STRING,
           msg[msgId]);
    printf("%s", msg[++msgId]);                     /* ? */
    printf("%s %d\n", msg[++msgId], wolfSSLPort);   /* -p */
#ifndef WOLFSSL_TLS13
    printf("%s %d\n", msg[++msgId], SERVER_DEFAULT_VERSION); /* -v */
#else
    printf("%s %d\n", msg[++msgId], SERVER_DEFAULT_VERSION); /* -v */
#endif
    printf("%s", msg[++msgId]);     /* -l */
    printf("%s %s\n", msg[++msgId], svrCertFile);    /* -c */
    printf("%s %s\n", msg[++msgId], svrKeyFile);     /* -k */
    printf("%s %s\n", msg[++msgId], cliCertFile);    /* -A */
    printf("%s", msg[++msgId]);     /* -R */
#ifndef NO_DH
    printf("%s %s\n", msg[++msgId], dhParamFile);           /* -D */
    printf("%s %d\n", msg[++msgId], DEFAULT_MIN_DHKEY_BITS);/* -Z */
#endif
#ifdef HAVE_ALPN
    printf("%s", msg[++msgId]);     /* -L */
#endif
    printf("%s", msg[++msgId]);     /* -d */
    printf("%s", msg[++msgId]);     /* -b */
    printf("%s", msg[++msgId]);     /* -s */
    printf("%s", msg[++msgId]);     /* -u */
#ifdef WOLFSSL_SCTP
    printf("%s", msg[++msgId]);     /* -G */
#endif
    printf("%s", msg[++msgId]);     /* -f */
    printf("%s", msg[++msgId]);     /* -r */
    printf("%s", msg[++msgId]);     /* -N */
    printf("%s", msg[++msgId]);     /* -S */
    printf("%s", msg[++msgId]);     /* -w */
#ifdef HAVE_SECURE_RENEGOTIATION
    printf("-M          Allow Secure Renegotiation\n");
    printf("-m          Force Server Initiated Secure Renegotiation\n");
#endif /* HAVE_SECURE_RENEGOTIATION */
#ifdef HAVE_OCSP
    printf("%s", msg[++msgId]);     /* -o */
    printf("%s", msg[++msgId]);     /* -O */
#endif
#ifdef HAVE_PK_CALLBACKS
    printf("%s", msg[++msgId]);     /* -P */
#endif
#ifdef HAVE_ANON
    printf("%s", msg[++msgId]);     /* -a */
#endif
#ifndef NO_PSK
    printf("%s", msg[++msgId]);     /* -I */
#endif
    printf("%s", msg[++msgId]);     /* -x */
    printf("%s", msg[++msgId]);     /* -i */
    printf("%s", msg[++msgId]);     /* -e */
#ifdef HAVE_NTRU
    printf("%s", msg[++msgId]);     /* -n */
#endif
    printf("%s", msg[++msgId]);     /* -B */
#ifdef HAVE_CRL
    printf("%s", msg[++msgId]);     /* -V */
#endif
#ifdef WOLFSSL_TRUST_PEER_CERT
    printf("%s", msg[++msgId]);     /* -E */
#endif
#ifdef HAVE_WNR
    printf("%s %s\n", msg[++msgId], wnrConfig);  /* -q */
#endif
    printf("%s", msg[++msgId]);     /* -g */
    printf("%s", msg[++msgId]);     /* -C */
    printf("%s", msg[++msgId]);     /* -H */
    printf("%s", msg[++msgId]);     /* more -H options */
#ifdef WOLFSSL_TLS13
    printf("%s", msg[++msgId]);     /* -U */
    printf("%s", msg[++msgId]);     /* -K */
#ifndef NO_DH
    printf("%s", msg[++msgId]);     /* -y */
#endif
#ifdef HAVE_ECC
    printf("%s", msg[++msgId]);     /* -Y */
#endif
#ifdef HAVE_CURVE25519
    printf("%s", msg[++msgId]);     /* -t */
#endif
#ifdef HAVE_SESSION_TICKET
    printf("%s", msg[++msgId]);     /* -T */
#endif
    printf("%s", msg[++msgId]);     /* -F */
#ifdef WOLFSSL_POST_HANDSHAKE_AUTH
    printf("%s", msg[++msgId]);     /* -Q */
#endif
#ifdef WOLFSSL_SEND_HRR_COOKIE
    printf("%s", msg[++msgId]);     /* -J */
#endif
#endif /* WOLFSSL_TLS13 */
#ifdef WOLFSSL_EARLY_DATA
    printf("%s", msg[++msgId]);     /* -0 */
#endif
#if !defined(NO_DH) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST) && !defined(WOLFSSL_OLD_PRIME_CHECK)
    printf("-2          Disable DH Prime check\n");
#endif
#ifdef WOLFSSL_DTLS
    printf("-4 <seq>    DTLS fake would-block for message seq\n");
#endif
#ifdef WOLFSSL_MULTICAST
    printf("%s", msg[++msgId]);     /* -3 */
#endif
    printf("%s", msg[++msgId]);     /* -1 */
#ifdef HAVE_TRUSTED_CA
    printf("%s", msg[++msgId]);     /* -5 */
#endif /* HAVE_TRUSTED_CA */
#ifdef HAVE_CURVE448
    printf("%s", msg[++msgId]);     /* -8 */
#endif
}

THREAD_RETURN WOLFSSL_THREAD server_test(void* args)
{
    SOCKET_T sockfd   = WOLFSSL_SOCKET_INVALID;
    SOCKET_T clientfd = WOLFSSL_SOCKET_INVALID;

    wolfSSL_method_func method = NULL;
    SSL_CTX*    ctx    = 0;
    SSL*        ssl    = 0;

#ifndef WOLFSSL_ALT_TEST_STRINGS
    const char msg[] = "I hear you fa shizzle!";
#else
    const char msg[] = "I hear you fa shizzle!\n";
#endif
    int    useWebServerMsg = 0;
    char   input[80];
#ifndef WOLFSSL_VXWORKS
    int    ch;
#endif
    int    version = SERVER_DEFAULT_VERSION;
#ifndef WOLFSSL_NO_CLIENT_AUTH
    int    doCliCertCheck = 1;
#else
    int    doCliCertCheck = 0;
#endif
#ifdef HAVE_CRL
    int    disableCRL = 0;
#endif
    int    useAnyAddr = 0;
    word16 port = wolfSSLPort;
    int    usePsk = 0;
    int    usePskPlus = 0;
    int    useAnon = 0;
    int    doDTLS = 0;
    int    dtlsUDP = 0;
    int    dtlsSCTP = 0;
    int    doMcast = 0;
#ifdef WOLFSSL_DTLS
    int    doBlockSeq = 0;
    WOLFSSL_TEST_DTLS_CTX dtlsCtx;
#endif
    int    needDH = 0;
    int    useNtruKey   = 0;
    int    nonBlocking  = 0;
    int    fewerPackets = 0;
#ifdef HAVE_PK_CALLBACKS
    int    pkCallbacks  = 0;
    PkCbInfo pkCbInfo;
#endif
    int    wc_shutdown     = 0;
    int    resume = 0;
    int    resumeCount = 0;
    int    loops = 1;
    int    cnt = 0;
    int    echoData = 0;
    int    block = TEST_BUFFER_SIZE;
    size_t throughput = 0;
    int    minDhKeyBits  = DEFAULT_MIN_DHKEY_BITS;
    short  minRsaKeyBits = DEFAULT_MIN_RSAKEY_BITS;
    short  minEccKeyBits = DEFAULT_MIN_ECCKEY_BITS;
    int    doListen = 1;
    int    crlFlags = 0;
    int    ret;
    int    err = 0;
    char*  serverReadyFile = NULL;
    char*  alpnList = NULL;
    unsigned char alpn_opt = 0;
    char*  cipherList = NULL;
    int    useDefCipherList = 0;
    int    overrideDateErrors = 0;
    const char* verifyCert;
    const char* ourCert;
    const char* ourKey;
    const char* ourDhParam = dhParamFile;
    tcp_ready*  readySignal = NULL;
    int    argc = ((func_args*)args)->argc;
    char** argv = ((func_args*)args)->argv;

#ifdef WOLFSSL_TRUST_PEER_CERT
    const char* trustCert  = NULL;
#endif

#ifndef NO_PSK
    int sendPskIdentityHint = 1;
#endif

#ifdef HAVE_SNI
    char*  sniHostName = NULL;
#endif

#ifdef HAVE_TRUSTED_CA
    int trustedCaKeyId = 0;
#endif /* HAVE_TRUSTED_CA */

#ifdef HAVE_OCSP
    int    useOcsp  = 0;
    char*  ocspUrl  = NULL;
#endif

#ifdef HAVE_WNR
    const char* wnrConfigFile = wnrConfig;
#endif
    char buffer[WOLFSSL_MAX_ERROR_SZ];
#ifdef WOLFSSL_TLS13
    int noPskDheKe = 0;
#endif
    int updateKeysIVs = 0;
    int mutualAuth = 0;
    int postHandAuth = 0;
#ifdef WOLFSSL_EARLY_DATA
    int earlyData = 0;
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
    int scr = 0;
    int forceScr = 0;
#endif /* HAVE_SECURE_RENEGOTIATION */
#ifdef WOLFSSL_SEND_HRR_COOKIE
    int hrrCookie = 0;
#endif
    byte mcastID = 0;
#if !defined(NO_DH) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST) && !defined(WOLFSSL_OLD_PRIME_CHECK)
    int doDhKeyCheck = 1;
#endif

#ifdef WOLFSSL_STATIC_MEMORY
    #if (defined(HAVE_ECC) && !defined(ALT_ECC_SIZE)) \
        || defined(SESSION_CERTS)
        /* big enough to handle most cases including session certs */
        byte memory[204000];
    #else
        byte memory[80000];
    #endif
    byte memoryIO[34500]; /* max for IO buffer (TLS packet can be 16k) */
    WOLFSSL_MEM_CONN_STATS ssl_stats;
    #ifdef DEBUG_WOLFSSL
        WOLFSSL_MEM_STATS mem_stats;
    #endif
#endif
#ifdef WOLFSSL_TLS13
    int onlyKeyShare = 0;
    int noTicket = 0;
#endif
    int useX25519 = 0;
    int useX448 = 0;
    int exitWithRet = 0;
    int loadCertKeyIntoSSLObj = 0;

#ifdef HAVE_ENCRYPT_THEN_MAC
    int disallowETM = 0;
#endif

    ((func_args*)args)->return_code = -1; /* error state */

#ifndef NO_RSA
    verifyCert = cliCertFile;
    ourCert    = svrCertFile;
    ourKey     = svrKeyFile;
#else
    #ifdef HAVE_ECC
        verifyCert = cliEccCertFile;
        ourCert    = eccCertFile;
        ourKey     = eccKeyFile;
    #elif defined(HAVE_ED25519)
        verifyCert = cliEdCertFile;
        ourCert    = edCertFile;
        ourKey     = edKeyFile;
    #elif defined(HAVE_ED448)
        verifyCert = cliEd448CertFile;
        ourCert    = ed448CertFile;
        ourKey     = ed448KeyFile;
    #else
        verifyCert = NULL;
        ourCert    = NULL;
        ourKey     = NULL;
    #endif
#endif

    (void)needDH;
    (void)ourKey;
    (void)ourCert;
    (void)ourDhParam;
    (void)verifyCert;
    (void)useNtruKey;
    (void)doCliCertCheck;
    (void)minDhKeyBits;
    (void)minRsaKeyBits;
    (void)minEccKeyBits;
    (void)alpnList;
    (void)alpn_opt;
    (void)crlFlags;
    (void)readySignal;
    (void)updateKeysIVs;
    (void)mutualAuth;
    (void)postHandAuth;
    (void)mcastID;
    (void)loadCertKeyIntoSSLObj;
    (void)overrideDateErrors;
    (void)nonBlocking;

#ifdef WOLFSSL_TIRTOS
    fdOpenSession(Task_self());
#endif

#ifdef WOLFSSL_VXWORKS
    useAnyAddr = 1;
#else
    /* Not Used: h, z, F, T, V, W, X */
    while ((ch = mygetopt(argc, argv, "?:"
                "abc:defgijk:l:mnop:q:rstuv:wxy"
                "A:B:C:D:E:FGH:IJKL:MNO:PQR:S:TUVYZ:"
                "01:23:4:58")) != -1) {
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

            case 'x' :
                runWithErrors = 1;
                break;

            case 'd' :
                doCliCertCheck = 0;
                break;

            case 'V' :
                #ifdef HAVE_CRL
                    disableCRL = 1;
                #endif
                break;

            case 'b' :
                useAnyAddr = 1;
                break;

            case 's' :
                usePsk = 1;
                break;

            case 'j' :
                usePskPlus = 1;
                break;

            case 'n' :
                useNtruKey = 1;
                break;

            case 'u' :
                doDTLS  = 1;
                dtlsUDP = 1;
                break;

            case 'G' :
            #ifdef WOLFSSL_SCTP
                doDTLS  = 1;
                dtlsSCTP = 1;
            #endif
                break;

            case 'f' :
                fewerPackets = 1;
                break;

            case 'R' :
                serverReadyFile = myoptarg;
                break;

            case 'r' :
                #ifndef NO_SESSION_CACHE
                    resume = 1;
                #endif
                break;

            case 'P' :
            #ifdef HAVE_PK_CALLBACKS
                pkCallbacks = 1;
            #endif
                break;

            case 'p' :
                port = (word16)atoi(myoptarg);
                break;

            case 'w' :
                wc_shutdown = 1;
                break;

            case 'v' :
                if (myoptarg[0] == 'd') {
                    version = SERVER_DOWNGRADE_VERSION;
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
                else if (XSTRNCMP(myoptarg, "loadSSL", 7) == 0) {
                    printf("Also load cert/key into wolfSSL object\n");
                #ifndef NO_CERTS
                    loadCertKeyIntoSSLObj = 2;
                #endif
                }
                else if (XSTRNCMP(myoptarg, "loadSSLOnly", 11) == 0) {
                    printf("Only load cert/key into wolfSSL object\n");
                #ifndef NO_CERTS
                    loadCertKeyIntoSSLObj = 1;
                #endif
                }
                else if (XSTRNCMP(myoptarg, "disallowETM", 11) == 0) {
                    printf("Disallow Encrypt-Then-MAC\n");
                #ifdef HAVE_ENCRYPT_THEN_MAC
                    disallowETM = 1;
                #endif
                }
                else if (XSTRNCMP(myoptarg, "overrideDateErr", 15) == 0) {
                #if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
                    overrideDateErrors = 1;
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

            case 'D' :
                #ifndef NO_DH
                    ourDhParam = myoptarg;
                #endif
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

            case 'N':
                nonBlocking = 1;
                break;

            case 'S' :
                #ifdef HAVE_SNI
                    sniHostName = myoptarg;
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
            case 'I':
                #ifndef NO_PSK
                    sendPskIdentityHint = 0;
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

            case 'i' :
                loops = -1;
                break;

            case 'C' :
                loops = atoi(myoptarg);
                if (loops <= 0) {
                    Usage();
                    XEXIT_T(MY_EX_USAGE);
                }
                break;

            case 'e' :
                echoData = 1;
                break;

            case 'B':
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

            #ifdef WOLFSSL_TRUST_PEER_CERT
            case 'E' :
                 trustCert = myoptarg;
                break;
            #endif

            case 'q' :
                #ifdef HAVE_WNR
                    wnrConfigFile = myoptarg;
                #endif
                break;

            case 'g' :
                useWebServerMsg = 1;
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

            case 't' :
                #ifdef HAVE_CURVE25519
                    useX25519 = 1;
                    #if defined(WOLFSSL_TLS13) && defined(HAVE_ECC)
                        onlyKeyShare = 2;
                    #endif
                #endif
                break;

            case 'K' :
                #ifdef WOLFSSL_TLS13
                    noPskDheKe = 1;
                #endif
                break;

            case 'T' :
                #if defined(WOLFSSL_TLS13) && defined(HAVE_SESSION_TICKET)
                    noTicket = 1;
                #endif
                break;

            case 'U' :
                #ifdef WOLFSSL_TLS13
                    updateKeysIVs = 1;
                #endif
                break;

            case 'F' :
                    mutualAuth = 1;
                break;

            case 'Q' :
            #if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
                postHandAuth = 1;
                doCliCertCheck = 0;
            #endif
                break;

            case 'J' :
            #ifdef WOLFSSL_SEND_HRR_COOKIE
                hrrCookie = 1;
            #endif
                break;

            case 'M' :
            #ifdef HAVE_SECURE_RENEGOTIATION
                scr = 1;
            #endif /* HAVE_SECURE_RENEGOTIATION */
                break;

            case 'm' :
            #ifdef HAVE_SECURE_RENEGOTIATION
                scr = 1;
                forceScr = 1;
            #endif /* HAVE_SECURE_RENEGOTIATION */
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
                #ifdef WOLFSSL_DTLS
                    XMEMSET(&dtlsCtx, 0, sizeof(dtlsCtx));
                    doBlockSeq = 1;
                    dtlsCtx.blockSeq = atoi(myoptarg);
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
                    #if defined(WOLFSSL_TLS13) && defined(HAVE_ECC)
                        onlyKeyShare = 2;
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

    /* Can only use DTLS over UDP or SCTP, can't do both. */
    if (dtlsUDP && dtlsSCTP) {
        err_sys_ex(runWithErrors, "Cannot use DTLS with both UDP and SCTP.");
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
        err_sys_ex(runWithErrors, "can't load whitewood net random config "
                   "file");
#endif

    switch (version) {
#ifndef NO_OLD_TLS
    #ifdef WOLFSSL_ALLOW_SSLV3
        case 0:
            method = wolfSSLv3_server_method_ex;
            break;
    #endif

    #ifndef NO_TLS
        #ifdef WOLFSSL_ALLOW_TLSV10
        case 1:
            method = wolfTLSv1_server_method_ex;
            break;
        #endif

        case 2:
            method = wolfTLSv1_1_server_method_ex;
            break;
    #endif /* !NO_TLS */
#endif /* !NO_OLD_TLS */

#ifndef NO_TLS
    #ifndef WOLFSSL_NO_TLS12
        case 3:
            method = wolfTLSv1_2_server_method_ex;
            break;
    #endif

    #ifdef WOLFSSL_TLS13
        case 4:
            method = wolfTLSv1_3_server_method_ex;
            break;
    #endif

        case SERVER_DOWNGRADE_VERSION:
            method = wolfSSLv23_server_method_ex;
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
            method = wolfDTLSv1_server_method_ex;
            break;
    #endif

    #ifndef WOLFSSL_NO_TLS12
        case -2:
            method = wolfDTLSv1_2_server_method_ex;
            break;
    #endif
    #if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EITHER_SIDE)
        case -3:
            method = wolfDTLSv1_2_method_ex;
            break;
    #endif
#endif

        default:
            err_sys_ex(runWithErrors, "Bad SSL version");
    }

    if (method == NULL)
        err_sys_ex(runWithErrors, "unable to get method");

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

    if (wolfSSL_CTX_load_static_memory(&ctx, method, memory, sizeof(memory),0,1)
            != WOLFSSL_SUCCESS)
        err_sys_ex(catastrophic, "unable to load static memory and create ctx");

    /* load in a buffer for IO */
    if (wolfSSL_CTX_load_static_memory(&ctx, NULL, memoryIO, sizeof(memoryIO),
                                 WOLFMEM_IO_POOL_FIXED | WOLFMEM_TRACK_STATS, 1)
            != WOLFSSL_SUCCESS)
        err_sys_ex(catastrophic, "unable to load static memory and create ctx");
#else
    ctx = SSL_CTX_new(method(NULL));
#endif /* WOLFSSL_STATIC_MEMORY */
    if (ctx == NULL)
        err_sys_ex(catastrophic, "unable to get ctx");

#if defined(HAVE_SESSION_TICKET) && defined(HAVE_CHACHA) && \
                                    defined(HAVE_POLY1305)
    if (TicketInit() != 0)
        err_sys_ex(catastrophic, "unable to setup Session Ticket Key context");
    wolfSSL_CTX_set_TicketEncCb(ctx, myTicketEncCb);
#endif

    if (cipherList && !useDefCipherList) {
        if (SSL_CTX_set_cipher_list(ctx, cipherList) != WOLFSSL_SUCCESS)
            err_sys_ex(runWithErrors, "server can't set custom cipher list");
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

#ifdef WOLFSSL_SCTP
    if (dtlsSCTP)
        wolfSSL_CTX_dtls_set_sctp(ctx);
#endif

#ifdef WOLFSSL_ENCRYPTED_KEYS
    SSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#if !defined(NO_CERTS)
    if ((!usePsk || usePskPlus) && !useAnon && !(loadCertKeyIntoSSLObj == 1)) {
    #ifndef TEST_LOAD_BUFFER
        if (SSL_CTX_use_certificate_chain_file(ctx, ourCert)
                                         != WOLFSSL_SUCCESS)
            err_sys_ex(catastrophic, "can't load server cert file, check file "
                       "and run from wolfSSL home dir");
    #else
        /* loads cert chain file using buffer API */
        load_buffer(ctx, ourCert, WOLFSSL_CERT_CHAIN);
    #endif
    }
#endif

#ifndef NO_DH
    if (wolfSSL_CTX_SetMinDhKey_Sz(ctx, (word16)minDhKeyBits)
        != WOLFSSL_SUCCESS) {
        err_sys_ex(runWithErrors, "Error setting minimum DH key size");
    }
#endif
#ifndef NO_RSA
    if (wolfSSL_CTX_SetMinRsaKey_Sz(ctx, minRsaKeyBits) != WOLFSSL_SUCCESS){
        err_sys_ex(runWithErrors, "Error setting minimum RSA key size");
    }
#endif
#ifdef HAVE_ECC
    if (wolfSSL_CTX_SetMinEccKey_Sz(ctx, minEccKeyBits) != WOLFSSL_SUCCESS){
        err_sys_ex(runWithErrors, "Error setting minimum ECC key size");
    }
#endif

#ifdef HAVE_NTRU
    if (useNtruKey) {
        if (wolfSSL_CTX_use_NTRUPrivateKey_file(ctx, ourKey)
                                != WOLFSSL_SUCCESS)
            err_sys_ex(catastrophic, "can't load ntru key file, "
                    "Please run from wolfSSL home dir");
    }
#endif
#if !defined(NO_CERTS)
    #ifdef HAVE_PK_CALLBACKS
        pkCbInfo.ourKey = ourKey;
    #endif
    if (!useNtruKey && (!usePsk || usePskPlus) && !useAnon
        && !(loadCertKeyIntoSSLObj == 1)
    #if defined(HAVE_PK_CALLBACKS) && defined(TEST_PK_PRIVKEY)
        && !pkCallbacks
    #endif /* HAVE_PK_CALLBACKS && TEST_PK_PRIVKEY */
    ) {
    #ifndef TEST_LOAD_BUFFER
        if (SSL_CTX_use_PrivateKey_file(ctx, ourKey, WOLFSSL_FILETYPE_PEM)
                                         != WOLFSSL_SUCCESS)
            err_sys_ex(catastrophic, "can't load server private key file, "
                       "check file and run from wolfSSL home dir");
    #else
        /* loads private key file using buffer API */
        load_buffer(ctx, ourKey, WOLFSSL_KEY);
    #endif
    }
#endif

    if (usePsk || usePskPlus) {
#ifndef NO_PSK
        SSL_CTX_set_psk_server_callback(ctx, my_psk_server_cb);
    #ifdef WOLFSSL_TLS13
        wolfSSL_CTX_set_psk_server_tls13_callback(ctx, my_psk_server_tls13_cb);
    #endif

        if (sendPskIdentityHint == 1)
            SSL_CTX_use_psk_identity_hint(ctx, "cyassl server");

        if (cipherList == NULL && !usePskPlus) {
            const char *defaultCipherList;
        #if defined(HAVE_AESGCM) && !defined(NO_DH)
            #ifdef WOLFSSL_TLS13
                defaultCipherList = "DHE-PSK-AES128-GCM-SHA256:"
                                    "TLS13-AES128-GCM-SHA256";
            #else
                defaultCipherList = "DHE-PSK-AES128-GCM-SHA256";
            #endif
                needDH = 1;
        #elif defined(HAVE_NULL_CIPHER)
                defaultCipherList = "PSK-NULL-SHA256";
        #else
                defaultCipherList = "PSK-AES128-CBC-SHA256";
        #endif
            if (SSL_CTX_set_cipher_list(ctx, defaultCipherList)
                != WOLFSSL_SUCCESS)
                err_sys_ex(runWithErrors, "server can't set cipher list 2");
        }
#endif
    }
#ifndef NO_CERTS
    if (mutualAuth)
        wolfSSL_CTX_mutual_auth(ctx, 1);
#endif


#ifdef HAVE_ECC
    /* Use ECDHE key size that matches long term key.
     * Zero means use ctx->privateKeySz.
     * Default ECDHE_SIZE is 32 bytes
     */
    if (wolfSSL_CTX_SetTmpEC_DHE_Sz(ctx, 0) != WOLFSSL_SUCCESS){
        err_sys_ex(runWithErrors, "Error setting ECDHE size");
    }
#endif

    if (useAnon) {
#ifdef HAVE_ANON
        wolfSSL_CTX_allow_anon_cipher(ctx);
        if (cipherList == NULL || (cipherList && useDefCipherList)) {
            const char* defaultCipherList;
            defaultCipherList = "ADH-AES256-GCM-SHA384:"
                                "ADH-AES128-SHA";
            if (SSL_CTX_set_cipher_list(ctx, defaultCipherList)
                                                            != WOLFSSL_SUCCESS)
                err_sys_ex(runWithErrors, "server can't set cipher list 4");
        }
#endif
    }

#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    /* if not using PSK, verify peer with certs
       if using PSK Plus then verify peer certs except PSK suites */
    if (doCliCertCheck && (usePsk == 0 || usePskPlus) && useAnon == 0) {
        unsigned int verify_flags = 0;
        SSL_CTX_set_verify(ctx, WOLFSSL_VERIFY_PEER |
                            (usePskPlus ? WOLFSSL_VERIFY_FAIL_EXCEPT_PSK :
                                WOLFSSL_VERIFY_FAIL_IF_NO_PEER_CERT),
                            overrideDateErrors == 1 ? myDateCb : NULL);

    #ifdef TEST_BEFORE_DATE
        verify_flags |= WOLFSSL_LOAD_FLAG_DATE_ERR_OKAY;
    #endif

        if (wolfSSL_CTX_load_verify_locations_ex(ctx, verifyCert, 0,
            verify_flags) != WOLFSSL_SUCCESS) {
            err_sys_ex(catastrophic,
                       "can't load ca file, Please run from wolfSSL home dir");
        }
        #ifdef WOLFSSL_TRUST_PEER_CERT
        if (trustCert) {
            if ((ret = wolfSSL_CTX_trust_peer_cert(ctx, trustCert,
                                                   WOLFSSL_FILETYPE_PEM))
                                                   != WOLFSSL_SUCCESS) {
                err_sys_ex(runWithErrors, "can't load trusted peer cert file");
            }
        }
        #endif /* WOLFSSL_TRUST_PEER_CERT */
   }
#endif

#if defined(WOLFSSL_SNIFFER)
    /* don't use EDH, can't sniff tmp keys */
    if (cipherList == NULL) {
        if (SSL_CTX_set_cipher_list(ctx, "AES128-SHA") != WOLFSSL_SUCCESS)
            err_sys_ex(runWithErrors, "server can't set cipher list 3");
    }
#endif

#ifdef HAVE_SNI
    if (sniHostName)
        if (wolfSSL_CTX_UseSNI(ctx, WOLFSSL_SNI_HOST_NAME, sniHostName,
                    (word16) XSTRLEN(sniHostName)) != WOLFSSL_SUCCESS)
            err_sys_ex(runWithErrors, "UseSNI failed");
#endif

#ifdef USE_WINDOWS_API
    if (port == 0) {
        /* Generate random port for testing */
        port = GetRandomPort();
    }
#endif /* USE_WINDOWS_API */

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfAsync_DevOpen(&devId);
    if (ret < 0) {
        printf("Async device open failed\nRunning without async\n");
    }
    wolfSSL_CTX_UseAsync(ctx, devId);
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifdef WOLFSSL_TLS13
    if (noPskDheKe)
        wolfSSL_CTX_no_dhe_psk(ctx);
    if (noTicket)
        wolfSSL_CTX_no_ticket_TLSv13(ctx);
#endif

    while (1) {
        /* allow resume option */
        if (resumeCount > 1) {
            if (dtlsUDP == 0) {
                SOCKADDR_IN_T client;
                socklen_t client_len = sizeof(client);
                clientfd = accept(sockfd, (struct sockaddr*)&client,
                                 (ACCEPT_THIRD_T)&client_len);
            }
            else {
                tcp_listen(&sockfd, &port, useAnyAddr, dtlsUDP, dtlsSCTP);
                clientfd = sockfd;
            }
            if (WOLFSSL_SOCKET_IS_INVALID(clientfd)) {
                err_sys_ex(runWithErrors, "tcp accept failed");
            }
        }
#if defined(WOLFSSL_STATIC_MEMORY) && defined(DEBUG_WOLFSSL)
        fprintf(stderr, "Before creating SSL\n");
        if (wolfSSL_CTX_is_static_memory(ctx, &mem_stats) != 1)
            err_sys_ex(runWithErrors, "ctx not using static memory");
        if (wolfSSL_PrintStats(&mem_stats) != 1) /* function in test.h */
            err_sys_ex(runWithErrors, "error printing out memory stats");
#endif

    if (doMcast) {
#ifdef WOLFSSL_MULTICAST
        wolfSSL_CTX_mcast_set_member_id(ctx, mcastID);
        if (wolfSSL_CTX_set_cipher_list(ctx, "WDM-NULL-SHA256")
            != WOLFSSL_SUCCESS)
            err_sys("Couldn't set multicast cipher list.");
#endif
    }

    if (doDTLS && dtlsUDP) {
#ifdef WOLFSSL_DTLS
        if (doBlockSeq) {
            wolfSSL_CTX_SetIOSend(ctx, TestEmbedSendTo);
        }
#endif
    }

#ifdef HAVE_PK_CALLBACKS
        if (pkCallbacks)
            SetupPkCallbacks(ctx);
#endif

        ssl = SSL_new(ctx);
        if (ssl == NULL)
            err_sys_ex(catastrophic, "unable to create an SSL object");
        #ifdef OPENSSL_EXTRA
        wolfSSL_KeepArrays(ssl);
        #endif

    /* Support for loading private key and cert using WOLFSSL object */
#if !defined(NO_CERTS)
    if ((!usePsk || usePskPlus) && !useAnon && loadCertKeyIntoSSLObj) {
    #ifndef TEST_LOAD_BUFFER
        if (SSL_use_certificate_chain_file(ssl, ourCert)
                                         != WOLFSSL_SUCCESS)
            err_sys_ex(catastrophic, "can't load server cert file, check file "
                       "and run from wolfSSL home dir");
    #else
        /* loads cert chain file using buffer API */
        load_ssl_buffer(ssl, ourCert, WOLFSSL_CERT_CHAIN);
    #endif
    }

    if (!useNtruKey && (!usePsk || usePskPlus) && !useAnon &&
        loadCertKeyIntoSSLObj
    #if defined(HAVE_PK_CALLBACKS) && defined(TEST_PK_PRIVKEY)
        && !pkCallbacks
    #endif /* HAVE_PK_CALLBACKS && TEST_PK_PRIVKEY */
    ) {
    #ifndef TEST_LOAD_BUFFER
        if (SSL_use_PrivateKey_file(ssl, ourKey, WOLFSSL_FILETYPE_PEM)
                                         != WOLFSSL_SUCCESS)
            err_sys_ex(catastrophic, "can't load server private key file, check"
                       "file and run from wolfSSL home dir");
    #else
        /* loads private key file using buffer API */
        load_ssl_buffer(ssl, ourKey, WOLFSSL_KEY);
    #endif
    }
#endif /* !NO_CERTS */

#ifdef WOLFSSL_SEND_HRR_COOKIE
        if (hrrCookie && wolfSSL_send_hrr_cookie(ssl, NULL, 0)
            != WOLFSSL_SUCCESS) {
            err_sys("unable to set use of cookie with HRR msg");
        }
#endif

#if defined(WOLFSSL_STATIC_MEMORY) && defined(DEBUG_WOLFSSL)
        fprintf(stderr, "After creating SSL\n");
        if (wolfSSL_CTX_is_static_memory(ctx, &mem_stats) != 1)
            err_sys_ex(runWithErrors, "ctx not using static memory");
        if (wolfSSL_PrintStats(&mem_stats) != 1) /* function in test.h */
            err_sys_ex(runWithErrors, "error printing out memory stats");
#endif

    if (doMcast) {
#ifdef WOLFSSL_MULTICAST
        byte pms[512];
        byte cr[32];
        byte sr[32];
        const byte suite[2] = {0, 0xfe};  /* WDM_WITH_NULL_SHA256 */

        XMEMSET(pms, 0x23, sizeof(pms));
        XMEMSET(cr, 0xA5, sizeof(cr));
        XMEMSET(sr, 0x5A, sizeof(sr));

        if (wolfSSL_set_secret(ssl, 1, pms, sizeof(pms), cr, sr, suite)
                != WOLFSSL_SUCCESS)
            err_sys("unable to set mcast secret");
#endif
    }

#ifdef HAVE_SECURE_RENEGOTIATION
        if (scr) {
            if (wolfSSL_UseSecureRenegotiation(ssl) != WOLFSSL_SUCCESS) {
                err_sys_ex(runWithErrors, "can't enable secure renegotiation");
            }
        }
#endif /* HAVE_SECURE_RENEGOTIATION */

#ifndef NO_HANDSHAKE_DONE_CB
        wolfSSL_SetHsDoneCb(ssl, myHsDoneCb, NULL);
#endif
#ifdef HAVE_CRL
    if (!disableCRL) {
#ifdef HAVE_CRL_MONITOR
        crlFlags = WOLFSSL_CRL_MONITOR | WOLFSSL_CRL_START_MON;
#endif
        if (wolfSSL_EnableCRL(ssl, 0) != WOLFSSL_SUCCESS)
            err_sys_ex(runWithErrors, "unable to enable CRL");
        if (wolfSSL_LoadCRL(ssl, crlPemDir, WOLFSSL_FILETYPE_PEM, crlFlags)
                            != WOLFSSL_SUCCESS)
            err_sys_ex(runWithErrors, "unable to load CRL");
        if (wolfSSL_SetCRL_Cb(ssl, CRL_CallBack) != WOLFSSL_SUCCESS)
            err_sys_ex(runWithErrors, "unable to set CRL callback url");
    }
#endif
#ifdef HAVE_OCSP
        if (useOcsp) {
            if (ocspUrl != NULL) {
                wolfSSL_CTX_SetOCSP_OverrideURL(ctx, ocspUrl);
                wolfSSL_CTX_EnableOCSP(ctx, WOLFSSL_OCSP_NO_NONCE
                                                   | WOLFSSL_OCSP_URL_OVERRIDE);
            }
            else
                wolfSSL_CTX_EnableOCSP(ctx, WOLFSSL_OCSP_NO_NONCE);
        }
#ifndef NO_RSA
    /* All the OSCP Stapling test certs are RSA. */
#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
    || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
        { /* scope start */
            const char* ca1 = "certs/ocsp/intermediate1-ca-cert.pem";
            const char* ca2 = "certs/ocsp/intermediate2-ca-cert.pem";
            const char* ca3 = "certs/ocsp/intermediate3-ca-cert.pem";
            int fails = 0;

            if (wolfSSL_CTX_EnableOCSPStapling(ctx) != WOLFSSL_SUCCESS) {
                err_sys_ex(catastrophic, "can't enable OCSP Stapling "
                           "Certificate Manager");
            }
            if (SSL_CTX_load_verify_locations(ctx, ca1, 0) != WOLFSSL_SUCCESS) {
                fails++;
                err_sys_ex(runWithErrors, "can't load ca file, Please run from "
                           "wolfSSL home dir");
            }
            if (SSL_CTX_load_verify_locations(ctx, ca2, 0) != WOLFSSL_SUCCESS) {
                fails++;
                err_sys_ex(runWithErrors, "can't load ca file, Please run from "
                           "wolfSSL home dir");
            }
            if (SSL_CTX_load_verify_locations(ctx, ca3, 0) != WOLFSSL_SUCCESS) {
                fails++;
                err_sys_ex(runWithErrors, "can't load ca file, Please run from "
                           "wolfSSL home dir");
            }
            if (fails > 2) {
                err_sys_ex(catastrophic, "Failed to load any intermediates for "
                           "OCSP stapling test");
            }
        } /* scope end */
#endif /* HAVE_CERTIFICATE_STATUS_REQUEST HAVE_CERTIFICATE_STATUS_REQUEST_V2 */
#endif /* NO_RSA */
#endif /* HAVE_OCSP */

#ifdef HAVE_PK_CALLBACKS
        if (pkCallbacks)
            SetupPkCallbackContexts(ssl, &pkCbInfo);
#endif

    #ifdef WOLFSSL_TLS13
        if (version >= 4) {
            WOLFSSL_START(WC_FUNC_CLIENT_KEY_EXCHANGE_DO);
            if (onlyKeyShare == 2) {
                if (useX25519 == 1) {
        #ifdef HAVE_CURVE25519
                    int groups[1] = { WOLFSSL_ECC_X25519 };

                    if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X25519)
                                                           != WOLFSSL_SUCCESS) {
                        err_sys("unable to use curve x25519");
                    }
                    if (wolfSSL_set_groups(ssl, groups, 1) != WOLFSSL_SUCCESS) {
                        err_sys("unable to set groups: x25519");
                    }
        #endif
                }
                else if (useX448 == 1) {
        #ifdef HAVE_CURVE448
                    int groups[1] = { WOLFSSL_ECC_X448 };

                    if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_X448)
                                                           != WOLFSSL_SUCCESS) {
                        err_sys("unable to use curve x448");
                    }
                    if (wolfSSL_set_groups(ssl, groups, 1) != WOLFSSL_SUCCESS) {
                        err_sys("unable to set groups: x448");
                    }
        #endif
                }
                else {
        #ifdef HAVE_ECC
            #if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
                    int groups[1] = { WOLFSSL_ECC_SECP256R1 };

                    if (wolfSSL_UseKeyShare(ssl, WOLFSSL_ECC_SECP256R1)
                                                           != WOLFSSL_SUCCESS) {
                        err_sys("unable to use curve secp256r1");
                    }
                    if (wolfSSL_set_groups(ssl, groups, 1) != WOLFSSL_SUCCESS) {
                        err_sys("unable to set groups: secp256r1");
                    }
            #endif
        #endif
                }
            }
            else if (onlyKeyShare == 1) {
        #ifdef HAVE_FFDHE_2048
                int groups[1] = { WOLFSSL_FFDHE_2048 };

                if (wolfSSL_UseKeyShare(ssl, WOLFSSL_FFDHE_2048)
                                                           != WOLFSSL_SUCCESS) {
                    err_sys("unable to use DH 2048-bit parameters");
                }
                if (wolfSSL_set_groups(ssl, groups, 1) != WOLFSSL_SUCCESS) {
                    err_sys("unable to set groups: DH 2048-bit");
                }
        #endif
            }
            WOLFSSL_END(WC_FUNC_CLIENT_KEY_EXCHANGE_DO);
        }
    #endif

    #ifdef HAVE_ENCRYPT_THEN_MAC
        if (disallowETM)
            wolfSSL_AllowEncryptThenMac(ssl, 0);
    #endif


        /* do accept */
        readySignal = ((func_args*)args)->signal;
        if (readySignal) {
            readySignal->srfName = serverReadyFile;
        }
        tcp_accept(&sockfd, &clientfd, (func_args*)args, port, useAnyAddr,
                       dtlsUDP, dtlsSCTP, serverReadyFile ? 1 : 0, doListen);
        doListen = 0; /* Don't listen next time */

        if (SSL_set_fd(ssl, clientfd) != WOLFSSL_SUCCESS) {
            err_sys_ex(catastrophic, "error in setting fd");
        }

#ifdef HAVE_TRUSTED_CA
        if (trustedCaKeyId) {
            if (wolfSSL_UseTrustedCA(ssl, WOLFSSL_TRUSTED_CA_PRE_AGREED,
                        NULL, 0) != WOLFSSL_SUCCESS) {
                err_sys_ex(runWithErrors, "UseTrustedCA failed");
            }
        }
#endif /* HAVE_TRUSTED_CA */

#ifdef HAVE_ALPN
        if (alpnList != NULL) {
            printf("ALPN accepted protocols list : %s\n", alpnList);
            wolfSSL_UseALPN(ssl, alpnList, (word32)XSTRLEN(alpnList), alpn_opt);
        }
#endif

#ifdef WOLFSSL_DTLS
        if (doDTLS && dtlsUDP) {
            SOCKADDR_IN_T cliaddr;
            byte          b[1500];
            int           n;
            socklen_t     len = sizeof(cliaddr);

            /* For DTLS, peek at the next datagram so we can get the client's
             * address and set it into the ssl object later to generate the
             * cookie. */
            n = (int)recvfrom(clientfd, (char*)b, sizeof(b), MSG_PEEK,
                              (struct sockaddr*)&cliaddr, &len);
            if (n <= 0)
                err_sys_ex(runWithErrors, "recvfrom failed");

            if (doBlockSeq) {
                XMEMCPY(&dtlsCtx.peer.sa, &cliaddr, len);
                dtlsCtx.peer.sz = len;
                dtlsCtx.wfd = clientfd;
                dtlsCtx.failOnce = 1;

                wolfSSL_SetIOWriteCtx(ssl, &dtlsCtx);
            }
            else {
                wolfSSL_dtls_set_peer(ssl, &cliaddr, len);
            }
        }
#endif
        if ((usePsk == 0 || usePskPlus) || useAnon == 1 || cipherList != NULL
                                                               || needDH == 1) {
            #if !defined(NO_FILESYSTEM) && !defined(NO_DH) && !defined(NO_ASN)
                wolfSSL_SetTmpDH_file(ssl, ourDhParam, WOLFSSL_FILETYPE_PEM);
            #elif !defined(NO_DH)
                SetDH(ssl);  /* repick suites with DHE, higher priority than
                              * PSK */
            #endif
#if !defined(NO_DH) && !defined(WOLFSSL_OLD_PRIME_CHECK) && \
    !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
            if (!doDhKeyCheck)
                wolfSSL_SetEnableDhKeyTest(ssl, 0);
#endif
        }

#ifndef WOLFSSL_CALLBACKS
        if (nonBlocking) {
            #ifdef WOLFSSL_DTLS
            if (doDTLS) {
                wolfSSL_dtls_set_using_nonblock(ssl, 1);
            }
            #endif
            tcp_set_nonblocking(&clientfd);

            ret = NonBlockingSSL_Accept(ssl);
        }
        else {
    #ifdef WOLFSSL_EARLY_DATA
            if (earlyData) {
                do {
                    int len;
                    err = 0; /* reset error */
                    ret = wolfSSL_read_early_data(ssl, input, sizeof(input)-1,
                                                                          &len);
                    if (ret != WOLFSSL_SUCCESS) {
                        err = SSL_get_error(ssl, 0);
                    #ifdef WOLFSSL_ASYNC_CRYPT
                        if (err == WC_PENDING_E) {
                            ret = wolfSSL_AsyncPoll(ssl,
                                                    WOLF_POLL_FLAG_CHECK_HW);
                            if (ret < 0) break;
                        }
                    #endif
                    }
                    if (ret > 0) {
                        input[ret] = 0; /* null terminate message */
                        printf("Early Data Client message: %s\n", input);
                    }
                } while (err == WC_PENDING_E || ret > 0);
            }
    #endif
            do {
                err = 0; /* reset error */
                ret = SSL_accept(ssl);
                if (ret != WOLFSSL_SUCCESS) {
                    err = SSL_get_error(ssl, 0);
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
        ret = NonBlockingSSL_Accept(ssl);
#endif
        if (ret != WOLFSSL_SUCCESS) {
            err = SSL_get_error(ssl, 0);
            printf("SSL_accept error %d, %s\n", err,
                                                ERR_error_string(err, buffer));
            if (!exitWithRet) {
                err_sys_ex(runWithErrors, "SSL_accept failed");
            } else {
                /* cleanup */
                SSL_free(ssl); ssl = NULL;
                SSL_CTX_free(ctx); ctx = NULL;
                CloseSocket(clientfd);
                CloseSocket(sockfd);
                ((func_args*)args)->return_code = err;
                goto exit;
            }
        }

        showPeerEx(ssl, lng_index);
        if (SSL_state(ssl) != 0) {
            err_sys_ex(runWithErrors, "SSL in error state");
        }

#ifdef OPENSSL_EXTRA
    {
        byte*  rnd;
        byte*  pt;
        size_t size;

        /* get size of buffer then print */
        size = wolfSSL_get_server_random(NULL, NULL, 0);
        if (size == 0) {
            err_sys_ex(runWithErrors, "error getting server random buffer "
                       "size");
        }

        rnd = (byte*)XMALLOC(size, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (rnd == NULL) {
            err_sys_ex(runWithErrors, "error creating server random buffer");
        }

        size = wolfSSL_get_server_random(ssl, rnd, size);
        if (size == 0) {
            if (rnd) {
                XFREE(rnd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                rnd = NULL;
            }
            err_sys_ex(runWithErrors, "error getting server random buffer");
        }

        if (rnd) {
            printf("Server Random : ");
            for (pt = rnd; pt < rnd + size; pt++) printf("%02X", *pt);
            printf("\n");

            XFREE(rnd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            rnd = NULL;
        }
    }
#endif

#ifdef HAVE_ALPN
        if (alpnList != NULL) {
            char *protocol_name = NULL, *list = NULL;
            word16 protocol_nameSz = 0, listSz = 0;

            err = wolfSSL_ALPN_GetProtocol(ssl, &protocol_name,
                                           &protocol_nameSz);
            if (err == WOLFSSL_SUCCESS)
                printf("Sent ALPN protocol : %s (%d)\n",
                       protocol_name, protocol_nameSz);
            else if (err == WOLFSSL_ALPN_NOT_FOUND)
                printf("No ALPN response sent (no match)\n");
            else
                printf("Getting ALPN protocol name failed\n");

            err = wolfSSL_ALPN_GetPeerProtocol(ssl, &list, &listSz);
            if (err == WOLFSSL_SUCCESS)
                printf("List of protocol names sent by Client: %s (%d)\n",
                       list, listSz);
            else
                printf("Get list of client's protocol name failed\n");

            free(list);
        }
#endif

#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    #if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
        if (postHandAuth) {
            unsigned int verify_flags = 0;

            SSL_set_verify(ssl, WOLFSSL_VERIFY_PEER |
                                ((usePskPlus) ? WOLFSSL_VERIFY_FAIL_EXCEPT_PSK :
                                WOLFSSL_VERIFY_FAIL_IF_NO_PEER_CERT), 0);

        #ifdef TEST_BEFORE_DATE
            verify_flags |= WOLFSSL_LOAD_FLAG_DATE_ERR_OKAY;
        #endif

            if (wolfSSL_CTX_load_verify_locations_ex(ctx, verifyCert, 0,
                                                     verify_flags)
                                                     != WOLFSSL_SUCCESS) {
                err_sys_ex(runWithErrors, "can't load ca file, Please run from "
                                          "wolfSSL home dir");
            }
            #ifdef WOLFSSL_TRUST_PEER_CERT
            if (trustCert) {
                if ((ret = wolfSSL_trust_peer_cert(ssl, trustCert,
                                    WOLFSSL_FILETYPE_PEM)) != WOLFSSL_SUCCESS) {
                    err_sys_ex(runWithErrors, "can't load trusted peer cert "
                                              "file");
                }
            }
            #endif /* WOLFSSL_TRUST_PEER_CERT */
       }
    #endif
#endif

        if (echoData == 0 && throughput == 0) {
            ServerRead(ssl, input, sizeof(input)-1);
            err = SSL_get_error(ssl, 0);
        }

#if defined(HAVE_SECURE_RENEGOTIATION) && \
    defined(HAVE_SERVER_RENEGOTIATION_INFO)
        if (scr && forceScr) {
            if (nonBlocking) {
                printf("not doing secure renegotiation on example with"
                       " nonblocking yet\n");
            } else {
                if (wolfSSL_Rehandshake(ssl) != WOLFSSL_SUCCESS) {
                    printf("not doing secure renegotiation\n");
                }
                else {
                    printf("RENEGOTIATION SUCCESSFUL\n");
                }
            }
        }
#endif /* HAVE_SECURE_RENEGOTIATION */

        if (err == 0 && echoData == 0 && throughput == 0) {
            const char* write_msg;
            int write_msg_sz;

#ifdef WOLFSSL_TLS13
            if (updateKeysIVs)
                wolfSSL_update_keys(ssl);
#endif
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
            if (postHandAuth)
                wolfSSL_request_certificate(ssl);
#endif

            /* Write data */
            if (!useWebServerMsg) {
                write_msg = msg;
                write_msg_sz = sizeof(msg);
            }
            else {
                write_msg = webServerMsg;
                write_msg_sz = sizeof(webServerMsg);
            }
            ServerWrite(ssl, write_msg, write_msg_sz);

#ifdef WOLFSSL_TLS13
            if (updateKeysIVs || postHandAuth)
                ServerRead(ssl, input, sizeof(input)-1);
#endif
        }
        else if (err == 0 || err == WOLFSSL_ERROR_ZERO_RETURN) {
            ServerEchoData(ssl, clientfd, echoData, block, throughput);
        }

#if defined(WOLFSSL_MDK_SHELL) && defined(HAVE_MDK_RTX)
        os_dly_wait(500) ;
#elif defined (WOLFSSL_TIRTOS)
        Task_yield();
#endif

        if (dtlsUDP == 0) {
            ret = SSL_shutdown(ssl);
            if (wc_shutdown && ret == WOLFSSL_SHUTDOWN_NOT_DONE) {
                ret = SSL_shutdown(ssl); /* bidirectional shutdown */
                if (ret == WOLFSSL_SUCCESS)
                    printf("Bidirectional shutdown complete\n");
            }
        }

        /* display collected statistics */
#ifdef WOLFSSL_STATIC_MEMORY
        if (wolfSSL_is_static_memory(ssl, &ssl_stats) != 1)
            err_sys_ex(runWithErrors, "static memory was not used with ssl");

        fprintf(stderr, "\nprint off SSL memory stats\n");
        fprintf(stderr, "*** This is memory state before wolfSSL_free is "
                "called\n");
        fprintf(stderr, "peak connection memory = %d\n", ssl_stats.peakMem);
        fprintf(stderr, "current memory in use  = %d\n", ssl_stats.curMem);
        fprintf(stderr, "peak connection allocs = %d\n", ssl_stats.peakAlloc);
        fprintf(stderr, "current connection allocs = %d\n",ssl_stats.curAlloc);
        fprintf(stderr, "total connection allocs   = %d\n",
                ssl_stats.totalAlloc);
        fprintf(stderr, "total connection frees    = %d\n\n",
                ssl_stats.totalFr);

#endif
        SSL_free(ssl); ssl = NULL;

        CloseSocket(clientfd);

        if (resume == 1 && resumeCount == 0) {
            resumeCount++;           /* only do one resume for testing */
            continue;
        }
        resumeCount = 0;

        cnt++;
        if (loops > 0 && --loops == 0) {
            break;  /* out of while loop, done with normal and resume option */
        }
    } /* while(1) */

    WOLFSSL_TIME(cnt);
    (void)cnt;

#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
 || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
    wolfSSL_CTX_DisableOCSPStapling(ctx);
#endif

    CloseSocket(sockfd);
    SSL_CTX_free(ctx); ctx = NULL;

    ((func_args*)args)->return_code = 0;

exit:

#if defined(HAVE_ECC) && defined(FP_ECC) && defined(HAVE_THREAD_LS) \
                      && (defined(NO_MAIN_DRIVER) || defined(HAVE_STACK_SIZE))
    wc_ecc_fp_free();  /* free per thread cache */
#endif

#ifdef WOLFSSL_TIRTOS
    fdCloseSession(Task_self());
#endif

#if defined(HAVE_SESSION_TICKET) && defined(HAVE_CHACHA) && \
                                    defined(HAVE_POLY1305)
    TicketCleanup();
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    wolfAsync_DevClose(&devId);
#endif

    /* There are use cases  when these assignments are not read. To avoid
     * potential confusion those warnings have been handled here.
     */
    (void) ourKey;
    (void) verifyCert;
    (void) doCliCertCheck;
    (void) useNtruKey;
    (void) ourDhParam;
    (void) ourCert;
    (void) useX25519;
    (void) useX448;
#ifdef HAVE_SECURE_RENEGOTIATION
    (void) forceScr;
#endif
#ifndef WOLFSSL_TIRTOS
    return 0;
#endif
}

#endif /* !NO_WOLFSSL_SERVER */


/* so overall tests can pull in test function */
#ifndef NO_MAIN_DRIVER

    int main(int argc, char** argv)
    {
        func_args args;
        tcp_ready ready;


        StartTCP();

        args.argc = argc;
        args.argv = argv;
        args.signal = &ready;
        args.return_code = 0;
        InitTcpReady(&ready);

#if defined(DEBUG_WOLFSSL) && !defined(WOLFSSL_MDK_SHELL)
        wolfSSL_Debugging_ON();
#endif
        wolfSSL_Init();
        ChangeToWolfRoot();

#ifndef NO_WOLFSSL_SERVER
#ifdef HAVE_STACK_SIZE
        StackSizeCheck(&args, server_test);
#else
        server_test(&args);
#endif
#else
        printf("Server not compiled in!\n");
#endif

        wolfSSL_Cleanup();
        FreeTcpReady(&ready);

#ifdef HAVE_WNR
    if (wc_FreeNetRandom() < 0)
        err_sys_ex(runWithErrors, "Failed to free netRandom context");
#endif /* HAVE_WNR */

        return args.return_code;
    }

    int myoptind = 0;
    char* myoptarg = NULL;

#endif /* NO_MAIN_DRIVER */
