/* test.h */

#ifndef CyaSSL_TEST_H
#define CyaSSL_TEST_H

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <ctype.h>
#include <cyassl/ssl.h>
#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/error-crypt.h>

#ifdef ATOMIC_USER
    #include <cyassl/ctaocrypt/aes.h>
    #include <cyassl/ctaocrypt/arc4.h>
    #include <cyassl/ctaocrypt/hmac.h>
#endif
#ifdef HAVE_PK_CALLBACKS
    #include <cyassl/ctaocrypt/random.h>
    #include <cyassl/ctaocrypt/asn.h>
    #ifdef HAVE_ECC
        #include <cyassl/ctaocrypt/ecc.h>
    #endif /* HAVE_ECC */
#endif /*HAVE_PK_CALLBACKS */

#ifdef USE_WINDOWS_API 
    #include <winsock2.h>
    #include <process.h>
    #ifdef TEST_IPV6            /* don't require newer SDK for IPV4 */
        #include <ws2tcpip.h>
        #include <wspiapi.h>
    #endif
    #define SOCKET_T SOCKET
    #define SNPRINTF _snprintf
#elif defined(CYASSL_MDK_ARM)
    #include <string.h>
#else
    #include <string.h>
    #include <sys/types.h>
#ifndef CYASSL_LEANPSK
    #include <unistd.h>
    #include <netdb.h>
    #include <netinet/in.h>
    #include <netinet/tcp.h>
    #include <arpa/inet.h>
    #include <sys/ioctl.h>
    #include <sys/time.h>
    #include <sys/socket.h>
    #include <pthread.h>
    #include <fcntl.h>
    #ifdef TEST_IPV6
        #include <netdb.h>
    #endif
#endif
    #define SOCKET_T int
    #ifndef SO_NOSIGPIPE
        #include <signal.h>  /* ignore SIGPIPE */
    #endif
    #define SNPRINTF snprintf
#endif /* USE_WINDOWS_API */

#ifdef HAVE_CAVIUM
    #include "cavium_sysdep.h"
    #include "cavium_common.h"
    #include "cavium_ioctl.h"
#endif

#ifdef _MSC_VER
    /* disable conversion warning */
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable:4244 4996)
#endif


#if defined(__MACH__) || defined(USE_WINDOWS_API)
    #ifndef _SOCKLEN_T
        typedef int socklen_t;
    #endif
#endif


/* HPUX doesn't use socklent_t for third parameter to accept, unless
   _XOPEN_SOURCE_EXTENDED is defined */
#if !defined(__hpux__) && !defined(CYASSL_MDK_ARM) && !defined(CYASSL_IAR_ARM)
    typedef socklen_t* ACCEPT_THIRD_T;
#else
    #if defined _XOPEN_SOURCE_EXTENDED
        typedef socklen_t* ACCEPT_THIRD_T;
    #else
        typedef int*       ACCEPT_THIRD_T;
    #endif
#endif


#ifdef USE_WINDOWS_API 
    #define CloseSocket(s) closesocket(s)
    #define StartTCP() { WSADATA wsd; WSAStartup(0x0002, &wsd); }
#elif defined(CYASSL_MDK_ARM)
    #define CloseSocket(s) closesocket(s)
    #define StartTCP() 
#else
    #define CloseSocket(s) close(s)
    #define StartTCP() 
#endif


#ifdef SINGLE_THREADED
    typedef unsigned int  THREAD_RETURN;
    typedef void*         THREAD_TYPE;
    #define CYASSL_THREAD
#else
    #if defined(_POSIX_THREADS) && !defined(__MINGW32__)
        typedef void*         THREAD_RETURN;
        typedef pthread_t     THREAD_TYPE;
        #define CYASSL_THREAD
        #define INFINITE -1
        #define WAIT_OBJECT_0 0L
    #elif defined(CYASSL_MDK_ARM)
        typedef unsigned int  THREAD_RETURN;
        typedef int           THREAD_TYPE;
        #define CYASSL_THREAD
    #else
        typedef unsigned int  THREAD_RETURN;
        typedef intptr_t      THREAD_TYPE;
        #define CYASSL_THREAD __stdcall
    #endif
#endif


#ifdef TEST_IPV6
    typedef struct sockaddr_in6 SOCKADDR_IN_T;
    #define AF_INET_V    AF_INET6
#else
    typedef struct sockaddr_in  SOCKADDR_IN_T;
    #define AF_INET_V    AF_INET
#endif
   

#define SERVER_DEFAULT_VERSION 3
#define SERVER_DTLS_DEFAULT_VERSION (-2)
#define SERVER_INVALID_VERSION (-99)
#define CLIENT_DEFAULT_VERSION 3
#define CLIENT_DTLS_DEFAULT_VERSION (-2)
#define CLIENT_INVALID_VERSION (-99)

/* all certs relative to CyaSSL home directory now */
#define caCert     "./certs/ca-cert.pem"
#define eccCert    "./certs/server-ecc.pem"
#define eccKey     "./certs/ecc-key.pem"
#define svrCert    "./certs/server-cert.pem"
#define svrKey     "./certs/server-key.pem"
#define cliCert    "./certs/client-cert.pem"
#define cliKey     "./certs/client-key.pem"
#define ntruCert   "./certs/ntru-cert.pem"
#define ntruKey    "./certs/ntru-key.raw"
#define dhParam    "./certs/dh2048.pem"
#define cliEccKey  "./certs/ecc-client-key.pem"
#define cliEccCert "./certs/client-ecc-cert.pem"
#define crlPemDir  "./certs/crl"

typedef struct tcp_ready {
    word16 ready;              /* predicate */
    word16 port;
#if defined(_POSIX_THREADS) && !defined(__MINGW32__)
    pthread_mutex_t mutex;
    pthread_cond_t  cond;
#endif
} tcp_ready;    


void InitTcpReady(tcp_ready*);
void FreeTcpReady(tcp_ready*);

typedef CYASSL_METHOD* (*method_provider)(void);
typedef void (*ctx_callback)(CYASSL_CTX* ctx);
typedef void (*ssl_callback)(CYASSL* ssl);

typedef struct callback_functions {
    method_provider method;
    ctx_callback ctx_ready;
    ssl_callback ssl_ready;
    ssl_callback on_result;
} callback_functions;

typedef struct func_args {
    int    argc;
    char** argv;
    int    return_code;
    tcp_ready* signal;
    callback_functions *callbacks;
} func_args;

void wait_tcp_ready(func_args*);

typedef THREAD_RETURN CYASSL_THREAD THREAD_FUNC(void*);

void start_thread(THREAD_FUNC, func_args*, THREAD_TYPE*);
void join_thread(THREAD_TYPE);

/* yaSSL */
#ifndef TEST_IPV6
    static const char* const yasslIP   = "127.0.0.1";
#else
    static const char* const yasslIP   = "::1";
#endif
static const word16      yasslPort = 11111;

static INLINE void err_sys(const char* msg)
{
    printf("yassl error: %s\n", msg);
    if (msg)
        exit(EXIT_FAILURE);
}


#define MY_EX_USAGE 2

extern int   myoptind;
extern char* myoptarg;

static INLINE int mygetopt(int argc, char** argv, const char* optstring)
{
    static char* next = NULL;

    char  c;
    char* cp;

    if (myoptind == 0)
        next = NULL;   /* we're starting new/over */

    if (next == NULL || *next == '\0') {
        if (myoptind == 0)
            myoptind++;

        if (myoptind >= argc || argv[myoptind][0] != '-' ||
                                argv[myoptind][1] == '\0') {
            myoptarg = NULL;
            if (myoptind < argc)
                myoptarg = argv[myoptind];

            return -1;
        }

        if (strcmp(argv[myoptind], "--") == 0) {
            myoptind++;
            myoptarg = NULL;

            if (myoptind < argc)
                myoptarg = argv[myoptind];

            return -1;
        }

        next = argv[myoptind];
        next++;                  /* skip - */
        myoptind++;
    }

    c  = *next++;
    /* The C++ strchr can return a different value */
    cp = (char*)strchr(optstring, c);

    if (cp == NULL || c == ':') 
        return '?';

    cp++;

    if (*cp == ':') {
        if (*next != '\0') {
            myoptarg = next;
            next     = NULL;
        }
        else if (myoptind < argc) {
            myoptarg = argv[myoptind];
            myoptind++;
        }
        else 
            return '?';
    }

    return c;
}


#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)

static INLINE int PasswordCallBack(char* passwd, int sz, int rw, void* userdata)
{
    (void)rw;
    (void)userdata;
    strncpy(passwd, "yassl123", sz);
    return 8;
}

#endif


#if defined(KEEP_PEER_CERT) || defined(SESSION_CERTS)

static INLINE void ShowX509(CYASSL_X509* x509, const char* hdr)
{
    char* altName;
    char* issuer  = CyaSSL_X509_NAME_oneline(
                                       CyaSSL_X509_get_issuer_name(x509), 0, 0);
    char* subject = CyaSSL_X509_NAME_oneline(
                                      CyaSSL_X509_get_subject_name(x509), 0, 0);
    byte  serial[32];
    int   ret;
    int   sz = sizeof(serial);
        
    printf("%s\n issuer : %s\n subject: %s\n", hdr, issuer, subject);

    while ( (altName = CyaSSL_X509_get_next_altname(x509)) != NULL)
        printf(" altname = %s\n", altName);

    ret = CyaSSL_X509_get_serial_number(x509, serial, &sz);
    if (ret == SSL_SUCCESS) {
        int  i;
        int  strLen;
        char serialMsg[80];

        /* testsuite has multiple threads writing to stdout, get output
           message ready to write once */
        strLen = sprintf(serialMsg, " serial number");
        for (i = 0; i < sz; i++)
            sprintf(serialMsg + strLen + (i*3), ":%02x ", serial[i]);
        printf("%s\n", serialMsg);
    }

    XFREE(subject, 0, DYNAMIC_TYPE_OPENSSL);
    XFREE(issuer,  0, DYNAMIC_TYPE_OPENSSL);
}

#endif /* KEEP_PEER_CERT || SESSION_CERTS */


static INLINE void showPeer(CYASSL* ssl)
{

    CYASSL_CIPHER* cipher;
#ifdef KEEP_PEER_CERT
    CYASSL_X509* peer = CyaSSL_get_peer_certificate(ssl);
    if (peer)
        ShowX509(peer, "peer's cert info:");
    else
        printf("peer has no cert!\n");
#endif
    printf("SSL version is %s\n", CyaSSL_get_version(ssl));

    cipher = CyaSSL_get_current_cipher(ssl);
    printf("SSL cipher suite is %s\n", CyaSSL_CIPHER_get_name(cipher));

#if defined(SESSION_CERTS) && defined(SHOW_CERTS)
    {
        CYASSL_X509_CHAIN* chain = CyaSSL_get_peer_chain(ssl);
        int                count = CyaSSL_get_chain_count(chain);
        int i;

        for (i = 0; i < count; i++) {
            int length;
            unsigned char buffer[3072];
            CYASSL_X509* chainX509;

            CyaSSL_get_chain_cert_pem(chain,i,buffer, sizeof(buffer), &length);
            buffer[length] = 0;
            printf("cert %d has length %d data = \n%s\n", i, length, buffer);

            chainX509 = CyaSSL_get_chain_X509(chain, i);
            if (chainX509)
                ShowX509(chainX509, "session cert info:");
            else
                printf("get_chain_X509 failed\n");
            CyaSSL_FreeX509(chainX509);
        }
    }
#endif
  (void)ssl;
}


static INLINE void build_addr(SOCKADDR_IN_T* addr, const char* peer,
                              word16 port, int udp)
{
    int useLookup = 0;
    (void)useLookup;
    (void)udp;

    memset(addr, 0, sizeof(SOCKADDR_IN_T));

#ifndef TEST_IPV6
    /* peer could be in human readable form */
    if ( (peer != INADDR_ANY) && isalpha((int)peer[0])) {
        #ifdef CYASSL_MDK_ARM
            int err;
            struct hostent* entry = gethostbyname(peer, &err);
        #else
            struct hostent* entry = gethostbyname(peer);
        #endif

        if (entry) {
            memcpy(&addr->sin_addr.s_addr, entry->h_addr_list[0],
                   entry->h_length);
            useLookup = 1;
        }
        else
            err_sys("no entry for host");
    }
#endif


#ifndef TEST_IPV6
    #if defined(CYASSL_MDK_ARM)
        addr->sin_family = PF_INET;
    #else
        addr->sin_family = AF_INET_V;
    #endif
    addr->sin_port = htons(port);
    if (peer == INADDR_ANY)
        addr->sin_addr.s_addr = INADDR_ANY;
    else {
        if (!useLookup)
            addr->sin_addr.s_addr = inet_addr(peer);
    }
#else
    addr->sin6_family = AF_INET_V;
    addr->sin6_port = htons(port);
    if (peer == INADDR_ANY)
        addr->sin6_addr = in6addr_any;
    else {
        #ifdef HAVE_GETADDRINFO
            struct addrinfo  hints;
            struct addrinfo* answer = NULL;
            int    ret;
            char   strPort[80];

            memset(&hints, 0, sizeof(hints));

            hints.ai_family   = AF_INET_V;
            hints.ai_socktype = udp ? SOCK_DGRAM : SOCK_STREAM;
            hints.ai_protocol = udp ? IPPROTO_UDP : IPPROTO_TCP;

            SNPRINTF(strPort, sizeof(strPort), "%d", port);
            strPort[79] = '\0';

            ret = getaddrinfo(peer, strPort, &hints, &answer);
            if (ret < 0 || answer == NULL)
                err_sys("getaddrinfo failed");

            memcpy(addr, answer->ai_addr, answer->ai_addrlen);
            freeaddrinfo(answer);
        #else
            printf("no ipv6 getaddrinfo, loopback only tests/examples\n");
            addr->sin6_addr = in6addr_loopback;
        #endif
    }
#endif
}


static INLINE void tcp_socket(SOCKET_T* sockfd, int udp)
{
    if (udp)
        *sockfd = socket(AF_INET_V, SOCK_DGRAM, 0);
    else
        *sockfd = socket(AF_INET_V, SOCK_STREAM, 0);

#ifdef USE_WINDOWS_API
    if (*sockfd == INVALID_SOCKET)
        err_sys("socket failed\n");
#else
    if (*sockfd < 0)
        err_sys("socket failed\n");
#endif

#ifndef USE_WINDOWS_API 
#ifdef SO_NOSIGPIPE
    {
        int       on = 1;
        socklen_t len = sizeof(on);
        int       res = setsockopt(*sockfd, SOL_SOCKET, SO_NOSIGPIPE, &on, len);
        if (res < 0)
            err_sys("setsockopt SO_NOSIGPIPE failed\n");
    }
#elif defined(CYASSL_MDK_ARM)
    /* nothing to define */
#else  /* no S_NOSIGPIPE */
    signal(SIGPIPE, SIG_IGN);
#endif /* S_NOSIGPIPE */

#if defined(TCP_NODELAY)
    if (!udp)
    {
        int       on = 1;
        socklen_t len = sizeof(on);
        int       res = setsockopt(*sockfd, IPPROTO_TCP, TCP_NODELAY, &on, len);
        if (res < 0)
            err_sys("setsockopt TCP_NODELAY failed\n");
    }
#endif
#endif  /* USE_WINDOWS_API */
}

static INLINE void tcp_connect(SOCKET_T* sockfd, const char* ip, word16 port,
                               int udp)
{
    SOCKADDR_IN_T addr;
    build_addr(&addr, ip, port, udp);
    tcp_socket(sockfd, udp);

    if (!udp) {
        if (connect(*sockfd, (const struct sockaddr*)&addr, sizeof(addr)) != 0)
            err_sys("tcp connect failed");
    }
}


static INLINE void udp_connect(SOCKET_T* sockfd, void* addr, int addrSz)
{
    if (connect(*sockfd, (const struct sockaddr*)addr, addrSz) != 0)
        err_sys("tcp connect failed");
}


enum {
    TEST_SELECT_FAIL,
    TEST_TIMEOUT,
    TEST_RECV_READY,
    TEST_ERROR_READY
};


#if !defined(CYASSL_MDK_ARM)
static INLINE int tcp_select(SOCKET_T socketfd, int to_sec)
{
    fd_set recvfds, errfds;
    SOCKET_T nfds = socketfd + 1;
    struct timeval timeout = { (to_sec > 0) ? to_sec : 0, 0};
    int result;

    FD_ZERO(&recvfds);
    FD_SET(socketfd, &recvfds);
    FD_ZERO(&errfds);
    FD_SET(socketfd, &errfds);

    result = select(nfds, &recvfds, NULL, &errfds, &timeout);

    if (result == 0)
        return TEST_TIMEOUT;
    else if (result > 0) {
        if (FD_ISSET(socketfd, &recvfds))
            return TEST_RECV_READY;
        else if(FD_ISSET(socketfd, &errfds))
            return TEST_ERROR_READY;
    }

    return TEST_SELECT_FAIL;
}
#endif /* !CYASSL_MDK_ARM */


static INLINE void tcp_listen(SOCKET_T* sockfd, word16* port, int useAnyAddr,
                              int udp)
{
    SOCKADDR_IN_T addr;

    /* don't use INADDR_ANY by default, firewall may block, make user switch
       on */
    build_addr(&addr, (useAnyAddr ? INADDR_ANY : yasslIP), *port, udp);
    tcp_socket(sockfd, udp);

#if !defined(USE_WINDOWS_API) && !defined(CYASSL_MDK_ARM)
    {
        int       res, on  = 1;
        socklen_t len = sizeof(on);
        res = setsockopt(*sockfd, SOL_SOCKET, SO_REUSEADDR, &on, len);
        if (res < 0)
            err_sys("setsockopt SO_REUSEADDR failed\n");
    }
#endif

    if (bind(*sockfd, (const struct sockaddr*)&addr, sizeof(addr)) != 0)
        err_sys("tcp bind failed");
    if (!udp) {
        if (listen(*sockfd, 5) != 0)
            err_sys("tcp listen failed");
    }
    #if defined(NO_MAIN_DRIVER) && !defined(USE_WINDOWS_API)
        if (*port == 0) {
            socklen_t len = sizeof(addr);
            if (getsockname(*sockfd, (struct sockaddr*)&addr, &len) == 0) {
                #ifndef TEST_IPV6
                    *port = ntohs(addr.sin_port);
                #else
                    *port = ntohs(addr.sin6_port);
                #endif
            }
        }
    #endif
}


static INLINE int udp_read_connect(SOCKET_T sockfd)
{
    SOCKADDR_IN_T cliaddr;
    byte          b[1500];
    int           n;
    socklen_t     len = sizeof(cliaddr);

    n = (int)recvfrom(sockfd, (char*)b, sizeof(b), MSG_PEEK,
                      (struct sockaddr*)&cliaddr, &len);
    if (n > 0) {
        if (connect(sockfd, (const struct sockaddr*)&cliaddr,
                    sizeof(cliaddr)) != 0)
            err_sys("udp connect failed");
    }
    else
        err_sys("recvfrom failed");

    return sockfd;
}

static INLINE void udp_accept(SOCKET_T* sockfd, SOCKET_T* clientfd,
                              int useAnyAddr, word16 port, func_args* args)
{
    SOCKADDR_IN_T addr;

    (void)args;
    build_addr(&addr, (useAnyAddr ? INADDR_ANY : yasslIP), port, 1);
    tcp_socket(sockfd, 1);


#if !defined(USE_WINDOWS_API) && !defined(CYASSL_MDK_ARM)
    {
        int       res, on  = 1;
        socklen_t len = sizeof(on);
        res = setsockopt(*sockfd, SOL_SOCKET, SO_REUSEADDR, &on, len);
        if (res < 0)
            err_sys("setsockopt SO_REUSEADDR failed\n");
    }
#endif

    if (bind(*sockfd, (const struct sockaddr*)&addr, sizeof(addr)) != 0)
        err_sys("tcp bind failed");

    #if defined(NO_MAIN_DRIVER) && !defined(USE_WINDOWS_API)
        if (port == 0) {
            socklen_t len = sizeof(addr);
            if (getsockname(*sockfd, (struct sockaddr*)&addr, &len) == 0) {
                #ifndef TEST_IPV6
                    port = ntohs(addr.sin_port);
                #else
                    port = ntohs(addr.sin6_port);
                #endif
            }
        }
    #endif

#if defined(_POSIX_THREADS) && defined(NO_MAIN_DRIVER) && !defined(__MINGW32__)
    /* signal ready to accept data */
    {
    tcp_ready* ready = args->signal;
    pthread_mutex_lock(&ready->mutex);
    ready->ready = 1;
    ready->port = port;
    pthread_cond_signal(&ready->cond);
    pthread_mutex_unlock(&ready->mutex);
    }
#endif

    *clientfd = udp_read_connect(*sockfd);
}

static INLINE void tcp_accept(SOCKET_T* sockfd, SOCKET_T* clientfd,
                              func_args* args, word16 port, int useAnyAddr,
                              int udp)
{
    SOCKADDR_IN_T client;
    socklen_t client_len = sizeof(client);

    if (udp) {
        udp_accept(sockfd, clientfd, useAnyAddr, port, args);
        return;
    }

    tcp_listen(sockfd, &port, useAnyAddr, udp);

#if defined(_POSIX_THREADS) && defined(NO_MAIN_DRIVER) && !defined(__MINGW32__)
    /* signal ready to tcp_accept */
    {
    tcp_ready* ready = args->signal;
    pthread_mutex_lock(&ready->mutex);
    ready->ready = 1;
    ready->port = port;
    pthread_cond_signal(&ready->cond);
    pthread_mutex_unlock(&ready->mutex);
    }
#endif

    *clientfd = accept(*sockfd, (struct sockaddr*)&client,
                      (ACCEPT_THIRD_T)&client_len);
#ifdef USE_WINDOWS_API
    if (*clientfd == INVALID_SOCKET)
        err_sys("tcp accept failed");
#else
    if (*clientfd == -1)
        err_sys("tcp accept failed");
#endif
}


static INLINE void tcp_set_nonblocking(SOCKET_T* sockfd)
{
    #ifdef USE_WINDOWS_API 
        unsigned long blocking = 1;
        int ret = ioctlsocket(*sockfd, FIONBIO, &blocking);
        if (ret == SOCKET_ERROR)
            err_sys("ioctlsocket failed");
    #elif defined(CYASSL_MDK_ARM)
         /* non blocking not suppported, for now */ 
    #else
        int flags = fcntl(*sockfd, F_GETFL, 0);
        if (flags < 0)
            err_sys("fcntl get failed");
        flags = fcntl(*sockfd, F_SETFL, flags | O_NONBLOCK);
        if (flags < 0)
            err_sys("fcntl set failed");
    #endif
}


#ifndef NO_PSK

static INLINE unsigned int my_psk_client_cb(CYASSL* ssl, const char* hint,
        char* identity, unsigned int id_max_len, unsigned char* key,
        unsigned int key_max_len)
{
    (void)ssl;
    (void)hint;
    (void)key_max_len;

    /* identity is OpenSSL testing default for openssl s_client, keep same */
    strncpy(identity, "Client_identity", id_max_len);


    /* test key in hex is 0x1a2b3c4d , in decimal 439,041,101 , we're using
       unsigned binary */
    key[0] = 26;
    key[1] = 43;
    key[2] = 60;
    key[3] = 77;

    return 4;   /* length of key in octets or 0 for error */
}


static INLINE unsigned int my_psk_server_cb(CYASSL* ssl, const char* identity,
        unsigned char* key, unsigned int key_max_len)
{
    (void)ssl;
    (void)key_max_len;

    /* identity is OpenSSL testing default for openssl s_client, keep same */
    if (strncmp(identity, "Client_identity", 15) != 0)
        return 0;

    /* test key in hex is 0x1a2b3c4d , in decimal 439,041,101 , we're using
       unsigned binary */
    key[0] = 26;
    key[1] = 43;
    key[2] = 60;
    key[3] = 77;

    return 4;   /* length of key in octets or 0 for error */
}

#endif /* NO_PSK */


#ifdef USE_WINDOWS_API 

    #define WIN32_LEAN_AND_MEAN
    #include <windows.h>

    static INLINE double current_time()
    {
        static int init = 0;
        static LARGE_INTEGER freq;
    
        LARGE_INTEGER count;

        if (!init) {
            QueryPerformanceFrequency(&freq);
            init = 1;
        }

        QueryPerformanceCounter(&count);

        return (double)count.QuadPart / freq.QuadPart;
    }

#else

#if !defined(CYASSL_MDK_ARM)
    #include <sys/time.h>

    static INLINE double current_time(void)
    {
        struct timeval tv;
        gettimeofday(&tv, 0);

        return (double)tv.tv_sec + (double)tv.tv_usec / 1000000;
    }
        
#endif
#endif /* USE_WINDOWS_API */


#if defined(NO_FILESYSTEM) && !defined(NO_CERTS)

    enum {
        CYASSL_CA   = 1,
        CYASSL_CERT = 2,
        CYASSL_KEY  = 3
    };

    static INLINE void load_buffer(CYASSL_CTX* ctx, const char* fname, int type)
    {
        /* test buffer load */
        long  sz = 0;
        byte  buff[10000];
        FILE* file = fopen(fname, "rb");

        if (!file)
            err_sys("can't open file for buffer load "
                    "Please run from CyaSSL home directory if not");
        fseek(file, 0, SEEK_END);
        sz = ftell(file);
        rewind(file);
        fread(buff, sizeof(buff), 1, file);
  
        if (type == CYASSL_CA) {
            if (CyaSSL_CTX_load_verify_buffer(ctx, buff, sz, SSL_FILETYPE_PEM)
                                              != SSL_SUCCESS)
                err_sys("can't load buffer ca file");
        }
        else if (type == CYASSL_CERT) {
            if (CyaSSL_CTX_use_certificate_buffer(ctx, buff, sz,
                        SSL_FILETYPE_PEM) != SSL_SUCCESS)
                err_sys("can't load buffer cert file");
        }
        else if (type == CYASSL_KEY) {
            if (CyaSSL_CTX_use_PrivateKey_buffer(ctx, buff, sz,
                        SSL_FILETYPE_PEM) != SSL_SUCCESS)
                err_sys("can't load buffer key file");
        }
    }

#endif /* NO_FILESYSTEM */

#ifdef VERIFY_CALLBACK

static INLINE int myVerify(int preverify, CYASSL_X509_STORE_CTX* store)
{
    (void)preverify;
    char buffer[CYASSL_MAX_ERROR_SZ];

#ifdef OPENSSL_EXTRA
    CYASSL_X509* peer;
#endif

    printf("In verification callback, error = %d, %s\n", store->error,
                                 CyaSSL_ERR_error_string(store->error, buffer));
#ifdef OPENSSL_EXTRA
    peer = store->current_cert;
    if (peer) {
        char* issuer  = CyaSSL_X509_NAME_oneline(
                                       CyaSSL_X509_get_issuer_name(peer), 0, 0);
        char* subject = CyaSSL_X509_NAME_oneline(
                                      CyaSSL_X509_get_subject_name(peer), 0, 0);
        printf("peer's cert info:\n issuer : %s\n subject: %s\n", issuer,
                                                                  subject);
        XFREE(subject, 0, DYNAMIC_TYPE_OPENSSL);
        XFREE(issuer,  0, DYNAMIC_TYPE_OPENSSL);
    }
    else
        printf("peer has no cert!\n");
#endif
    printf("Subject's domain name is %s\n", store->domain);

    printf("Allowing to continue anyway (shouldn't do this, EVER!!!)\n");
    return 1;
}

#endif /* VERIFY_CALLBACK */


static INLINE int myDateCb(int preverify, CYASSL_X509_STORE_CTX* store)
{
    char buffer[CYASSL_MAX_ERROR_SZ];
    (void)preverify;

    printf("In verification callback, error = %d, %s\n", store->error,
                                 CyaSSL_ERR_error_string(store->error, buffer));
    printf("Subject's domain name is %s\n", store->domain);

    if (store->error == ASN_BEFORE_DATE_E || store->error == ASN_AFTER_DATE_E) {
        printf("Overriding cert date error as example for bad clock testing\n");
        return 1;
    }
    printf("Cert error is not date error, not overriding\n");

    return 0;
}


#ifdef HAVE_CRL

static INLINE void CRL_CallBack(const char* url)
{
    printf("CRL callback url = %s\n", url);
}

#endif

#ifndef NO_CERTS

static INLINE void CaCb(unsigned char* der, int sz, int type)
{
    (void)der;
    printf("Got CA cache add callback, derSz = %d, type = %d\n", sz, type);
}


#ifndef NO_DH
static INLINE void SetDH(CYASSL* ssl)
{
    /* dh1024 p */
    static unsigned char p[] =
    {
        0xE6, 0x96, 0x9D, 0x3D, 0x49, 0x5B, 0xE3, 0x2C, 0x7C, 0xF1, 0x80, 0xC3,
        0xBD, 0xD4, 0x79, 0x8E, 0x91, 0xB7, 0x81, 0x82, 0x51, 0xBB, 0x05, 0x5E,
        0x2A, 0x20, 0x64, 0x90, 0x4A, 0x79, 0xA7, 0x70, 0xFA, 0x15, 0xA2, 0x59,
        0xCB, 0xD5, 0x23, 0xA6, 0xA6, 0xEF, 0x09, 0xC4, 0x30, 0x48, 0xD5, 0xA2,
        0x2F, 0x97, 0x1F, 0x3C, 0x20, 0x12, 0x9B, 0x48, 0x00, 0x0E, 0x6E, 0xDD,
        0x06, 0x1C, 0xBC, 0x05, 0x3E, 0x37, 0x1D, 0x79, 0x4E, 0x53, 0x27, 0xDF,
        0x61, 0x1E, 0xBB, 0xBE, 0x1B, 0xAC, 0x9B, 0x5C, 0x60, 0x44, 0xCF, 0x02,
        0x3D, 0x76, 0xE0, 0x5E, 0xEA, 0x9B, 0xAD, 0x99, 0x1B, 0x13, 0xA6, 0x3C,
        0x97, 0x4E, 0x9E, 0xF1, 0x83, 0x9E, 0xB5, 0xDB, 0x12, 0x51, 0x36, 0xF7,
        0x26, 0x2E, 0x56, 0xA8, 0x87, 0x15, 0x38, 0xDF, 0xD8, 0x23, 0xC6, 0x50,
        0x50, 0x85, 0xE2, 0x1F, 0x0D, 0xD5, 0xC8, 0x6B,
    };

    /* dh1024 g */
    static unsigned char g[] =
    {
      0x02,
    };

    CyaSSL_SetTmpDH(ssl, p, sizeof(p), g, sizeof(g));
}

static INLINE void SetDHCtx(CYASSL_CTX* ctx)
{
    /* dh1024 p */
    static unsigned char p[] =
    {
        0xE6, 0x96, 0x9D, 0x3D, 0x49, 0x5B, 0xE3, 0x2C, 0x7C, 0xF1, 0x80, 0xC3,
        0xBD, 0xD4, 0x79, 0x8E, 0x91, 0xB7, 0x81, 0x82, 0x51, 0xBB, 0x05, 0x5E,
        0x2A, 0x20, 0x64, 0x90, 0x4A, 0x79, 0xA7, 0x70, 0xFA, 0x15, 0xA2, 0x59,
        0xCB, 0xD5, 0x23, 0xA6, 0xA6, 0xEF, 0x09, 0xC4, 0x30, 0x48, 0xD5, 0xA2,
        0x2F, 0x97, 0x1F, 0x3C, 0x20, 0x12, 0x9B, 0x48, 0x00, 0x0E, 0x6E, 0xDD,
        0x06, 0x1C, 0xBC, 0x05, 0x3E, 0x37, 0x1D, 0x79, 0x4E, 0x53, 0x27, 0xDF,
        0x61, 0x1E, 0xBB, 0xBE, 0x1B, 0xAC, 0x9B, 0x5C, 0x60, 0x44, 0xCF, 0x02,
        0x3D, 0x76, 0xE0, 0x5E, 0xEA, 0x9B, 0xAD, 0x99, 0x1B, 0x13, 0xA6, 0x3C,
        0x97, 0x4E, 0x9E, 0xF1, 0x83, 0x9E, 0xB5, 0xDB, 0x12, 0x51, 0x36, 0xF7,
        0x26, 0x2E, 0x56, 0xA8, 0x87, 0x15, 0x38, 0xDF, 0xD8, 0x23, 0xC6, 0x50,
        0x50, 0x85, 0xE2, 0x1F, 0x0D, 0xD5, 0xC8, 0x6B,
    };

    /* dh1024 g */
    static unsigned char g[] =
    {
      0x02,
    };

    CyaSSL_CTX_SetTmpDH(ctx, p, sizeof(p), g, sizeof(g));
}
#endif /* NO_DH */
#endif /* !NO_CERTS */

#ifdef HAVE_CAVIUM

static INLINE int OpenNitroxDevice(int dma_mode,int dev_id)
{
   Csp1CoreAssignment core_assign;
   Uint32             device;

   if (CspInitialize(CAVIUM_DIRECT,CAVIUM_DEV_ID))
      return -1;
   if (Csp1GetDevType(&device))
      return -1;
   if (device != NPX_DEVICE) {
      if (ioctl(gpkpdev_hdlr[CAVIUM_DEV_ID], IOCTL_CSP1_GET_CORE_ASSIGNMENT,
                (Uint32 *)&core_assign)!= 0)
         return -1;
   }
   CspShutdown(CAVIUM_DEV_ID);

   return CspInitialize(dma_mode, dev_id);
}

#endif /* HAVE_CAVIUM */


#ifdef USE_WINDOWS_API 

/* do back x number of directories */
static INLINE void ChangeDirBack(int x)
{
    char path[MAX_PATH];

    if (x == 1)
        strncpy(path, "..\\", MAX_PATH);
    else if (x == 2)
        strncpy(path, "..\\..\\", MAX_PATH);
    else if (x == 3)
        strncpy(path, "..\\..\\..\\", MAX_PATH);
    else if (x == 4)
        strncpy(path, "..\\..\\..\\..\\", MAX_PATH);
    else
        strncpy(path, ".\\", MAX_PATH);
    
    SetCurrentDirectoryA(path);
}

/* does current dir contain str */
static INLINE int CurrentDir(const char* str)
{
    char  path[MAX_PATH];
    char* baseName;

    GetCurrentDirectoryA(sizeof(path), path);

    baseName = strrchr(path, '\\');
    if (baseName)
        baseName++;
    else
        baseName = path;

    if (strstr(baseName, str))
        return 1;

    return 0;
}

#elif defined(CYASSL_MDK_ARM)
    /* KEIL-RL File System does not support relative directry */
#else

#ifndef MAX_PATH
    #define MAX_PATH 256
#endif

/* do back x number of directories */
static INLINE void ChangeDirBack(int x)
{
    char path[MAX_PATH];

    if (x == 1)
        strncpy(path, "../", MAX_PATH);
    else if (x == 2)
        strncpy(path, "../../", MAX_PATH);
    else if (x == 3)
        strncpy(path, "../../../", MAX_PATH);
    else if (x == 4)
        strncpy(path, "../../../../", MAX_PATH);
    else
        strncpy(path, "./", MAX_PATH);
    
    if (chdir(path) < 0)
        printf("chdir to %s failed\n", path);
}

/* does current dir contain str */
static INLINE int CurrentDir(const char* str)
{
    char  path[MAX_PATH];
    char* baseName;

    if (getcwd(path, sizeof(path)) == NULL) {
        printf("no current dir?\n");
        return 0;
    }

    baseName = strrchr(path, '/');
    if (baseName)
        baseName++;
    else
        baseName = path;

    if (strstr(baseName, str))
        return 1;

    return 0;
}

#endif /* USE_WINDOWS_API */


#ifdef USE_CYASSL_MEMORY

    typedef struct memoryStats {
        size_t totalAllocs;     /* number of allocations */
        size_t totalBytes;      /* total number of bytes allocated */
        size_t peakBytes;       /* concurrent max bytes */
        size_t currentBytes;    /* total current bytes in use */
    } memoryStats;

    typedef struct memHint {
        size_t thisSize;      /* size of this memory */
        void*  thisMemory;    /* actual memory for user */
    } memHint;

    typedef struct memoryTrack {
        union {
            memHint hint;
            byte    alignit[16];   /* make sure we have strong alignment */
        } u;
    } memoryTrack;

    #if defined(CYASSL_TRACK_MEMORY)
        #define DO_MEM_STATS
        static memoryStats ourMemStats;
    #endif

    static INLINE void* TrackMalloc(size_t sz)
    {
        memoryTrack* mt;

        if (sz == 0)
            return NULL;

        mt = (memoryTrack*)malloc(sizeof(memoryTrack) + sz);
        if (mt == NULL)
            return NULL;

        mt->u.hint.thisSize   = sz;
        mt->u.hint.thisMemory = (byte*)mt + sizeof(memoryTrack);

#ifdef DO_MEM_STATS
        ourMemStats.totalAllocs++;
        ourMemStats.totalBytes   += sz;
        ourMemStats.currentBytes += sz;
        if (ourMemStats.currentBytes > ourMemStats.peakBytes)
            ourMemStats.peakBytes = ourMemStats.currentBytes;
#endif

        return mt->u.hint.thisMemory;
    }


    static INLINE void TrackFree(void* ptr)
    {
        memoryTrack* mt;

        if (ptr == NULL)
            return;

        mt = (memoryTrack*)ptr;
        --mt;   /* same as minus sizeof(memoryTrack), removes header */

#ifdef DO_MEM_STATS 
        ourMemStats.currentBytes -= mt->u.hint.thisSize; 
#endif

        free(mt);
    }


    static INLINE void* TrackRealloc(void* ptr, size_t sz)
    {
        void* ret = TrackMalloc(sz);

        if (ptr) {
            /* if realloc is bigger, don't overread old ptr */
            memoryTrack* mt = (memoryTrack*)ptr;
            --mt;  /* same as minus sizeof(memoryTrack), removes header */

            if (mt->u.hint.thisSize < sz)
                sz = mt->u.hint.thisSize;
        }

        if (ret && ptr)
            memcpy(ret, ptr, sz);

        if (ret)
            TrackFree(ptr);

        return ret;
    }

    static INLINE void InitMemoryTracker(void) 
    {
        if (CyaSSL_SetAllocators(TrackMalloc, TrackFree, TrackRealloc) != 0)
            err_sys("CyaSSL SetAllocators failed for track memory");

    #ifdef DO_MEM_STATS
        ourMemStats.totalAllocs  = 0;
        ourMemStats.totalBytes   = 0;
        ourMemStats.peakBytes    = 0;
        ourMemStats.currentBytes = 0;
    #endif
    }

    static INLINE void ShowMemoryTracker(void) 
    {
    #ifdef DO_MEM_STATS 
        printf("total   Allocs = %9lu\n",
                                       (unsigned long)ourMemStats.totalAllocs);
        printf("total   Bytes  = %9lu\n",
                                       (unsigned long)ourMemStats.totalBytes);
        printf("peak    Bytes  = %9lu\n",
                                       (unsigned long)ourMemStats.peakBytes);
        printf("current Bytes  = %9lu\n",
                                       (unsigned long)ourMemStats.currentBytes);
    #endif
    }

#endif /* USE_CYASSL_MEMORY */


#ifdef HAVE_STACK_SIZE

typedef THREAD_RETURN CYASSL_THREAD (*thread_func)(void* args);


static INLINE void StackSizeCheck(func_args* args, thread_func tf)
{
    int            ret, i, used;
    unsigned char* myStack;
    int            stackSize = 1024*128;
    pthread_attr_t myAttr;
    pthread_t      threadId;

#ifdef PTHREAD_STACK_MIN
    if (stackSize < PTHREAD_STACK_MIN)
        stackSize = PTHREAD_STACK_MIN;
#endif

    ret = posix_memalign((void**)&myStack, sysconf(_SC_PAGESIZE), stackSize);
    if (ret != 0) 
        err_sys("posix_memalign failed\n");        

    memset(myStack, 0x01, stackSize);

    ret = pthread_attr_init(&myAttr);
    if (ret != 0)
        err_sys("attr_init failed");

    ret = pthread_attr_setstack(&myAttr, myStack, stackSize);
    if (ret != 0)
        err_sys("attr_setstackaddr failed");

    ret = pthread_create(&threadId, &myAttr, tf, args);
    if (ret != 0) {
        perror("pthread_create failed");
        exit(EXIT_FAILURE);
    }

    ret = pthread_join(threadId, NULL);
    if (ret != 0)
        err_sys("pthread_join failed");

    for (i = 0; i < stackSize; i++) {
        if (myStack[i] != 0x01) {
            break;
        }
    }

    used = stackSize - i;
    printf("stack used = %d\n", used);
}


#endif /* HAVE_STACK_SIZE */


#ifdef STACK_TRAP

/* good settings
   --enable-debug --disable-shared C_EXTRA_FLAGS="-DUSER_TIME -DTFM_TIMING_RESISTANT -DPOSITIVE_EXP_ONLY -DSTACK_TRAP"

*/

#ifdef HAVE_STACK_SIZE
    /* client only for now, setrlimit will fail if pthread_create() called */
    /* STACK_SIZE does pthread_create() on client */
    #error "can't use STACK_TRAP with STACK_SIZE, setrlimit will fail"
#endif /* HAVE_STACK_SIZE */

static INLINE void StackTrap(void)
{
    struct rlimit  rl;
    if (getrlimit(RLIMIT_STACK, &rl) != 0)
        err_sys("getrlimit failed");
    printf("rlim_cur = %llu\n", rl.rlim_cur);
    rl.rlim_cur = 1024*21;  /* adjust trap size here */
    if (setrlimit(RLIMIT_STACK, &rl) != 0) {
        perror("setrlimit");
        err_sys("setrlimit failed");
    }
}

#else /* STACK_TRAP */

static INLINE void StackTrap(void)
{
}

#endif /* STACK_TRAP */


#ifdef ATOMIC_USER

/* Atomic Encrypt Context example */
typedef struct AtomicEncCtx {
    int  keySetup;           /* have we done key setup yet */
    Aes  aes;                /* for aes example */
} AtomicEncCtx;


/* Atomic Decrypt Context example */
typedef struct AtomicDecCtx {
    int  keySetup;           /* have we done key setup yet */
    Aes  aes;                /* for aes example */
} AtomicDecCtx;


static INLINE int myMacEncryptCb(CYASSL* ssl, unsigned char* macOut, 
       const unsigned char* macIn, unsigned int macInSz, int macContent, 
       int macVerify, unsigned char* encOut, const unsigned char* encIn,
       unsigned int encSz, void* ctx)
{
    int  ret;
    Hmac hmac;
    byte myInner[CYASSL_TLS_HMAC_INNER_SZ];
    AtomicEncCtx* encCtx = (AtomicEncCtx*)ctx;
    const char* tlsStr = "TLS";

    /* example supports (d)tls aes */
    if (CyaSSL_GetBulkCipher(ssl) != cyassl_aes) {
        printf("myMacEncryptCb not using AES\n");
        return -1;
    }

    if (strstr(CyaSSL_get_version(ssl), tlsStr) == NULL) {
        printf("myMacEncryptCb not using (D)TLS\n");
        return -1;
    }

    /* hmac, not needed if aead mode */
    CyaSSL_SetTlsHmacInner(ssl, myInner, macInSz, macContent, macVerify);

    ret = HmacSetKey(&hmac, CyaSSL_GetHmacType(ssl),
               CyaSSL_GetMacSecret(ssl, macVerify), CyaSSL_GetHmacSize(ssl));
    if (ret != 0)
        return ret;
    ret = HmacUpdate(&hmac, myInner, sizeof(myInner));
    if (ret != 0)
        return ret;
    ret = HmacUpdate(&hmac, macIn, macInSz);
    if (ret != 0)
        return ret;
    ret = HmacFinal(&hmac, macOut);
    if (ret != 0)
        return ret;


    /* encrypt setup on first time */
    if (encCtx->keySetup == 0) {
        int   keyLen = CyaSSL_GetKeySize(ssl);
        const byte* key;
        const byte* iv;

        if (CyaSSL_GetSide(ssl) == CYASSL_CLIENT_END) {
            key = CyaSSL_GetClientWriteKey(ssl);
            iv  = CyaSSL_GetClientWriteIV(ssl);
        }
        else {
            key = CyaSSL_GetServerWriteKey(ssl);
            iv  = CyaSSL_GetServerWriteIV(ssl);
        }

        ret = AesSetKey(&encCtx->aes, key, keyLen, iv, AES_ENCRYPTION);
        if (ret != 0) {
            printf("AesSetKey failed in myMacEncryptCb\n");
            return ret;
        }
        encCtx->keySetup = 1;
    }

    /* encrypt */
    return AesCbcEncrypt(&encCtx->aes, encOut, encIn, encSz);
}


static INLINE int myDecryptVerifyCb(CYASSL* ssl, 
       unsigned char* decOut, const unsigned char* decIn,
       unsigned int decSz, int macContent, int macVerify,
       unsigned int* padSz, void* ctx)
{
    AtomicDecCtx* decCtx = (AtomicDecCtx*)ctx;
    int ret      = 0;
    int macInSz  = 0;
    int ivExtra  = 0;
    int digestSz = CyaSSL_GetHmacSize(ssl);
    unsigned int pad     = 0;
    unsigned int padByte = 0;
    Hmac hmac;
    byte myInner[CYASSL_TLS_HMAC_INNER_SZ];
    byte verify[MAX_DIGEST_SIZE];
    const char* tlsStr = "TLS";

    /* example supports (d)tls aes */
    if (CyaSSL_GetBulkCipher(ssl) != cyassl_aes) {
        printf("myMacEncryptCb not using AES\n");
        return -1;
    }

    if (strstr(CyaSSL_get_version(ssl), tlsStr) == NULL) {
        printf("myMacEncryptCb not using (D)TLS\n");
        return -1;
    }

    /*decrypt */
    if (decCtx->keySetup == 0) {
        int   keyLen = CyaSSL_GetKeySize(ssl);
        const byte* key;
        const byte* iv;

        /* decrypt is from other side (peer) */
        if (CyaSSL_GetSide(ssl) == CYASSL_SERVER_END) {
            key = CyaSSL_GetClientWriteKey(ssl);
            iv  = CyaSSL_GetClientWriteIV(ssl);
        }
        else {
            key = CyaSSL_GetServerWriteKey(ssl);
            iv  = CyaSSL_GetServerWriteIV(ssl);
        }

        ret = AesSetKey(&decCtx->aes, key, keyLen, iv, AES_DECRYPTION);
        if (ret != 0) {
            printf("AesSetKey failed in myDecryptVerifyCb\n");
            return ret;
        }
        decCtx->keySetup = 1;
    }

    /* decrypt */
    ret = AesCbcDecrypt(&decCtx->aes, decOut, decIn, decSz);

    if (CyaSSL_GetCipherType(ssl) == CYASSL_AEAD_TYPE) {
        *padSz = CyaSSL_GetAeadMacSize(ssl);
        return 0; /* hmac, not needed if aead mode */
    }

    if (CyaSSL_GetCipherType(ssl) == CYASSL_BLOCK_TYPE) {
        pad     = *(decOut + decSz - 1);
        padByte = 1;
        if (CyaSSL_IsTLSv1_1(ssl))
            ivExtra = CyaSSL_GetCipherBlockSize(ssl);
    }

    *padSz  = CyaSSL_GetHmacSize(ssl) + pad + padByte;
    macInSz = decSz - ivExtra - digestSz - pad - padByte;

    CyaSSL_SetTlsHmacInner(ssl, myInner, macInSz, macContent, macVerify);

    ret = HmacSetKey(&hmac, CyaSSL_GetHmacType(ssl),
               CyaSSL_GetMacSecret(ssl, macVerify), digestSz);
    if (ret != 0)
        return ret;
    ret = HmacUpdate(&hmac, myInner, sizeof(myInner));
    if (ret != 0)
        return ret;
    ret = HmacUpdate(&hmac, decOut + ivExtra, macInSz);
    if (ret != 0)
        return ret;
    ret = HmacFinal(&hmac, verify);
    if (ret != 0)
        return ret;

    if (memcmp(verify, decOut + decSz - digestSz - pad - padByte,
               digestSz) != 0) {
        printf("myDecryptVerify verify failed\n");
        return -1;
    }

    return ret;
}


static INLINE void SetupAtomicUser(CYASSL_CTX* ctx, CYASSL* ssl)
{
    AtomicEncCtx* encCtx;
    AtomicDecCtx* decCtx;

    encCtx = (AtomicEncCtx*)malloc(sizeof(AtomicEncCtx));
    if (encCtx == NULL)
        err_sys("AtomicEncCtx malloc failed");
    memset(encCtx, 0, sizeof(AtomicEncCtx));

    decCtx = (AtomicDecCtx*)malloc(sizeof(AtomicDecCtx));
    if (decCtx == NULL) {
        free(encCtx);
        err_sys("AtomicDecCtx malloc failed");
    }
    memset(decCtx, 0, sizeof(AtomicDecCtx));

    CyaSSL_CTX_SetMacEncryptCb(ctx, myMacEncryptCb);
    CyaSSL_SetMacEncryptCtx(ssl, encCtx);

    CyaSSL_CTX_SetDecryptVerifyCb(ctx, myDecryptVerifyCb);
    CyaSSL_SetDecryptVerifyCtx(ssl, decCtx);
}


static INLINE void FreeAtomicUser(CYASSL* ssl)
{
    AtomicEncCtx* encCtx = CyaSSL_GetMacEncryptCtx(ssl);
    AtomicDecCtx* decCtx = CyaSSL_GetDecryptVerifyCtx(ssl);

    free(decCtx);
    free(encCtx);
}

#endif /* ATOMIC_USER */


#ifdef HAVE_PK_CALLBACKS

#ifdef HAVE_ECC

static INLINE int myEccSign(CYASSL* ssl, const byte* in, word32 inSz,
        byte* out, word32* outSz, const byte* key, word32 keySz, void* ctx)
{
    RNG     rng;
    int     ret;
    word32  idx = 0;
    ecc_key myKey;

    (void)ssl;
    (void)ctx;

    ret = InitRng(&rng);
    if (ret != 0)
        return ret;

    ecc_init(&myKey);
    
    ret = EccPrivateKeyDecode(key, &idx, &myKey, keySz);    
    if (ret == 0)
        ret = ecc_sign_hash(in, inSz, out, outSz, &rng, &myKey);
    ecc_free(&myKey);

    return ret;
}


static INLINE int myEccVerify(CYASSL* ssl, const byte* sig, word32 sigSz,
        const byte* hash, word32 hashSz, const byte* key, word32 keySz,
        int* result, void* ctx)
{
    int     ret;
    ecc_key myKey;

    (void)ssl;
    (void)ctx;

    ecc_init(&myKey);
    
    ret = ecc_import_x963(key, keySz, &myKey);
    if (ret == 0)
        ret = ecc_verify_hash(sig, sigSz, hash, hashSz, result, &myKey);
    ecc_free(&myKey);

    return ret;
}

#endif /* HAVE_ECC */

#ifndef NO_RSA

static INLINE int myRsaSign(CYASSL* ssl, const byte* in, word32 inSz,
        byte* out, word32* outSz, const byte* key, word32 keySz, void* ctx)
{
    RNG     rng;
    int     ret;
    word32  idx = 0;
    RsaKey  myKey;

    (void)ssl;
    (void)ctx;

    ret = InitRng(&rng);
    if (ret != 0)
        return ret;

    InitRsaKey(&myKey, NULL);
    
    ret = RsaPrivateKeyDecode(key, &idx, &myKey, keySz);    
    if (ret == 0)
        ret = RsaSSL_Sign(in, inSz, out, *outSz, &myKey, &rng);
    if (ret > 0) {  /* save and convert to 0 success */
        *outSz = ret;
        ret = 0;
    }
    FreeRsaKey(&myKey);

    return ret;
}


static INLINE int myRsaVerify(CYASSL* ssl, byte* sig, word32 sigSz,
        byte** out,
        const byte* key, word32 keySz,
        void* ctx)
{
    int     ret;
    word32  idx = 0;
    RsaKey  myKey;

    (void)ssl;
    (void)ctx;

    InitRsaKey(&myKey, NULL);
    
    ret = RsaPublicKeyDecode(key, &idx, &myKey, keySz);
    if (ret == 0)
        ret = RsaSSL_VerifyInline(sig, sigSz, out, &myKey);
    FreeRsaKey(&myKey);

    return ret;
}


static INLINE int myRsaEnc(CYASSL* ssl, const byte* in, word32 inSz,
                           byte* out, word32* outSz, const byte* key,
                           word32 keySz, void* ctx)
{
    int     ret;
    word32  idx = 0;
    RsaKey  myKey;
    RNG     rng;

    (void)ssl;
    (void)ctx;

    ret = InitRng(&rng);
    if (ret != 0)
        return ret;

    InitRsaKey(&myKey, NULL);
    
    ret = RsaPublicKeyDecode(key, &idx, &myKey, keySz);
    if (ret == 0) {
        ret = RsaPublicEncrypt(in, inSz, out, *outSz, &myKey, &rng);
        if (ret > 0) {
            *outSz = ret;
            ret = 0;  /* reset to success */
        }
    }
    FreeRsaKey(&myKey);

    return ret;
}

static INLINE int myRsaDec(CYASSL* ssl, byte* in, word32 inSz,
                           byte** out,
                           const byte* key, word32 keySz, void* ctx)
{
    int     ret;
    word32  idx = 0;
    RsaKey  myKey;

    (void)ssl;
    (void)ctx;

    InitRsaKey(&myKey, NULL);
    
    ret = RsaPrivateKeyDecode(key, &idx, &myKey, keySz);
    if (ret == 0) {
        ret = RsaPrivateDecryptInline(in, inSz, out, &myKey);
    }
    FreeRsaKey(&myKey);

    return ret;
}

#endif /* NO_RSA */

static INLINE void SetupPkCallbacks(CYASSL_CTX* ctx, CYASSL* ssl)
{
    (void)ctx;
    (void)ssl;

    #ifdef HAVE_ECC
        CyaSSL_CTX_SetEccSignCb(ctx, myEccSign);
        CyaSSL_CTX_SetEccVerifyCb(ctx, myEccVerify);
    #endif /* HAVE_ECC */
    #ifndef NO_RSA 
        CyaSSL_CTX_SetRsaSignCb(ctx, myRsaSign);
        CyaSSL_CTX_SetRsaVerifyCb(ctx, myRsaVerify);
        CyaSSL_CTX_SetRsaEncCb(ctx, myRsaEnc);
        CyaSSL_CTX_SetRsaDecCb(ctx, myRsaDec);
    #endif /* NO_RSA */
}

#endif /* HAVE_PK_CALLBACKS */





#if defined(__hpux__) || defined(__MINGW32__)

/* HP/UX doesn't have strsep, needed by test/suites.c */
static INLINE char* strsep(char **stringp, const char *delim)
{
    char* start;
    char* end;

    start = *stringp;
    if (start == NULL)
        return NULL;

    if ((end = strpbrk(start, delim))) {
        *end++ = '\0';
        *stringp = end;
    } else {
        *stringp = NULL;
    }

    return start;
}

#endif /* __hpux__ */

#endif /* CyaSSL_TEST_H */

