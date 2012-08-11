/* test.h */

#ifndef CyaSSL_TEST_H
#define CyaSSL_TEST_H

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <ctype.h>
#include <cyassl/ctaocrypt/types.h>

#ifdef USE_WINDOWS_API 
    #include <winsock2.h>
    #include <process.h>
    #ifdef TEST_IPV6            /* don't require newer SDK for IPV4 */
	    #include <ws2tcpip.h>
        #include <wspiapi.h>
    #endif
    #define SOCKET_T int
#else
    #include <string.h>
    #include <unistd.h>
    #include <netdb.h>
    #include <netinet/in.h>
    #include <netinet/tcp.h>
    #include <arpa/inet.h>
    #include <sys/ioctl.h>
    #include <sys/time.h>
    #include <sys/types.h>
    #include <sys/socket.h>
    #include <pthread.h>
    #ifdef NON_BLOCKING
        #include <fcntl.h>
    #endif
    #ifdef TEST_IPV6
        #include <netdb.h>
    #endif
    #define SOCKET_T unsigned int
#endif /* USE_WINDOWS_API */

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


/* HPUX doesn't use socklent_t for third parameter to accept */
#if !defined(__hpux__)
    typedef socklen_t* ACCEPT_THIRD_T;
#else
    typedef int*       ACCEPT_THIRD_T;
#endif


#ifdef USE_WINDOWS_API 
    #define CloseSocket(s) closesocket(s)
    #define StartTCP() { WSADATA wsd; WSAStartup(0x0002, &wsd); }
#else
    #define CloseSocket(s) close(s)
    #define StartTCP() 
#endif


#ifdef SINGLE_THREADED
    typedef unsigned int  THREAD_RETURN;
    typedef void*         THREAD_TYPE;
    #define CYASSL_THREAD
#else
    #ifdef _POSIX_THREADS
        typedef void*         THREAD_RETURN;
        typedef pthread_t     THREAD_TYPE;
        #define CYASSL_THREAD
        #define INFINITE -1
        #define WAIT_OBJECT_0 0L
    #else
        typedef unsigned int  THREAD_RETURN;
        typedef HANDLE        THREAD_TYPE;
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
   

/* all certs relative to CyaSSL home directory now */
static const char* caCert   = "./certs/ca-cert.pem";
static const char* eccCert  = "./certs/server-ecc.pem";
static const char* eccKey   = "./certs/ecc-key.pem";
static const char* svrCert  = "./certs/server-cert.pem";
static const char* svrKey   = "./certs/server-key.pem";
static const char* cliCert  = "./certs/client-cert.pem";
static const char* cliKey   = "./certs/client-key.pem";
static const char* ntruCert = "./certs/ntru-cert.pem";
static const char* ntruKey  = "./certs/ntru-key.raw";
static const char* dhParam  = "./certs/dh2048.pem";
static const char* cliEccKey  = "./certs/ecc-client-key.pem";
static const char* cliEccCert = "./certs/client-ecc-cert.pem";
static const char* crlPemDir  = "./certs/crl";

typedef struct tcp_ready {
    int ready;              /* predicate */
#ifdef _POSIX_THREADS
    pthread_mutex_t mutex;
    pthread_cond_t  cond;
#endif
} tcp_ready;    


void InitTcpReady(tcp_ready*);
void FreeTcpReady(tcp_ready*);


typedef struct func_args {
    int    argc;
    char** argv;
    int    return_code;
    tcp_ready* signal;
} func_args;


typedef THREAD_RETURN CYASSL_THREAD THREAD_FUNC(void*);

void start_thread(THREAD_FUNC, func_args*, THREAD_TYPE*);
void join_thread(THREAD_TYPE);

/* yaSSL */
static const char* const yasslIP   = "127.0.0.1";
static const word16      yasslPort = 11111;


static INLINE void err_sys(const char* msg)
{
    printf("yassl error: %s\n", msg);
    exit(EXIT_FAILURE);
}


#ifdef OPENSSL_EXTRA

static int PasswordCallBack(char* passwd, int sz, int rw, void* userdata)
{
    strncpy(passwd, "yassl123", sz);
    return 8;
}

#endif


static INLINE void showPeer(CYASSL* ssl)
{
#ifdef OPENSSL_EXTRA

    CYASSL_CIPHER* cipher;
    CYASSL_X509*   peer = CyaSSL_get_peer_certificate(ssl);
    if (peer) {
        char* issuer  = CyaSSL_X509_NAME_oneline(
                                       CyaSSL_X509_get_issuer_name(peer), 0, 0);
        char* subject = CyaSSL_X509_NAME_oneline(
                                      CyaSSL_X509_get_subject_name(peer), 0, 0);
        byte  serial[32];
        int   ret;
        int   sz = sizeof(serial);
        
        printf("peer's cert info:\n issuer : %s\n subject: %s\n", issuer,
                                                                  subject);
        ret = CyaSSL_X509_get_serial_number(peer, serial, &sz);
        if (ret == 0) {
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
    else
        printf("peer has no cert!\n");
    printf("SSL version is %s\n", CyaSSL_get_version(ssl));

    cipher = CyaSSL_get_current_cipher(ssl);
    printf("SSL cipher suite is %s\n", CyaSSL_CIPHER_get_name(cipher));
#endif

#if defined(SESSION_CERTS) && defined(SHOW_CERTS)
    {
        X509_CHAIN* chain = CyaSSL_get_peer_chain(ssl);
        int         count = CyaSSL_get_chain_count(chain);
        int i;

        for (i = 0; i < count; i++) {
            int length;
            unsigned char buffer[3072];

            CyaSSL_get_chain_cert_pem(chain,i,buffer, sizeof(buffer), &length);
            buffer[length] = 0;
            printf("cert %d has length %d data = \n%s\n", i, length, buffer);
        }
    }
#endif

}


static INLINE void tcp_socket(SOCKET_T* sockfd, SOCKADDR_IN_T* addr,
                              const char* peer, word16 port)
{
#ifndef TEST_IPV6
    const char* host = peer;

    /* peer could be in human readable form */
    if (peer != INADDR_ANY && isalpha(peer[0])) {
        struct hostent* entry = gethostbyname(peer);

        if (entry) {
            struct sockaddr_in tmp;
            memset(&tmp, 0, sizeof(struct sockaddr_in));
            memcpy(&tmp.sin_addr.s_addr, entry->h_addr_list[0],
                   entry->h_length);
            host = inet_ntoa(tmp.sin_addr);
        }
        else
            err_sys("no entry for host");
    }
#endif

#ifdef CYASSL_DTLS
    *sockfd = socket(AF_INET_V, SOCK_DGRAM, 0);
#else
    *sockfd = socket(AF_INET_V, SOCK_STREAM, 0);
#endif
    memset(addr, 0, sizeof(SOCKADDR_IN_T));

#ifndef TEST_IPV6
    addr->sin_family = AF_INET_V;
    addr->sin_port = htons(port);
    if (host == INADDR_ANY)
        addr->sin_addr.s_addr = INADDR_ANY;
    else
        addr->sin_addr.s_addr = inet_addr(host);
#else
    addr->sin6_family = AF_INET_V;
    addr->sin6_port = htons(port);
    addr->sin6_addr = in6addr_loopback;
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
#endif

#if defined(TCP_NODELAY) && !defined(CYASSL_DTLS)
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


static INLINE void tcp_connect(SOCKET_T* sockfd, const char* ip, word16 port)
{
    SOCKADDR_IN_T addr;
    tcp_socket(sockfd, &addr, ip, port);

    if (connect(*sockfd, (const struct sockaddr*)&addr, sizeof(addr)) != 0)
        err_sys("tcp connect failed");
}


static INLINE void tcp_listen(SOCKET_T* sockfd)
{
    SOCKADDR_IN_T addr;

    /* don't use INADDR_ANY by default, firewall may block, make user switch
       on */
#ifdef USE_ANY_ADDR
    tcp_socket(sockfd, &addr, INADDR_ANY, yasslPort);
#else
    tcp_socket(sockfd, &addr, yasslIP, yasslPort);
#endif

#ifndef USE_WINDOWS_API 
    {
        int       on  = 1;
        socklen_t len = sizeof(on);
        setsockopt(*sockfd, SOL_SOCKET, SO_REUSEADDR, &on, len);
    }
#endif

    if (bind(*sockfd, (const struct sockaddr*)&addr, sizeof(addr)) != 0)
        err_sys("tcp bind failed");
#ifndef CYASSL_DTLS
    if (listen(*sockfd, 5) != 0)
        err_sys("tcp listen failed");
#endif
}


static INLINE int udp_read_connect(SOCKET_T sockfd)
{
    SOCKADDR_IN_T cliaddr;
    byte          b[1500];
    int           n;
    socklen_t     len = sizeof(cliaddr);

    n = recvfrom(sockfd, (char*)b, sizeof(b), MSG_PEEK,
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

static INLINE void udp_accept(SOCKET_T* sockfd, int* clientfd, func_args* args)
{
    SOCKADDR_IN_T addr;

    tcp_socket(sockfd, &addr, yasslIP, yasslPort);


#ifndef USE_WINDOWS_API 
    {
        int       on  = 1;
        socklen_t len = sizeof(on);
        setsockopt(*sockfd, SOL_SOCKET, SO_REUSEADDR, &on, len);
    }
#endif

    if (bind(*sockfd, (const struct sockaddr*)&addr, sizeof(addr)) != 0)
        err_sys("tcp bind failed");

#if defined(_POSIX_THREADS) && defined(NO_MAIN_DRIVER)
    /* signal ready to accept data */
    {
    tcp_ready* ready = args->signal;
    pthread_mutex_lock(&ready->mutex);
    ready->ready = 1;
    pthread_cond_signal(&ready->cond);
    pthread_mutex_unlock(&ready->mutex);
    }
#endif

    *clientfd = udp_read_connect(*sockfd);
}

static INLINE void tcp_accept(SOCKET_T* sockfd, int* clientfd, func_args* args)
{
    SOCKADDR_IN_T client;
    socklen_t client_len = sizeof(client);

    #ifdef CYASSL_DTLS
        udp_accept(sockfd, clientfd, args);
        return;
    #endif

    tcp_listen(sockfd);

#if defined(_POSIX_THREADS) && defined(NO_MAIN_DRIVER)
    /* signal ready to tcp_accept */
    {
    tcp_ready* ready = args->signal;
    pthread_mutex_lock(&ready->mutex);
    ready->ready = 1;
    pthread_cond_signal(&ready->cond);
    pthread_mutex_unlock(&ready->mutex);
    }
#endif

    *clientfd = accept(*sockfd, (struct sockaddr*)&client,
                      (ACCEPT_THIRD_T)&client_len);
    if (*clientfd == -1)
        err_sys("tcp accept failed");
}


static INLINE void tcp_set_nonblocking(SOCKET_T* sockfd)
{
#ifdef NON_BLOCKING
    #ifdef USE_WINDOWS_API 
        unsigned long blocking = 1;
        int ret = ioctlsocket(*sockfd, FIONBIO, &blocking);
    #else
        int flags = fcntl(*sockfd, F_GETFL, 0);
        int ret = fcntl(*sockfd, F_SETFL, flags | O_NONBLOCK);
    #endif
#endif
}


#ifndef NO_PSK

static INLINE unsigned int my_psk_client_cb(CYASSL* ssl, const char* hint,
        char* identity, unsigned int id_max_len, unsigned char* key,
        unsigned int key_max_len)
{
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

    #include <sys/time.h>

    static INLINE double current_time()
    {
        struct timeval tv;
        gettimeofday(&tv, 0);

        return (double)tv.tv_sec + (double)tv.tv_usec / 1000000;
    }

#endif /* USE_WINDOWS_API */


#ifdef NO_FILESYSTEM

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

static int myVerify(int preverify, CYASSL_X509_STORE_CTX* store)
{
    char buffer[80];

    printf("In verification callback, error = %d, %s\n", store->error,
                                 CyaSSL_ERR_error_string(store->error, buffer));
#ifdef OPENSSL_EXTRA
    CYASSL_X509* peer = store->current_cert;
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


#ifdef HAVE_CRL

static void CRL_CallBack(char* url)
{
    printf("CRL callback url = %s\n", url);
}

#endif


static INLINE void CaCb(unsigned char* der, int sz, int type)
{
    printf("Got CA cache add callback, derSz = %d, type = %d\n", sz, type);
}


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
    char path[MAX_PATH];

    GetCurrentDirectoryA(sizeof(path), path);
    if (strstr(path, str))
        return 1;

    return 0;
}

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
    char path[MAX_PATH];

    if (getcwd(path, sizeof(path)) == NULL) {
        printf("no current dir?\n");
        return 0;
    }
    if (strstr(path, str))
        return 1;

    return 0;
}

#endif /* USE_WINDOWS_API */

#endif /* CyaSSL_TEST_H */

