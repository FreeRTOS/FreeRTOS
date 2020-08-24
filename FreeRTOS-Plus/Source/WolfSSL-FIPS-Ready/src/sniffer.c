/* sniffer.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
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

#ifndef WOLFCRYPT_ONLY
#ifdef WOLFSSL_SNIFFER

#include <assert.h>
#include <time.h>

#ifndef _WIN32
  #include <arpa/inet.h>
#else
  #include <WS2tcpip.h>
#endif

#ifdef _WIN32
    #define SNPRINTF _snprintf
#else
    #define SNPRINTF snprintf
#endif

#include <wolfssl/internal.h>
#include <wolfssl/error-ssl.h>
#include <wolfssl/sniffer.h>
#include <wolfssl/sniffer_error.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
    #ifdef HAVE_INTEL_QA_SYNC
        #include <wolfssl/wolfcrypt/port/intel/quickassist_sync.h>
    #endif
    #ifdef HAVE_CAVIUM_OCTEON_SYNC
        #include <wolfssl/wolfcrypt/port/cavium/cavium_octeon_sync.h>
    #endif
#endif


#ifndef WOLFSSL_SNIFFER_TIMEOUT
    #define WOLFSSL_SNIFFER_TIMEOUT 900
    /* Cache unclosed Sessions for 15 minutes since last used */
#endif

/* Misc constants */
enum {
    MAX_SERVER_ADDRESS = 128, /* maximum server address length */
    MAX_SERVER_NAME    = 128, /* maximum server name length */
    MAX_ERROR_LEN      = 80,  /* maximum error length */
    ETHER_IF_ADDR_LEN  = 6,   /* ethernet interface address length */
    LOCAL_IF_ADDR_LEN  = 4,   /* localhost interface address length, !windows */
    TCP_PROTO          = 6,   /* TCP_PROTOCOL */
    IP_HDR_SZ          = 20,  /* IPv4 header length, min */
    IP6_HDR_SZ         = 40,  /* IPv6 header length, min */
    TCP_HDR_SZ         = 20,  /* TCP header length, min */
    IPV4               = 4,   /* IP version 4 */
    IPV6               = 6,   /* IP version 6 */
    TCP_PROTOCOL       = 6,   /* TCP Protocol id */
    NO_NEXT_HEADER     = 59,  /* IPv6 no headers follow */
    TRACE_MSG_SZ       = 80,  /* Trace Message buffer size */
    HASH_SIZE          = 499, /* Session Hash Table Rows */
    PSEUDO_HDR_SZ      = 12,  /* TCP Pseudo Header size in bytes */
    FATAL_ERROR_STATE  = 1,   /* SnifferSession fatal error state */
    TICKET_HINT_LEN    = 4,   /* Session Ticket Hint length */
    TICKET_HINT_AGE_LEN= 4,   /* Session Ticket Age add length */        
    EXT_TYPE_SZ        = 2,   /* Extension type length */
    MAX_INPUT_SZ       = MAX_RECORD_SIZE + COMP_EXTRA + MAX_MSG_EXTRA +
                         MTU_EXTRA,  /* Max input sz of reassembly */
    
    /* TLS Extensions */
    EXT_SERVER_NAME                = 0x0000, /* a.k.a. SNI  */
    EXT_MAX_FRAGMENT_LENGTH        = 0x0001,
    EXT_TRUSTED_CA_KEYS            = 0x0003,
    EXT_TRUNCATED_HMAC             = 0x0004,
    EXT_STATUS_REQUEST             = 0x0005, /* a.k.a. OCSP stapling   */
    EXT_SUPPORTED_GROUPS           = 0x000a, /* a.k.a. Supported Curves */
    EXT_EC_POINT_FORMATS           = 0x000b,
    EXT_SIGNATURE_ALGORITHMS       = 0x000d,
    EXT_APPLICATION_LAYER_PROTOCOL = 0x0010, /* a.k.a. ALPN */
    EXT_STATUS_REQUEST_V2          = 0x0011, /* a.k.a. OCSP stapling v2 */
    EXT_ENCRYPT_THEN_MAC           = 0x0016, /* RFC 7366 */
    EXT_MASTER_SECRET              = 0x0017, /* Extended Master Secret Extension ID */
    EXT_TICKET_ID                  = 0x0023, /* Session Ticket Extension ID */
    EXT_PRE_SHARED_KEY             = 0x0029,
    EXT_EARLY_DATA                 = 0x002a,
    EXT_SUPPORTED_VERSIONS         = 0x002b,
    EXT_COOKIE                     = 0x002c,
    EXT_PSK_KEY_EXCHANGE_MODES     = 0x002d,
    EXT_POST_HANDSHAKE_AUTH        = 0x0031,
    EXT_SIGNATURE_ALGORITHMS_CERT  = 0x0032,
    EXT_KEY_SHARE                  = 0x0033,
    EXT_RENEGOTIATION_INFO         = 0xff01
};


#ifdef _WIN32

static HMODULE dllModule;  /* for error string resources */

BOOL APIENTRY DllMain( HMODULE hModule,
                       DWORD  ul_reason_for_call,
                       LPVOID lpReserved
                     )
{
	static int didInit = 0;

    switch (ul_reason_for_call)
    {
    case DLL_PROCESS_ATTACH:
		if (didInit == 0) {
            dllModule = hModule;
			ssl_InitSniffer();
			didInit = 1;
		}
        break;
    case DLL_THREAD_ATTACH:
        break;
    case DLL_THREAD_DETACH:
        break;
    case DLL_PROCESS_DETACH:
		if (didInit) {
			ssl_FreeSniffer();
			didInit = 0;
		}
        break;
    }
    return TRUE;
}

#endif /* _WIN32 */


static WOLFSSL_GLOBAL int TraceOn = 0;         /* Trace is off by default */
static WOLFSSL_GLOBAL FILE* TraceFile = 0;


/* windows uses .rc table for this */
#ifndef _WIN32

static const char* const msgTable[] =
{
    /* 1 */
    "Out of Memory",
    "New SSL Sniffer Server Registered",
    "Checking IP Header",
    "SSL Sniffer Server Not Registered",
    "Checking TCP Header",

    /* 6 */
    "SSL Sniffer Server Port Not Registered",
    "RSA Private Decrypt Error",
    "RSA Private Decode Error",
    "Set Cipher Spec Error",
    "Server Hello Input Malformed",

    /* 11 */
    "Couldn't Resume Session Error",
    "Server Did Resumption",
    "Client Hello Input Malformed",
    "Client Trying to Resume",
    "Handshake Input Malformed",

    /* 16 */
    "Got Hello Verify msg",
    "Got Server Hello msg",
    "Got Cert Request msg",
    "Got Server Key Exchange msg",
    "Got Cert msg",

    /* 21 */
    "Got Server Hello Done msg",
    "Got Finished msg",
    "Got Client Hello msg",
    "Got Client Key Exchange msg",
    "Got Cert Verify msg",

    /* 26 */
    "Got Unknown Handshake msg",
    "New SSL Sniffer Session created",
    "Couldn't create new SSL",
    "Got a Packet to decode",
    "No data present",

    /* 31 */
    "Session Not Found",
    "Got an Old Client Hello msg",
    "Old Client Hello Input Malformed",
    "Old Client Hello OK",
    "Bad Old Client Hello",

    /* 36 */
    "Bad Record Header",
    "Record Header Input Malformed",
    "Got a HandShake msg",
    "Bad HandShake msg",
    "Got a Change Cipher Spec msg",

    /* 41 */
    "Got Application Data msg",
    "Bad Application Data",
    "Got an Alert msg",
    "Another msg to Process",
    "Removing Session From Table",

    /* 46 */
    "Bad Key File",
    "Wrong IP Version",
    "Wrong Protocol type",
    "Packet Short for header processing",
    "Got Unknown Record Type",

    /* 51 */
    "Can't Open Trace File",
    "Session in Fatal Error State",
    "Partial SSL record received",
    "Buffer Error, malformed input",
    "Added to Partial Input",

    /* 56 */
    "Received a Duplicate Packet",
    "Received an Out of Order Packet",
    "Received an Overlap Duplicate Packet",
    "Received an Overlap Reassembly Begin Duplicate Packet",
    "Received an Overlap Reassembly End Duplicate Packet",

    /* 61 */
    "Missed the Client Hello Entirely",
    "Got Hello Request msg",
    "Got Session Ticket msg",
    "Bad Input",
    "Bad Decrypt Type",

    /* 66 */
    "Bad Finished Message Processing",
    "Bad Compression Type",
    "Bad DeriveKeys Error",
    "Saw ACK for Missing Packet Error",
    "Bad Decrypt Operation",

    /* 71 */
    "Decrypt Keys Not Set Up",
    "Late Key Load Error",
    "Got Certificate Status msg",
    "RSA Key Missing Error",
    "Secure Renegotiation Not Supported",

    /* 76 */
    "Get Session Stats Failure",
    "Reassembly Buffer Size Exceeded",
    "Dropping Lost Fragment",
    "Dropping Partial Record",
    "Clear ACK Fault",

    /* 81 */
    "Bad Decrypt Size",
    "Extended Master Secret Hash Error",
    "Handshake Message Split Across TLS Records",
    "ECC Private Decode Error",
    "ECC Public Decode Error",

    /* 86 */
    "Watch callback not set",
    "Watch hash failed",
    "Watch callback failed",
    "Bad Certificate Message",
    "Store data callback not set",

    /* 91 */
    "No data destination Error",
    "Store data callback failed",
    "Loading chain input",
    "Got encrypted extension",
};


/* *nix version uses table above */
static void GetError(int idx, char* str)
{
    XSTRNCPY(str, msgTable[idx - 1], MAX_ERROR_LEN-1);
    str[MAX_ERROR_LEN-1] = '\0';
}


#else /* _WIN32 */


/* Windows version uses .rc table */
static void GetError(int idx, char* buffer)
{
    if (!LoadStringA(dllModule, idx, buffer, MAX_ERROR_LEN))
        buffer[0] = 0;
}


#endif /* _WIN32 */


/* Packet Buffer for reassembly list and ready list */
typedef struct PacketBuffer {
    word32  begin;      /* relative sequence begin */
    word32  end;        /* relative sequence end   */
    byte*   data;       /* actual data             */
    struct PacketBuffer* next; /* next on reassembly list or ready list */
} PacketBuffer;


#ifdef HAVE_SNI

/* NamedKey maps a SNI name to a specific private key */
typedef struct NamedKey {
    char             name[MAX_SERVER_NAME];      /* server DNS name */
    word32           nameSz;                     /* size of server DNS name */
    byte*            key;                        /* DER private key */
    word32           keySz;                      /* size of DER private key */
    int              isEphemeralKey;
    struct NamedKey* next;                       /* for list */
} NamedKey;

#endif


typedef struct IpAddrInfo {
    int version;
    union {
        word32 ip4;
        byte   ip6[16];
    };
} IpAddrInfo;


/* Sniffer Server holds info for each server/port monitored */
typedef struct SnifferServer {
    WOLFSSL_CTX*   ctx;                          /* SSL context */
    char           address[MAX_SERVER_ADDRESS];  /* passed in server address */
    IpAddrInfo     server;                       /* network order address */
    int            port;                         /* server port */
#ifdef HAVE_SNI
    NamedKey*      namedKeys;                    /* mapping of names and keys */
    wolfSSL_Mutex  namedKeysMutex;               /* mutex for namedKey list */
#endif
    struct SnifferServer* next;                  /* for list */
} SnifferServer;


/* Session Flags */
typedef struct Flags {
    byte           side;            /* which end is current packet headed */
    byte           serverCipherOn;  /* indicates whether cipher is active */
    byte           clientCipherOn;  /* indicates whether cipher is active */
    byte           resuming;        /* did this session come from resumption */
    byte           cached;          /* have we cached this session yet */
    byte           clientHello;     /* processed client hello yet, for SSLv2 */
    byte           finCount;        /* get both FINs before removing */
    byte           fatalError;      /* fatal error state */
    byte           cliAckFault;     /* client acked unseen data from server */
    byte           srvAckFault;     /* server acked unseen data from client */
    byte           cliSkipPartial;  /* client skips partial data to catch up */
    byte           srvSkipPartial;  /* server skips partial data to catch up */
#ifdef HAVE_EXTENDED_MASTER
    byte           expectEms;       /* expect extended master secret */
#endif
    byte           gotFinished;     /* processed finished */
} Flags;


/* Out of Order FIN capture */
typedef struct FinCapture {
    word32 cliFinSeq;               /* client relative sequence FIN  0 is no */
    word32 srvFinSeq;               /* server relative sequence FIN, 0 is no */
    byte   cliCounted;              /* did we count yet, detects duplicates */
    byte   srvCounted;              /* did we count yet, detects duplicates */
} FinCapture;


typedef struct HsHashes {
#ifndef NO_OLD_TLS
#ifndef NO_SHA
    wc_Sha hashSha;
#endif
#ifndef NO_MD5
    wc_Md5 hashMd5;
#endif
#endif /* !NO_OLD_TLS */
#ifndef NO_SHA256
    wc_Sha256 hashSha256;
#endif
#ifdef WOLFSSL_SHA384
    wc_Sha384 hashSha384;
#endif
} HsHashes;

typedef struct KeyShareInfo {
    word16      named_group;
    int         key_len;
    const byte* key;

    /* additional info */
    int         dh_key_bits;
    int         curve_id;
} KeyShareInfo;


/* Sniffer Session holds info for each client/server SSL/TLS session */
typedef struct SnifferSession {
    SnifferServer* context;         /* server context */
    WOLFSSL*       sslServer;       /* SSL server side decode */
    WOLFSSL*       sslClient;       /* SSL client side decode */
    IpAddrInfo     server;          /* server address in network byte order */
    IpAddrInfo     client;          /* client address in network byte order */
    word16         srvPort;         /* server port */
    word16         cliPort;         /* client port */
    word32         cliSeqStart;     /* client start sequence */
    word32         srvSeqStart;     /* server start sequence */
    word32         cliExpected;     /* client expected sequence (relative) */
    word32         srvExpected;     /* server expected sequence (relative) */
    FinCapture     finCapture;      /* retain out of order FIN s */
    Flags          flags;           /* session flags */
    time_t         lastUsed;        /* last used ticks */
    word32         keySz;           /* size of the private key */
    PacketBuffer*  cliReassemblyList; /* client out of order packets */
    PacketBuffer*  srvReassemblyList; /* server out of order packets */
    word32         cliReassemblyMemory; /* client packet memory used */
    word32         srvReassemblyMemory; /* server packet memory used */
    struct SnifferSession* next;    /* for hash table list */
    byte*          ticketID;        /* mac ID of session ticket */
#ifdef HAVE_SNI
    const char*    sni;             /* server name indication */
#endif
#ifdef HAVE_EXTENDED_MASTER
    HsHashes*      hash;
#endif
#ifdef WOLFSSL_TLS13
    byte*          cliKeyShare;
    word32         cliKeyShareSz;
    KeyShareInfo   srvKs;
    KeyShareInfo   cliKs;
#endif
} SnifferSession;


/* Sniffer Server List and mutex */
static WOLFSSL_GLOBAL SnifferServer* ServerList = 0;
static WOLFSSL_GLOBAL wolfSSL_Mutex ServerListMutex;


/* Session Hash Table, mutex, and count */
static WOLFSSL_GLOBAL SnifferSession* SessionTable[HASH_SIZE];
static WOLFSSL_GLOBAL wolfSSL_Mutex SessionMutex;
static WOLFSSL_GLOBAL int SessionCount = 0;

/* Recovery of missed data switches and stats */
static WOLFSSL_GLOBAL wolfSSL_Mutex RecoveryMutex; /* for stats */
static WOLFSSL_GLOBAL int RecoveryEnabled    = 0;  /* global switch */
static WOLFSSL_GLOBAL int MaxRecoveryMemory  = -1;
                                           /* per session max recovery memory */
static WOLFSSL_GLOBAL word32 MissedDataSessions = 0;
                                            /* # of sessions with missed data */

/* Connection Info Callback */
static WOLFSSL_GLOBAL SSLConnCb ConnectionCb;
static WOLFSSL_GLOBAL void* ConnectionCbCtx = NULL;

#ifdef WOLFSSL_SNIFFER_STATS
/* Sessions Statistics */
static WOLFSSL_GLOBAL SSLStats SnifferStats;
static WOLFSSL_GLOBAL wolfSSL_Mutex StatsMutex;
#endif

#ifdef WOLFSSL_SNIFFER_WATCH
/* Watch Key Callback */
static WOLFSSL_GLOBAL SSLWatchCb WatchCb;
static WOLFSSL_GLOBAL void* WatchCbCtx = NULL;
#endif

#ifdef WOLFSSL_SNIFFER_STORE_DATA_CB
/* Store Data Callback */
static WOLFSSL_GLOBAL SSLStoreDataCb StoreDataCb;
#endif


static void UpdateMissedDataSessions(void)
{
    wc_LockMutex(&RecoveryMutex);
    MissedDataSessions += 1;
    wc_UnLockMutex(&RecoveryMutex);
}


#ifdef WOLFSSL_SNIFFER_STATS
#define LOCK_STAT() do { wc_LockMutex(&StatsMutex); } while (0)
#define UNLOCK_STAT() do { wc_UnLockMutex(&StatsMutex); } while (0)
#define NOLOCK_ADD_TO_STAT(x,y) do { TraceStat(#x, y); x += y; } while (0)
#define NOLOCK_INC_STAT(x) NOLOCK_ADD_TO_STAT(x,1)
#define ADD_TO_STAT(x,y) do { LOCK_STAT(); \
    NOLOCK_ADD_TO_STAT(x,y); UNLOCK_STAT(); } while (0)
#define INC_STAT(x) do { LOCK_STAT(); \
    NOLOCK_INC_STAT(x); UNLOCK_STAT(); } while (0)
#endif


#ifdef WOLF_CRYPTO_CB
    static WOLFSSL_GLOBAL int CryptoDeviceId = INVALID_DEVID;
#endif


/* Initialize overall Sniffer */
void ssl_InitSniffer(void)
{
    wolfSSL_Init();
    wc_InitMutex(&ServerListMutex);
    wc_InitMutex(&SessionMutex);
    wc_InitMutex(&RecoveryMutex);
#ifdef WOLFSSL_SNIFFER_STATS
    XMEMSET(&SnifferStats, 0, sizeof(SSLStats));
    wc_InitMutex(&StatsMutex);
#endif
#ifdef WOLF_CRYPTO_CB
    #ifdef HAVE_INTEL_QA_SYNC
    CryptoDeviceId = wc_CryptoCb_InitIntelQa();
    if (INVALID_DEVID == CryptoDeviceId) {
        printf("Couldn't init the Intel QA\n");
    }
    #endif
    #ifdef HAVE_CAVIUM_OCTEON_SYNC
    CryptoDeviceId = wc_CryptoCb_InitOcteon();
    if (INVALID_DEVID == CryptoDeviceId) {
        printf("Couldn't init the Intel QA\n");
    }
    #endif
#endif
}


#ifdef HAVE_SNI

/* Free Named Key and the zero out the private key it holds */
static void FreeNamedKey(NamedKey* in)
{
    if (in) {
        if (in->key) {
            ForceZero(in->key, in->keySz);
            XFREE(in->key, NULL, DYNAMIC_TYPE_X509);
        }
        XFREE(in, NULL, DYNAMIC_TYPE_SNIFFER_NAMED_KEY);
    }
}


static void FreeNamedKeyList(NamedKey* in)
{
    NamedKey* next;

    while (in) {
        next = in->next;
        FreeNamedKey(in);
        in = next;
    }
}

#endif


/* Free Sniffer Server's resources/self */
static void FreeSnifferServer(SnifferServer* srv)
{
    if (srv) {
#ifdef HAVE_SNI
        wc_LockMutex(&srv->namedKeysMutex);
        FreeNamedKeyList(srv->namedKeys);
        wc_UnLockMutex(&srv->namedKeysMutex);
        wc_FreeMutex(&srv->namedKeysMutex);
#endif
        wolfSSL_CTX_free(srv->ctx);
    }
    XFREE(srv, NULL, DYNAMIC_TYPE_SNIFFER_SERVER);
}


/* free PacketBuffer's resources/self */
static void FreePacketBuffer(PacketBuffer* del)
{
    if (del) {
        XFREE(del->data, NULL, DYNAMIC_TYPE_SNIFFER_PB_BUFFER);
        XFREE(del, NULL, DYNAMIC_TYPE_SNIFFER_PB);
    }
}


/* remove PacketBuffer List */
static void FreePacketList(PacketBuffer* in)
{
    if (in) {
        PacketBuffer* del;
        PacketBuffer* packet = in;

        while (packet) {
            del = packet;
            packet = packet->next;
            FreePacketBuffer(del);
        }
    }
}


/* Free Sniffer Session's resources/self */
static void FreeSnifferSession(SnifferSession* session)
{
    if (session) {
        wolfSSL_free(session->sslClient);
        wolfSSL_free(session->sslServer);

        FreePacketList(session->cliReassemblyList);
        FreePacketList(session->srvReassemblyList);

        XFREE(session->ticketID, NULL, DYNAMIC_TYPE_SNIFFER_TICKET_ID);
#ifdef HAVE_EXTENDED_MASTER
        XFREE(session->hash, NULL, DYNAMIC_TYPE_HASHES);
#endif
#ifdef WOLFSSL_TLS13
        if (session->cliKeyShare)
            XFREE(session->cliKeyShare, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    }
    XFREE(session, NULL, DYNAMIC_TYPE_SNIFFER_SESSION);
}


/* Free overall Sniffer */
void ssl_FreeSniffer(void)
{
    SnifferServer*  srv;
    SnifferServer*  removeServer;
    SnifferSession* session;
    SnifferSession* removeSession;
    int i;

    wc_LockMutex(&ServerListMutex);
    wc_LockMutex(&SessionMutex);

    srv = ServerList;
    while (srv) {
        removeServer = srv;
        srv = srv->next;
        FreeSnifferServer(removeServer);
    }
    ServerList = NULL;

    for (i = 0; i < HASH_SIZE; i++) {
        session = SessionTable[i];
        while (session) {
            removeSession = session;
            session = session->next;
            FreeSnifferSession(removeSession);
        }
    }
    SessionCount = 0;

    wc_UnLockMutex(&SessionMutex);
    wc_UnLockMutex(&ServerListMutex);

    wc_FreeMutex(&RecoveryMutex);
    wc_FreeMutex(&SessionMutex);
    wc_FreeMutex(&ServerListMutex);

#ifdef WOLF_CRYPTO_CB
#ifdef HAVE_INTEL_QA_SYNC
    wc_CryptoCb_CleanupIntelQa(&CryptoDeviceId);
#endif
#ifdef HAVE_CAVIUM_OCTEON_SYNC
    wc_CryptoCb_CleanupOcteon(&CryptoDeviceId);
#endif
#endif

    if (TraceFile) {
        TraceOn = 0;
        fclose(TraceFile);
        TraceFile = NULL;
    }

    wolfSSL_Cleanup();
}


#ifdef HAVE_EXTENDED_MASTER

static int HashInit(HsHashes* hash)
{
    int ret = 0;

    XMEMSET(hash, 0, sizeof(HsHashes));

#ifndef NO_OLD_TLS
#ifndef NO_SHA
    if (ret == 0)
        ret = wc_InitSha(&hash->hashSha);
#endif
#ifndef NO_MD5
    if (ret == 0)
        ret = wc_InitMd5(&hash->hashMd5);
#endif
#endif /* !NO_OLD_TLS */
#ifndef NO_SHA256
    if (ret == 0)
        ret = wc_InitSha256(&hash->hashSha256);
#endif
#ifdef WOLFSSL_SHA384
    if (ret == 0)
        ret = wc_InitSha384(&hash->hashSha384);
#endif

    return ret;
}

static int HashUpdate(HsHashes* hash, const byte* input, int sz)
{
    int ret = 0;

    input -= HANDSHAKE_HEADER_SZ;
    sz += HANDSHAKE_HEADER_SZ;

#ifndef NO_OLD_TLS
#ifndef NO_SHA
    if (ret == 0)
        ret = wc_ShaUpdate(&hash->hashSha, input, sz);
#endif
#ifndef NO_MD5
    if (ret == 0)
        ret = wc_Md5Update(&hash->hashMd5, input, sz);
#endif
#endif /* !NO_OLD_TLS */
#ifndef NO_SHA256
    if (ret == 0)
        ret = wc_Sha256Update(&hash->hashSha256, input, sz);
#endif
#ifdef WOLFSSL_SHA384
    if (ret == 0)
        ret = wc_Sha384Update(&hash->hashSha384, input, sz);
#endif

    return ret;
}

static int HashCopy(HS_Hashes* d, HsHashes* s)
{
#ifndef NO_OLD_TLS
#ifndef NO_SHA
    XMEMCPY(&d->hashSha, &s->hashSha, sizeof(wc_Sha));
#endif
#ifndef NO_MD5
    XMEMCPY(&d->hashMd5, &s->hashMd5, sizeof(wc_Md5));
#endif
#endif /* !NO_OLD_TLS */
#ifndef NO_SHA256
    XMEMCPY(&d->hashSha256, &s->hashSha256, sizeof(wc_Sha256));
#endif
#ifdef WOLFSSL_SHA384
    XMEMCPY(&d->hashSha384, &s->hashSha384, sizeof(wc_Sha384));
#endif

    return 0;
}

#endif


/* Initialize a SnifferServer */
static void InitSnifferServer(SnifferServer* sniffer)
{
    XMEMSET(sniffer, 0, sizeof(SnifferServer));
}


/* Initialize session flags */
static void InitFlags(Flags* flags)
{
    XMEMSET(flags, 0, sizeof(Flags));
}


/* Initialize FIN Capture */
static void InitFinCapture(FinCapture* cap)
{
    XMEMSET(cap, 0, sizeof(FinCapture));
}


/* Initialize a Sniffer Session */
static void InitSession(SnifferSession* session)
{
    XMEMSET(session, 0, sizeof(SnifferSession));
    InitFlags(&session->flags);
    InitFinCapture(&session->finCapture);
}


/* IP Info from IP Header */
typedef struct IpInfo {
    int    length;        /* length of this header */
    int    total;         /* total length of fragment */
    IpAddrInfo src;       /* network order source address */
    IpAddrInfo dst;       /* network order destination address */
} IpInfo;


/* TCP Info from TCP Header */
typedef struct TcpInfo {
    int    srcPort;       /* source port */
    int    dstPort;       /* source port */
    int    length;        /* length of this header */
    word32 sequence;      /* sequence number */
    word32 ackNumber;     /* ack number */
    byte   fin;           /* FIN set */
    byte   rst;           /* RST set */
    byte   syn;           /* SYN set */
    byte   ack;           /* ACK set */
} TcpInfo;


/* Tcp Pseudo Header for Checksum calculation */
typedef struct TcpPseudoHdr {
    word32  src;        /* source address */
    word32  dst;        /* destination address */
    byte    rsv;        /* reserved, always 0 */
    byte    protocol;   /* IP protocol */
    word16  length;     /* tcp header length + data length (doesn't include */
                        /* pseudo header length) network order */
} TcpPseudoHdr;


/* Password Setting Callback */
static int SetPassword(char* passwd, int sz, int rw, void* userdata)
{
    (void)rw;
    XSTRNCPY(passwd, (const char*)userdata, sz);
    return (int)XSTRLEN((const char*)userdata);
}


/* Ethernet Header */
typedef struct EthernetHdr {
    byte   dst[ETHER_IF_ADDR_LEN];    /* destination host address */
    byte   src[ETHER_IF_ADDR_LEN];    /* source  host address */
    word16 type;                      /* IP, ARP, etc */
} EthernetHdr;


/* IPv4 Header */
typedef struct IpHdr {
    byte    ver_hl;              /* version/header length */
    byte    tos;                 /* type of service */
    word16  length;              /* total length */
    word16  id;                  /* identification */
    word16  offset;              /* fragment offset field */
    byte    ttl;                 /* time to live */
    byte    protocol;            /* protocol */
    word16  sum;                 /* checksum */
    word32  src;                 /* source address */
    word32  dst;                 /* destination address */
} IpHdr;


/* IPv6 Header */
typedef struct Ip6Hdr {
    byte    ver_hl;              /* version/traffic class high */
    byte    tc_fl;               /* traffic class low/flow label high */
    word16  fl;                  /* flow label low */
    word16  length;              /* payload length */
    byte    next_header;         /* next header (6 for TCP, any other skip) */
    byte    hl;                  /* hop limit */
    byte    src[16];             /* source address */
    byte    dst[16];             /* destination address */
} Ip6Hdr;


/* IPv6 extension header */
typedef struct Ip6ExtHdr {
    byte next_header;            /* next header (6 for TCP, any other skip) */
    byte length;                 /* length in 8-octet units - 1 */
    byte reserved[6];
} Ip6ExtHdr;


#define IP_HL(ip)      ( (((ip)->ver_hl) & 0x0f) * 4)
#define IP_V(ip)       ( ((ip)->ver_hl) >> 4)

/* TCP Header */
typedef struct TcpHdr {
    word16  srcPort;            /* source port */
    word16  dstPort;            /* destination port */
    word32  sequence;           /* sequence number */
    word32  ack;                /* acknowledgment number */
    byte    offset;             /* data offset, reserved */
    byte    flags;              /* option flags */
    word16  window;             /* window */
    word16  sum;                /* checksum */
    word16  urgent;             /* urgent pointer */
} TcpHdr;

#define TCP_LEN(tcp)  ( (((tcp)->offset & 0xf0) >> 4) * 4)
#define TCP_FIN 0x01
#define TCP_SYN 0x02
#define TCP_RST 0x04
#define TCP_ACK 0x10





/* Use platform specific GetError to write to trace file if tracing */
static void Trace(int idx)
{
    if (TraceOn) {
        char myBuffer[MAX_ERROR_LEN];
        GetError(idx, myBuffer);
        fprintf(TraceFile, "\t%s\n", myBuffer);
#ifdef DEBUG_SNIFFER
        fprintf(stderr,    "\t%s\n", myBuffer);
#endif
    }
}


/* Show TimeStamp for beginning of packet Trace */
static void TraceHeader(void)
{
    if (TraceOn) {
        time_t ticks = time(NULL);
        fprintf(TraceFile, "\n%s", ctime(&ticks));
    }
}


/* Show Set Server info for Trace */
static void TraceSetServer(const char* srv, int port, const char* keyFile)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tTrying to install a new Sniffer Server with\n");
        fprintf(TraceFile, "\tserver: %s, port: %d, keyFile: %s\n", srv, port,
                                                                    keyFile);
    }
}


#ifdef HAVE_SNI

/* Show Set Named Server info for Trace */
static void TraceSetNamedServer(const char* name,
                                 const char* srv, int port, const char* keyFile)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tTrying to install a new Sniffer Server with\n");
        fprintf(TraceFile, "\tname: %s, server: %s, port: %d, keyFile: %s\n",
                                                      name, srv, port, keyFile);
    }
}

#endif


/* Trace got packet number */
static void TracePacket(void)
{
    if (TraceOn) {
        static word32 packetNumber = 0;
        fprintf(TraceFile, "\tGot a Packet to decode, packet %u\n",
                ++packetNumber);
    }
}


/* Convert network byte order address into human readable */
static const char* IpToS(int version, void* src, char* dst)
{
    return inet_ntop(version, src, dst, TRACE_MSG_SZ);
}


/* Show destination and source address from Ip Hdr for packet Trace */
static void TraceIP(IpHdr* iphdr)
{
    if (TraceOn) {
        char src[TRACE_MSG_SZ];
        char dst[TRACE_MSG_SZ];
        fprintf(TraceFile, "\tdst:%s src:%s\n",
                IpToS(AF_INET, &iphdr->dst, dst),
                IpToS(AF_INET, &iphdr->src, src));
    }
}


/* Show destination and source address from Ip6Hdr for packet Trace */
static void TraceIP6(Ip6Hdr* iphdr)
{
    if (TraceOn) {
        char src[TRACE_MSG_SZ];
        char dst[TRACE_MSG_SZ];
        fprintf(TraceFile, "\tdst: %s src: %s\n",
                IpToS(AF_INET6, iphdr->dst, dst),
                IpToS(AF_INET6, iphdr->src, src));
    }
}


/* Show destination and source port from Tcp Hdr for packet Trace */
static void TraceTcp(TcpHdr* tcphdr)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tdstPort:%u srcPort:%u\n", ntohs(tcphdr->dstPort),
                ntohs(tcphdr->srcPort));
    }
}


/* Show sequence and payload length for Trace */
static void TraceSequence(word32 seq, int len)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tSequence:%u, payload length:%d\n", seq, len);
    }
}


/* Show sequence and payload length for Trace */
static void TraceAck(word32 ack, word32 expected)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tAck:%u Expected:%u\n", ack, expected);
    }
}


/* Show relative expected and relative received sequences */
static void TraceRelativeSequence(word32 expected, word32 got)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tExpected sequence:%u, received sequence:%u\n",
                expected, got);
    }
}


/* Show server sequence startup from SYN */
static void TraceServerSyn(word32 seq)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tServer SYN, Sequence Start:%u\n", seq);
    }
}


/* Show client sequence startup from SYN */
static void TraceClientSyn(word32 seq)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tClient SYN, Sequence Start:%u\n", seq);
    }
}


/* Show client FIN capture */
static void TraceClientFin(word32 finSeq, word32 relSeq)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tClient FIN capture:%u, current SEQ:%u\n",
                finSeq, relSeq);
    }
}


/* Show server FIN capture */
static void TraceServerFin(word32 finSeq, word32 relSeq)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tServer FIN capture:%u, current SEQ:%u\n",
                finSeq, relSeq);
    }
}


/* Show number of SSL data bytes decoded, could be 0 (ok) */
static void TraceGotData(int bytes)
{
    if (TraceOn) {
        fprintf(TraceFile, "\t%d bytes of SSL App data processed\n", bytes);
    }
}


/* Show bytes added to old SSL App data */
static void TraceAddedData(int newBytes, int existingBytes)
{
    if (TraceOn) {
        fprintf(TraceFile,
                "\t%d bytes added to %d existing bytes in User Buffer\n",
                newBytes, existingBytes);
    }
}


/* Show Stale Session */
static void TraceStaleSession(void)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tFound a stale session\n");
    }
}


/* Show Finding Stale Sessions */
static void TraceFindingStale(void)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tTrying to find Stale Sessions\n");
    }
}


/* Show Removed Session */
static void TraceRemovedSession(void)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tRemoved it\n");
    }
}


/* Show SSLInfo if provided and is valid. */
static void TraceSessionInfo(SSLInfo* sslInfo)
{
    if (TraceOn) {
        if (sslInfo != NULL && sslInfo->isValid) {
            fprintf(TraceFile,
                    "\tver:(%u %u) suiteId:(%02x %02x) suiteName:(%s) "
                    #ifdef HAVE_SNI
                    "sni:(%s) "
                    #endif
                    "keySize:(%u)\n",
                    sslInfo->protocolVersionMajor,
                    sslInfo->protocolVersionMinor,
                    sslInfo->serverCipherSuite0,
                    sslInfo->serverCipherSuite,
                    sslInfo->serverCipherSuiteName,
                    #ifdef HAVE_SNI
                    sslInfo->serverNameIndication,
                    #endif
                    sslInfo->keySize);
        }
    }
}


#ifdef WOLFSSL_SNIFFER_STATS

/* Show value added to a named statistic. */
static void TraceStat(const char* name, int add)
{
    if (TraceOn) {
        fprintf(TraceFile, "\tAdding %d to %s\n", add, name);
    }
}

#endif


/* Set user error string */
static void SetError(int idx, char* error, SnifferSession* session, int fatal)
{
    GetError(idx, error);
    Trace(idx);
    if (session && fatal == FATAL_ERROR_STATE)
        session->flags.fatalError = 1;
}


/* Compare IpAddrInfo structs */
static WC_INLINE int MatchAddr(IpAddrInfo l, IpAddrInfo r)
{
    if (l.version == r.version) {
        if (l.version == IPV4)
            return (l.ip4 == r.ip4);
        else if (l.version == IPV6)
            return (0 == XMEMCMP(l.ip6, r.ip6, sizeof(l.ip6)));
    }
    return 0;
}


#ifndef WOLFSSL_SNIFFER_WATCH

/* See if this IPV4 network order address has been registered */
/* return 1 is true, 0 is false */
static int IsServerRegistered(word32 addr)
{
    int ret = 0;     /* false */
    SnifferServer* sniffer;

    wc_LockMutex(&ServerListMutex);

    sniffer = ServerList;
    while (sniffer) {
        if (sniffer->server.ip4 == addr) {
            ret = 1;
            break;
        }
        sniffer = sniffer->next;
    }

    wc_UnLockMutex(&ServerListMutex);

    return ret;
}


/* See if this port has been registered to watch */
/* See if this IPV4 network order address has been registered */
/* return 1 is true, 0 is false */
static int IsServerRegistered6(byte* addr)
{
    int ret = 0;     /* false */
    SnifferServer* sniffer;

    wc_LockMutex(&ServerListMutex);

    sniffer = ServerList;
    while (sniffer) {
        if (sniffer->server.version == IPV6 &&
                0 == XMEMCMP(sniffer->server.ip6, addr, sizeof(sniffer->server.ip6))) {
            ret = 1;
            break;
        }
        sniffer = sniffer->next;
    }

    wc_UnLockMutex(&ServerListMutex);

    return ret;
}


/* See if this port has been registered to watch */
/* return 1 is true, 0 is false */
static int IsPortRegistered(word32 port)
{
    int ret = 0;    /* false */
    SnifferServer* sniffer;

    wc_LockMutex(&ServerListMutex);

    sniffer = ServerList;
    while (sniffer) {
        if (sniffer->port == (int)port) {
            ret = 1;
            break;
        }
        sniffer = sniffer->next;
    }

    wc_UnLockMutex(&ServerListMutex);

    return ret;
}

#endif


/* Get SnifferServer from IP and Port */
static SnifferServer* GetSnifferServer(IpInfo* ipInfo, TcpInfo* tcpInfo)
{
    SnifferServer* sniffer;

    wc_LockMutex(&ServerListMutex);

    sniffer = ServerList;

#ifndef WOLFSSL_SNIFFER_WATCH
    while (sniffer) {
        if (sniffer->port == tcpInfo->srcPort &&
                MatchAddr(sniffer->server, ipInfo->src))
            break;
        if (sniffer->port == tcpInfo->dstPort &&
                MatchAddr(sniffer->server, ipInfo->dst))
            break;

        sniffer = sniffer->next;
    }
#else
    (void)ipInfo;
    (void)tcpInfo;
#endif

    wc_UnLockMutex(&ServerListMutex);

    return sniffer;
}


/* Hash the Session Info, return hash row */
static word32 SessionHash(IpInfo* ipInfo, TcpInfo* tcpInfo)
{
    word32 hash = 1;

    if (ipInfo->src.version == IPV4) {
        hash *= ipInfo->src.ip4 * ipInfo->dst.ip4;
    }
    else if (ipInfo->src.version == IPV6) {
        word32* x;
        word32  y;
        x = (word32*)ipInfo->src.ip6;
        y = x[0] ^ x[1] ^ x[2] ^ x[3];
        hash *= y;
        x = (word32*)ipInfo->dst.ip6;
        y = x[0] ^ x[1] ^ x[2] ^ x[3];
        hash *= y;
    }
    hash *= tcpInfo->srcPort * tcpInfo->dstPort;

    return hash % HASH_SIZE;
}


/* Get Existing SnifferSession from IP and Port */
static SnifferSession* GetSnifferSession(IpInfo* ipInfo, TcpInfo* tcpInfo)
{
    SnifferSession* session;
    time_t          currTime = time(NULL);
    word32          row = SessionHash(ipInfo, tcpInfo);

    assert(row <= HASH_SIZE);

    wc_LockMutex(&SessionMutex);

    session = SessionTable[row];
    while (session) {
        if (MatchAddr(session->server, ipInfo->src) &&
            MatchAddr(session->client, ipInfo->dst) &&
                    session->srvPort == tcpInfo->srcPort &&
                    session->cliPort == tcpInfo->dstPort)
            break;

        if (MatchAddr(session->client, ipInfo->src) &&
            MatchAddr(session->server, ipInfo->dst) &&
                    session->cliPort == tcpInfo->srcPort &&
                    session->srvPort == tcpInfo->dstPort)
            break;

        session = session->next;
    }

    if (session)
        session->lastUsed= currTime; /* keep session alive, remove stale will */
                                     /* leave alone */
    wc_UnLockMutex(&SessionMutex);

    /* determine side */
    if (session) {
        if (MatchAddr(ipInfo->dst, session->server) &&
            tcpInfo->dstPort == session->srvPort) {

            session->flags.side = WOLFSSL_SERVER_END;
        }
        else {
            session->flags.side = WOLFSSL_CLIENT_END;
        }
    }

    return session;
}


#if defined(HAVE_SNI) || defined(WOLFSSL_SNIFFER_WATCH)

static int LoadKeyFile(byte** keyBuf, word32* keyBufSz,
                const char* keyFile, int keySz, int typeKey,
                const char* password)
{
    byte* loadBuf;
    long fileSz = 0;
    XFILE file;
    int ret = -1;

    if (keyBuf == NULL || keyBufSz == NULL || keyFile == NULL) {
        return -1;
    }

    if (keySz == 0) {
        /* load from file */
        file = XFOPEN(keyFile, "rb");
        if (file == XBADFILE) return -1;
        if(XFSEEK(file, 0, XSEEK_END) != 0) {
            XFCLOSE(file);
            return -1;
        }
        fileSz = XFTELL(file);
        if (fileSz > MAX_WOLFSSL_FILE_SIZE || fileSz < 0) {
            XFCLOSE(file);
            return -1;
        }
        XREWIND(file);

        loadBuf = (byte*)XMALLOC(fileSz, NULL, DYNAMIC_TYPE_FILE);
        if (loadBuf == NULL) {
            XFCLOSE(file);
            return -1;
        }

        ret = (int)XFREAD(loadBuf, 1, fileSz, file);
        XFCLOSE(file);

        if (ret != fileSz) {
            XFREE(loadBuf, NULL, DYNAMIC_TYPE_FILE);
            return -1;
        }
    }
    else {
        /* use buffer directly */
        loadBuf = (byte*)XMALLOC(keySz, NULL, DYNAMIC_TYPE_FILE);
        if (loadBuf == NULL) {
            return -1;
        }
        fileSz = keySz;
        XMEMCPY(loadBuf, keyFile, fileSz);        
    }

    if (typeKey == WOLFSSL_FILETYPE_PEM) {
        byte* saveBuf   = (byte*)XMALLOC(fileSz, NULL, DYNAMIC_TYPE_X509);
        int   saveBufSz = 0;

        ret = -1;
        if (saveBuf != NULL) {
            saveBufSz = wc_KeyPemToDer(loadBuf, (int)fileSz,
                                                saveBuf, (int)fileSz, password);
            if (saveBufSz < 0) {
                saveBufSz = 0;
                XFREE(saveBuf, NULL, DYNAMIC_TYPE_X509);
                saveBuf = NULL;
            }
            else
                ret = 0;
        }

        ForceZero(loadBuf, (word32)fileSz);
        XFREE(loadBuf, NULL, DYNAMIC_TYPE_FILE);

        if (saveBuf) {
            *keyBuf = saveBuf;
            *keyBufSz = (word32)saveBufSz;
        }
    }
    else {
        *keyBuf = loadBuf;
        *keyBufSz = (word32)fileSz;
    }

    if (ret < 0) {
        return -1;
    }

    return ret;
}

#endif


#ifdef WOLFSSL_SNIFFER_WATCH

static int CreateWatchSnifferServer(char* error)
{
    SnifferServer* sniffer;

    sniffer = (SnifferServer*)XMALLOC(sizeof(SnifferServer), NULL,
            DYNAMIC_TYPE_SNIFFER_SERVER);
    if (sniffer == NULL) {
        SetError(MEMORY_STR, error, NULL, 0);
        return -1;
    }
    InitSnifferServer(sniffer);
    sniffer->ctx = wolfSSL_CTX_new(SSLv23_client_method());
    if (!sniffer->ctx) {
        SetError(MEMORY_STR, error, NULL, 0);
        FreeSnifferServer(sniffer);
        return -1;
    }
#ifdef WOLF_CRYPTO_CB
    if (CryptoDeviceId != INVALID_DEVID)
	    wolfSSL_CTX_SetDevId(sniffer->ctx, CryptoDeviceId);
#endif
    ServerList = sniffer;

    return 0;
}

#endif


static int SetNamedPrivateKey(const char* name, const char* address, int port,
    const char* keyFile, int keySz, int typeKey, const char* password,
    char* error, int isEphemeralKey)
{
    SnifferServer* sniffer;
    int            ret;
    int            type = (typeKey == FILETYPE_PEM) ? WOLFSSL_FILETYPE_PEM :
                                                      WOLFSSL_FILETYPE_ASN1;
    int            isNew = 0;
    IpAddrInfo     serverIp;

#ifdef HAVE_SNI
    NamedKey* namedKey = NULL;
#endif

    (void)name;
#ifdef HAVE_SNI
    if (name != NULL) {
        namedKey = (NamedKey*)XMALLOC(sizeof(NamedKey),
                NULL, DYNAMIC_TYPE_SNIFFER_NAMED_KEY);
        if (namedKey == NULL) {
            SetError(MEMORY_STR, error, NULL, 0);
            return -1;
        }
        XMEMSET(namedKey, 0, sizeof(NamedKey));

        namedKey->nameSz = (word32)XSTRLEN(name);
        if (namedKey->nameSz > sizeof(namedKey->name)-1)
            namedKey->nameSz = sizeof(namedKey->name)-1;
        XSTRNCPY(namedKey->name, name, namedKey->nameSz);
        namedKey->name[MAX_SERVER_NAME-1] = '\0';
        namedKey->isEphemeralKey = isEphemeralKey;
        ret = LoadKeyFile(&namedKey->key, &namedKey->keySz,
                          keyFile, keySz, type, password);
        if (ret < 0) {
            SetError(KEY_FILE_STR, error, NULL, 0);
            FreeNamedKey(namedKey);
            return -1;
        }
    }
#endif

    serverIp.version = IPV4;
    serverIp.ip4 = inet_addr(address);
    if (serverIp.ip4 == INADDR_NONE) {
        if (inet_pton(AF_INET6, address, serverIp.ip6) == 1) {
            serverIp.version = IPV6;
        }
    }
    sniffer = ServerList;
    while (sniffer != NULL &&
            (!MatchAddr(sniffer->server, serverIp) || sniffer->port != port)) {
        sniffer = sniffer->next;
    }

    if (sniffer == NULL) {
        isNew = 1;
        sniffer = (SnifferServer*)XMALLOC(sizeof(SnifferServer),
                NULL, DYNAMIC_TYPE_SNIFFER_SERVER);
        if (sniffer == NULL) {
            SetError(MEMORY_STR, error, NULL, 0);
#ifdef HAVE_SNI
            FreeNamedKey(namedKey);
#endif
            return -1;
        }
        InitSnifferServer(sniffer);

        XSTRNCPY(sniffer->address, address, MAX_SERVER_ADDRESS-1);
        sniffer->address[MAX_SERVER_ADDRESS-1] = '\0';
        sniffer->server = serverIp;
        sniffer->port = port;

        sniffer->ctx = wolfSSL_CTX_new(SSLv23_client_method());
        if (!sniffer->ctx) {
            SetError(MEMORY_STR, error, NULL, 0);
#ifdef HAVE_SNI
            FreeNamedKey(namedKey);
#endif
            FreeSnifferServer(sniffer);
            return -1;
        }
    }

    if (name == NULL) {
        if (password) {
    #ifdef WOLFSSL_ENCRYPTED_KEYS
            wolfSSL_CTX_set_default_passwd_cb(sniffer->ctx, SetPassword);
            wolfSSL_CTX_set_default_passwd_cb_userdata(
                                                 sniffer->ctx, (void*)password);
    #endif
        }

    #ifdef WOLFSSL_STATIC_EPHEMERAL
        if (isEphemeralKey) {
            /* auto detect key type with WC_PK_TYPE_NONE */
            /* keySz == 0 mean load file */
            ret = wolfSSL_CTX_set_ephemeral_key(sniffer->ctx, WC_PK_TYPE_NONE, 
                keyFile, 0, type);
            if (ret == 0)
                ret = WOLFSSL_SUCCESS;
        }
        else
    #endif
        {
            if (keySz == 0) {
                ret = wolfSSL_CTX_use_PrivateKey_file(sniffer->ctx, keyFile, type);
            }
            else {
                ret = wolfSSL_CTX_use_PrivateKey_buffer(sniffer->ctx,
                                            (const byte*)keyFile, keySz, type);
            }
        }
        if (ret != WOLFSSL_SUCCESS) {
            SetError(KEY_FILE_STR, error, NULL, 0);
            if (isNew)
                FreeSnifferServer(sniffer);
            return -1;
        }
	#ifdef WOLF_CRYPTO_CB
		wolfSSL_CTX_SetDevId(sniffer->ctx, CryptoDeviceId);
	#endif
    }
#ifdef HAVE_SNI
    else {
        wc_LockMutex(&sniffer->namedKeysMutex);
        namedKey->next = sniffer->namedKeys;
        sniffer->namedKeys = namedKey;
        wc_UnLockMutex(&sniffer->namedKeysMutex);
    }
#endif

    if (isNew) {
        sniffer->next = ServerList;
        ServerList = sniffer;
    }

    return 0;
}


#ifdef HAVE_SNI
/* Sets the private key for a specific name, server and port  */
/* returns 0 on success, -1 on error */
int ssl_SetNamedPrivateKey(const char* name,
                           const char* address, int port,
                           const char* keyFile, int typeKey,
                           const char* password, char* error)
{
    int ret;

    TraceHeader();
    TraceSetNamedServer(name, address, port, keyFile);

    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(name, address, port, keyFile, 0,
                             typeKey, password, error, 0);
    wc_UnLockMutex(&ServerListMutex);

    if (ret == 0)
        Trace(NEW_SERVER_STR);

    return ret;
}

int ssl_SetNamedPrivateKeyBuffer(const char* name,
                                 const char* address, int port,
                                 const char* keyBuf, int keySz, int typeKey, 
                                 const char* password, char* error)
{
    int ret;

    TraceHeader();
    TraceSetNamedServer(name, address, port, NULL);

    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(name, address, port, keyBuf, keySz,
                             typeKey, password, error, 0);
    wc_UnLockMutex(&ServerListMutex);

    if (ret == 0)
        Trace(NEW_SERVER_STR);

    return ret;
}
#endif /* HAVE_SNI */

/* Sets the private key for a specific server and port  */
/* returns 0 on success, -1 on error */
int ssl_SetPrivateKey(const char* address, int port, 
                      const char* keyFile, int typeKey, 
                      const char* password, char* error)
{
    int ret;

    TraceHeader();
    TraceSetServer(address, port, keyFile);

    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(NULL, address, port, keyFile, 0,
                             typeKey, password, error, 0);
    wc_UnLockMutex(&ServerListMutex);

    if (ret == 0)
        Trace(NEW_SERVER_STR);

    return ret;
}

int ssl_SetPrivateKeyBuffer(const char* address, int port,
                            const char* keyBuf, int keySz, int typeKey, 
                            const char* password, char* error)
{
    int ret;

    TraceHeader();
    TraceSetServer(address, port, "from buffer");

    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(NULL, address, port, keyBuf, keySz,
                             typeKey, password, error, 0);
    wc_UnLockMutex(&ServerListMutex);

    if (ret == 0)
        Trace(NEW_SERVER_STR);

    return ret;
}

#ifdef WOLFSSL_STATIC_EPHEMERAL
#ifdef HAVE_SNI
/* Sets the ephemeral key for a specific name, server and port  */
/* returns 0 on success, -1 on error */
int ssl_SetNamedEphemeralKey(const char* name,
                             const char* address, int port,
                             const char* keyFile, int typeKey,
                             const char* password, char* error)
{
    int ret;
    
    TraceHeader();
    TraceSetNamedServer(name, address, port, keyFile);
    
    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(name, address, port, keyFile, 0,
                             typeKey, password, error, 1);
    wc_UnLockMutex(&ServerListMutex);
    
    if (ret == 0)
        Trace(NEW_SERVER_STR);
    
    return ret;
}

int ssl_SetNamedEphemeralKeyBuffer(const char* name,
                                   const char* address, int port,
                                   const char* keyBuf, int keySz, int typeKey, 
                                   const char* password, char* error)
{
    int ret;
    
    TraceHeader();
    TraceSetNamedServer(name, address, port, NULL);
    
    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(name, address, port, keyBuf, keySz,
                             typeKey, password, error, 1);
    wc_UnLockMutex(&ServerListMutex);
    
    if (ret == 0)
        Trace(NEW_SERVER_STR);
    
    return ret;
}
#endif /* HAVE_SNI */

/* Sets the ephemeral key for a specific server and port  */
/* returns 0 on success, -1 on error */
int ssl_SetEphemeralKey(const char* address, int port, 
                        const char* keyFile, int typeKey, 
                        const char* password, char* error)
{
    int ret;
    
    TraceHeader();
    TraceSetServer(address, port, keyFile);
    
    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(NULL, address, port, keyFile, 0,
                             typeKey, password, error, 1);
    wc_UnLockMutex(&ServerListMutex);
    
    if (ret == 0)
        Trace(NEW_SERVER_STR);
    
    return ret;
}

int ssl_SetEphemeralKeyBuffer(const char* address, int port, 
                              const char* keyBuf, int keySz, int typeKey, 
                              const char* password, char* error)
{
    int ret;
    
    TraceHeader();
    TraceSetServer(address, port, "from buffer");
    
    wc_LockMutex(&ServerListMutex);
    ret = SetNamedPrivateKey(NULL, address, port, keyBuf, keySz,
                             typeKey, password, error, 1);
    wc_UnLockMutex(&ServerListMutex);
    
    if (ret == 0)
        Trace(NEW_SERVER_STR);
    
    return ret;
}
#endif /* WOLFSSL_STATIC_EPHEMERAL */

/* Check IP Header for IPV6, TCP, and a registered server address */
/* returns 0 on success, -1 on error */
static int CheckIp6Hdr(Ip6Hdr* iphdr, IpInfo* info, int length, char* error)
{
    int        version = IP_V(iphdr);
    int        exthdrsz = IP6_HDR_SZ;

    TraceIP6(iphdr);
    Trace(IP_CHECK_STR);

    if (version != IPV6) {
        SetError(BAD_IPVER_STR, error, NULL, 0);
        return -1;
    }

    /* Here, we need to move onto next header if not TCP. */
    if (iphdr->next_header != TCP_PROTOCOL) {
        Ip6ExtHdr* exthdr = (Ip6ExtHdr*)((byte*)iphdr + IP6_HDR_SZ);
        do {
            int hdrsz = (exthdr->length + 1) * 8;
            if (hdrsz > length - exthdrsz) {
                SetError(PACKET_HDR_SHORT_STR, error, NULL, 0);
                return -1;
            }
            exthdrsz += hdrsz;
            exthdr = (Ip6ExtHdr*)((byte*)exthdr + hdrsz);
        }
        while (exthdr->next_header != TCP_PROTOCOL &&
                exthdr->next_header != NO_NEXT_HEADER);
    }

#ifndef WOLFSSL_SNIFFER_WATCH
    if (!IsServerRegistered6(iphdr->src) && !IsServerRegistered6(iphdr->dst)) {
        SetError(SERVER_NOT_REG_STR, error, NULL, 0);
        return -1;
    }
#endif

    info->length = exthdrsz;
    info->total = ntohs(iphdr->length) + info->length;
    /* IPv6 doesn't include its own header size in the length like v4. */
    info->src.version = IPV6;
    XMEMCPY(info->src.ip6, iphdr->src, sizeof(info->src.ip6));
    info->dst.version = IPV6;
    XMEMCPY(info->dst.ip6, iphdr->dst, sizeof(info->dst.ip6));

    return 0;
}


/* Check IP Header for IPV4, TCP, and a registered server address */
/* If header IPv6, pass to CheckIp6Hdr(). */
/* returns 0 on success, -1 on error */
static int CheckIpHdr(IpHdr* iphdr, IpInfo* info, int length, char* error)
{
    int    version = IP_V(iphdr);

    if (version == IPV6)
        return CheckIp6Hdr((Ip6Hdr*)iphdr, info, length, error);

    TraceIP(iphdr);
    Trace(IP_CHECK_STR);

    if (version != IPV4) {
        SetError(BAD_IPVER_STR, error, NULL, 0);
        return -1;
    }

    if (iphdr->protocol != TCP_PROTOCOL) {
        SetError(BAD_PROTO_STR, error, NULL, 0);
        return -1;
    }

#ifndef WOLFSSL_SNIFFER_WATCH
    if (!IsServerRegistered(iphdr->src) && !IsServerRegistered(iphdr->dst)) {
        SetError(SERVER_NOT_REG_STR, error, NULL, 0);
        return -1;
    }
#endif

    info->length  = IP_HL(iphdr);
    info->total   = ntohs(iphdr->length);
    info->src.version = IPV4;
    info->src.ip4 = iphdr->src;
    info->dst.version = IPV4;
    info->dst.ip4 = iphdr->dst;

    if (info->total == 0)
        info->total = length;  /* reassembled may be off */

    return 0;
}


/* Check TCP Header for a registered port */
/* returns 0 on success, -1 on error */
static int CheckTcpHdr(TcpHdr* tcphdr, TcpInfo* info, char* error)
{
    TraceTcp(tcphdr);
    Trace(TCP_CHECK_STR);
    info->srcPort   = ntohs(tcphdr->srcPort);
    info->dstPort   = ntohs(tcphdr->dstPort);
    info->length    = TCP_LEN(tcphdr);
    info->sequence  = ntohl(tcphdr->sequence);
    info->fin       = tcphdr->flags & TCP_FIN;
    info->rst       = tcphdr->flags & TCP_RST;
    info->syn       = tcphdr->flags & TCP_SYN;
    info->ack       = tcphdr->flags & TCP_ACK;
    if (info->ack)
        info->ackNumber = ntohl(tcphdr->ack);

#ifndef WOLFSSL_SNIFFER_WATCH
    if (!IsPortRegistered(info->srcPort) && !IsPortRegistered(info->dstPort)) {
        SetError(SERVER_PORT_NOT_REG_STR, error, NULL, 0);
        return -1;
    }
#else
    (void)error;
#endif

    return 0;
}


/* Decode Record Layer Header */
static int GetRecordHeader(const byte* input, RecordLayerHeader* rh, int* size)
{
    XMEMCPY(rh, input, RECORD_HEADER_SZ);
    *size = (rh->length[0] << 8) | rh->length[1];

    if (*size > (MAX_RECORD_SIZE + COMP_EXTRA + MAX_MSG_EXTRA))
        return LENGTH_ERROR;

    return 0;
}


/* Copies the session's information to the provided sslInfo. Skip copy if
 * SSLInfo is not provided. */
static void CopySessionInfo(SnifferSession* session, SSLInfo* sslInfo)
{
    if (NULL != sslInfo) {
        XMEMSET(sslInfo, 0, sizeof(SSLInfo));

        /* Pass back Session Info after we have processed the Server Hello. */
        if (0 != session->sslServer->options.cipherSuite) {
            const char* pCipher;

            sslInfo->isValid = 1;
            sslInfo->protocolVersionMajor = session->sslServer->version.major;
            sslInfo->protocolVersionMinor = session->sslServer->version.minor;
            sslInfo->serverCipherSuite0 =
                        session->sslServer->options.cipherSuite0;
            sslInfo->serverCipherSuite =
                        session->sslServer->options.cipherSuite;

            pCipher = wolfSSL_get_cipher(session->sslServer);
            if (NULL != pCipher) {
                XSTRNCPY((char*)sslInfo->serverCipherSuiteName, pCipher,
                         sizeof(sslInfo->serverCipherSuiteName));
                sslInfo->serverCipherSuiteName
                         [sizeof(sslInfo->serverCipherSuiteName) - 1] = '\0';
            }
            sslInfo->keySize = session->keySz;
        #ifdef HAVE_SNI
            if (NULL != session->sni) {
                XSTRNCPY((char*)sslInfo->serverNameIndication,
                         session->sni, sizeof(sslInfo->serverNameIndication));
                sslInfo->serverNameIndication
                         [sizeof(sslInfo->serverNameIndication) - 1] = '\0';
            }
        #endif
            TraceSessionInfo(sslInfo);
        }
    }
}


/* Call the session connection start callback. */
static void CallConnectionCb(SnifferSession* session)
{
    if (ConnectionCb != NULL) {
        SSLInfo info;
        CopySessionInfo(session, &info);
        ConnectionCb((const void*)session, &info, ConnectionCbCtx);
    }
}

#ifdef SHOW_SECRETS
static void PrintSecret(const char* desc, const byte* buf, int sz)
{
    int i;
    printf("%s: ", desc);
    for (i = 0; i < sz; i++) {
        printf("%02x", buf[i]);
    }
    printf("\n");
}

static void ShowTlsSecrets(SnifferSession* session)
{
    PrintSecret("server master secret", session->sslServer->arrays->masterSecret, SECRET_LEN);
    PrintSecret("client master secret", session->sslClient->arrays->masterSecret, SECRET_LEN);
    printf("server suite = %d\n", session->sslServer->options.cipherSuite);
    printf("client suite = %d\n", session->sslClient->options.cipherSuite);
}
#endif /* SHOW_SECRETS */


/* Process Keys */
static int SetupKeys(const byte* input, int* sslBytes, SnifferSession* session, 
    char* error, KeyShareInfo* ksInfo, DerBuffer* keyBuf)
{
    word32 idx = 0;
    int ret;

#ifndef NO_RSA
    /* Static RSA */
    if (ksInfo == NULL) {
        RsaKey key;
        int length;

        ret = wc_InitRsaKey(&key, 0);
        if (ret == 0) {
            ret = wc_RsaPrivateKeyDecode(keyBuf->buffer, &idx, &key, keyBuf->length);
            if (ret != 0) {
            #ifndef HAVE_ECC
                SetError(RSA_DECODE_STR, error, session, FATAL_ERROR_STATE);
            #else
                /* If we can do ECC, this isn't fatal. Not loading an ECC
                    * key will be fatal, though. */
                SetError(RSA_DECODE_STR, error, session, 0);
            #endif
            }
        }

        if (ret == 0) {
            length = wc_RsaEncryptSize(&key);
            if (IsTLS(session->sslServer)) {
                input += 2;     /* tls pre length */
            }

            if (length > *sslBytes) {
                SetError(PARTIAL_INPUT_STR, error, session, FATAL_ERROR_STATE);
                ret = -1;
            }
        }

        #ifdef WC_RSA_BLINDING
        if (ret == 0) {
            ret = wc_RsaSetRNG(&key, session->sslServer->rng);
            if (ret != 0) {
                SetError(RSA_DECRYPT_STR, error, session, FATAL_ERROR_STATE);
            }
        }
        #endif

        if (ret == 0) {
            session->keySz = length * WOLFSSL_BIT_SIZE;
            /* length is the key size in bytes */
            session->sslServer->arrays->preMasterSz = SECRET_LEN;

            do {
            #ifdef WOLFSSL_ASYNC_CRYPT
                ret = wc_AsyncWait(ret, &key.asyncDev,
                        WC_ASYNC_FLAG_CALL_AGAIN);
            #endif
                if (ret >= 0) {
                    ret = wc_RsaPrivateDecrypt(input, length,
                          session->sslServer->arrays->preMasterSecret,
                          session->sslServer->arrays->preMasterSz, &key);
                }
            } while (ret == WC_PENDING_E);

            if (ret != SECRET_LEN) {
                SetError(RSA_DECRYPT_STR, error, session, FATAL_ERROR_STATE);
            }
        }

        wc_FreeRsaKey(&key);
    }
#endif /* !NO_RSA */

#if !defined(NO_DH) && defined(WOLFSSL_DH_EXTRA)
    /* Static Ephemeral DH Key */
    if (ksInfo && ksInfo->dh_key_bits != 0) {
        DhKey dhKey;
        const DhParams* params;
        word32 privKeySz;
        byte privKey[52]; /* max for TLS */

        /* get DH params */
        switch (ksInfo->named_group) {
        #ifdef HAVE_FFDHE_2048
            case WOLFSSL_FFDHE_2048:
                params = wc_Dh_ffdhe2048_Get();
                privKeySz = 29;
                break;
        #endif
        #ifdef HAVE_FFDHE_3072
            case WOLFSSL_FFDHE_3072:
                params = wc_Dh_ffdhe3072_Get();
                privKeySz = 34;
                break;
        #endif
        #ifdef HAVE_FFDHE_4096
            case WOLFSSL_FFDHE_4096:
                params = wc_Dh_ffdhe4096_Get();
                privKeySz = 39;
                break;
        #endif
        #ifdef HAVE_FFDHE_6144
            case WOLFSSL_FFDHE_6144:
                params = wc_Dh_ffdhe6144_Get();
                privKeySz = 46;
                break;
        #endif
        #ifdef HAVE_FFDHE_8192
            case WOLFSSL_FFDHE_8192:
                params = wc_Dh_ffdhe8192_Get();
                privKeySz = 52;
                break;
        #endif
            default:
                return BAD_FUNC_ARG;
        }

        ret = wc_InitDhKey(&dhKey);
        if (ret == 0) {
            ret = wc_DhSetKey(&dhKey,
                (byte*)params->p, params->p_len,
                (byte*)params->g, params->g_len);
            if (ret == 0) {
                ret = wc_DhKeyDecode(keyBuf->buffer, &idx, &dhKey, 
                    keyBuf->length);
            }
            if (ret == 0) {
                ret = wc_DhExportKeyPair(&dhKey, privKey, &privKeySz, NULL, 
                    NULL);
            }

            /* Derive secret from private key and peer's public key */
            do {
            #ifdef WOLFSSL_ASYNC_CRYPT
                ret = wc_AsyncWait(ret, &dhPriv.asyncDev,
                        WC_ASYNC_FLAG_CALL_AGAIN);
            #endif
                if (ret >= 0) {
                    ret = wc_DhAgree(&dhKey,
                        session->sslServer->arrays->preMasterSecret,
                        &session->sslServer->arrays->preMasterSz,
                        privKey, privKeySz,
                        input, *sslBytes);
                }
            } while (ret == WC_PENDING_E);

            wc_FreeDhKey(&dhKey);
        
            /* left-padded with zeros up to the size of the prime */
            if (params->p_len > session->sslServer->arrays->preMasterSz) {
                word32 diff = params->p_len - session->sslServer->arrays->preMasterSz;
                XMEMMOVE(session->sslServer->arrays->preMasterSecret + diff,
                        session->sslServer->arrays->preMasterSecret, 
                        session->sslServer->arrays->preMasterSz);
                XMEMSET(session->sslServer->arrays->preMasterSecret, 0, diff);
                session->sslServer->arrays->preMasterSz = params->p_len;
            }
        }
    }
#endif /* !NO_DH && WOLFSSL_DH_EXTRA */

#ifdef HAVE_ECC
    /* Static Ephemeral ECC Key */
    if (ksInfo && ksInfo->curve_id != 0) {
        ecc_key key;
        ecc_key pubKey;
        int length, keyInit = 0, pubKeyInit = 0;

        idx = 0;
        ret = wc_ecc_init(&key);
        if (ret == 0) {
            keyInit = 1;
            ret = wc_ecc_init(&pubKey);
        }
        if (ret == 0) {
            pubKeyInit = 1;
            ret = wc_EccPrivateKeyDecode(keyBuf->buffer, &idx, &key, keyBuf->length);
            if (ret != 0) {
                SetError(ECC_DECODE_STR, error, session, FATAL_ERROR_STATE);
            }
        }

        if (ret == 0) {
            length = wc_ecc_size(&key) * 2 + 1;
            /* The length should be 2 times the key size (x and y), plus 1
             * for the type byte. */
            if (IsTLS(session->sslServer) && !IsAtLeastTLSv1_3(session->sslServer->version)) {
                input += 1; /* Don't include the TLS length for the key. */
            }

            if (length > *sslBytes) {
                SetError(PARTIAL_INPUT_STR, error, session, FATAL_ERROR_STATE);
                ret = -1;
            }
        }

        if (ret == 0) {
            ret = wc_ecc_import_x963_ex(input, length, &pubKey, ksInfo->curve_id);
            if (ret != 0) {
                SetError(ECC_PUB_DECODE_STR, error, session, FATAL_ERROR_STATE);
            }
        }

        if (ret == 0) {
            session->keySz = ((length - 1) / 2) * WOLFSSL_BIT_SIZE;
            /* Length is in bytes. Subtract 1 for the ECC key type. Divide
             * by two as the key is in (x,y) coordinates, where x and y are
             * the same size, the key size. Convert from bytes to bits. */
            session->sslServer->arrays->preMasterSz = ENCRYPT_LEN;

            do {
            #ifdef WOLFSSL_ASYNC_CRYPT
                ret = wc_AsyncWait(ret, &key.asyncDev,
                        WC_ASYNC_FLAG_CALL_AGAIN);
            #endif
                if (ret >= 0) {
                    ret = wc_ecc_shared_secret(&key, &pubKey,
                          session->sslServer->arrays->preMasterSecret,
                          &session->sslServer->arrays->preMasterSz);
                }
            } while (ret == WC_PENDING_E);
        }

#ifdef WOLFSSL_SNIFFER_STATS
        if (ret != 0)
            INC_STAT(SnifferStats.sslKeyFails);
#endif

        if (keyInit)
            wc_ecc_free(&key);
        if (pubKeyInit)
            wc_ecc_free(&pubKey);
    }
#endif /* HAVE_ECC */

    /* store for client side as well */
    XMEMCPY(session->sslClient->arrays->preMasterSecret,
           session->sslServer->arrays->preMasterSecret,
           session->sslServer->arrays->preMasterSz);
    session->sslClient->arrays->preMasterSz =
        session->sslServer->arrays->preMasterSz;

#ifdef SHOW_SECRETS
    PrintSecret("pre master secret", 
                session->sslServer->arrays->preMasterSecret, 
                session->sslServer->arrays->preMasterSz);
#endif

    if (SetCipherSpecs(session->sslServer) != 0) {
        SetError(BAD_CIPHER_SPEC_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    if (SetCipherSpecs(session->sslClient) != 0) {
        SetError(BAD_CIPHER_SPEC_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

#ifdef WOLFSSL_TLS13
    /* TLS v1.3 derive handshake key */
    if (IsAtLeastTLSv1_3(session->sslServer->version)) {
        ret  = DeriveEarlySecret(session->sslServer);
        ret += DeriveEarlySecret(session->sslClient);
        ret += DeriveHandshakeSecret(session->sslServer);
        ret += DeriveHandshakeSecret(session->sslClient);
        ret += DeriveTls13Keys(session->sslServer, handshake_key, ENCRYPT_AND_DECRYPT_SIDE, 1);
        ret += DeriveTls13Keys(session->sslClient, handshake_key, ENCRYPT_AND_DECRYPT_SIDE, 1);
    #ifdef WOLFSSL_EARLY_DATA
        ret += SetKeysSide(session->sslServer, DECRYPT_SIDE_ONLY);
        ret += SetKeysSide(session->sslClient, DECRYPT_SIDE_ONLY);
    #else
        ret += SetKeysSide(session->sslServer, ENCRYPT_AND_DECRYPT_SIDE);
        ret += SetKeysSide(session->sslClient, ENCRYPT_AND_DECRYPT_SIDE);
    #endif
    }
    else
#endif
    {
        ret  = MakeMasterSecret(session->sslServer);
        ret += MakeMasterSecret(session->sslClient);
        ret += SetKeysSide(session->sslServer, ENCRYPT_AND_DECRYPT_SIDE);
        ret += SetKeysSide(session->sslClient, ENCRYPT_AND_DECRYPT_SIDE);
    }
    if (ret != 0) {
        SetError(BAD_DERIVE_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

#ifdef SHOW_SECRETS
    #ifdef WOLFSSL_TLS13
    if (!IsAtLeastTLSv1_3(session->sslServer->version))
    #endif
        ShowTlsSecrets(session);
#endif

    CallConnectionCb(session);

    return ret;
}

/* Process Client Key Exchange, static RSA  */
static int ProcessClientKeyExchange(const byte* input, int* sslBytes,
                            SnifferSession* session, char* error)
{
    if (session->sslServer->buffers.key == NULL ||
        session->sslServer->buffers.key->buffer == NULL ||
        session->sslServer->buffers.key->length == 0) {

        SetError(RSA_KEY_MISSING_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    return SetupKeys(input, sslBytes, session, error, NULL, 
        session->sslServer->buffers.key);
}

#ifdef WOLFSSL_TLS13
static int ProcessKeyShare(KeyShareInfo* info, const byte* input, int len,
    word16 filter_group)
{
    int index = 0;
    while (index < len) {
        /* Named group and public key */
        info->named_group = (word16)((input[index] << 8) | input[index+1]);
        index += OPAQUE16_LEN;
        info->key_len = (word16)((input[index] << 8) | input[index+1]);
        index += OPAQUE16_LEN;
        if (info->key_len == 0 || info->key_len > len - index) {
            return -1;
        }
        info->key = &input[index];
        index += info->key_len;

        switch (info->named_group) {
    #ifndef NO_DH
        #ifdef HAVE_FFDHE_2048
            case WOLFSSL_FFDHE_2048:
                info->dh_key_bits = 2048;
                break;
        #endif
        #ifdef HAVE_FFDHE_3072
            case WOLFSSL_FFDHE_3072:
                info->dh_key_bits = 3072;
                break;
        #endif
        #ifdef HAVE_FFDHE_4096
            case WOLFSSL_FFDHE_4096:
                info->dh_key_bits = 4096;
                break;
        #endif
        #ifdef HAVE_FFDHE_6144
            case WOLFSSL_FFDHE_6144:
                info->dh_key_bits = 6144;
                break;
        #endif
        #ifdef HAVE_FFDHE_8192
            case WOLFSSL_FFDHE_8192:
                info->dh_key_bits = 8192;
                break;
        #endif
    #endif /* !NO_DH */
    #ifdef HAVE_ECC
        #if !defined(NO_ECC256)  || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP256R1:
                info->curve_id = ECC_SECP256R1;
                break;
            #endif /* !NO_ECC_SECP */
        #endif
        #if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP384R1:
                info->curve_id = ECC_SECP384R1;
                break;
            #endif /* !NO_ECC_SECP */
        #endif
        #if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP521R1:
                info->curve_id = ECC_SECP521R1;
                break;
            #endif /* !NO_ECC_SECP */
        #endif
    #endif /* HAVE_ECC */
        #ifdef HAVE_CURVE25519
            case WOLFSSL_ECC_X25519:
                info->curve_id = ECC_X25519;
                break;
        #endif
        #ifdef HAVE_X448
            case WOLFSSL_ECC_X448:
                info->curve_id = ECC_X448;
                break;
        #endif
            default:
                /* unsupported curve */
                return ECC_PEERKEY_ERROR;
        }

        if (filter_group == 0 || filter_group == info->named_group) {
            return 0;
        }
    }
    return -1;
}

static int ProcessServerKeyShare(SnifferSession* session, const byte* input, int len,
    char* error)
{
    int ret;

    if (session->cliKeyShare == NULL || session->cliKeyShareSz == 0) {
        SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    /* Get server_hello key share */
    ret = ProcessKeyShare(&session->srvKs, input, len, 0);
    if (ret == 0) {
        /* Get client_hello key share */
        ret = ProcessKeyShare(&session->cliKs, session->cliKeyShare,
            session->cliKeyShareSz, session->srvKs.named_group);
    }
    if (ret != 0) {
        SetError(SERVER_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    return ret;
} 
#endif /* WOLFSSL_TLS13 */

/* Process Session Ticket */
static int ProcessSessionTicket(const byte* input, int* sslBytes,
                                SnifferSession* session, char* error)
{
    word16 len;
    WOLFSSL* ssl;

    if (session->flags.side == WOLFSSL_SERVER_END)
        ssl = session->sslServer;
    else
        ssl = session->sslClient;

    /* make sure can read through hint len */
    if (TICKET_HINT_LEN > *sslBytes) {
        SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    input     += TICKET_HINT_LEN; /* skip over hint len */
    *sslBytes -= TICKET_HINT_LEN;

#ifdef WOLFSSL_TLS13
    /* TLS v1.3 has hint age and nonce */
    if (IsAtLeastTLSv1_3(ssl->version)) {
        /* make sure can read through hint age and nonce len */
        if (TICKET_HINT_AGE_LEN + 1 > *sslBytes) {
            SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        input     += TICKET_HINT_AGE_LEN; /* skip over hint age */
        *sslBytes -= TICKET_HINT_AGE_LEN;

        /* ticket nonce */
        len = input[0];
        if (len > MAX_TICKET_NONCE_SZ) {
            SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        input += OPAQUE8_LEN;
        *sslBytes -= OPAQUE8_LEN;
    #ifdef HAVE_SESSION_TICKET
        /* store nonce in server for DeriveResumptionPSK */
        session->sslServer->session.ticketNonce.len = len;
        if (len > 0)
            XMEMCPY(&session->sslServer->session.ticketNonce.data, input, len);
    #endif
        input += len;
        *sslBytes -= len;
    }
#endif

    /* make sure can read through len */
    if (OPAQUE16_LEN > *sslBytes) {
        SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    len = (word16)((input[0] << 8) | input[1]);
    input     += OPAQUE16_LEN;
    *sslBytes -= OPAQUE16_LEN;

    /* make sure can read through ticket */
    if (len > *sslBytes) {
        SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

#ifdef WOLFSSL_TLS13
    /* TLS v1.3 has hint age and nonce */
    if (IsAtLeastTLSv1_3(ssl->version)) {
    #ifdef HAVE_SESSION_TICKET
        if (SetTicket(ssl, input, len) != 0) {
            SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        /* set haveSessionId to use the wolfSession cache */
        ssl->options.haveSessionId = 1;

        /* Use the wolf Session cache to retain resumption secret */
        if (session->flags.cached == 0) {
            WOLFSSL_SESSION* sess = GetSession(ssl, NULL, 0);
            if (sess == NULL) {
                AddSession(ssl); /* don't re add */
            #ifdef WOLFSSL_SNIFFER_STATS
                INC_STAT(SnifferStats.sslResumptionInserts);
            #endif
            }
            session->flags.cached = 1;
        }
    #endif /* HAVE_SESSION_TICKET */
    }
    else
#endif /* WOLFSSL_TLS13 */
    {
        /* make sure ticket id isn't too long */
        if (len > ID_LEN) {
            SetError(BAD_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        /* store session with macID as sessionID */
        session->sslServer->options.haveSessionId = 1;
        XMEMCPY(session->sslServer->arrays->sessionID, 
            input + len - ID_LEN, ID_LEN);
    }

    return 0;
}


/* Process Server Hello */
static int ProcessServerHello(int msgSz, const byte* input, int* sslBytes,
                              SnifferSession* session, char* error)
{
    int             ret = 0;
    ProtocolVersion pv;
    byte            b, b0;
    int             toRead = VERSION_SZ + RAN_LEN + ENUM_LEN;
    int             doResume = 0;
    int             initialBytes = *sslBytes;

    (void)msgSz;
    (void)initialBytes;

    /* make sure we didn't miss ClientHello */
    if (session->flags.clientHello == 0) {
        SetError(MISSED_CLIENT_HELLO_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    /* make sure can read through session len */
    if (toRead > *sslBytes) {
        SetError(SERVER_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    XMEMCPY(&pv, input, VERSION_SZ);
    input     += VERSION_SZ;
    *sslBytes -= VERSION_SZ;

    session->sslServer->version = pv;
    session->sslClient->version = pv;

    XMEMCPY(session->sslServer->arrays->serverRandom, input, RAN_LEN);
    XMEMCPY(session->sslClient->arrays->serverRandom, input, RAN_LEN);
    input     += RAN_LEN;
    *sslBytes -= RAN_LEN;

    b = *input++;
    *sslBytes -= 1;

    /* make sure can read through compression */
    if ( (b + SUITE_LEN + ENUM_LEN) > *sslBytes) {
        SetError(SERVER_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    if (b) {
    #ifdef WOLFSSL_TLS13
        XMEMCPY(session->sslServer->session.sessionID, input, ID_LEN);
    #endif
        XMEMCPY(session->sslServer->arrays->sessionID, input, ID_LEN);
        session->sslServer->options.haveSessionId = 1;
    }
    input     += b;
    *sslBytes -= b;

    /* cipher suite */
    b0 = *input++;  /* first byte, ECC or not */
    session->sslServer->options.cipherSuite0 = b0;
    session->sslClient->options.cipherSuite0 = b0;
    b = *input++;
    session->sslServer->options.cipherSuite = b;
    session->sslClient->options.cipherSuite = b;
    *sslBytes -= SUITE_LEN;

#ifdef WOLFSSL_SNIFFER_STATS
    {
        const CipherSuiteInfo* suites = GetCipherNames();
        int suitesSz = GetCipherNamesSize();
        int match = 0;

        while (suitesSz) {
            if (b0 == suites->cipherSuite0 && b == suites->cipherSuite) {
                match = 1;
                break;
            }
            suites++;
            suitesSz--;
        }
        if (!match)
            INC_STAT(SnifferStats.sslCiphersUnsupported);
    }
#endif /* WOLFSSL_SNIFFER_STATS */

    /* compression */
    b = *input++;
    *sslBytes -= ENUM_LEN;

    if (b) {
        SetError(BAD_COMPRESSION_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    /* extensions */
    if ((initialBytes - *sslBytes) < msgSz) {
        word16 len;

        /* skip extensions until extended master secret */
        /* make sure can read len */
        if (SUITE_LEN > *sslBytes) {
            SetError(SERVER_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        len = (word16)((input[0] << 8) | input[1]);
        input     += SUITE_LEN;
        *sslBytes -= SUITE_LEN;
        /* make sure can read through all extensions */
        if (len > *sslBytes) {
            SetError(SERVER_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }

        while (len >= EXT_TYPE_SZ + LENGTH_SZ) {
            word16 extType;
            word16 extLen;

            extType    = (word16)((input[0] << 8) | input[1]);
            input     += EXT_TYPE_SZ;
            *sslBytes -= EXT_TYPE_SZ;

            extLen     = (word16)((input[0] << 8) | input[1]);
            input     += LENGTH_SZ;
            *sslBytes -= LENGTH_SZ;

            /* make sure can read through individual extension */
            if (extLen > *sslBytes) {
                SetError(SERVER_HELLO_INPUT_STR, error, session,
                         FATAL_ERROR_STATE);
                return -1;
            }

            switch (extType) {
        #ifdef WOLFSSL_TLS13
            case EXT_KEY_SHARE:
                ret = ProcessServerKeyShare(session, input, extLen, error);
                if (ret != 0) {
                    SetError(SERVER_HELLO_INPUT_STR, error, session, 
                        FATAL_ERROR_STATE);
                    return -1;
                }
                break;
        #endif
        #ifdef HAVE_SESSION_TICKET
            case EXT_PRE_SHARED_KEY:
                /* indicates we want to use resumption */
                session->sslServer->options.resuming = 1;
                session->sslClient->options.resuming = 1;
                /* default nonce to len = 1, data = 0 */
                session->sslServer->session.ticketNonce.len = 1;
                session->sslServer->session.ticketNonce.data[0] = 0;
                session->sslClient->session.ticketNonce.len = 1;
                session->sslClient->session.ticketNonce.data[0] = 0;
                break;
        #endif
            case EXT_SUPPORTED_VERSIONS:
                session->sslServer->version.major = input[0];
                session->sslServer->version.minor = input[1];
                session->sslClient->version.major = input[0];
                session->sslClient->version.minor = input[1];
                break;
            case EXT_MASTER_SECRET:
            #ifdef HAVE_EXTENDED_MASTER
                session->flags.expectEms = 1;
            #endif
                break;
            }

            input     += extLen;
            *sslBytes -= extLen;
            len       -= extLen + EXT_TYPE_SZ + LENGTH_SZ;
        }
    }

#ifdef HAVE_EXTENDED_MASTER
    if (!session->flags.expectEms) {
        XFREE(session->hash, NULL, DYNAMIC_TYPE_HASHES);
        session->hash = NULL;
    }
#endif

    if (session->sslServer->options.haveSessionId) {
        if (XMEMCMP(session->sslServer->arrays->sessionID,
                session->sslClient->arrays->sessionID, ID_LEN) == 0) {
            doResume = 1;
        }    
    }        
    else if (session->sslClient->options.haveSessionId == 0 &&
             session->sslServer->options.haveSessionId == 0 &&
             session->ticketID) {
        doResume = 1;
    }

    if (session->ticketID && doResume) {
        /* use ticketID to retrieve from session, prefer over sessionID */
        XMEMCPY(session->sslServer->arrays->sessionID,session->ticketID,ID_LEN);
        session->sslServer->options.haveSessionId = 1;  /* may not have
                                                           actual sessionID */
    }

    if (doResume) {
        WOLFSSL_SESSION* resume;
        if (IsAtLeastTLSv1_3(session->sslServer->version)) {
            resume = GetSession(session->sslServer, 
                                session->sslServer->session.masterSecret, 0);
        }
        else {
            resume = GetSession(session->sslServer,
                               session->sslServer->arrays->masterSecret, 0);
        }
        if (resume == NULL) {
#ifdef WOLFSSL_SNIFFER_STATS
            INC_STAT(SnifferStats.sslResumeMisses);
#endif
            SetError(BAD_SESSION_RESUME_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }

        /* make sure client has master secret too */
        if (IsAtLeastTLSv1_3(session->sslServer->version)) {
            XMEMCPY(session->sslClient->session.masterSecret,
                    session->sslServer->session.masterSecret, SECRET_LEN);
        }
        else {
            XMEMCPY(session->sslClient->arrays->masterSecret,
                    session->sslServer->arrays->masterSecret, SECRET_LEN);
        }
        session->flags.resuming = 1;

        Trace(SERVER_DID_RESUMPTION_STR);
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslResumedConns);
        INC_STAT(SnifferStats.sslResumptionValid);
#endif
        if (SetCipherSpecs(session->sslServer) != 0) {
            SetError(BAD_CIPHER_SPEC_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }

        if (SetCipherSpecs(session->sslClient) != 0) {
            SetError(BAD_CIPHER_SPEC_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }

    #ifdef WOLFSSL_TLS13
        if (IsAtLeastTLSv1_3(session->sslServer->version)) {
        #ifdef HAVE_SESSION_TICKET
            /* Resumption PSK is resumption master secret. */
            session->sslServer->arrays->psk_keySz = session->sslServer->specs.hash_size;
            session->sslClient->arrays->psk_keySz = session->sslClient->specs.hash_size;
            ret  = DeriveResumptionPSK(session->sslServer, session->sslServer->session.ticketNonce.data, 
                session->sslServer->session.ticketNonce.len, session->sslServer->arrays->psk_key);
            /* Copy resumption PSK to client */
            XMEMCPY(session->sslClient->arrays->psk_key, 
                session->sslServer->arrays->psk_key,
                session->sslServer->arrays->psk_keySz);
        #endif
            /* handshake key setup below and traffic keys done in SetupKeys */
        }
        else
    #endif
        {
            if (IsTLS(session->sslServer)) {
                ret =  DeriveTlsKeys(session->sslServer);
                ret += DeriveTlsKeys(session->sslClient);
            }
            else {
                ret =  DeriveKeys(session->sslServer);
                ret += DeriveKeys(session->sslClient);
            }
            ret += SetKeysSide(session->sslServer, ENCRYPT_AND_DECRYPT_SIDE);
            ret += SetKeysSide(session->sslClient, ENCRYPT_AND_DECRYPT_SIDE);
        }

        if (ret != 0) {
            SetError(BAD_DERIVE_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
    }
    else {
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslStandardConns);
#endif
    }

#ifdef SHOW_SECRETS
    printf("cipher suite = 0x%02x\n", session->sslServer->options.cipherSuite);
    PrintSecret("server random", session->sslServer->arrays->serverRandom, RAN_LEN);
#endif

#ifdef WOLFSSL_TLS13
    /* Setup handshake keys */
    if (IsAtLeastTLSv1_3(session->sslServer->version)) {
        DerBuffer* key = session->sslServer->buffers.key;
    #ifdef WOLFSSL_STATIC_EPHEMERAL
        if (session->sslServer->staticKE.key)
            key = session->sslServer->staticKE.key;
    #endif
        ret = SetupKeys(session->cliKs.key, &session->cliKs.key_len, 
            session, error, &session->cliKs, key);
        if (ret != 0) {
            SetError(SERVER_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return ret;
        }

        if (session->flags.side == WOLFSSL_SERVER_END)
            session->flags.serverCipherOn = 1;
        else
            session->flags.clientCipherOn = 1;
    }
#endif

    return 0;
}


/* Process normal Client Hello */
static int ProcessClientHello(const byte* input, int* sslBytes,
                              SnifferSession* session, char* error)
{
    int ret = 0;
    byte   bLen;
    word16 len;
    int    toRead = VERSION_SZ + RAN_LEN + ENUM_LEN;
    const byte* inputHello = input;
    int inputHelloSz = *sslBytes;
    WOLFSSL* ssl = session->sslServer;
    int didHash = 0;

#ifdef HAVE_SNI
    {
        byte name[MAX_SERVER_NAME];
        word32 nameSz = sizeof(name);

        ret = wolfSSL_SNI_GetFromBuffer(
                             input - HANDSHAKE_HEADER_SZ - RECORD_HEADER_SZ,
                             *sslBytes + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ,
                             WOLFSSL_SNI_HOST_NAME, name, &nameSz);

        if (ret == WOLFSSL_SUCCESS) {
            NamedKey* namedKey;

            if (nameSz > sizeof(name) - 1)
                nameSz = sizeof(name) - 1;
            name[nameSz] = 0;
            wc_LockMutex(&session->context->namedKeysMutex);
            namedKey = session->context->namedKeys;
            while (namedKey != NULL) {
                if (nameSz == namedKey->nameSz &&
                           XSTRNCMP((char*)name, namedKey->name, nameSz) == 0) {
                #ifdef WOLFSSL_STATIC_EPHEMERAL
                    if (namedKey->isEphemeralKey) {
                        /* auto detect key type with WC_PK_TYPE_NONE */
                        ret = wolfSSL_set_ephemeral_key(ssl, 
                            WC_PK_TYPE_NONE, (const char*)namedKey->key, 
                            namedKey->keySz, WOLFSSL_FILETYPE_ASN1);
                        if (ret == 0)
                            ret = WOLFSSL_SUCCESS;
                    }
                    else
                #endif
                    {
                        ret = wolfSSL_use_PrivateKey_buffer(ssl,
                            namedKey->key, namedKey->keySz, 
                            WOLFSSL_FILETYPE_ASN1);
                    }
                    if (ret != WOLFSSL_SUCCESS) {
                        wc_UnLockMutex(&session->context->namedKeysMutex);
                        SetError(CLIENT_HELLO_LATE_KEY_STR, error, session,
                                                             FATAL_ERROR_STATE);
                        return -1;
                    }
                    session->sni = namedKey->name;
                    break;
                }
                else
                    namedKey = namedKey->next;
            }
            wc_UnLockMutex(&session->context->namedKeysMutex);
        }
    }
#endif

    session->flags.clientHello = 1;  /* don't process again */

    /* make sure can read up to session len */
    if (toRead > *sslBytes) {
        SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    /* skip, get negotiated one from server hello */
    input     += VERSION_SZ;
    *sslBytes -= VERSION_SZ;

    XMEMCPY(session->sslServer->arrays->clientRandom, input, RAN_LEN);
    XMEMCPY(session->sslClient->arrays->clientRandom, input, RAN_LEN);

    input     += RAN_LEN;
    *sslBytes -= RAN_LEN;

    /* store session in case trying to resume */
    bLen = *input++;
    *sslBytes -= ENUM_LEN;
    if (bLen) {
        if (ID_LEN > *sslBytes) {
            SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        Trace(CLIENT_RESUME_TRY_STR);
#ifdef WOLFSSL_TLS13
        XMEMCPY(session->sslClient->session.sessionID, input, ID_LEN);
#endif
        XMEMCPY(session->sslClient->arrays->sessionID, input, ID_LEN);
        session->sslClient->options.haveSessionId = 1;
    }

#ifdef SHOW_SECRETS
    PrintSecret("client random", ssl->arrays->clientRandom, RAN_LEN);
#endif

    input     += bLen;
    *sslBytes -= bLen;

    /* skip cipher suites */
    /* make sure can read len */
    if (SUITE_LEN > *sslBytes) {
        SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    len = (word16)((input[0] << 8) | input[1]);
    input     += SUITE_LEN;
    *sslBytes -= SUITE_LEN;
    /* make sure can read suites + comp len */
    if (len + ENUM_LEN > *sslBytes) {
        SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    input     += len;
    *sslBytes -= len;

    /* skip compression */
    bLen       = *input++;
    *sslBytes -= ENUM_LEN;
    /* make sure can read len */
    if (bLen > *sslBytes) {
        SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    input     += bLen;
    *sslBytes -= bLen;

    if (*sslBytes == 0) {
        /* no extensions */
        return 0;
    }

    /* skip extensions until session ticket */
    /* make sure can read len */
    if (SUITE_LEN > *sslBytes) {
        SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    len = (word16)((input[0] << 8) | input[1]);
    input     += SUITE_LEN;
    *sslBytes -= SUITE_LEN;
    /* make sure can read through all extensions */
    if (len > *sslBytes) {
        SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    while (len >= EXT_TYPE_SZ + LENGTH_SZ) {
        word16 extType;
        word16 extLen;

        extType    = (word16)((input[0] << 8) | input[1]);
        input     += EXT_TYPE_SZ;
        *sslBytes -= EXT_TYPE_SZ;

        extLen     = (word16)((input[0] << 8) | input[1]);
        input     += LENGTH_SZ;
        *sslBytes -= LENGTH_SZ;

        /* make sure can read through individual extension */
        if (extLen > *sslBytes) {
            SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }

        switch (extType) {
    #ifdef WOLFSSL_TLS13
        case EXT_KEY_SHARE:
        {
            word16 ksLen = (word16)((input[0] << 8) | input[1]);
            if (ksLen + OPAQUE16_LEN > extLen) {
                SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
                return -1;
            }
            /* cache key share data till server_hello */
            session->cliKeyShareSz = ksLen;
            session->cliKeyShare = (byte*)XMALLOC(ksLen, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            if (session->cliKeyShare == NULL) {
                SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
                break;
            }
            XMEMCPY(session->cliKeyShare, &input[2], ksLen);

            /* The server side handshake encryption is on for future packets */
            session->flags.serverCipherOn = 1;
            break;
        }
        #ifdef HAVE_SESSION_TICKET
        case EXT_PRE_SHARED_KEY:
        {
            word16 idsLen, idLen, bindersLen, idx = 0;
            word32 ticketAge;
            const byte *identity, *binders;

            idsLen = (word16)((input[idx] << 8) | input[idx+1]);
            if (idsLen + OPAQUE16_LEN + idx > extLen) {
                SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
                return -1;
            }
            idx += OPAQUE16_LEN;

            /* PSK identity */
            idLen = (word16)((input[idx] << 8) | input[idx+1]);
            if (idLen + OPAQUE16_LEN + idx > extLen) {
                SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
                return -1;
            }
            idx += OPAQUE16_LEN;
            identity = &input[idx];
            idx += idLen;

            /* Obfuscated Ticket Age 32-bits */
            ticketAge = (word32)((input[idx] << 24) | (input[idx+1] << 16) | 
                                 (input[idx+2] << 8) | input[idx+3]);
            (void)ticketAge; /* not used */
            idx += OPAQUE32_LEN;

            /* binders - all binders */
            bindersLen = (word16)((input[idx] << 8) | input[idx+1]);
            if (bindersLen + OPAQUE16_LEN + idx > extLen) {
                SetError(CLIENT_HELLO_INPUT_STR, error, session, FATAL_ERROR_STATE);
                return -1;
            }
            idx += OPAQUE16_LEN;
            binders = &input[idx];
            bindersLen += OPAQUE16_LEN; /* includes 2 bytes for total len */
            (void)binders; /* not used */

            /* Hash data up to binders for deriving binders in PSK extension. */
            HashRaw(session->sslServer, inputHello - HANDSHAKE_HEADER_SZ, 
                inputHelloSz - bindersLen + HANDSHAKE_HEADER_SZ);
            HashRaw(session->sslClient, inputHello - HANDSHAKE_HEADER_SZ, 
                inputHelloSz - bindersLen + HANDSHAKE_HEADER_SZ);

            /* call to decrypt session ticket */
            if (DoClientTicket(ssl, identity, idLen) != 0) {
                /* we aren't decrypting the resumption, since we know the master secret */
                /* ignore errors */
            }
            ssl->options.resuming  = 1;

            /* Hash the rest of the ClientHello. */
            HashRaw(session->sslServer, inputHello + inputHelloSz - bindersLen, bindersLen);
            HashRaw(session->sslClient, inputHello + inputHelloSz - bindersLen, bindersLen);
            didHash = 1;
            break;
        }
        #endif /* HAVE_SESSION_TICKET */
    #endif /* WOLFSSL_TLS13 */
        case EXT_SUPPORTED_VERSIONS:
            break;
        case EXT_TICKET_ID:
            /* make sure can read through ticket if there is a non blank one */
            if (extLen && extLen < ID_LEN) {
                SetError(CLIENT_HELLO_INPUT_STR, error, session,
                         FATAL_ERROR_STATE);
                return -1;
            }
            if (extLen) {
                if (session->ticketID == NULL) {
                    session->ticketID = (byte*)XMALLOC(ID_LEN,
                            NULL, DYNAMIC_TYPE_SNIFFER_TICKET_ID);
                    if (session->ticketID == 0) {
                        SetError(MEMORY_STR, error, session,
                                 FATAL_ERROR_STATE);
                        return -1;
                    }
                }
                XMEMCPY(session->ticketID, input + extLen - ID_LEN, ID_LEN);
            }
            break;
        }

        input     += extLen;
        *sslBytes -= extLen;
        len       -= extLen + EXT_TYPE_SZ + LENGTH_SZ;
    }

    if (!didHash) {
        HashRaw(session->sslServer, inputHello - HANDSHAKE_HEADER_SZ, 
            inputHelloSz + HANDSHAKE_HEADER_SZ);
        HashRaw(session->sslClient, inputHello - HANDSHAKE_HEADER_SZ, 
            inputHelloSz + HANDSHAKE_HEADER_SZ);
    }

    (void)ssl;

    return ret;
}


#ifdef WOLFSSL_SNIFFER_WATCH

static int KeyWatchCall(SnifferSession* session, const byte* data, int dataSz,
    char* error)
{
    int ret;
    Sha256 sha;
    byte digest[SHA256_DIGEST_SIZE];

    if (WatchCb == NULL) {
        SetError(WATCH_CB_MISSING_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    ret = wc_InitSha256(&sha);
    if (ret == 0)
        ret = wc_Sha256Update(&sha, data, dataSz);
    if (ret == 0)
        ret = wc_Sha256Final(&sha, digest);
    if (ret != 0) {
        SetError(WATCH_HASH_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    ret = WatchCb((void*)session, digest, sizeof(digest),
            data, dataSz, WatchCbCtx, error);
    if (ret != 0) {
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslKeysUnmatched);
#endif
        SetError(WATCH_FAIL_STR, error, session, FATAL_ERROR_STATE);
        ret = -1;
    }
    else {
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslKeyMatches);
#endif
    }
    return ret;
}

/* Process Certificate */
static int ProcessCertificate(const byte* input, int* sslBytes,
        SnifferSession* session, char* error)
{
    int ret;
    const byte* certChain;
    word32 certChainSz;
    word32 certSz;

    /* If the receiver is the server, this is the client certificate message,
     * and it should be ignored at this point. */
    if (session->flags.side == WOLFSSL_SERVER_END)
        return 0;

    if (*sslBytes < CERT_HEADER_SZ) {
        SetError(BAD_CERT_MSG_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    ato24(input, &certChainSz);
    *sslBytes -= CERT_HEADER_SZ;
    input += CERT_HEADER_SZ;

    if (*sslBytes < (int)certChainSz) {
        SetError(BAD_CERT_MSG_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    certChain = input;

    ato24(input, &certSz);
    input += OPAQUE24_LEN;
    if (*sslBytes < (int)certSz) {
        SetError(BAD_CERT_MSG_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    *sslBytes -= certChainSz;

    return KeyWatchCall(session, input, certSz, error);
}

#endif


/* Process Finished */
static int ProcessFinished(const byte* input, int size, int* sslBytes,
                           SnifferSession* session, char* error)
{
    WOLFSSL* ssl;
    word32 inOutIdx = 0;
    int    ret;

    if (session->flags.side == WOLFSSL_SERVER_END)
        ssl = session->sslServer;
    else
        ssl = session->sslClient;

#ifdef WOLFSSL_TLS13
    if (IsAtLeastTLSv1_3(ssl->version)) {
        ret = DoTls13Finished(ssl, input, &inOutIdx, (word32)size, 
            (word32)*sslBytes, SNIFF);

        ssl->options.handShakeState = HANDSHAKE_DONE;
        ssl->options.handShakeDone  = 1;
    }
    else
#endif
    {
        ret = DoFinished(ssl, input, &inOutIdx, (word32)size, 
            (word32)*sslBytes, SNIFF);
    }
    *sslBytes -= (int)inOutIdx;

    if (ret < 0) {
        SetError(BAD_FINISHED_MSG, error, session, FATAL_ERROR_STATE);
        return ret;
    }

    if (ret == 0 && session->flags.cached == 0) {
        if (session->sslServer->options.haveSessionId) {
            WOLFSSL_SESSION* sess = GetSession(session->sslServer, NULL, 0);
            if (sess == NULL) {
                AddSession(session->sslServer);  /* don't re add */
#ifdef WOLFSSL_SNIFFER_STATS
                INC_STAT(SnifferStats.sslResumptionInserts);
#endif
            }
            session->flags.cached = 1;
         }
    }

#ifdef WOLFSSL_TLS13
    /* Derive TLS v1.3 traffic keys */
    if (IsAtLeastTLSv1_3(ssl->version)) {
        if (!session->flags.gotFinished) {
            /* When either side gets "finished" derive master secret and keys */
            ret  = DeriveMasterSecret(session->sslServer);
            ret += DeriveMasterSecret(session->sslClient);
        #ifdef WOLFSSL_EARLY_DATA
            ret += DeriveTls13Keys(session->sslServer, traffic_key, ENCRYPT_AND_DECRYPT_SIDE, ssl->earlyData == no_early_data);
            ret += DeriveTls13Keys(session->sslClient, traffic_key, ENCRYPT_AND_DECRYPT_SIDE, ssl->earlyData == no_early_data);
        #else
            ret += DeriveTls13Keys(session->sslServer, traffic_key, ENCRYPT_AND_DECRYPT_SIDE, 1);
            ret += DeriveTls13Keys(session->sslClient, traffic_key, ENCRYPT_AND_DECRYPT_SIDE, 1);
        #endif

            if (ret != 0) {
                SetError(BAD_FINISHED_MSG, error, session, FATAL_ERROR_STATE);
                return -1;
            }

            session->flags.gotFinished = 1;
        #ifdef SHOW_SECRETS
            ShowTlsSecrets(session);    
        #endif
        }

        if (session->flags.side == WOLFSSL_SERVER_END) {
            /* finished from client to server */
            ret  = SetKeysSide(session->sslServer, DECRYPT_SIDE_ONLY);
            ret += SetKeysSide(session->sslClient, ENCRYPT_SIDE_ONLY);

        #ifdef HAVE_SESSION_TICKET
            /* derive resumption secret for next session - on finished (from client) */
            ret += DeriveResumptionSecret(session->sslClient, session->sslClient->session.masterSecret);

            /* copy resumption secret to server */
            XMEMCPY(session->sslServer->session.masterSecret,
                session->sslClient->session.masterSecret, SECRET_LEN);
            #ifdef SHOW_SECRETS
            PrintSecret("resumption secret", session->sslClient->session.masterSecret, SECRET_LEN);
            #endif
        #endif
        }
        else {
            /* finished from server to client */
            ret  = SetKeysSide(session->sslServer, ENCRYPT_SIDE_ONLY);
            ret += SetKeysSide(session->sslClient, DECRYPT_SIDE_ONLY);
        }

        if (ret != 0) {
            SetError(BAD_FINISHED_MSG, error, session, FATAL_ERROR_STATE);
            return -1;
        }
    }
#endif

    /* If receiving a finished message from one side, free the resources
     * from the other side's tracker. */
    if (session->flags.side == WOLFSSL_SERVER_END)
        FreeHandshakeResources(session->sslClient);
    else
        FreeHandshakeResources(session->sslServer);

    return ret;
}


/* Process HandShake input */
static int DoHandShake(const byte* input, int* sslBytes,
                       SnifferSession* session, char* error)
{
    byte type;
    int  size;
    int  ret = 0;
    int  startBytes;
    WOLFSSL* ssl;

    if (*sslBytes < HANDSHAKE_HEADER_SZ) {
        SetError(HANDSHAKE_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    type = input[0];
    size = (input[1] << 16) | (input[2] << 8) | input[3];

    input     += HANDSHAKE_HEADER_SZ;
    *sslBytes -= HANDSHAKE_HEADER_SZ;
    startBytes = *sslBytes;

    if (*sslBytes < size) {
        Trace(SPLIT_HANDSHAKE_MSG_STR);
        *sslBytes = 0;
        return ret;
    }

    if (session->flags.side == WOLFSSL_SERVER_END)
        ssl = session->sslServer;
    else
        ssl = session->sslClient;

#ifdef HAVE_SECURE_RENEGOTIATION
    if (!IsAtLeastTLSv1_3(ssl->version)) {
        /* A session's arrays are released when the handshake is completed. */
        if (session->sslServer->arrays == NULL &&
            session->sslClient->arrays == NULL) {

            SetError(NO_SECURE_RENEGOTIATION, error, session, FATAL_ERROR_STATE);
            return -1;
        }
    }
#endif

#ifdef WOLFSSL_TLS13
    if (type != client_hello) {
        /* For resumption the hash is before / after client_hello PSK binder */
        /* hash the packet including header */
        /* TLS v1.3 requires the hash for the handshake and transfer key derivation */
        /* we hash even for non TLS v1.3, since we don't know if its actually 
            TLS v1.3 till later at EXT_SUPPORTED_VERSIONS in server_hello */
        HashRaw(session->sslServer, input - HANDSHAKE_HEADER_SZ, size + HANDSHAKE_HEADER_SZ);
        HashRaw(session->sslClient, input - HANDSHAKE_HEADER_SZ, size + HANDSHAKE_HEADER_SZ);
    }
#endif
#ifdef HAVE_EXTENDED_MASTER
    if (session->hash) {
        if (HashUpdate(session->hash, input, size) != 0) {
            SetError(EXTENDED_MASTER_HASH_STR, error,
                     session, FATAL_ERROR_STATE);
            return -1;
        }
    }
#endif

    switch (type) {
        case hello_verify_request:
            Trace(GOT_HELLO_VERIFY_STR);
            break;
        case hello_request:
            Trace(GOT_HELLO_REQUEST_STR);
            break;
        case session_ticket:
            Trace(GOT_SESSION_TICKET_STR);
            ret = ProcessSessionTicket(input, sslBytes, session, error);
            break;
        case server_hello:
            Trace(GOT_SERVER_HELLO_STR);
            ret = ProcessServerHello(size, input, sslBytes, session, error);
            break;
        case certificate_request:
            Trace(GOT_CERT_REQ_STR);
            break;
        case server_key_exchange:
#ifdef WOLFSSL_SNIFFER_STATS
            INC_STAT(SnifferStats.sslEphemeralMisses);
#endif
            Trace(GOT_SERVER_KEY_EX_STR);
            /* can't know temp key passively */
            SetError(BAD_CIPHER_SPEC_STR, error, session, FATAL_ERROR_STATE);
            ret = -1;
            break;
        case encrypted_extensions:
            Trace(GOT_ENC_EXT_STR);
            ssl->msgsReceived.got_encrypted_extensions = 1;
            break;
        case certificate:
            Trace(GOT_CERT_STR);
            if (session->flags.side == WOLFSSL_SERVER_END) {
#ifdef WOLFSSL_SNIFFER_STATS
                INC_STAT(SnifferStats.sslClientAuthConns);
#endif
            }
#ifdef WOLFSSL_SNIFFER_WATCH
            ret = ProcessCertificate(input, sslBytes, session, error);
#endif
            break;
        case server_hello_done:
            Trace(GOT_SERVER_HELLO_DONE_STR);
            break;
        case finished:
            Trace(GOT_FINISHED_STR);
            ret = ProcessFinished(input, size, sslBytes, session, error);
            break;
        case client_hello:
            Trace(GOT_CLIENT_HELLO_STR);
            ret = ProcessClientHello(input, sslBytes, session, error);
            break;
        case client_key_exchange:
            Trace(GOT_CLIENT_KEY_EX_STR);
#ifdef HAVE_EXTENDED_MASTER
            if (session->flags.expectEms && session->hash != NULL) {
                if (HashCopy(session->sslServer->hsHashes,
                             session->hash) == 0 &&
                    HashCopy(session->sslClient->hsHashes,
                             session->hash) == 0) {

                    session->sslServer->options.haveEMS = 1;
                    session->sslClient->options.haveEMS = 1;
                }
                else {
                    SetError(EXTENDED_MASTER_HASH_STR, error,
                             session, FATAL_ERROR_STATE);
                    ret = -1;
                }
                XMEMSET(session->hash, 0, sizeof(HsHashes));
                XFREE(session->hash, NULL, DYNAMIC_TYPE_HASHES);
                session->hash = NULL;
            }
            else {
                session->sslServer->options.haveEMS = 0;
                session->sslClient->options.haveEMS = 0;
            }
#endif
            if (ret == 0)
                ret = ProcessClientKeyExchange(input, sslBytes, session, error);
            break;
        case certificate_verify:
            Trace(GOT_CERT_VER_STR);
            break;
        case certificate_status:
            Trace(GOT_CERT_STATUS_STR);
            break;
        default:
            SetError(GOT_UNKNOWN_HANDSHAKE_STR, error, session, 0);
            return -1;
    }

    *sslBytes = startBytes - size;  /* actual bytes of full process */

    return ret;
}


/* Decrypt input into plain output, 0 on success */
static int Decrypt(WOLFSSL* ssl, byte* output, const byte* input, word32 sz)
{
    int ret = 0;

    (void)output;
    (void)input;
    (void)sz;

    switch (ssl->specs.bulk_cipher_algorithm) {
        #ifdef BUILD_ARC4
        case wolfssl_rc4:
            wc_Arc4Process(ssl->decrypt.arc4, output, input, sz);
            break;
        #endif

        #ifdef BUILD_DES3
        case wolfssl_triple_des:
            ret = wc_Des3_CbcDecrypt(ssl->decrypt.des3, output, input, sz);
            break;
        #endif

        #ifdef BUILD_AES
        case wolfssl_aes:
            ret = wc_AesCbcDecrypt(ssl->decrypt.aes, output, input, sz);
            break;
        #endif

        #ifdef HAVE_HC128
        case wolfssl_hc128:
            wc_Hc128_Process(ssl->decrypt.hc128, output, input, sz);
            break;
        #endif

        #ifdef BUILD_RABBIT
        case wolfssl_rabbit:
            wc_RabbitProcess(ssl->decrypt.rabbit, output, input, sz);
            break;
        #endif

        #ifdef HAVE_CAMELLIA
        case wolfssl_camellia:
            wc_CamelliaCbcDecrypt(ssl->decrypt.cam, output, input, sz);
            break;
        #endif

        #ifdef HAVE_IDEA
        case wolfssl_idea:
            wc_IdeaCbcDecrypt(ssl->decrypt.idea, output, input, sz);
            break;
        #endif

        #ifdef HAVE_AESGCM
        case wolfssl_aes_gcm:
            if (sz >= (word32)(AESGCM_EXP_IV_SZ + ssl->specs.aead_mac_size))
            {
                /* scratch buffer, sniffer ignores auth tag*/
                byte authTag[WOLFSSL_MIN_AUTH_TAG_SZ];
                byte nonce[AESGCM_NONCE_SZ];
                XMEMCPY(nonce, ssl->keys.aead_dec_imp_IV, AESGCM_IMP_IV_SZ);
                XMEMCPY(nonce + AESGCM_IMP_IV_SZ, input, AESGCM_EXP_IV_SZ);

                if (wc_AesGcmEncrypt(ssl->decrypt.aes,
                            output,
                            input + AESGCM_EXP_IV_SZ,
                            sz - AESGCM_EXP_IV_SZ - ssl->specs.aead_mac_size,
                            nonce, AESGCM_NONCE_SZ,
                            authTag, sizeof(authTag),
                            NULL, 0) < 0) {
                    Trace(BAD_DECRYPT);
                    ret = -1;
                }
                ForceZero(nonce, AESGCM_NONCE_SZ);
            }
            else {
                Trace(BAD_DECRYPT_SIZE);
                ret = -1;
            }
            break;
        #endif

        #ifdef HAVE_NULL_CIPHER
        case wolfssl_cipher_null:
            XMEMCPY(output, input, sz);
            break;
        #endif

        default:
            Trace(BAD_DECRYPT_TYPE);
            ret = -1;
            break;
    }

    return ret;
}


/* Decrypt input message into output, adjust output steam if needed */
static const byte* DecryptMessage(WOLFSSL* ssl, const byte* input, word32 sz,
                byte* output, int* error, int* advance, RecordLayerHeader* rh)
{
    int ivExtra = 0;
    int ret;
    
#ifdef WOLFSSL_TLS13
    if (IsAtLeastTLSv1_3(ssl->version)) {
        ret = DecryptTls13(ssl, output, input, sz, (byte*)rh, RECORD_HEADER_SZ);
    }
    else
#endif
    {
        ret = Decrypt(ssl, output, input, sz);
    }
    if (ret != 0) {
        *error = ret;
        return NULL;
    }
    ssl->keys.encryptSz = sz;
    if (ssl->options.tls1_1 && ssl->specs.cipher_type == block) {
        output += ssl->specs.block_size; /* go past TLSv1.1 IV */
        ivExtra = ssl->specs.block_size;
        *advance = ssl->specs.block_size;
    }

    if (ssl->specs.cipher_type == aead) {
        *advance = ssl->specs.aead_mac_size;
        ssl->keys.padSz = ssl->specs.aead_mac_size;
    }
    else
        ssl->keys.padSz = ssl->specs.hash_size;

    if (ssl->specs.cipher_type == block)
        ssl->keys.padSz += *(output + sz - ivExtra - 1) + 1;

#ifdef WOLFSSL_TLS13
    if (IsAtLeastTLSv1_3(ssl->version)) {
        word16 i = (word16)(sz - ssl->keys.padSz);
        /* Remove padding from end of plain text. */
        for (--i; i > 0; i--) {
            if (output[i] != 0)
                break;
        }
        /* Get the real content type from the end of the data. */
        rh->type = output[i];
        ssl->keys.padSz = sz - i;
    }
#endif
    (void)rh;

    return output;
}


/* remove session from table, use rowHint if no info (means we have a lock) */
static void RemoveSession(SnifferSession* session, IpInfo* ipInfo,
                        TcpInfo* tcpInfo, word32 rowHint)
{
    SnifferSession* previous = 0;
    SnifferSession* current;
    word32          row = rowHint;
    int             haveLock = 0;

    if (ipInfo && tcpInfo)
        row = SessionHash(ipInfo, tcpInfo);
    else
        haveLock = 1;

    assert(row <= HASH_SIZE);
    Trace(REMOVE_SESSION_STR);

    if (!haveLock)
        wc_LockMutex(&SessionMutex);

    current = SessionTable[row];

    while (current) {
        if (current == session) {
            if (previous)
                previous->next = current->next;
            else
                SessionTable[row] = current->next;
            FreeSnifferSession(session);
            TraceRemovedSession();
            break;
        }
        previous = current;
        current  = current->next;
    }

    if (!haveLock)
        wc_UnLockMutex(&SessionMutex);
}


/* Remove stale sessions from the Session Table, have a lock */
static void RemoveStaleSessions(void)
{
    word32 i;
    SnifferSession* session;

    for (i = 0; i < HASH_SIZE; i++) {
        session = SessionTable[i];
        while (session) {
            SnifferSession* next = session->next;
            if (time(NULL) >= session->lastUsed + WOLFSSL_SNIFFER_TIMEOUT) {
                TraceStaleSession();
                RemoveSession(session, NULL, NULL, i);
            }
            session = next;
        }
    }
}


/* Create a new Sniffer Session */
static SnifferSession* CreateSession(IpInfo* ipInfo, TcpInfo* tcpInfo,
                                     char* error)
{
    SnifferSession* session = 0;
    int row;

    Trace(NEW_SESSION_STR);
    /* create a new one */
    session = (SnifferSession*)XMALLOC(sizeof(SnifferSession),
            NULL, DYNAMIC_TYPE_SNIFFER_SESSION);
    if (session == NULL) {
        SetError(MEMORY_STR, error, NULL, 0);
        return 0;
    }
    InitSession(session);
#ifdef HAVE_EXTENDED_MASTER
    {
        HsHashes* newHash = (HsHashes*)XMALLOC(sizeof(HsHashes),
                NULL, DYNAMIC_TYPE_HASHES);
        if (newHash == NULL) {
            SetError(MEMORY_STR, error, NULL, 0);
            XFREE(session, NULL, DYNAMIC_TYPE_SNIFFER_SESSION);
            return 0;
        }
        if (HashInit(newHash) != 0) {
            SetError(EXTENDED_MASTER_HASH_STR, error, NULL, 0);
            XFREE(session, NULL, DYNAMIC_TYPE_SNIFFER_SESSION);
            return 0;
        }
        session->hash = newHash;
    }
#endif
    session->server  = ipInfo->dst;
    session->client  = ipInfo->src;
    session->srvPort = (word16)tcpInfo->dstPort;
    session->cliPort = (word16)tcpInfo->srcPort;
    session->cliSeqStart = tcpInfo->sequence;
    session->cliExpected = 1;  /* relative */
    session->lastUsed= time(NULL);
    session->keySz = 0;
#ifdef HAVE_SNI
    session->sni = NULL;
#endif

    session->context = GetSnifferServer(ipInfo, tcpInfo);
    if (session->context == NULL) {
        SetError(SERVER_NOT_REG_STR, error, NULL, 0);
        XFREE(session, NULL, DYNAMIC_TYPE_SNIFFER_SESSION);
        return 0;
    }

    session->sslServer = wolfSSL_new(session->context->ctx);
    if (session->sslServer == NULL) {
        SetError(BAD_NEW_SSL_STR, error, session, FATAL_ERROR_STATE);
        XFREE(session, NULL, DYNAMIC_TYPE_SNIFFER_SESSION);
        return 0;
    }
    session->sslClient = wolfSSL_new(session->context->ctx);
    if (session->sslClient == NULL) {
        wolfSSL_free(session->sslServer);
        session->sslServer = 0;

        SetError(BAD_NEW_SSL_STR, error, session, FATAL_ERROR_STATE);
        XFREE(session, NULL, DYNAMIC_TYPE_SNIFFER_SESSION);
        return 0;
    }
    /* put server back into server mode */
    session->sslServer->options.side = WOLFSSL_SERVER_END;

    row = SessionHash(ipInfo, tcpInfo);

    /* add it to the session table */
    wc_LockMutex(&SessionMutex);

    session->next = SessionTable[row];
    SessionTable[row] = session;

    SessionCount++;

    if ( (SessionCount % HASH_SIZE) == 0) {
        TraceFindingStale();
        RemoveStaleSessions();
    }

    wc_UnLockMutex(&SessionMutex);

    /* CreateSession is called in response to a SYN packet, we know this
     * is headed to the server. Also we know the server is one we care
     * about as we've passed the GetSnifferServer() successfully. */
    session->flags.side = WOLFSSL_SERVER_END;

    return session;
}


#ifdef OLD_HELLO_ALLOWED

/* Process Old Client Hello Input */
static int DoOldHello(SnifferSession* session, const byte* sslFrame,
                      int* rhSize, int* sslBytes, char* error)
{
    const byte* input = sslFrame;
    byte        b0, b1;
    word32      idx = 0;
    int         ret;

    Trace(GOT_OLD_CLIENT_HELLO_STR);
    session->flags.clientHello = 1;    /* don't process again */
    b0 = *input++;
    b1 = *input++;
    *sslBytes -= 2;
    *rhSize = ((b0 & 0x7f) << 8) | b1;

    if (*rhSize > *sslBytes) {
        SetError(OLD_CLIENT_INPUT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    ret = ProcessOldClientHello(session->sslServer, input, &idx, *sslBytes,
                                (word16)*rhSize);
    if (ret < 0 && ret != MATCH_SUITE_ERROR) {
        SetError(BAD_OLD_CLIENT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }

    Trace(OLD_CLIENT_OK_STR);
    XMEMCPY(session->sslClient->arrays->clientRandom,
           session->sslServer->arrays->clientRandom, RAN_LEN);

    *sslBytes -= *rhSize;
    return 0;
}

#endif /* OLD_HELLO_ALLOWED */


#if 0
/* Calculate the TCP checksum, see RFC 1071 */
/* return 0 for success, -1 on error */
/* can be called from decode() with
   TcpChecksum(&ipInfo, &tcpInfo, sslBytes, packet + ipInfo.length);
   could also add a 64bit version if type available and using this
*/
int TcpChecksum(IpInfo* ipInfo, TcpInfo* tcpInfo, int dataLen,
                const byte* packet)
{
    TcpPseudoHdr  pseudo;
    int           count = PSEUDO_HDR_SZ;
    const word16* data = (word16*)&pseudo;
    word32        sum = 0;
    word16        checksum;

    pseudo.src = ipInfo->src;
    pseudo.dst = ipInfo->dst;
    pseudo.rsv = 0;
    pseudo.protocol = TCP_PROTO;
    pseudo.length = htons(tcpInfo->length + dataLen);

    /* pseudo header sum */
    while (count >= 2) {
        sum   += *data++;
        count -= 2;
    }

    count = tcpInfo->length + dataLen;
    data = (word16*)packet;

    /* main sum */
    while (count > 1) {
        sum   += *data++;
        count -=2;
    }

    /* get left-over, if any */
    packet = (byte*)data;
    if (count > 0) {
        sum += *packet;
    }

    /* fold 32bit sum into 16 bits */
    while (sum >> 16)
        sum = (sum & 0xffff) + (sum >> 16);

    checksum = (word16)~sum;
    /* checksum should now equal 0, since included already calcd checksum */
    /* field, but tcp checksum offloading could negate calculation */
    if (checksum == 0)
        return 0;
    return -1;
}
#endif


/* Check IP and TCP headers, set payload */
/* returns 0 on success, -1 on error */
static int CheckHeaders(IpInfo* ipInfo, TcpInfo* tcpInfo, const byte* packet,
                  int length, const byte** sslFrame, int* sslBytes, char* error)
{
    TraceHeader();
    TracePacket();

    /* ip header */
    if (length < IP_HDR_SZ) {
        SetError(PACKET_HDR_SHORT_STR, error, NULL, 0);
        return -1;
    }
    if (CheckIpHdr((IpHdr*)packet, ipInfo, length, error) != 0)
        return -1;

    /* tcp header */
    if (length < (ipInfo->length + TCP_HDR_SZ)) {
        SetError(PACKET_HDR_SHORT_STR, error, NULL, 0);
        return -1;
    }
    if (CheckTcpHdr((TcpHdr*)(packet + ipInfo->length), tcpInfo, error) != 0)
        return -1;

    /* setup */
    *sslFrame = packet + ipInfo->length + tcpInfo->length;
    if (*sslFrame > packet + length) {
        SetError(PACKET_HDR_SHORT_STR, error, NULL, 0);
        return -1;
    }
    /* We only care about the data in the TCP/IP record. There may be extra
     * data after the IP record for the FCS for Ethernet. */
    *sslBytes = (int)(packet + ipInfo->total - *sslFrame);

    return 0;
}


/* Create or Find existing session */
/* returns 0 on success (continue), -1 on error, 1 on success (end) */
static int CheckSession(IpInfo* ipInfo, TcpInfo* tcpInfo, int sslBytes,
                        SnifferSession** session, char* error)
{
    /* create a new SnifferSession on client SYN */
    if (tcpInfo->syn && !tcpInfo->ack) {
        TraceClientSyn(tcpInfo->sequence);
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslEncryptedConns);
#endif
        *session = CreateSession(ipInfo, tcpInfo, error);
        if (*session == NULL) {
            *session = GetSnifferSession(ipInfo, tcpInfo);
            /* already had existing, so OK */
            if (*session)
                return 1;

            SetError(MEMORY_STR, error, NULL, 0);
            return -1;
        }
        return 1;
    }
    /* get existing sniffer session */
    else {
        *session = GetSnifferSession(ipInfo, tcpInfo);
        if (*session == NULL) {
            /* don't worry about extraneous RST or duplicate FINs */
            if (tcpInfo->fin || tcpInfo->rst)
                return 1;
            /* don't worry about duplicate ACKs either */
            if (sslBytes == 0 && tcpInfo->ack)
                return 1;

#ifdef WOLFSSL_SNIFFER_STATS
            LOCK_STAT();
            NOLOCK_INC_STAT(SnifferStats.sslDecryptedPackets);
            NOLOCK_ADD_TO_STAT(SnifferStats.sslDecryptedBytes, sslBytes);
            UNLOCK_STAT();
#endif

            SetError(BAD_SESSION_STR, error, NULL, 0);
            return -1;
        }
    }
    return 0;
}


/* Create a Packet Buffer from *begin - end, adjust new *begin and bytesLeft */
static PacketBuffer* CreateBuffer(word32* begin, word32 end, const byte* data,
                                  int* bytesLeft)
{
    PacketBuffer* pb;

    int added = end - *begin + 1;
    assert(*begin <= end);

    pb = (PacketBuffer*)XMALLOC(sizeof(PacketBuffer),
            NULL, DYNAMIC_TYPE_SNIFFER_PB);
    if (pb == NULL) return NULL;

    pb->next  = 0;
    pb->begin = *begin;
    pb->end   = end;
    pb->data = (byte*)XMALLOC(added, NULL, DYNAMIC_TYPE_SNIFFER_PB_BUFFER);

    if (pb->data == NULL) {
        XFREE(pb, NULL, DYNAMIC_TYPE_SNIFFER_PB);
        return NULL;
    }
    XMEMCPY(pb->data, data, added);

    *bytesLeft -= added;
    *begin      = pb->end + 1;

    return pb;
}


/* Add sslFrame to Reassembly List */
/* returns 1 (end) on success, -1, on error */
static int AddToReassembly(byte from, word32 seq, const byte* sslFrame,
                           int sslBytes, SnifferSession* session, char* error)
{
    PacketBuffer*  add;
    PacketBuffer** front = (from == WOLFSSL_SERVER_END) ?
                       &session->cliReassemblyList: &session->srvReassemblyList;
    PacketBuffer*  curr = *front;
    PacketBuffer*  prev = curr;

    word32* reassemblyMemory = (from == WOLFSSL_SERVER_END) ?
                  &session->cliReassemblyMemory : &session->srvReassemblyMemory;
    word32  startSeq = seq;
    word32  added;
    int     bytesLeft = sslBytes;  /* could be overlapping fragment */

    /* if list is empty add full frame to front */
    if (!curr) {
        if (MaxRecoveryMemory != -1 &&
                      (int)(*reassemblyMemory + sslBytes) > MaxRecoveryMemory) {
            SetError(REASSEMBLY_MAX_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        add = CreateBuffer(&seq, seq + sslBytes - 1, sslFrame, &bytesLeft);
        if (add == NULL) {
            SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        *front = add;
        *reassemblyMemory += sslBytes;
        return 1;
    }

    /* add to front if before current front, up to next->begin */
    if (seq < curr->begin) {
        word32 end = seq + sslBytes - 1;

        if (end >= curr->begin)
            end = curr->begin - 1;

        if (MaxRecoveryMemory -1 &&
                      (int)(*reassemblyMemory + sslBytes) > MaxRecoveryMemory) {
            SetError(REASSEMBLY_MAX_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        add = CreateBuffer(&seq, end, sslFrame, &bytesLeft);
        if (add == NULL) {
            SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        add->next = curr;
        *front = add;
        *reassemblyMemory += sslBytes;
    }

    /* while we have bytes left, try to find a gap to fill */
    while (bytesLeft > 0) {
        /* get previous packet in list */
        while (curr && (seq >= curr->begin)) {
            prev = curr;
            curr = curr->next;
        }

        /* don't add  duplicate data */
        if (prev->end >= seq) {
            if ( (seq + bytesLeft - 1) <= prev->end)
                return 1;
            seq = prev->end + 1;
            bytesLeft = startSeq + sslBytes - seq;
        }

        if (!curr)
            /* we're at the end */
            added = bytesLeft;
        else
            /* we're in between two frames */
            added = min((word32)bytesLeft, curr->begin - seq);

        /* data already there */
        if (added == 0)
            continue;

        if (MaxRecoveryMemory != -1 &&
                         (int)(*reassemblyMemory + added) > MaxRecoveryMemory) {
            SetError(REASSEMBLY_MAX_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        add = CreateBuffer(&seq, seq + added - 1, &sslFrame[seq - startSeq],
                           &bytesLeft);
        if (add == NULL) {
            SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        add->next  = prev->next;
        prev->next = add;
        *reassemblyMemory += added;
    }
    return 1;
}


/* Add out of order FIN capture */
/* returns 1 for success (end) */
static int AddFinCapture(SnifferSession* session, word32 sequence)
{
    if (session->flags.side == WOLFSSL_SERVER_END) {
        if (session->finCapture.cliCounted == 0)
            session->finCapture.cliFinSeq = sequence;
    }
    else {
        if (session->finCapture.srvCounted == 0)
            session->finCapture.srvFinSeq = sequence;
    }
    return 1;
}


/* Adjust incoming sequence based on side */
/* returns 0 on success (continue), -1 on error, 1 on success (end) */
static int AdjustSequence(TcpInfo* tcpInfo, SnifferSession* session,
                          int* sslBytes, const byte** sslFrame, char* error)
{
    word32  seqStart = (session->flags.side == WOLFSSL_SERVER_END) ?
                                     session->cliSeqStart :session->srvSeqStart;
    word32  real     = tcpInfo->sequence - seqStart;
    word32* expected = (session->flags.side == WOLFSSL_SERVER_END) ?
                                  &session->cliExpected : &session->srvExpected;
    PacketBuffer* reassemblyList = (session->flags.side == WOLFSSL_SERVER_END) ?
                        session->cliReassemblyList : session->srvReassemblyList;
    byte  skipPartial = (session->flags.side == WOLFSSL_SERVER_END) ?
                                session->flags.srvSkipPartial :
                                session->flags.cliSkipPartial;

    /* handle rollover of sequence */
    if (tcpInfo->sequence < seqStart)
        real = 0xffffffffU - seqStart + tcpInfo->sequence;

    TraceRelativeSequence(*expected, real);

    if (real < *expected) {
        Trace(DUPLICATE_STR);
        if (real + *sslBytes > *expected) {
            int overlap = *expected - real;
            Trace(OVERLAP_DUPLICATE_STR);

            /* adjust to expected, remove duplicate */
            *sslFrame += overlap;
            *sslBytes -= overlap;

            /* The following conditional block is duplicated below. It is the
             * same action but for a different setup case. If changing this
             * block be sure to also update the block below. */
            if (reassemblyList) {
                word32 newEnd = *expected + *sslBytes;

                if (newEnd > reassemblyList->begin) {
                    Trace(OVERLAP_REASSEMBLY_BEGIN_STR);

                    /* remove bytes already on reassembly list */
                    *sslBytes -= newEnd - reassemblyList->begin;
                }
                if (newEnd > reassemblyList->end) {
                    Trace(OVERLAP_REASSEMBLY_END_STR);

                    /* may be past reassembly list end (could have more on list)
                       so try to add what's past the front->end */
                    AddToReassembly(session->flags.side, reassemblyList->end +1,
                                *sslFrame + reassemblyList->end - *expected + 1,
                                 newEnd - reassemblyList->end, session, error);
                }
            }
        }
        else
            return 1;
    }
    else if (real > *expected) {
        Trace(OUT_OF_ORDER_STR);
        if (*sslBytes > 0) {
            int addResult = AddToReassembly(session->flags.side, real,
                                          *sslFrame, *sslBytes, session, error);
            if (skipPartial) {
                *sslBytes = 0;
                return 0;
            }
            else
                return addResult;
        }
        else if (tcpInfo->fin)
            return AddFinCapture(session, real);
    }
    else if (*sslBytes > 0) {
        if (skipPartial) {
            AddToReassembly(session->flags.side, real,
                                          *sslFrame, *sslBytes, session, error);
            *expected += *sslBytes;
            *sslBytes = 0;
            if (tcpInfo->fin)
                *expected += 1;
            return 0;
        }
        /* The following conditional block is duplicated above. It is the
         * same action but for a different setup case. If changing this
         * block be sure to also update the block above. */
        else if (reassemblyList) {
            word32 newEnd = *expected + *sslBytes;

            if (newEnd > reassemblyList->begin) {
                Trace(OVERLAP_REASSEMBLY_BEGIN_STR);

                /* remove bytes already on reassembly list */
                *sslBytes -= newEnd - reassemblyList->begin;
            }
            if (newEnd > reassemblyList->end) {
                Trace(OVERLAP_REASSEMBLY_END_STR);

                /* may be past reassembly list end (could have more on list)
                   so try to add what's past the front->end */
                AddToReassembly(session->flags.side, reassemblyList->end +1,
                            *sslFrame + reassemblyList->end - *expected + 1,
                             newEnd - reassemblyList->end, session, error);
            }
        }
    }
    /* got expected sequence */
    *expected += *sslBytes;
    if (tcpInfo->fin)
        *expected += 1;

    return 0;
}


static int FindNextRecordInAssembly(SnifferSession* session,
                                    const byte** sslFrame, int* sslBytes,
                                    const byte** end, char* error)
{
    PacketBuffer**     front = (session->flags.side == WOLFSSL_SERVER_END) ?
                                    &session->cliReassemblyList :
                                    &session->srvReassemblyList;
    PacketBuffer*       curr = *front;
    PacketBuffer*       prev = NULL;
    byte*        skipPartial = (session->flags.side == WOLFSSL_SERVER_END) ?
                                    &session->flags.srvSkipPartial :
                                    &session->flags.cliSkipPartial;
    word32* reassemblyMemory = (session->flags.side == WOLFSSL_SERVER_END) ?
                                    &session->cliReassemblyMemory :
                                    &session->srvReassemblyMemory;
    WOLFSSL*             ssl = (session->flags.side == WOLFSSL_SERVER_END) ?
                                    session->sslServer :
                                    session->sslClient;
    ProtocolVersion       pv = ssl->version;
    word32*         expected = (session->flags.side == WOLFSSL_SERVER_END) ?
                                    &session->cliExpected :
                                    &session->srvExpected;

    while (curr != NULL) {
        *expected = curr->end + 1;

        if (curr->data[0] == application_data &&
            curr->data[1] == pv.major &&
            curr->data[2] == pv.minor) {

            if (ssl->buffers.inputBuffer.length > 0)
                Trace(DROPPING_PARTIAL_RECORD);

            *sslBytes = curr->end - curr->begin + 1;
            if ( (word32)*sslBytes > ssl->buffers.inputBuffer.bufferSize) {
                if (GrowInputBuffer(ssl, *sslBytes, 0) < 0) {
                    SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
                    return -1;
                }
            }

            XMEMCPY(ssl->buffers.inputBuffer.buffer, curr->data, *sslBytes);

            *front = curr->next;
            *reassemblyMemory -= *sslBytes;
            FreePacketBuffer(curr);

            ssl->buffers.inputBuffer.length = *sslBytes;
            *sslFrame = ssl->buffers.inputBuffer.buffer;
            *end = *sslFrame + *sslBytes;
            *skipPartial = 0;

            return 0;
        }
        else if (ssl->specs.cipher_type == block) {
            if (ssl->specs.bulk_cipher_algorithm == wolfssl_aes) {
#ifdef BUILD_AES
                wc_AesSetIV(ssl->decrypt.aes,
                            curr->data + curr->end - curr->begin
                                       - ssl->specs.block_size + 1);
#endif
            }
            else if (ssl->specs.bulk_cipher_algorithm == wolfssl_triple_des) {
#ifdef BUILD_DES3
                wc_Des3_SetIV(ssl->decrypt.des3,
                              curr->data + curr->end - curr->begin
                                         - ssl->specs.block_size + 1);
#endif
            }
        }

        Trace(DROPPING_LOST_FRAG_STR);
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslDecodeFails);
#endif
        prev = curr;
        curr = curr->next;
        *reassemblyMemory -= (prev->end - prev->begin + 1);
        FreePacketBuffer(prev);
    }

    *front = curr;

    return 0;
}


static int FixSequence(TcpInfo* tcpInfo, SnifferSession* session)
{
    word32*   expected = (session->flags.side == WOLFSSL_SERVER_END) ?
                                &session->srvExpected : &session->cliExpected;
    PacketBuffer* list = (session->flags.side == WOLFSSL_SERVER_END) ?
                                session->srvReassemblyList :
                                session->cliReassemblyList;
    byte*  skipPartial = (session->flags.side != WOLFSSL_SERVER_END) ?
                                &session->flags.srvSkipPartial :
                                &session->flags.cliSkipPartial;

    *skipPartial = 1;
    if (list != NULL)
        *expected = list->begin;
    else {
        word32 seqStart = (session->flags.side == WOLFSSL_SERVER_END) ?
                                session->srvSeqStart : session->cliSeqStart;
        word32     real = tcpInfo->ackNumber - seqStart;

        *expected = real;
    }

    return 1;
}


/* Check latest ack number for missing packets
   return 0 ok, <0 on error */
static int CheckAck(TcpInfo* tcpInfo, SnifferSession* session)
{
    if (tcpInfo->ack) {
        word32  seqStart = (session->flags.side == WOLFSSL_SERVER_END) ?
                                     session->srvSeqStart :session->cliSeqStart;
        word32  real     = tcpInfo->ackNumber - seqStart;
        word32  expected = (session->flags.side == WOLFSSL_SERVER_END) ?
                                  session->srvExpected : session->cliExpected;

        /* handle rollover of sequence */
        if (tcpInfo->ackNumber < seqStart)
            real = 0xffffffffU - seqStart + tcpInfo->ackNumber;

        TraceAck(real, expected);

        if (real > expected)
            return -1;  /* we missed a packet, ACKing data we never saw */
    }
    return 0;
}


/* Check TCP Sequence status */
/* returns 0 on success (continue), -1 on error, 1 on success (end) */
static int CheckSequence(IpInfo* ipInfo, TcpInfo* tcpInfo,
                         SnifferSession* session, int* sslBytes,
                         const byte** sslFrame, char* error)
{
    int actualLen;
    byte* ackFault = (session->flags.side == WOLFSSL_SERVER_END) ?
                        &session->flags.cliAckFault :
                        &session->flags.srvAckFault;

    /* init SEQ from server to client */
    if (tcpInfo->syn && tcpInfo->ack) {
        session->srvSeqStart = tcpInfo->sequence;
        session->srvExpected = 1;
        TraceServerSyn(tcpInfo->sequence);
        return 1;
    }

    /* adjust potential ethernet trailer */
    actualLen = ipInfo->total - ipInfo->length - tcpInfo->length;
    if (*sslBytes > actualLen) {
        *sslBytes = actualLen;
    }

    TraceSequence(tcpInfo->sequence, *sslBytes);
    if (CheckAck(tcpInfo, session) < 0) {
        if (!RecoveryEnabled) {
            UpdateMissedDataSessions();
            SetError(ACK_MISSED_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        else {
            SetError(ACK_MISSED_STR, error, session, 0);
            if (*ackFault == 0) {
                *ackFault = 1;
                UpdateMissedDataSessions();
            }
            return FixSequence(tcpInfo, session);
        }
    }

    if (*ackFault) {
        Trace(CLEAR_ACK_FAULT);
        *ackFault = 0;
    }

    return AdjustSequence(tcpInfo, session, sslBytes, sslFrame, error);
}


/* Check Status before record processing */
/* returns 0 on success (continue), -1 on error, 1 on success (end) */
static int CheckPreRecord(IpInfo* ipInfo, TcpInfo* tcpInfo,
                          const byte** sslFrame, SnifferSession** session,
                          int* sslBytes, const byte** end,
                          void* vChain, word32 chainSz, char* error)
{
    word32 length;
    WOLFSSL* ssl = ((*session)->flags.side == WOLFSSL_SERVER_END) ?
                                  (*session)->sslServer : (*session)->sslClient;
    byte  skipPartial = ((*session)->flags.side == WOLFSSL_SERVER_END) ?
                        (*session)->flags.srvSkipPartial :
                        (*session)->flags.cliSkipPartial;
    /* remove SnifferSession on 2nd FIN or RST */
    if (tcpInfo->fin || tcpInfo->rst) {
        /* flag FIN and RST */
        if (tcpInfo->fin)
            (*session)->flags.finCount += 1;
        else if (tcpInfo->rst)
            (*session)->flags.finCount += 2;

        if ((*session)->flags.finCount >= 2) {
            RemoveSession(*session, ipInfo, tcpInfo, 0);
            *session = NULL;
            return 1;
        }
    }

    if ((*session)->flags.fatalError == FATAL_ERROR_STATE) {
        SetError(FATAL_ERROR_STR, error, NULL, 0);
        return -1;
    }

    if (skipPartial) {
        if (FindNextRecordInAssembly(*session,
                                     sslFrame, sslBytes, end, error) < 0) {
            return -1;
        }
    }

    if (*sslBytes == 0) {
        Trace(NO_DATA_STR);
        return 1;
    }

    /* if current partial data, add to end of partial */
    /* if skipping, the data is already at the end of partial */
    if ( !skipPartial && (length = ssl->buffers.inputBuffer.length) ) {
        Trace(PARTIAL_ADD_STR);

        if ( (*sslBytes + length) > ssl->buffers.inputBuffer.bufferSize) {
            if (GrowInputBuffer(ssl, *sslBytes, length) < 0) {
                SetError(MEMORY_STR, error, *session, FATAL_ERROR_STATE);
                return -1;
            }
        }
        if (vChain == NULL) {
            XMEMCPY(&ssl->buffers.inputBuffer.buffer[length],
                    *sslFrame, *sslBytes);
            *sslBytes += length;
            ssl->buffers.inputBuffer.length = *sslBytes;
            *sslFrame = ssl->buffers.inputBuffer.buffer;
            *end = *sslFrame + *sslBytes;
        }
    }

    if (vChain != NULL) {
#ifdef WOLFSSL_SNIFFER_CHAIN_INPUT
        struct iovec* chain = (struct iovec*)vChain;
        word32 i, offset, headerSz, qty, remainder;

        Trace(CHAIN_INPUT_STR);
        headerSz = (word32)*sslFrame - (word32)chain[0].iov_base;
        remainder = *sslBytes;

        if ( (*sslBytes + length) > ssl->buffers.inputBuffer.bufferSize) {
            if (GrowInputBuffer(ssl, *sslBytes, length) < 0) {
                SetError(MEMORY_STR, error, *session, FATAL_ERROR_STATE);
                return -1;
            }
        }

        qty = min(*sslBytes, (word32)chain[0].iov_len - headerSz);
        XMEMCPY(&ssl->buffers.inputBuffer.buffer[length],
               (byte*)chain[0].iov_base + headerSz, qty);
        offset = length;
        for (i = 1; i < chainSz; i++) {
            offset += qty;
            remainder -= qty;

            if (chain[i].iov_len > remainder)
                qty = remainder;
            else
                qty = (word32)chain[i].iov_len;
            XMEMCPY(ssl->buffers.inputBuffer.buffer + offset,
                    chain[i].iov_base, qty);
        }

        *sslBytes += length;
        ssl->buffers.inputBuffer.length = *sslBytes;
        *sslFrame = ssl->buffers.inputBuffer.buffer;
        *end = *sslFrame + *sslBytes;
#endif
        (void)chainSz;
    }

    if ((*session)->flags.clientHello == 0 && **sslFrame != handshake) {
        /* Sanity check the packet for an old style client hello. */
        int rhSize = (((*sslFrame)[0] & 0x7f) << 8) | ((*sslFrame)[1]);

        if ((rhSize <= (*sslBytes - 2)) &&
            (*sslFrame)[2] == OLD_HELLO_ID && (*sslFrame)[3] == SSLv3_MAJOR) {
#ifdef OLD_HELLO_ALLOWED
        int ret = DoOldHello(*session, *sslFrame, &rhSize, sslBytes, error);
        if (ret < 0)
            return -1;  /* error already set */
        if (*sslBytes <= 0)
            return 1;
#endif
        }
        else {
#ifdef STARTTLS_ALLOWED
            if (ssl->buffers.inputBuffer.dynamicFlag) {
                ssl->buffers.inputBuffer.length = 0;
                ShrinkInputBuffer(ssl, NO_FORCED_FREE);
            }
            return 1;
#endif
        }
    }

    return 0;
}


/* See if input on the reassembly list is ready for consuming */
/* returns 1 for TRUE, 0 for FALSE */
static int HaveMoreInput(SnifferSession* session, const byte** sslFrame,
                         int* sslBytes, const byte** end, char* error)
{
    /* sequence and reassembly based on from, not to */
    int            moreInput = 0;
    PacketBuffer** front = (session->flags.side == WOLFSSL_SERVER_END) ?
                      &session->cliReassemblyList : &session->srvReassemblyList;
    word32*        expected = (session->flags.side == WOLFSSL_SERVER_END) ?
                                  &session->cliExpected : &session->srvExpected;
    /* buffer is on receiving end */
    word32*          length = (session->flags.side == WOLFSSL_SERVER_END) ?
                               &session->sslServer->buffers.inputBuffer.length :
                               &session->sslClient->buffers.inputBuffer.length;
    byte**         myBuffer = (session->flags.side == WOLFSSL_SERVER_END) ?
                               &session->sslServer->buffers.inputBuffer.buffer :
                               &session->sslClient->buffers.inputBuffer.buffer;
    word32*      bufferSize = (session->flags.side == WOLFSSL_SERVER_END) ?
                           &session->sslServer->buffers.inputBuffer.bufferSize :
                           &session->sslClient->buffers.inputBuffer.bufferSize;
    WOLFSSL*           ssl  = (session->flags.side == WOLFSSL_SERVER_END) ?
                            session->sslServer : session->sslClient;
    word32*     reassemblyMemory = (session->flags.side == WOLFSSL_SERVER_END) ?
                  &session->cliReassemblyMemory : &session->srvReassemblyMemory;

    while (*front && ((*front)->begin == *expected) ) {
        word32 room = *bufferSize - *length;
        word32 packetLen = (*front)->end - (*front)->begin + 1;

        if (packetLen > room && *bufferSize < MAX_INPUT_SZ) {
            if (GrowInputBuffer(ssl, packetLen, *length) < 0) {
                SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
                return 0;
            }
            room = *bufferSize - *length;   /* bufferSize is now bigger */
        }

        if (packetLen <= room) {
            PacketBuffer* del = *front;
            byte*         buf = *myBuffer;

            XMEMCPY(&buf[*length], (*front)->data, packetLen);
            *length   += packetLen;
            *expected += packetLen;

            /* remove used packet */
            *front = (*front)->next;

            *reassemblyMemory -= packetLen;
            FreePacketBuffer(del);

            moreInput = 1;
        }
        else
            break;
    }
    if (moreInput) {
        *sslFrame = *myBuffer;
        *sslBytes = *length;
        *end      = *myBuffer + *length;
    }
    return moreInput;
}



/* Process Message(s) from sslFrame */
/* return Number of bytes on success, 0 for no data yet, and -1 on error */
static int ProcessMessage(const byte* sslFrame, SnifferSession* session,
                          int sslBytes, byte** data, const byte* end,
                          void* ctx, char* error)
{
    const byte*       sslBegin = sslFrame;
    const byte*       recordEnd;   /* end of record indicator */
    const byte*       inRecordEnd; /* indicator from input stream not decrypt */
    RecordLayerHeader rh;
    int               rhSize = 0;
    int               ret;
    int               errCode = 0;
    int               decoded = 0;      /* bytes stored for user in data */
    int               notEnough;        /* notEnough bytes yet flag */
    int               decrypted = 0;    /* was current msg decrypted */
    WOLFSSL*          ssl = (session->flags.side == WOLFSSL_SERVER_END) ?
                            session->sslServer : session->sslClient;
doMessage:
    notEnough = 0;
    if (sslBytes < 0) {
        SetError(PACKET_HDR_SHORT_STR, error, session, FATAL_ERROR_STATE);
        return -1;
    }
    if (sslBytes >= RECORD_HEADER_SZ) {
        if (GetRecordHeader(sslFrame, &rh, &rhSize) != 0) {
            SetError(BAD_RECORD_HDR_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
    }
    else
        notEnough = 1;

    if (notEnough || rhSize > (sslBytes - RECORD_HEADER_SZ)) {
        /* don't have enough input yet to process full SSL record */
        Trace(PARTIAL_INPUT_STR);

        /* store partial if not there already or we advanced */
        if (ssl->buffers.inputBuffer.length == 0 || sslBegin != sslFrame) {
            if (sslBytes > (int)ssl->buffers.inputBuffer.bufferSize) {
                if (GrowInputBuffer(ssl, sslBytes, 0) < 0) {
                    SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
                    return -1;
                }
            }
            XMEMMOVE(ssl->buffers.inputBuffer.buffer, sslFrame, sslBytes);
            ssl->buffers.inputBuffer.length = sslBytes;
        }
        if (HaveMoreInput(session, &sslFrame, &sslBytes, &end, error))
            goto doMessage;
        return decoded;
    }
    sslFrame += RECORD_HEADER_SZ;
    sslBytes -= RECORD_HEADER_SZ;
    recordEnd = sslFrame + rhSize;   /* may have more than one record */
    inRecordEnd = recordEnd;

    /* decrypt if needed */
    if ((session->flags.side == WOLFSSL_SERVER_END &&
                                               session->flags.serverCipherOn)
     || (session->flags.side == WOLFSSL_CLIENT_END &&
                                               session->flags.clientCipherOn)) {
        int ivAdvance = 0;  /* TLSv1.1 advance amount */
        if (ssl->decrypt.setup != 1) {
            SetError(DECRYPT_KEYS_NOT_SETUP, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        if (CheckAvailableSize(ssl, rhSize) < 0) {
            SetError(MEMORY_STR, error, session, FATAL_ERROR_STATE);
            return -1;
        }
        sslFrame = DecryptMessage(ssl, sslFrame, rhSize,
                                  ssl->buffers.outputBuffer.buffer, &errCode,
                                  &ivAdvance, &rh);
        recordEnd = sslFrame - ivAdvance + rhSize;  /* sslFrame moved so
                                                       should recordEnd */
        decrypted = 1;

#ifdef WOLFSSL_SNIFFER_STATS
        if (errCode != 0) {
            INC_STAT(SnifferStats.sslKeyFails);
        }
        else {
            LOCK_STAT();
            NOLOCK_INC_STAT(SnifferStats.sslDecryptedPackets);
            NOLOCK_ADD_TO_STAT(SnifferStats.sslDecryptedBytes, sslBytes);
            UNLOCK_STAT();
        }
#endif
        if (errCode != 0) {
            SetError(BAD_DECRYPT, error, session, FATAL_ERROR_STATE);
            return -1;
        }
    }

doPart:

    switch ((enum ContentType)rh.type) {
        case handshake:
            {
                int startIdx = sslBytes;
                int used;

                Trace(GOT_HANDSHAKE_STR);
                ret = DoHandShake(sslFrame, &sslBytes, session, error);
                if (ret != 0) {
                    if (session->flags.fatalError == 0)
                        SetError(BAD_HANDSHAKE_STR, error, session,
                                 FATAL_ERROR_STATE);
                    return -1;
                }

                /* DoHandShake now fully decrements sslBytes to remaining */
                used = startIdx - sslBytes;
                sslFrame += used;
                if (decrypted)
                    sslFrame += ssl->keys.padSz;
            }
            break;
        case change_cipher_spec:
            if (session->flags.side == WOLFSSL_SERVER_END)
                session->flags.serverCipherOn = 1;
            else
                session->flags.clientCipherOn = 1;
            Trace(GOT_CHANGE_CIPHER_STR);
            ssl->options.handShakeState = HANDSHAKE_DONE;
            ssl->options.handShakeDone  = 1;

            sslFrame += 1;
            sslBytes -= 1;

            break;
        case application_data:
            Trace(GOT_APP_DATA_STR);
            {
                word32 inOutIdx = 0;

                ret = DoApplicationData(ssl, (byte*)sslFrame, &inOutIdx);
                if (ret == 0) {
                    ret = ssl->buffers.clearOutputBuffer.length;
                    TraceGotData(ret);
                    if (ret) {  /* may be blank message */
                        if (data != NULL) {
                            byte* tmpData;  /* don't leak on realloc free */
                            /* add an extra byte at end of allocation in case
                             * user wants to null terminate plaintext */
                            tmpData = (byte*)XREALLOC(*data, decoded + ret + 1,
                                    NULL, DYNAMIC_TYPE_TMP_BUFFER);
                            if (tmpData == NULL) {
                                ForceZero(*data, decoded);
                                XFREE(*data, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                                *data = NULL;
                                SetError(MEMORY_STR, error, session,
                                         FATAL_ERROR_STATE);
                                return -1;
                            }
                            *data = tmpData;
                            XMEMCPY(*data + decoded,
                                    ssl->buffers.clearOutputBuffer.buffer, ret);
                        }
                        else {
#ifdef WOLFSSL_SNIFFER_STORE_DATA_CB
                            if (StoreDataCb) {
                                const byte* buf;
                                word32 offset = 0;
                                word32 bufSz;
                                int stored;

                                buf = ssl->buffers.clearOutputBuffer.buffer;
                                bufSz = ssl->buffers.clearOutputBuffer.length;
                                do {
                                    stored = StoreDataCb(buf, bufSz, offset,
                                            ctx);
                                    if (stored <= 0) {
                                        return -1;
                                    }
                                    offset += stored;
                                } while (offset < bufSz);
                            }
                            else {
                                SetError(STORE_DATA_CB_MISSING_STR, error,
                                        session, FATAL_ERROR_STATE);
                                return -1;
                            }
#else
                            (void)ctx;
                            SetError(NO_DATA_DEST_STR, error, session,
                                    FATAL_ERROR_STATE);
                            return -1;
#endif
                        }
                        TraceAddedData(ret, decoded);
                        decoded += ret;
                        ssl->buffers.clearOutputBuffer.length = 0;
                    }
                }
                else {
                    SetError(BAD_APP_DATA_STR, error,session,FATAL_ERROR_STATE);
                    return -1;
                }
                if (ssl->buffers.outputBuffer.dynamicFlag)
                    ShrinkOutputBuffer(ssl);

                sslFrame += inOutIdx;
                sslBytes -= inOutIdx;
            }
            break;
        case alert:
            Trace(GOT_ALERT_STR);
#ifdef WOLFSSL_SNIFFER_STATS
            INC_STAT(SnifferStats.sslAlerts);
#endif
            sslFrame += rhSize;
            sslBytes -= rhSize;
            break;
        case no_type:
        default:
            SetError(GOT_UNKNOWN_RECORD_STR, error, session, FATAL_ERROR_STATE);
            return -1;
    }

    /* do we have another msg in record ? */
    if (sslFrame < recordEnd) {
        Trace(ANOTHER_MSG_STR);
        goto doPart;
    }

    /* back to input stream instead of potential decrypt buffer */
    recordEnd = inRecordEnd;

    /* do we have more records ? */
    if (recordEnd < end) {
        Trace(ANOTHER_MSG_STR);
        sslFrame = recordEnd;
        sslBytes = (int)(end - recordEnd);
        goto doMessage;
    }

    /* clear used input */
    ssl->buffers.inputBuffer.length = 0;

    /* could have more input ready now */
    if (HaveMoreInput(session, &sslFrame, &sslBytes, &end, error))
        goto doMessage;

    if (ssl->buffers.inputBuffer.dynamicFlag)
        ShrinkInputBuffer(ssl, NO_FORCED_FREE);

    return decoded;
}


/* See if we need to process any pending FIN captures */
/* Return 0=normal, else = session removed */
static int CheckFinCapture(IpInfo* ipInfo, TcpInfo* tcpInfo,
                            SnifferSession* session)
{
    int ret = 0;
    if (session->finCapture.cliFinSeq && session->finCapture.cliFinSeq <=
                                         session->cliExpected) {
        if (session->finCapture.cliCounted == 0) {
            session->flags.finCount += 1;
            session->finCapture.cliCounted = 1;
            TraceClientFin(session->finCapture.cliFinSeq, session->cliExpected);
        }
    }

    if (session->finCapture.srvFinSeq && session->finCapture.srvFinSeq <=
                                         session->srvExpected) {
        if (session->finCapture.srvCounted == 0) {
            session->flags.finCount += 1;
            session->finCapture.srvCounted = 1;
            TraceServerFin(session->finCapture.srvFinSeq, session->srvExpected);
        }
    }

    if (session->flags.finCount >= 2) {
        RemoveSession(session, ipInfo, tcpInfo, 0);
        ret = 1;
    }
    return ret;
}


/* If session is in fatal error state free resources now
   return true if removed, 0 otherwise */
static int RemoveFatalSession(IpInfo* ipInfo, TcpInfo* tcpInfo,
                              SnifferSession* session, char* error)
{
    if (session && session->flags.fatalError == FATAL_ERROR_STATE) {
        RemoveSession(session, ipInfo, tcpInfo, 0);
        SetError(FATAL_ERROR_STR, error, NULL, 0);
        return 1;
    }
    return 0;
}


/* Passes in an IP/TCP packet for decoding (ethernet/localhost frame) removed */
/* returns Number of bytes on success, 0 for no data yet, and -1 on error */
static int ssl_DecodePacketInternal(const byte* packet, int length,
                                    void* vChain, word32 chainSz,
                                    byte** data, SSLInfo* sslInfo,
                                    void* ctx, char* error)
{
    TcpInfo           tcpInfo;
    IpInfo            ipInfo;
    const byte*       sslFrame;
    const byte*       end;
    int               sslBytes;                /* ssl bytes unconsumed */
    int               ret;
    SnifferSession*   session = 0;

#ifdef WOLFSSL_SNIFFER_CHAIN_INPUT
    if (packet == NULL && vChain != NULL) {
        struct iovec* chain = (struct iovec*)vChain;
        word32 i;

        length = 0;
        for (i = 0; i < chainSz; i++)
            length += chain[i].iov_len;
        packet = (const byte*)chain[0].iov_base;
    }
#endif

    if (CheckHeaders(&ipInfo, &tcpInfo, packet, length, &sslFrame, &sslBytes,
                     error) != 0)
        return -1;

    end = sslFrame + sslBytes;

    ret = CheckSession(&ipInfo, &tcpInfo, sslBytes, &session, error);
    if (RemoveFatalSession(&ipInfo, &tcpInfo, session, error)) return -1;
    else if (ret == -1) return -1;
    else if (ret ==  1) {
#ifdef WOLFSSL_SNIFFER_STATS
        if (sslBytes > 0) {
            LOCK_STAT();
            NOLOCK_INC_STAT(SnifferStats.sslEncryptedPackets);
            NOLOCK_ADD_TO_STAT(SnifferStats.sslEncryptedBytes, sslBytes);
            UNLOCK_STAT();
        }
        else
            INC_STAT(SnifferStats.sslDecryptedPackets);
#endif
         return  0;   /* done for now */
    }

    ret = CheckSequence(&ipInfo, &tcpInfo, session, &sslBytes, &sslFrame,error);
    if (RemoveFatalSession(&ipInfo, &tcpInfo, session, error)) return -1;
    else if (ret == -1) return -1;
    else if (ret ==  1) {
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslDecryptedPackets);
#endif
        return  0;   /* done for now */
    }

    ret = CheckPreRecord(&ipInfo, &tcpInfo, &sslFrame, &session, &sslBytes,
                         &end, vChain, chainSz, error);
    if (RemoveFatalSession(&ipInfo, &tcpInfo, session, error)) return -1;
    else if (ret == -1) return -1;
    else if (ret ==  1) {
#ifdef WOLFSSL_SNIFFER_STATS
        INC_STAT(SnifferStats.sslDecryptedPackets);
#endif
        return  0;   /* done for now */
    }

#ifdef WOLFSSL_SNIFFER_STATS
    if (sslBytes > 0) {
        LOCK_STAT();
        NOLOCK_INC_STAT(SnifferStats.sslEncryptedPackets);
        NOLOCK_ADD_TO_STAT(SnifferStats.sslEncryptedBytes, sslBytes);
        UNLOCK_STAT();
    }
    else
        INC_STAT(SnifferStats.sslDecryptedPackets);
#endif

    ret = ProcessMessage(sslFrame, session, sslBytes, data, end, ctx, error);
    if (RemoveFatalSession(&ipInfo, &tcpInfo, session, error)) return -1;
    if (CheckFinCapture(&ipInfo, &tcpInfo, session) == 0) {
        CopySessionInfo(session, sslInfo);
    }

    return ret;
}


/* Passes in an IP/TCP packet for decoding (ethernet/localhost frame) removed */
/* returns Number of bytes on success, 0 for no data yet, and -1 on error */
/* Also returns Session Info if available */
int ssl_DecodePacketWithSessionInfo(const unsigned char* packet, int length,
    unsigned char** data, SSLInfo* sslInfo, char* error)
{
    return ssl_DecodePacketInternal(packet, length, NULL, 0, data, sslInfo,
            NULL, error);
}


/* Passes in an IP/TCP packet for decoding (ethernet/localhost frame) removed */
/* returns Number of bytes on success, 0 for no data yet, and -1 on error */
int ssl_DecodePacket(const byte* packet, int length, byte** data, char* error)
{
    return ssl_DecodePacketInternal(packet, length, NULL, 0, data, NULL, NULL,
            error);
}


#ifdef WOLFSSL_SNIFFER_STORE_DATA_CB

int ssl_DecodePacketWithSessionInfoStoreData(const unsigned char* packet,
        int length, void* ctx, SSLInfo* sslInfo, char* error)
{
    return ssl_DecodePacketInternal(packet, length, NULL, 0, NULL, sslInfo,
            ctx, error);
}

#endif


#ifdef WOLFSSL_SNIFFER_CHAIN_INPUT

int ssl_DecodePacketWithChain(void* vChain, word32 chainSz, byte** data,
        char* error)
{
    return ssl_DecodePacketInternal(NULL, 0, vChain, chainSz, data, NULL, NULL,
            error);
}

#endif


#if defined(WOLFSSL_SNIFFER_CHAIN_INPUT) && \
     defined(WOLFSSL_SNIFFER_STORE_DATA_CB)

int ssl_DecodePacketWithChainSessionInfoStoreData(void* vChain, word32 chainSz,
        void* ctx, SSLInfo* sslInfo, char* error)
{
    return ssl_DecodePacketInternal(NULL, 0, vChain, chainSz, NULL, sslInfo,
            ctx, error);
}

#endif


/* Deallocator for the decoded data buffer. */
/* returns 0 on success, -1 on error */
int ssl_FreeDecodeBuffer(byte** data, char* error)
{
    return ssl_FreeZeroDecodeBuffer(data, 0, error);
}


/* Deallocator for the decoded data buffer, zeros out buffer. */
/* returns 0 on success, -1 on error */
int ssl_FreeZeroDecodeBuffer(byte** data, int sz, char* error)
{
    (void)error;

    if (sz < 0) {
        return -1;
    }

    if (data != NULL) {
        ForceZero(*data, (word32)sz);
        XFREE(*data, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        *data = NULL;
    }

    return 0;
}


/* Enables (if traceFile)/ Disables debug tracing */
/* returns 0 on success, -1 on error */
int ssl_Trace(const char* traceFile, char* error)
{
    if (traceFile) {
        /* Don't try to reopen the file */
        if (TraceFile == NULL) {
            TraceFile = fopen(traceFile, "a");
            if (!TraceFile) {
                SetError(BAD_TRACE_FILE_STR, error, NULL, 0);
                return -1;
             }
            TraceOn = 1;
        }
    }
    else
        TraceOn = 0;

    return 0;
}


/* Enables/Disables Recovery of missed data if later packets allow
 * maxMemory is number of bytes to use for reassembly buffering per session,
 * -1 means unlimited
 * returns 0 on success, -1 on error */
int ssl_EnableRecovery(int onOff, int maxMemory, char* error)
{
    (void)error;

    RecoveryEnabled = onOff;
    if (onOff)
        MaxRecoveryMemory = maxMemory;

    return 0;
}



#ifdef WOLFSSL_SESSION_STATS

int ssl_GetSessionStats(unsigned int* active,     unsigned int* total,
                        unsigned int* peak,       unsigned int* maxSessions,
                        unsigned int* missedData, unsigned int* reassemblyMem,
                        char* error)
{
    int ret;

    if (missedData) {
        wc_LockMutex(&RecoveryMutex);
        *missedData = MissedDataSessions;
        wc_UnLockMutex(&RecoveryMutex);
    }

    if (reassemblyMem) {
        SnifferSession* session;
        int i;

        *reassemblyMem = 0;
        wc_LockMutex(&SessionMutex);
        for (i = 0; i < HASH_SIZE; i++) {
            session = SessionTable[i];
            while (session) {
                *reassemblyMem += session->cliReassemblyMemory;
                *reassemblyMem += session->srvReassemblyMemory;
                session = session->next;
            }
        }
        wc_UnLockMutex(&SessionMutex);
    }

    ret = wolfSSL_get_session_stats(active, total, peak, maxSessions);

    if (ret == WOLFSSL_SUCCESS)
        return 0;
    else {
        SetError(BAD_SESSION_STATS, error, NULL, 0);
        return -1;
    }
}

#endif



int ssl_SetConnectionCb(SSLConnCb cb)
{
    ConnectionCb = cb;
    return 0;
}



int ssl_SetConnectionCtx(void* ctx)
{
    ConnectionCbCtx = ctx;
    return 0;
}


#ifdef WOLFSSL_SNIFFER_STATS

/* Resets the statistics tracking global structure.
 * returns 0 on success, -1 on error */
int ssl_ResetStatistics(void)
{
    wc_LockMutex(&StatsMutex);
    XMEMSET(&SnifferStats, 0, sizeof(SSLStats));
    wc_UnLockMutex(&StatsMutex);
    return 0;
}


/* Copies the SSL statistics into the provided stats record.
 * returns 0 on success, -1 on error */
int ssl_ReadStatistics(SSLStats* stats)
{
    if (stats == NULL)
        return -1;

    LOCK_STAT();
    XMEMCPY(stats, &SnifferStats, sizeof(SSLStats));
    UNLOCK_STAT();
    return 0;
}

/* Copies the SSL statistics into the provided stats record then
 * resets the statistics tracking global structure.
 * returns 0 on success, -1 on error */
int ssl_ReadResetStatistics(SSLStats* stats)
{
    if (stats == NULL)
        return -1;

    LOCK_STAT();
    XMEMCPY(stats, &SnifferStats, sizeof(SSLStats));
    XMEMSET(&SnifferStats, 0, sizeof(SSLStats));
    UNLOCK_STAT();
    return 0;
}

#endif /* WOLFSSL_SNIFFER_STATS */


#ifdef WOLFSSL_SNIFFER_WATCH

int ssl_SetWatchKeyCallback_ex(SSLWatchCb cb, int devId, char* error)
{
    (void)devId;
    WatchCb = cb;
    return CreateWatchSnifferServer(error);
}


int ssl_SetWatchKeyCallback(SSLWatchCb cb, char* error)
{
    WatchCb = cb;
    return CreateWatchSnifferServer(error);
}


int ssl_SetWatchKeyCtx(void* ctx, char* error)
{
    (void)error;
    WatchCbCtx = ctx;
    return 0;
}


int ssl_SetWatchKey_buffer(void* vSniffer, const byte* key, word32 keySz,
        int keyType, char* error)
{
    SnifferSession* sniffer;
    int ret;

    if (vSniffer == NULL) {
        return -1;
    }
    if (key == NULL || keySz == 0) {
        return -1;
    }

    sniffer = (SnifferSession*)vSniffer;
    /* Remap the keyType from what the user can use to
     * what wolfSSL_use_PrivateKey_buffer expects. */
    keyType = (keyType == FILETYPE_PEM) ? WOLFSSL_FILETYPE_PEM :
                                          WOLFSSL_FILETYPE_ASN1;

    ret = wolfSSL_use_PrivateKey_buffer(sniffer->sslServer,
            key, keySz, keyType);
    if (ret != WOLFSSL_SUCCESS) {
        SetError(KEY_FILE_STR, error, sniffer, FATAL_ERROR_STATE);
        return -1;
    }

    return 0;
}


int ssl_SetWatchKey_file(void* vSniffer, const char* keyFile, int keyType,
        const char* password, char* error)
{
    byte* keyBuf = NULL;
    word32 keyBufSz = 0;
    int ret;

    if (vSniffer == NULL) {
        return -1;
    }
    if (keyFile == NULL) {
        return -1;
    }

    /* Remap the keyType from what the user can use to
     * what LoadKeyFile expects. */
    keyType = (keyType == FILETYPE_PEM) ? WOLFSSL_FILETYPE_PEM :
                                          WOLFSSL_FILETYPE_ASN1;

    ret = LoadKeyFile(&keyBuf, &keyBufSz, keyFile, 0, keyType, password);
    if (ret < 0) {
        SetError(KEY_FILE_STR, error, NULL, 0);
        XFREE(keyBuf, NULL, DYNAMIC_TYPE_X509);
        return -1;
    }

    ret = ssl_SetWatchKey_buffer(vSniffer, keyBuf, keyBufSz, FILETYPE_DER,
            error);
    XFREE(keyBuf, NULL, DYNAMIC_TYPE_X509);

    return ret;
}

#endif /* WOLFSSL_SNIFFER_WATCH */


#ifdef WOLFSSL_SNIFFER_STORE_DATA_CB

int ssl_SetStoreDataCallback(SSLStoreDataCb cb)
{
    StoreDataCb = cb;
    return 0;
}

#endif /* WOLFSSL_SNIFFER_STORE_DATA_CB */

#endif /* WOLFSSL_SNIFFER */
#endif /* WOLFCRYPT_ONLY */
