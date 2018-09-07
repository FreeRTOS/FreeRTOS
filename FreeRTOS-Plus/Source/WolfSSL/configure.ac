# configure.ac
#
# Copyright (C) 2006-2015 wolfSSL Inc.
#
# This file is part of wolfSSL. (formerly known as CyaSSL)
#
#

AC_INIT([wolfssl],[3.6.0],[https://github.com/wolfssl/wolfssl/issues],[wolfssl],[http://www.wolfssl.com])

AC_CONFIG_AUX_DIR([build-aux])

AC_CANONICAL_HOST
AC_CANONICAL_BUILD

AM_INIT_AUTOMAKE([1.11 -Wall -Werror -Wno-portability foreign tar-ustar subdir-objects no-define color-tests])
AC_PREREQ([2.63])

AC_ARG_PROGRAM
AC_DEFUN([PROTECT_AC_USE_SYSTEM_EXTENSIONS],
         [AX_SAVE_FLAGS
          AC_LANG_PUSH([C])
          AC_USE_SYSTEM_EXTENSIONS
          AC_LANG_POP([C])
          AX_RESTORE_FLAGS
          ])
#PROTECT_AC_USE_SYSTEM_EXTENSIONS

AC_CONFIG_MACRO_DIR([m4])

AC_CONFIG_HEADERS([config.h:config.in])dnl Keep filename to 8.3 for MS-DOS.

#shared library versioning
WOLFSSL_LIBRARY_VERSION=0:2:0
#                       | | |
#                +------+ | +---+
#                |        |     |
#               current:revision:age
#                |        |     |
#                |        |     +- increment if interfaces have been added
#                |        |        set to zero if interfaces have been removed
#                |        |        or changed
#                |        +- increment if source code has changed
#                |           set to zero if current is incremented
#                +- increment if interfaces have been added, removed or changed
AC_SUBST([WOLFSSL_LIBRARY_VERSION])

# capture user C_EXTRA_FLAGS from ./configure line, CFLAGS may hold -g -O2 even
# if user doesn't override, no way to tell
USER_C_EXTRA_FLAGS="$C_EXTRA_FLAGS"

LT_PREREQ([2.2])
LT_INIT([disable-static],[win32-dll])
LT_LANG([C++])
LT_LANG([C])

gl_VISIBILITY
AS_IF([ test -n "$CFLAG_VISIBILITY" ], [
       AM_CPPFLAGS="$AM_CPPFLAGS $CFLAG_VISIBILITY"
       CPPFLAGS="$CPPFLAGS $CFLAG_VISIBILITY"
       ])

m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

AC_CHECK_FUNCS([gethostbyname])
AC_CHECK_FUNCS([getaddrinfo])
AC_CHECK_FUNCS([gettimeofday])
AC_CHECK_FUNCS([inet_ntoa])
AC_CHECK_FUNCS([memset])
AC_CHECK_FUNCS([socket])
AC_CHECK_HEADERS([arpa/inet.h])
AC_CHECK_HEADERS([fcntl.h])
AC_CHECK_HEADERS([limits.h])
AC_CHECK_HEADERS([netdb.h])
AC_CHECK_HEADERS([netinet/in.h])
AC_CHECK_HEADERS([stddef.h])
AC_CHECK_HEADERS([sys/ioctl.h])
AC_CHECK_HEADERS([sys/socket.h])
AC_CHECK_HEADERS([sys/time.h])
AC_CHECK_HEADERS([errno.h])
AC_CHECK_LIB(network,socket)
AC_CHECK_SIZEOF(long long, 8)
AC_CHECK_SIZEOF(long, 4)
AC_CHECK_TYPES(__uint128_t)
AC_C_BIGENDIAN
# mktime check takes forever on some systems, if time supported it would be
# highly unusual for mktime to be missing
#AC_FUNC_MKTIME 

AC_PROG_CC
AC_PROG_CC_C_O
AC_PROG_CXX
AC_PROG_INSTALL
AC_TYPE_SIZE_T
AC_TYPE_UINT8_T
AM_PROG_AS
AM_PROG_CC_C_O
LT_LIB_M

OPTIMIZE_CFLAGS="-Os -fomit-frame-pointer"
OPTIMIZE_FAST_CFLAGS="-O2 -fomit-frame-pointer"
OPTIMIZE_HUGE_CFLAGS="-funroll-loops -DTFM_SMALL_SET -DTFM_HUGE_SET"
DEBUG_CFLAGS="-g -DDEBUG -DDEBUG_WOLFSSL"

thread_ls_on=no
# Thread local storage
AX_TLS([
        [AM_CFLAGS="$AM_CFLAGS -DHAVE_THREAD_LS"]
        [thread_ls_on=yes]
       ] , [:])


# DEBUG
AX_DEBUG
AS_IF([test "$ax_enable_debug" = "yes"],
      [AM_CFLAGS="$DEBUG_CFLAGS $AM_CFLAGS"],
      [AM_CFLAGS="$AM_CFLAGS -DNDEBUG"])


# SINGLE THREADED
AC_ARG_ENABLE([singlethreaded],
    [  --enable-singlethreaded Enable wolfSSL single threaded (default: disabled)],
    [ ENABLED_SINGLETHREADED=$enableval ],
    [ ENABLED_SINGLETHREADED=no ])

AS_IF([ test "x$ENABLED_SINGLETHREADED" = "xno" ],[
       AX_PTHREAD([
                   AC_DEFINE([HAVE_PTHREAD], [1], [Define if you have POSIX threads libraries and header files.])
                   AM_CFLAGS="-D_POSIX_THREADS $AM_CFLAGS $PTHREAD_CFLAGS"
                   LIBS="$LIBS $PTHREAD_LIBS"
                   ],[
                      ENABLED_SINGLETHREADED=yes
                      ])
       ])

AS_IF([ test "x$ENABLED_SINGLETHREADED" = "xyes" ],[ AM_CFLAGS="-DSINGLE_THREADED $AM_CFLAGS" ])


# DTLS
AC_ARG_ENABLE([dtls],
    [  --enable-dtls           Enable wolfSSL DTLS (default: disabled)],
    [ ENABLED_DTLS=$enableval ],
    [ ENABLED_DTLS=no ]
    )
if test "$ENABLED_DTLS" = "yes"
then
  AM_CFLAGS="-DWOLFSSL_DTLS $AM_CFLAGS"
fi


# OPENSSL Extra Compatibility
AC_ARG_ENABLE([opensslextra],
    [  --enable-opensslextra   Enable extra OpenSSL API, size+ (default: disabled)],
    [ ENABLED_OPENSSLEXTRA=$enableval ],
    [ ENABLED_OPENSSLEXTRA=no ]
    )
if test "$ENABLED_OPENSSLEXTRA" = "yes"
then
  AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
fi

if test "$ENABLED_OPENSSLEXTRA" = "yes" && test "$ENABLED_SMALL" = "yes"
then
    AC_MSG_ERROR([cannot enable small and opensslextra, only one or the other.])
fi


# High Strength Build
AC_ARG_ENABLE([maxstrength],
    [AS_HELP_STRING([--enable-maxstrength],[Enable Max Strengh build, allows TLSv1.2-AEAD-PFS ciphers only (default: disabled)])],
    [ENABLED_MAXSTRENGTH=$enableval],
    [ENABLED_MAXSTRENGTH=no])


# IPv6 Test Apps
AC_ARG_ENABLE([ipv6],
    [  --enable-ipv6           Enable testing of IPV6 (default: disabled)],
    [ ENABLED_IPV6=$enableval ],
    [ ENABLED_IPV6=no ]
    )

if test "$ENABLED_IPV6" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DTEST_IPV6"
fi

AM_CONDITIONAL([BUILD_IPV6], [test "x$ENABLED_IPV6" = "xyes"])


# Fortress build 
AC_ARG_ENABLE([fortress],
    [  --enable-fortress       Enable SSL fortress build (default: disabled)],
    [ ENABLED_FORTRESS=$enableval ],
    [ ENABLED_FORTRESS=no ]
    )

if test "$ENABLED_FORTRESS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DFORTRESS -DWOLFSSL_ALWAYS_VERIFY_CB -DOPENSSL_EXTRA -DWOLFSSL_DES_ECB -DWOLFSSL_AES_COUNTER -DWOLFSSL_AES_DIRECT -DWOLFSSL_DER_LOAD -DWOLFSSL_SHA512 -DWOLFSSL_SHA384 -DWOLFSSL_KEY_GEN"
fi


# ssl bump build 
AC_ARG_ENABLE([bump],
    [  --enable-bump           Enable SSL Bump build (default: disabled)],
    [ ENABLED_BUMP=$enableval ],
    [ ENABLED_BUMP=no ]
    )

if test "$ENABLED_BUMP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DLARGE_STATIC_BUFFERS -DWOLFSSL_CERT_GEN -DWOLFSSL_KEY_GEN -DHUGE_SESSION_CACHE -DOPENSSL_EXTRA -DFP_MAX_BITS=8192 -DWOLFSSL_DER_LOAD -DWOLFSSL_ALT_NAMES -DWOLFSSL_TEST_CERT"
fi

ENABLED_SLOWMATH="yes"

# lean psk build 
AC_ARG_ENABLE([leanpsk],
    [  --enable-leanpsk        Enable Lean PSK build (default: disabled)],
    [ ENABLED_LEANPSK=$enableval ],
    [ ENABLED_LEANPSK=no ]
    )

if test "$ENABLED_LEANPSK" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_LEANPSK -DHAVE_NULL_CIPHER -DSINGLE_THREADED -DNO_AES -DNO_FILESYSTEM -DNO_RABBIT -DNO_RSA -DNO_DSA -DNO_DH -DNO_CERTS -DNO_PWDBASED -DNO_DES3 -DNO_MD4 -DNO_MD5 -DNO_ERROR_STRINGS -DNO_OLD_TLS -DNO_RC4 -DNO_WRITEV -DNO_SESSION_CACHE -DNO_DEV_RANDOM -DWOLFSSL_USER_IO -DNO_SHA -DUSE_SLOW_SHA"
    ENABLED_SLOWMATH="no"
    ENABLED_SINGLETHREADED="yes"
fi

AM_CONDITIONAL([BUILD_LEANPSK], [test "x$ENABLED_LEANPSK" = "xyes"])


# big cache
AC_ARG_ENABLE([bigcache],
    [  --enable-bigcache       Enable big session cache (default: disabled)],
    [ ENABLED_BIGCACHE=$enableval ],
    [ ENABLED_BIGCACHE=no ]
    )

if test "$ENABLED_BIGCACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DBIG_SESSION_CACHE"
fi


# HUGE cache
AC_ARG_ENABLE([hugecache],
    [  --enable-hugecache      Enable huge session cache (default: disabled)],
    [ ENABLED_HUGECACHE=$enableval ],
    [ ENABLED_HUGECACHE=no ]
    )

if test "$ENABLED_HUGECACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHUGE_SESSION_CACHE"
fi


# SMALL cache
AC_ARG_ENABLE([smallcache],
    [  --enable-smallcache     Enable small session cache (default: disabled)],
    [ ENABLED_SMALLCACHE=$enableval ],
    [ ENABLED_SMALLCACHE=no ]
    )

if test "$ENABLED_SMALLCACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DSMALL_SESSION_CACHE"
fi


# Persistent session cache 
AC_ARG_ENABLE([savesession],
    [  --enable-savesession    Enable persistent session cache (default: disabled)],
    [ ENABLED_SAVESESSION=$enableval ],
    [ ENABLED_SAVESESSION=no ]
    )

if test "$ENABLED_SAVESESSION" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DPERSIST_SESSION_CACHE"
fi


# Persistent cert cache 
AC_ARG_ENABLE([savecert],
    [  --enable-savecert       Enable persistent cert cache (default: disabled)],
    [ ENABLED_SAVECERT=$enableval ],
    [ ENABLED_SAVECERT=no ]
    )

if test "$ENABLED_SAVECERT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DPERSIST_CERT_CACHE"
fi


# Atomic User Record Layer  
AC_ARG_ENABLE([atomicuser],
    [  --enable-atomicuser     Enable Atomic User Record Layer (default: disabled)],
    [ ENABLED_ATOMICUSER=$enableval ],
    [ ENABLED_ATOMICUSER=no ]
    )

if test "$ENABLED_ATOMICUSER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DATOMIC_USER"
fi


# Public Key Callbacks  
AC_ARG_ENABLE([pkcallbacks],
    [  --enable-pkcallbacks    Enable Public Key Callbacks (default: disabled)],
    [ ENABLED_PKCALLBACKS=$enableval ],
    [ ENABLED_PKCALLBACKS=no ]
    )

if test "$ENABLED_PKCALLBACKS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_PK_CALLBACKS"
fi


# SNIFFER
AC_ARG_ENABLE([sniffer],
   [AS_HELP_STRING([--enable-sniffer],[Enable wolfSSL sniffer support (default: disabled)])],
   [ ENABLED_SNIFFER=$enableval ],
   [ ENABLED_SNIFFER=no ]
   )

# sniffer does't work in maxstrength mode
if test "$ENABLED_SNIFFER" = "yes" && test "$ENABLED_MAXSTRENGTH" = "yes"
then
    AC_MSG_ERROR([cannot enable maxstrength in sniffer mode.])
fi

ENABLED_SNIFFTEST=no
AS_IF([ test "x$ENABLED_SNIFFER" = "xyes" ],
      [
          AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SNIFFER -DOPENSSL_EXTRA"
          AC_CHECK_HEADERS([pcap/pcap.h],
              [ ENABLED_SNIFFTEST=yes ],
              [ AC_MSG_WARN([cannot enable sniffer test without having libpcap available.]) ]
          )
      ])

AM_CONDITIONAL([BUILD_SNIFFER],   [ test "x$ENABLED_SNIFFER"   = "xyes" ])
AM_CONDITIONAL([BUILD_SNIFFTEST], [ test "x$ENABLED_SNIFFTEST" = "xyes" ])

# AES-GCM
AC_ARG_ENABLE([aesgcm],
    [AS_HELP_STRING([--enable-aesgcm],[Enable wolfSSL AES-GCM support (default: enabled)])],
    [ ENABLED_AESGCM=$enableval ],
    [ ENABLED_AESGCM=yes ]
    )

# lean psk does't need gcm
if test "$ENABLED_LEANPSK" = "yes"
then
    ENABLED_AESGCM=no
fi

if test "$ENABLED_AESGCM" = "word32"
then
    AM_CFLAGS="$AM_CFLAGS -DGCM_WORD32"
    ENABLED_AESGCM=yes
fi

if test "$ENABLED_AESGCM" = "small"
then
    AM_CFLAGS="$AM_CFLAGS -DGCM_SMALL"
    ENABLED_AESGCM=yes
fi

if test "$ENABLED_AESGCM" = "table"
then
    AM_CFLAGS="$AM_CFLAGS -DGCM_TABLE"
    ENABLED_AESGCM=yes
fi

if test "$ENABLED_AESGCM" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_AESGCM"
fi

AM_CONDITIONAL([BUILD_AESGCM], [test "x$ENABLED_AESGCM" = "xyes"])


# AES-CCM
AC_ARG_ENABLE([aesccm],
    [  --enable-aesccm         Enable wolfSSL AES-CCM support (default: disabled)],
    [ ENABLED_AESCCM=$enableval ],
    [ ENABLED_AESCCM=no ]
    )

if test "$ENABLED_AESCCM" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_AESCCM"
fi

AM_CONDITIONAL([BUILD_AESCCM], [test "x$ENABLED_AESCCM" = "xyes"])


# AES-NI
AC_ARG_ENABLE([aesni],
    [AS_HELP_STRING([--enable-aesni],[Enable wolfSSL AES-NI support (default: disabled)])],
    [ ENABLED_AESNI=$enableval ],
    [ ENABLED_AESNI=no ]
    )

# INTEL ASM
AC_ARG_ENABLE([intelasm],
    [AS_HELP_STRING([--enable-intelasm],[Enable All Intel ASM speedups (default: disabled)])],
    [ ENABLED_INTELASM=$enableval ],
    [ ENABLED_INTELASM=no ]
    )

if test "$ENABLED_AESNI" = "yes" || test "$ENABLED_INTELASM" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AESNI"
    if test "$GCC" = "yes"
    then
        # GCC needs these flags, icc doesn't
        # opt levels greater than 2 may cause problems on systems w/o aesni
        if test "$CC" != "icc"
        then
            AM_CFLAGS="$AM_CFLAGS -maes -msse4"
        fi
    fi
fi

if test "$ENABLED_INTELASM" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_INTEL_RDGEN -DUSE_INTEL_SPEEDUP"
    ENABLED_AESNI=yes
fi

AM_CONDITIONAL([BUILD_AESNI], [test "x$ENABLED_AESNI" = "xyes"])


# Camellia
AC_ARG_ENABLE([camellia],
    [  --enable-camellia       Enable wolfSSL Camellia support (default: disabled)],
    [ ENABLED_CAMELLIA=$enableval ],
    [ ENABLED_CAMELLIA=no ]
    )

if test "$ENABLED_CAMELLIA" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CAMELLIA"
fi

AM_CONDITIONAL([BUILD_CAMELLIA], [test "x$ENABLED_CAMELLIA" = "xyes"])


# MD2
AC_ARG_ENABLE([md2],
    [  --enable-md2            Enable wolfSSL MD2 support (default: disabled)],
    [ ENABLED_MD2=$enableval ],
    [ ENABLED_MD2=no ]
    )

if test "$ENABLED_BUMP" = "yes"
then
    ENABLED_MD2="yes"
fi

if test "$ENABLED_MD2" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_MD2"
fi

AM_CONDITIONAL([BUILD_MD2], [test "x$ENABLED_MD2" = "xyes"])


# NULL CIPHER 
AC_ARG_ENABLE([nullcipher],
    [  --enable-nullcipher     Enable wolfSSL NULL cipher support (default: disabled)],
    [ ENABLED_NULL_CIPHER=$enableval ],
    [ ENABLED_NULL_CIPHER=no ]
    )

if test "$ENABLED_NULL_CIPHER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_NULL_CIPHER"
fi

# RIPEMD
AC_ARG_ENABLE([ripemd],
    [  --enable-ripemd         Enable wolfSSL RIPEMD-160 support (default: disabled)],
    [ ENABLED_RIPEMD=$enableval ],
    [ ENABLED_RIPEMD=no ]
    )

if test "$ENABLED_RIPEMD" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_RIPEMD"
fi

AM_CONDITIONAL([BUILD_RIPEMD], [test "x$ENABLED_RIPEMD" = "xyes"])


# BLAKE2
AC_ARG_ENABLE([blake2],
    [  --enable-blake2         Enable wolfSSL BLAKE2 support (default: disabled)],
    [ ENABLED_BLAKE2=$enableval ],
    [ ENABLED_BLAKE2=no ]
    )

if test "$ENABLED_BLAKE2" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_BLAKE2"
fi

AM_CONDITIONAL([BUILD_BLAKE2], [test "x$ENABLED_BLAKE2" = "xyes"])


# set sha512 default
SHA512_DEFAULT=no
if test "$host_cpu" = "x86_64"
then
SHA512_DEFAULT=yes
fi

# SHA512
AC_ARG_ENABLE([sha512],
    [AS_HELP_STRING([--enable-sha512],[Enable wolfSSL SHA-512 support (default: enabled on x86_64)])],
    [ ENABLED_SHA512=$enableval ],
    [ ENABLED_SHA512=$SHA512_DEFAULT ]
    )

# lean psk does't need sha512
if test "$ENABLED_LEANPSK" = "yes"
then
    ENABLED_SHA512=no
fi

if test "$ENABLED_SHA512" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA512 -DWOLFSSL_SHA384"
fi

if test "$ENABLED_FORTRESS" = "yes"
then
    ENABLED_SHA512="yes"
fi


AM_CONDITIONAL([BUILD_SHA512], [test "x$ENABLED_SHA512" = "xyes"])


# SESSION CERTS
AC_ARG_ENABLE([sessioncerts],
    [  --enable-sessioncerts   Enable session cert storing (default: disabled)],
    [ ENABLED_SESSIONCERTS=$enableval ],
    [ ENABLED_SESSIONCERTS=no ]
    )

if test "$ENABLED_SESSIONCERTS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DSESSION_CERTS"
fi


# KEY GENERATION
AC_ARG_ENABLE([keygen],
    [  --enable-keygen         Enable key generation (default: disabled)],
    [ ENABLED_KEYGEN=$enableval ],
    [ ENABLED_KEYGEN=no ]
    )

if test "$ENABLED_KEYGEN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_KEY_GEN"
fi


# CERT GENERATION
AC_ARG_ENABLE([certgen],
    [  --enable-certgen        Enable cert generation (default: disabled)],
    [ ENABLED_CERTGEN=$enableval ],
    [ ENABLED_CERTGEN=no ]
    )

if test "$ENABLED_CERTGEN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN"
fi


# CERT REQUEST GENERATION
AC_ARG_ENABLE([certreq],
    [  --enable-certreq        Enable cert request generation (default: disabled)],
    [ ENABLED_CERTREQ=$enableval ],
    [ ENABLED_CERTREQ=no ]
    )

if test "$ENABLED_CERTREQ" = "yes"
then
    if test "$ENABLED_CERTGEN" = "no"
    then
        AC_MSG_ERROR([cannot enable certreq without enabling certgen.])
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_REQ"
fi


# SEP
AC_ARG_ENABLE([sep],
    [  --enable-sep            Enable sep extensions (default: disabled)],
    [ ENABLED_SEP=$enableval ],
    [ ENABLED_SEP=no ]
    )
if test "$ENABLED_SEP" = "yes"
then
  AM_CFLAGS="-DWOLFSSL_SEP -DKEEP_PEER_CERT $AM_CFLAGS"
fi


# HKDF 
AC_ARG_ENABLE([hkdf],
    [  --enable-hkdf           Enable HKDF (HMAC-KDF) support (default: disabled)],
    [ ENABLED_HKDF=$enableval ],
    [ ENABLED_HKDF=no ]
    )
if test "$ENABLED_HKDF" = "yes"
then
  AM_CFLAGS="$AM_CFLAGS -DHAVE_HKDF"
fi


# DSA
AC_ARG_ENABLE([dsa],
    [  --enable-dsa            Enable DSA (default: disabled)],
    [ ENABLED_DSA=$enableval ],
    [ ENABLED_DSA=no ]
    )

if test "$ENABLED_DSA" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_DSA"
fi

AM_CONDITIONAL([BUILD_DSA], [test "x$ENABLED_DSA" = "xyes"])


# set ecc default
ECC_DEFAULT=no

if test "$host_cpu" = "x86_64"
then
ECC_DEFAULT=yes
fi

# ECC
AC_ARG_ENABLE([ecc],
    [AS_HELP_STRING([--enable-ecc],[Enable ECC (default: enabled on x86_64)])],
    [ ENABLED_ECC=$enableval ],
    [ ENABLED_ECC=$ECC_DEFAULT ]
    )

# lean psk does't need ecc
if test "$ENABLED_LEANPSK" = "yes"
then
    ENABLED_ECC=no
fi

if test "$ENABLED_ECC" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC -DTFM_ECC256 -DECC_SHAMIR"
fi

AM_CONDITIONAL([BUILD_ECC], [test "x$ENABLED_ECC" = "xyes"])


if test "$ENABLED_ECC" = "yes" && test "$ENABLED_SMALL" = "yes"
then
    AC_MSG_ERROR([cannot enable ecc and small, ecc requires TLS which small turns off.])
fi


# for using memory optimization setting on both curve25519 and ed25519
ENABLED_CURVED25519_SMALL=no

# CURVE25519
AC_ARG_ENABLE([curve25519],
    [AS_HELP_STRING([--enable-curve25519],[Enable Curve25519 (default: disabled)])],
    [ ENABLED_CURVE25519=$enableval ],
    [ ENABLED_CURVE25519=no ]
    )


if test "$ENABLED_CURVE25519" = "small"
then
    AM_CFLAGS="$AM_CFLAGS -DCURVED25519_SMALL"
    ENABLED_CURVED25519_SMALL=yes
    ENABLED_CURVE25519=yes
fi

if test "$ENABLED_CURVE25519" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CURVE25519"
    ENABLED_FEMATH=yes
fi


AM_CONDITIONAL([BUILD_CURVE25519], [test "x$ENABLED_CURVE25519" = "xyes"])


# ED25519
AC_ARG_ENABLE([ed25519],
    [AS_HELP_STRING([--enable-ed25519],[Enable ED25519 (default: disabled)])],
    [ ENABLED_ED25519=$enableval ],
    [ ENABLED_ED25519=no ]
    )


if test "$ENABLED_ED25519" = "small"
then
    AM_CFLAGS="$AM_CFLAGS -DCURVED25519_SMALL"
    ENABLED_CURVED25519_SMALL=yes
    ENABLED_ED25519=yes
fi

if test "$ENABLED_ED25519" = "yes"
then
    if test "$ENABLED_SHA512" = "no"
    then
        AC_MSG_ERROR([cannot enable ed25519 without enabling sha512.])
    fi
    ENABLED_FEMATH=yes
    ENABLED_GEMATH=yes
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ED25519"
fi

AM_CONDITIONAL([BUILD_ED25519], [test "x$ENABLED_ED25519" = "xyes"])
AM_CONDITIONAL([BUILD_CURVED25519_SMALL], [test "x$ENABLED_CURVED25519_SMALL" = "xyes"])
AM_CONDITIONAL([BUILD_FEMATH],  [test "x$ENABLED_FEMATH" = "xyes"])
AM_CONDITIONAL([BUILD_GEMATH],  [test "x$ENABLED_GEMATH" = "xyes"])

# FP ECC, Fixed Point cache ECC
AC_ARG_ENABLE([fpecc],
    [  --enable-fpecc          Enable Fixed Point cache ECC (default: disabled)],
    [ ENABLED_FPECC=$enableval ],
    [ ENABLED_FPECC=no ]
    )

if test "$ENABLED_FPECC" = "yes"
then
    if test "$ENABLED_ECC" = "no"
    then
        AC_MSG_ERROR([cannot enable fpecc without enabling ecc.]) 
    fi
    AM_CFLAGS="$AM_CFLAGS -DFP_ECC"
fi


# ECC encrypt
AC_ARG_ENABLE([eccencrypt],
    [  --enable-eccencrypt     Enable ECC encrypt (default: disabled)],
    [ ENABLED_ECC_ENCRYPT=$enableval ],
    [ ENABLED_ECC_ENCRYPT=no ]
    )

if test "$ENABLED_ECC_ENCRYPT" = "yes"
then
    if test "$ENABLED_ECC" = "no"
    then
        AC_MSG_ERROR([cannot enable eccencrypt without enabling ecc.]) 
    fi
    if test "$ENABLED_HKDF" = "no"
    then
        AC_MSG_ERROR([cannot enable eccencrypt without enabling hkdf.]) 
    fi
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC_ENCRYPT"
fi


# PSK 
AC_ARG_ENABLE([psk],
    [  --enable-psk            Enable PSK (default: disabled)],
    [ ENABLED_PSK=$enableval ],
    [ ENABLED_PSK=no ]
    )

if test "$ENABLED_PSK" = "no" && test "$ENABLED_LEANPSK" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_PSK"
fi

if test "$ENABLED_PSK" = "no" && test "$ENABLED_LEANPSK" = "yes"
then
    ENABLED_PSK=yes
fi


# ERROR STRINGS
AC_ARG_ENABLE([errorstrings],
    [  --enable-errorstrings   Enable error strings table (default: enabled)],
    [ ENABLED_ERROR_STRINGS=$enableval ],
    [ ENABLED_ERROR_STRINGS=yes ]
    )

if test "$ENABLED_ERROR_STRINGS" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_ERROR_STRINGS"
else
    # turn off error strings if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_ERROR_STRINGS"
        ENABLED_ERROR_STRINGS=no
    fi
fi


# OLD TLS 
AC_ARG_ENABLE([oldtls],
    [  --enable-oldtls         Enable old TLS versions < 1.2 (default: enabled)],
    [ ENABLED_OLD_TLS=$enableval ],
    [ ENABLED_OLD_TLS=yes ]
    )

if test "$ENABLED_OLD_TLS" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_OLD_TLS"
else
    # turn off old if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_OLD_TLS"
        ENABLED_OLD_TLS=no
    fi
fi


# STACK SIZE info for examples 
AC_ARG_ENABLE([stacksize],
    [  --enable-stacksize      Enable stack size info on examples (default: disabled)],
    [ ENABLED_STACKSIZE=$enableval ],
    [ ENABLED_STACKSIZE=no ]
    )

if test "$ENABLED_STACKSIZE" = "yes"
then
    AC_CHECK_FUNC([posix_memalign], [], [AC_MSG_ERROR(stacksize needs posix_memalign)])
    AC_CHECK_FUNC([pthread_attr_setstack], [], AC_CHECK_LIB([pthread],[pthread_attr_setstack]))
    AM_CFLAGS="$AM_CFLAGS -DHAVE_STACK_SIZE -DWOLFSSL_LOW_MEMORY"
fi


# MEMORY 
AC_ARG_ENABLE([memory],
    [  --enable-memory         Enable memory callbacks (default: enabled)],
    [ ENABLED_MEMORY=$enableval ],
    [ ENABLED_MEMORY=yes ]
    )

if test "$ENABLED_MEMORY" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_WOLFSSL_MEMORY"
else
    # turn off memory cb if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        # but don't turn on NO_WOLFSSL_MEMORY because using own
        ENABLED_MEMORY=no
    fi
fi

AM_CONDITIONAL([BUILD_MEMORY], [test "x$ENABLED_MEMORY" = "xyes"])


# RSA 
AC_ARG_ENABLE([rsa],
    [  --enable-rsa            Enable RSA (default: enabled)],
    [ ENABLED_RSA=$enableval ],
    [ ENABLED_RSA=yes ]
    )

if test "$ENABLED_RSA" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_RSA"
else
    # turn off RSA if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_RSA"
        ENABLED_RSA=no
    fi
fi

AM_CONDITIONAL([BUILD_RSA], [test "x$ENABLED_RSA" = "xyes"])


# DH
AC_ARG_ENABLE([dh],
    [AS_HELP_STRING([--enable-dh],[Enable DH (default: enabled)])],
    [ ENABLED_DH=$enableval ],
    [ ENABLED_DH=yes ]
    )

if test "$ENABLED_DH" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_DH"
else
    # turn off DH if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_DH"
        ENABLED_DH=no
    fi
fi

AM_CONDITIONAL([BUILD_DH], [test "x$ENABLED_DH" = "xyes"])


# Anonymous
AC_ARG_ENABLE([anon],
    [AS_HELP_STRING([--enable-anon],[Enable Anonymous (default: disabled)])],
    [ ENABLED_ANON=$enableval ],
    [ ENABLED_ANON=no ]
    )


if test "x$ENABLED_ANON" = "xyes"
then
    if test "x$ENABLED_DH" != "xyes"
    then
        AC_MSG_ERROR([Anonymous suite requires DH.])
    fi
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ANON"
fi


# ASN
# turn off asn, which means no certs, no rsa, no dsa, no ecc,
# and no big int (unless dh is on)
AC_ARG_ENABLE([asn],
    [  --enable-asn            Enable ASN (default: enabled)],
    [ ENABLED_ASN=$enableval ],
    [ ENABLED_ASN=yes ]
    )

if test "$ENABLED_ASN" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_ASN -DNO_CERTS"
    if test "$ENABLED_DH" = "no"
    then
        # DH needs bigint
        AM_CFLAGS="$AM_CFLAGS -DNO_BIG_INT"
    fi
else
    # turn off ASN if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_ASN -DNO_CERTS -DNO_BIG_INT"
        ENABLED_ASN=no
    fi
fi

if test "$ENABLED_RSA" = "yes" && test "$ENABLED_ASN" = "no"
then
    AC_MSG_ERROR([please disable rsa if disabling asn.])
fi

if test "$ENABLED_DSA" = "yes" && test "$ENABLED_ASN" = "no"
then
    AC_MSG_ERROR([please disable dsa if disabling asn.])
fi

if test "$ENABLED_ECC" = "yes" && test "$ENABLED_ASN" = "no"
then
    AC_MSG_ERROR([please disable ecc if disabling asn.])
fi

if test "$ENABLED_PSK" = "no" && test "$ENABLED_ASN" = "no"
then
    AC_MSG_ERROR([please enable psk if disabling asn.])
fi

# DH needs bigint
if test "$ENABLED_ASN" = "no" && test "$ENABLED_DH" = "no"
then
    ENABLED_FASTMATH=no
    ENABLED_SLOWMATH=no
fi

AM_CONDITIONAL([BUILD_ASN], [test "x$ENABLED_ASN" = "xyes"])


# AES
AC_ARG_ENABLE([aes],
    [  --enable-aes            Enable AES (default: enabled)],
    [ ENABLED_AES=$enableval ],
    [ ENABLED_AES=yes ]
    )

if test "$ENABLED_AES" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_AES"
    if test "$ENABLED_AESGCM" = "yes"
    then
        AC_MSG_ERROR([AESGCM requires AES.])
    fi
    if test "$ENABLED_AESCCM" = "yes"
    then
        AC_MSG_ERROR([AESCCM requires AES.])
    fi
else
    # turn off AES if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_AES"
        ENABLED_AES=no
    fi
fi

AM_CONDITIONAL([BUILD_AES], [test "x$ENABLED_AES" = "xyes"])


# CODING
AC_ARG_ENABLE([coding],
    [  --enable-coding         Enable Coding base 16/64 (default: enabled)],
    [ ENABLED_CODING=$enableval ],
    [ ENABLED_CODING=yes ]
    )

if test "$ENABLED_CODING" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_CODING"
else
    # turn off CODING if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_CODING"
        ENABLED_CODING=no
    fi
fi

AM_CONDITIONAL([BUILD_CODING], [test "x$ENABLED_CODING" = "xyes"])


# DES3
AC_ARG_ENABLE([des3],
    [  --enable-des3           Enable DES3 (default: enabled)],
    [ ENABLED_DES3=$enableval ],
    [ ENABLED_DES3=yes ]
    )

if test "$ENABLED_DES3" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_DES3"
else
    # turn off DES3 if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_DES3"
        ENABLED_DES3=no
    fi
fi

AM_CONDITIONAL([BUILD_DES3], [test "x$ENABLED_DES3" = "xyes"])


# ARC4 
AC_ARG_ENABLE([arc4],
    [  --enable-arc4           Enable ARC4 (default: disabled)],
    [ ENABLED_ARC4=$enableval ],
    [ ENABLED_ARC4=no ]
    )

if test "$ENABLED_ARC4" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_RC4"
else
    # turn off ARC4 if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_RC4"
        ENABLED_ARC4=no
    fi
fi

AM_CONDITIONAL([BUILD_RC4], [test "x$ENABLED_ARC4" = "xyes"])


# MD5 
AC_ARG_ENABLE([md5],
    [  --enable-md5            Enable MD5 (default: enabled)],
    [ ENABLED_MD5=$enableval ],
    [ ENABLED_MD5=yes ]
    )

if test "$ENABLED_MD5" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_MD5 -DNO_OLD_TLS"
else
    # turn off MD5 if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_MD5 -DNO_OLD_TLS"
        ENABLED_MD5=no
    fi
fi

AM_CONDITIONAL([BUILD_MD5], [test "x$ENABLED_MD5" = "xyes"])


# SHA 
AC_ARG_ENABLE([sha],
    [  --enable-sha            Enable SHA (default: enabled)],
    [ ENABLED_SHA=$enableval ],
    [ ENABLED_SHA=yes ]
    )

if test "$ENABLED_SHA" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_SHA -DNO_OLD_TLS"
else
    # turn off SHA if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_SHA -DNO_OLD_TLS"
        ENABLED_SHA=no
    fi
fi

AM_CONDITIONAL([BUILD_SHA], [test "x$ENABLED_SHA" = "xyes"])


# MD4 
AC_ARG_ENABLE([md4],
    [  --enable-md4            Enable MD4 (default: disabled)],
    [ ENABLED_MD4=$enableval ],
    [ ENABLED_MD4=no ]
    )

if test "$ENABLED_MD4" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_MD4"
fi

AM_CONDITIONAL([BUILD_MD4], [test "x$ENABLED_MD4" = "xyes"])


# Web Server Build 
AC_ARG_ENABLE([webserver],
    [  --enable-webserver      Enable Web Server (default: disabled)],
    [ ENABLED_WEBSERVER=$enableval ],
    [ ENABLED_WEBSERVER=no ]
    )

if test "$ENABLED_WEBSERVER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_WEBSERVER"
fi



# HC128 
AC_ARG_ENABLE([hc128],
    [  --enable-hc128          Enable HC-128 (default: disabled)],
    [ ENABLED_HC128=$enableval ],
    [ ENABLED_HC128=no ]
    )

if test "$ENABLED_HC128" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_HC128"
else
    AM_CFLAGS="$AM_CFLAGS -DHAVE_HC128"
fi

AM_CONDITIONAL([BUILD_HC128], [test "x$ENABLED_HC128" = "xyes"])


# RABBIT
AC_ARG_ENABLE([rabbit],
    [  --enable-rabbit         Enable RABBIT (default: disabled)],
    [ ENABLED_RABBIT=$enableval ],
    [ ENABLED_RABBIT=no ]
    )

if test "$ENABLED_RABBIT" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_RABBIT"
else
    AM_CFLAGS="$AM_CFLAGS -DHAVE_RABBIT"
fi

AM_CONDITIONAL([BUILD_RABBIT], [test "x$ENABLED_RABBIT" = "xyes"])


# FIPS
AC_ARG_ENABLE([fips],
    [AS_HELP_STRING([--enable-fips],[Enable FIPS 140-2, Will NOT work w/o FIPS license (default: disabled)])],
    [ ENABLED_FIPS=$enableval ],
    [ ENABLED_FIPS=no ]
    )

if test "x$ENABLED_FIPS" = "xyes"
then
    # requires thread local storage
    if test "$thread_ls_on" = "no"
    then
        AC_MSG_ERROR([FIPS requires Thread Local Storage])
    fi
    # requires SHA512
    if test "x$ENABLED_SHA512" = "xno"
    then
        ENABLED_SHA512="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA512 -DWOLFSSL_SHA384"
        AM_CONDITIONAL([BUILD_SHA512], [test "x$ENABLED_SHA512" = "xyes"])
    fi
    # requires AESGCM
    if test "x$ENABLED_AESGCM" != "xyes"
    then
        ENABLED_AESGCM="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_AESGCM"
        AM_CONDITIONAL([BUILD_SHA512], [test "x$ENABLED_SHA512" = "xyes"])
    fi
    AM_CFLAGS="$AM_CFLAGS -DHAVE_FIPS"
fi

AM_CONDITIONAL([BUILD_FIPS], [test "x$ENABLED_FIPS" = "xyes"])


# set POLY1305 default
POLY1305_DEFAULT=yes

if test "x$ENABLED_FIPS" = "xyes"
then
POLY1305_DEFAULT=no
fi

# POLY1305
AC_ARG_ENABLE([poly1305],
    [AS_HELP_STRING([--enable-poly1305],[Enable wolfSSL POLY1305 support (default: enabled)])],
    [ ENABLED_POLY1305=$enableval ],
    [ ENABLED_POLY1305=$POLY1305_DEFAULT]
    )

# lean psk does't need poly1305
if test "$ENABLED_LEANPSK" = "yes"
then
    ENABLED_POLY1305=no
fi

if test "$ENABLED_POLY1305" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_POLY1305 -DHAVE_ONE_TIME_AUTH"
fi

AM_CONDITIONAL([BUILD_POLY1305], [test "x$ENABLED_POLY1305" = "xyes"])


# set CHACHA default
CHACHA_DEFAULT=yes

if test "x$ENABLED_FIPS" = "xyes"
then
CHACHA_DEFAULT=no
fi

# CHACHA
AC_ARG_ENABLE([chacha],
    [  --enable-chacha         Enable CHACHA (default: enabled)],
    [ ENABLED_CHACHA=$enableval ],
    [ ENABLED_CHACHA=$CHACHA_DEFAULT]
    )

# lean psk does't need chacha
if test "$ENABLED_LEANPSK" = "yes"
then
    ENABLED_CHACHA=no
fi

if test "$ENABLED_CHACHA" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CHACHA"
fi

AM_CONDITIONAL([BUILD_CHACHA], [test "x$ENABLED_CHACHA" = "xyes"])


# Hash DRBG
AC_ARG_ENABLE([hashdrbg],
    [  --enable-hashdrbg       Enable Hash DRBG support (default: enabled)],
    [ ENABLED_HASHDRBG=$enableval ],
    [ ENABLED_HASHDRBG=yes ]
    )

if test "x$ENABLED_HASHDRBG" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_HASHDRBG"
else
    # turn on Hash DRBG if FIPS is on or ARC4 is off
    if test "x$ENABLED_FIPS" = "xyes" || test "x$ENABLED_ARC4" = "xno"
    then
        AM_CFLAGS="$AM_CFLAGS -DHAVE_HASHDRBG"
        ENABLED_HASHDRBG=yes
    fi
fi


# Filesystem Build 
AC_ARG_ENABLE([filesystem],
    [  --enable-filesystem     Enable Filesystem support (default: enabled)],
    [ ENABLED_FILESYSTEM=$enableval ],
    [ ENABLED_FILESYSTEM=yes ]
    )

if test "$ENABLED_FILESYSTEM" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_FILESYSTEM"
else
    # turn off filesystem if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_FILESYSTEM"
        ENABLED_FILESYSTEM=no
    fi
fi


# inline Build 
AC_ARG_ENABLE([inline],
    [  --enable-inline         Enable inline functions (default: enabled)],
    [ ENABLED_INLINE=$enableval ],
    [ ENABLED_INLINE=yes ]
    )

if test "$ENABLED_INLINE" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_INLINE"
fi

AM_CONDITIONAL([BUILD_INLINE], [test "x$ENABLED_INLINE" = "xyes"])


# OCSP
AC_ARG_ENABLE([ocsp],
    [  --enable-ocsp           Enable OCSP (default: disabled)],
    [ ENABLED_OCSP=$enableval ],
    [ ENABLED_OCSP=no ],
    )

if test "$ENABLED_OCSP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
fi

AM_CONDITIONAL([BUILD_OCSP], [test "x$ENABLED_OCSP" = "xyes"])


if test "$ENABLED_OCSP" = "yes"
then
    # check openssl command tool for testing ocsp
    AC_CHECK_PROG([HAVE_OPENSSL_CMD],[openssl],[yes],[no])

    if test "$HAVE_OPENSSL_CMD" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OPENSSL_CMD"
    else
        AC_MSG_WARN([openssl command line tool not available for testing ocsp])
    fi
fi


# CRL 
AC_ARG_ENABLE([crl],
    [  --enable-crl            Enable CRL (default: disabled)],
    [ ENABLED_CRL=$enableval ],
    [ ENABLED_CRL=no ],
    )

if test "$ENABLED_CRL" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL"
fi

AM_CONDITIONAL([BUILD_CRL], [test "x$ENABLED_CRL" = "xyes"])


# CRL Monitor
AC_ARG_ENABLE([crl-monitor],
    [  --enable-crl-monitor    Enable CRL Monitor (default: disabled)],
    [ ENABLED_CRL_MONITOR=$enableval ],
    [ ENABLED_CRL_MONITOR=no ],
    )

if test "$ENABLED_CRL_MONITOR" = "yes"
then
    case $host_os in
    *linux* | *darwin* | *freebsd*)
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL_MONITOR" ;;
    *)
        AC_MSG_ERROR([crl monitor only allowed on linux, OS X, or freebsd]) ;;
    esac
fi

AM_CONDITIONAL([BUILD_CRL_MONITOR], [test "x$ENABLED_CRL_MONITOR" = "xyes"])


# NTRU
ENABLED_NTRU="no"
tryntrudir=""
AC_ARG_WITH([ntru],
    [  --with-ntru=PATH        Path to NTRU install (default /usr/) ],
    [
        AC_MSG_CHECKING([for NTRU])
        CPPFLAGS="$CPPFLAGS -DHAVE_NTRU"
        LIBS="$LIBS -lNTRUEncrypt"

        AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <ntru_crypto_drbg.h>]], [[ ntru_crypto_drbg_instantiate(0, 0, 0, 0, 0); ]])], [ ntru_linked=yes ],[ ntru_linked=no ])

        if test "x$ntru_linked" == "xno" ; then
            if test "x$withval" != "xno" ; then
                tryntrudir=$withval
            fi
            if test "x$withval" == "xyes" ; then
                tryntrudir="/usr"
            fi

            LDFLAGS="$AM_LDFLAGS -L$tryntrudir/lib"
            CPPFLAGS="$CPPFLAGS -I$tryntrudir/include"

            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <ntru_crypto_drbg.h>]], [[ ntru_crypto_drbg_instantiate(0, 0, 0, 0, 0); ]])], [ ntru_linked=yes ],[ ntru_linked=no ])

            if test "x$ntru_linked" == "xno" ; then
                AC_MSG_ERROR([NTRU isn't found.
                If it's already installed, specify its path using --with-ntru=/dir/])
            fi
            AC_MSG_RESULT([yes])
            AM_LDFLAGS="$AM_LDFLAGS -L$tryntrudir/lib"
        else
            AC_MSG_RESULT([yes])
        fi

        AM_CFLAGS="$AM_CFLAGS -DHAVE_NTRU"
        ENABLED_NTRU="yes"
    ]
)

AM_CONDITIONAL([BUILD_NTRU], [test "x$ENABLED_NTRU" = "xyes"])

if test "$ENABLED_NTRU" = "yes" && test "$ENABLED_SMALL" = "yes"
then
    AC_MSG_ERROR([cannot enable ntru and small, ntru requires TLS which small turns off.]) 
fi

# SNI
AC_ARG_ENABLE([sni],
    [  --enable-sni            Enable SNI (default: disabled)],
    [ ENABLED_SNI=$enableval ],
    [ ENABLED_SNI=no ]
    )

if test "x$ENABLED_SNI" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SNI"
fi

# Maximum Fragment Length
AC_ARG_ENABLE([maxfragment],
    [  --enable-maxfragment    Enable Maximum Fragment Length (default: disabled)],
    [ ENABLED_MAX_FRAGMENT=$enableval ],
    [ ENABLED_MAX_FRAGMENT=no ]
    )

if test "x$ENABLED_MAX_FRAGMENT" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_MAX_FRAGMENT"
fi

# Truncated HMAC
AC_ARG_ENABLE([truncatedhmac],
    [  --enable-truncatedhmac  Enable Truncated HMAC (default: disabled)],
    [ ENABLED_TRUNCATED_HMAC=$enableval ],
    [ ENABLED_TRUNCATED_HMAC=no ]
    )

if test "x$ENABLED_TRUNCATED_HMAC" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_TRUNCATED_HMAC"
fi

# Renegotiation Indication - (FAKE Secure Renegotiation)
AC_ARG_ENABLE([renegotiation-indication],
    [AS_HELP_STRING([--enable-renegotiation-indication],[Enable Renegotiation Indication (default: disabled)])],
    [ ENABLED_RENEGOTIATION_INDICATION=$enableval ],
    [ ENABLED_RENEGOTIATION_INDICATION=no ]
    )

if test "x$ENABLED_RENEGOTIATION_INDICATION" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_RENEGOTIATION_INDICATION"
fi

# Secure Renegotiation
AC_ARG_ENABLE([secure-renegotiation],
    [AS_HELP_STRING([--enable-secure-renegotiation],[Enable Secure Renegotiation (default: disabled)])],
    [ ENABLED_SECURE_RENEGOTIATION=$enableval ],
    [ ENABLED_SECURE_RENEGOTIATION=no ]
    )

if test "x$ENABLED_SECURE_RENEGOTIATION" = "xyes"
then
    if test "x$ENABLED_RENEGOTIATION_INDICATION" = "xyes"
    then
        AC_MSG_ERROR([cannot enable renegotiation-indication and secure-renegotiation.])
    fi
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SECURE_RENEGOTIATION"
fi

# Supported Elliptic Curves Extensions
AC_ARG_ENABLE([supportedcurves],
    [AS_HELP_STRING([--enable-supportedcurves],[Enable Supported Elliptic Curves (default: disabled)])],
    [ ENABLED_SUPPORTED_CURVES=$enableval ],
    [ ENABLED_SUPPORTED_CURVES=no ]
    )

if test "x$ENABLED_SUPPORTED_CURVES" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SUPPORTED_CURVES"
fi

# Session Ticket Extension
AC_ARG_ENABLE([session-ticket],
    [AS_HELP_STRING([--enable-session-ticket],[Enable Session Ticket (default: disabled)])],
    [ ENABLED_SESSION_TICKET=$enableval ],
    [ ENABLED_SESSION_TICKET=no ]
    )

if test "x$ENABLED_SESSION_TICKET" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SESSION_TICKET"
fi

# TLS Extensions
AC_ARG_ENABLE([tlsx],
    [  --enable-tlsx           Enable all TLS Extensions (default: disabled)],
    [ ENABLED_TLSX=$enableval ],
    [ ENABLED_TLSX=no ]
    )

if test "x$ENABLED_TLSX" = "xyes"
then
	ENABLED_SNI=yes
	ENABLED_MAX_FRAGMENT=yes
	ENABLED_TRUNCATED_HMAC=yes
	ENABLED_SUPPORTED_CURVES=yes
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SNI -DHAVE_MAX_FRAGMENT -DHAVE_TRUNCATED_HMAC -DHAVE_SUPPORTED_CURVES"
fi

# PKCS7
AC_ARG_ENABLE([pkcs7],
    [  --enable-pkcs7          Enable PKCS7 (default: disabled)],
    [ ENABLED_PKCS7=$enableval ],
    [ ENABLED_PKCS7=no ],
    )

if test "$ENABLED_PKCS7" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_PKCS7"
fi

AM_CONDITIONAL([BUILD_PKCS7], [test "x$ENABLED_PKCS7" = "xyes"])


# Simple Certificate Enrollment Protocol (SCEP)
AC_ARG_ENABLE([scep],
    [  --enable-scep           Enable wolfSCEP (default: disabled)],
    [ ENABLED_WOLFSCEP=$enableval ],
    [ ENABLED_WOLFSCEP=no ]
    )
if test "$ENABLED_WOLFSCEP" = "yes"
then
    # Enable prereqs if not already enabled
    if test "x$ENABLED_KEYGEN" = "xno"
    then
        ENABLED_KEYGEN="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_KEY_GEN"
    fi
    if test "x$ENABLED_CERTGEN" = "xno"
    then
        ENABLED_CERTGEN="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN"
    fi
    if test "x$ENABLED_CERTREQ" = "xno"
    then
        ENABLED_CERTREQ="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_REQ"
    fi
    if test "x$ENABLED_PKCS7" = "xno"
    then
        ENABLED_PKCS7="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_PKCS7"
        AM_CONDITIONAL([BUILD_PKCS7], [test "x$ENABLED_PKCS7" = "xyes"])
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAVE_WOLFSCEP"
fi


# Small Stack
AC_ARG_ENABLE([smallstack],
    [  --enable-smallstack     Enable Small Stack Usage (default: disabled)],
    [ ENABLED_SMALL_STACK=$enableval ],
    [ ENABLED_SMALL_STACK=no ]
    )

if test "x$ENABLED_SMALL_STACK" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SMALL_STACK"
fi


#valgrind
AC_ARG_ENABLE([valgrind],
    [  --enable-valgrind       Enable valgrind for unit tests (default: disabled)],
    [ ENABLED_VALGRIND=$enableval ],
    [ ENABLED_VALGRIND=no ]
    )

if test "$ENABLED_VALGRIND" = "yes"
then
    AC_CHECK_PROG([HAVE_VALGRIND],[valgrind],[yes],[no])

    if test "$HAVE_VALGRIND" = "no"
    then
        AC_MSG_ERROR([Valgrind not found.])
    fi
    enable_shared=no
    enable_static=yes
    AM_CFLAGS="$AM_CFLAGS -DHAVE_VALGRIND"
fi

AM_CONDITIONAL([USE_VALGRIND], [test "x$ENABLED_VALGRIND" = "xyes"])


# Test certs, use internal cert functions for extra testing 
AC_ARG_ENABLE([testcert],
    [  --enable-testcert       Enable Test Cert (default: disabled)],
    [ ENABLED_TESTCERT=$enableval ],
    [ ENABLED_TESTCERT=no ]
    )

if test "$ENABLED_TESTCERT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_TEST_CERT"
fi


# I/O Pool, an example to show user how to override memory handler and use
# a pool for the input/output buffer requests
AC_ARG_ENABLE([iopool],
    [  --enable-iopool         Enable I/O Pool example (default: disabled)],
    [ ENABLED_IOPOOL=$enableval ],
    [ ENABLED_IOPOOL=no ]
    )

if test "$ENABLED_IOPOOL" = "yes"
then
    if test "$thread_ls_on" = "no"
    then
        AC_MSG_ERROR([I/O Pool example requires Thread Local Storage])
    fi
    AM_CFLAGS="$AM_CFLAGS -DHAVE_IO_POOL -DXMALLOC_USER"
fi


# Certificate Service Support 
AC_ARG_ENABLE([certservice],
    [  --enable-certservice    Enable cert service (default: disabled)],
    [ ENABLED_CERT_SERVICE=$enableval ],
    [ ENABLED_CERT_SERVICE=no ]
    )
if test "$ENABLED_CERT_SERVICE" = "yes"
then
    # Requires ecc,certgen, and opensslextra make sure on
    if test "x$ENABLED_CERTGEN" = "xno"
    then
        ENABLED_CERTGEN="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN"
    fi
    if test "x$ENABLED_ECC" = "xno"
    then
        ENABLED_ECC="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC -DTFM_ECC256 -DECC_SHAMIR"
        AM_CONDITIONAL([BUILD_ECC], [test "x$ENABLED_ECC" = "xyes"])
    fi
    if test "x$ENABLED_OPENSSLEXTRA" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAVE_CERT_SERVICE"
fi


# PWDBASED has to come after certservice since we want it on w/o explicit on
# PWDBASED
AC_ARG_ENABLE([pwdbased],
    [  --enable-pwdbased       Enable PWDBASED (default: disabled)],
    [ ENABLED_PWDBASED=$enableval ],
    [ ENABLED_PWDBASED=no ]
    )

if test "$ENABLED_PWDBASED" = "no"
then
    if test "$ENABLED_OPENSSLEXTRA" = "yes" || test "$ENABLED_WEBSERVER" = "yes"
    then
        # opensslextra and webserver needs pwdbased
        ENABLED_PWDBASED=yes
    else
        AM_CFLAGS="$AM_CFLAGS -DNO_PWDBASED"
    fi
fi

AM_CONDITIONAL([BUILD_PWDBASED], [test "x$ENABLED_PWDBASED" = "xyes"])


# set fastmath default
FASTMATH_DEFAULT=no

if test "$host_cpu" = "x86_64"
then
FASTMATH_DEFAULT=yes
fi

# fastmath
AC_ARG_ENABLE([fastmath],
    [  --enable-fastmath       Enable fast math ops (default: enabled on x86_64)],
    [ ENABLED_FASTMATH=$enableval ],
    [ ENABLED_FASTMATH=$FASTMATH_DEFAULT]
    )

if test "x$ENABLED_FASTMATH" = "xyes"
then
    # turn off fastmth if leanpsk on or asn off (w/o dh)
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_ASN" = "no"
    then
        if test "$ENABLED_DH" = "no"
        then
            ENABLED_FASTMATH=no
        else
            AM_CFLAGS="$AM_CFLAGS -DUSE_FAST_MATH"
            ENABLED_SLOWMATH="no"
        fi
    else
        AM_CFLAGS="$AM_CFLAGS -DUSE_FAST_MATH"
        ENABLED_SLOWMATH="no"
    fi
    if test "$host_cpu" = "x86_64"
    then
        # Have settings.h set FP_MAX_BITS higher if user didn't set directly
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_X86_64_BUILD"
    fi
fi


# fast HUGE math
AC_ARG_ENABLE([fasthugemath],
    [  --enable-fasthugemath   Enable fast math + huge code (default: disabled)],
    [ ENABLED_FASTHUGEMATH=$enableval ],
    [ ENABLED_FASTHUGEMATH=no ]
    )

if test "$ENABLED_BUMP" = "yes"
then
    ENABLED_FASTHUGEMATH="yes"
fi

if test "$ENABLED_FASTHUGEMATH" = "yes"
then
    ENABLED_FASTMATH="yes"
    AM_CFLAGS="$AM_CFLAGS -DUSE_FAST_MATH"
    ENABLED_SLOWMATH="no"
fi

AM_CONDITIONAL([BUILD_FASTMATH], [test "x$ENABLED_FASTMATH" = "xyes"])
AM_CONDITIONAL([BUILD_SLOWMATH], [test "x$ENABLED_SLOWMATH" = "xyes"])


# Enable Examples, used to disable examples
AC_ARG_ENABLE([examples],
    [  --enable-examples       Enable Examples  (default: enabled)],
    [ ENABLED_EXAMPLES=$enableval ],
    [ ENABLED_EXAMPLES=yes ]
    )

AS_IF([test "x$ENABLED_FILESYSTEM" = "xno"], [ENABLED_EXAMPLES="no"])
AS_IF([test "x$ENABLED_INLINE" = "xno"], [ENABLED_EXAMPLES="no"])
AM_CONDITIONAL([BUILD_EXAMPLES], [test "x$ENABLED_EXAMPLES" = "xyes"])


# LIBZ
ENABLED_LIBZ="no"
trylibzdir=""
AC_ARG_WITH([libz],
    [  --with-libz=PATH        PATH to libz install (default /usr/) ],
    [
        AC_MSG_CHECKING([for libz])
        CPPFLAGS="$CPPFLAGS -DHAVE_LIBZ"
        LIBS="$LIBS -lz"

        AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <zlib.h>]], [[ deflateInit(0, 8); ]])],[ libz_linked=yes ],[ libz_linked=no ])

        if test "x$libz_linked" == "xno" ; then
            if test "x$withval" != "xno" ; then
                trylibzdir=$withval
            fi
            if test "x$withval" == "xyes" ; then
                trylibzdir="/usr"
            fi

            AM_LDFLAGS="$AM_LDFLAGS -L$trylibzdir/lib"
            CPPFLAGS="$CPPFLAGS -I$trylibzdir/include"

            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <zlib.h>]], [[ deflateInit(0, 8); ]])],[ libz_linked=yes ],[ libz_linked=no ])

            if test "x$libz_linked" == "xno" ; then
                AC_MSG_ERROR([libz isn't found.
                If it's already installed, specify its path using --with-libz=/dir/])
            fi
            AC_MSG_RESULT([yes])
        else
            AC_MSG_RESULT([yes])
        fi
        ENABLED_LIBZ="yes"
    ]
)
AM_CONDITIONAL([BUILD_LIBZ], [test "x$ENABLED_LIBZ" = "xyes"])


# cavium 
trycaviumdir=""
AC_ARG_WITH([cavium],
    [  --with-cavium=PATH      PATH to cavium/software dir ],
    [
        AC_MSG_CHECKING([for cavium])
        CPPFLAGS="$CPPFLAGS -DHAVE_CAVIUM"

            if test "x$withval" == "xyes" ; then
                AC_MSG_ERROR([need a PATH for --with-cavium])
            fi
            if test "x$withval" != "xno" ; then
                trycaviumdir=$withval
            fi

            LDFLAGS="$AM_LDFLAGS $trycaviumdir/api/cavium_common.o"
            CPPFLAGS="$CPPFLAGS -I$trycaviumdir/include"

            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include "cavium_common.h"]], [[ CspShutdown(CAVIUM_DEV_ID); ]])],[ cavium_linked=yes ],[ cavium_linked=no ])

            if test "x$cavium_linked" == "xno" ; then
                AC_MSG_ERROR([cavium isn't found.
                If it's already installed, specify its path using --with-cavium=/dir/])
            fi
            AC_MSG_RESULT([yes])
            enable_shared=no
            enable_static=yes
    ]
)


# microchip api
AC_ARG_ENABLE([mcapi],
    [  --enable-mcapi          Enable Microchip API (default: disabled)],
    [ ENABLED_MCAPI=$enableval ],
    [ ENABLED_MCAPI=no ]
    )

if test "$ENABLED_MCAPI" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_MCAPI -DWOLFSSL_AES_COUNTER -DWOLFSSL_AES_DIRECT"
fi

if test "$ENABLED_MCAPI" = "yes" && test "$ENABLED_SHA512" = "no"
then
    AC_MSG_ERROR([please enable sha512 if enabling mcapi.])
fi

if test "$ENABLED_MCAPI" = "yes" && test "$ENABLED_ECC" = "no"
then
    AC_MSG_ERROR([please enable ecc if enabling mcapi.])
fi

if test "$ENABLED_MCAPI" = "yes" && test "$ENABLED_LIBZ" = "no"
then
    AC_MSG_ERROR([please use --with-libz if enabling mcapi.])
fi

AM_CONDITIONAL([BUILD_MCAPI], [test "x$ENABLED_MCAPI" = "xyes"])


# wolfSSL JNI
AC_ARG_ENABLE([jni],
    [  --enable-jni            Enable wolfSSL JNI (default: disabled)],
    [ ENABLED_JNI=$enableval ],
    [ ENABLED_JNI=no ]
    )
if test "$ENABLED_JNI" = "yes"
then
    # Enable prereqs if not already enabled
    if test "x$ENABLED_DTLS" = "xno"
    then
        ENABLED_DTLS="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DTLS"
    fi
    if test "x$ENABLED_OPENSSLEXTRA" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="$AM_CFLAGS -DOPENSSL_EXTRA"
    fi
    if test "x$ENABLED_CRL" = "xno"
    then
        ENABLED_CRL="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL"
        AM_CONDITIONAL([BUILD_CRL], [test "x$ENABLED_CRL" = "xyes"])
    fi
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
        AM_CONDITIONAL([BUILD_OCSP], [test "x$ENABLED_OCSP" = "xyes"])
    fi
    if test "x$ENABLED_CRL_MONITOR" = "xno"
    then
        ENABLED_CRL_MONITOR="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL_MONITOR"
    fi
    if test "x$ENABLED_SAVESESSION" = "xno"
    then
        ENABLED_SAVESESSION="yes"
        AM_CFLAGS="$AM_CFLAGS -DPERSIST_SESSION_CACHE"
    fi
    if test "x$ENABLED_SAVECERT" = "xno"
    then
        ENABLED_SAVECERT="yes"
        AM_CFLAGS="$AM_CFLAGS -DPERSIST_CERT_CACHE"
    fi
    if test "x$ENABLED_ATOMICUSER" = "xno"
    then
        ENABLED_ATOMICUSER="yes"
        AM_CFLAGS="$AM_CFLAGS -DATOMIC_USER"
    fi
    if test "x$ENABLED_ECC" = "xno"
    then
        ENABLED_ECC="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC"
    fi
    if test "x$ENABLED_PKCALLBACKS" = "xno"
    then
        ENABLED_PKCALLBACKS="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_PK_CALLBACKS"
    fi
    if test "x$ENABLED_DH" = "xno"
    then
        ENABLED_DH="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_DH"
    fi
fi


# Check for build-type conflicts
AS_IF([test "x$ENABLED_MAXSTRENGTH" = "xyes" && \
       test "x$ENABLED_LEANPSK" = "xyes"],
      [AC_MSG_ERROR([Cannot use Max Strength and Lean PSK at the same time.])])


# Update CFLAGS based on options
AS_IF([test "x$ENABLED_MAXSTRENGTH" = "xyes"],
      [AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_MAX_STRENGTH"])

AS_IF([test "x$ENABLED_MAXSTRENGTH" = "xyes" && \
       test "x$ENABLED_OLD_TLS" = "xyes"],
      [AM_CFLAGS="$AM_CFLAGS -DNO_OLD_TLS"
       ENABLED_OLD_TLS=no])


# OPTIMIZE FLAGS
if test "$GCC" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -Wall -Wno-unused"
    if test "$ax_enable_debug" = "no"
    then
        if test "$ENABLED_FASTMATH" = "yes"
        then
            AM_CFLAGS="$AM_CFLAGS $OPTIMIZE_FAST_CFLAGS"
            if test "$ENABLED_FASTHUGEMATH" = "yes"
            then
                AM_CFLAGS="$AM_CFLAGS $OPTIMIZE_HUGE_CFLAGS"
            fi
        else
            AM_CFLAGS="$AM_CFLAGS $OPTIMIZE_CFLAGS"
        fi
    fi
fi

# ICC command line warning for non supported warning flags
if test "$CC" = "icc"
then
    AM_CFLAGS="$AM_CFLAGS -wd10006"
fi


LIB_SOCKET_NSL
AX_HARDEN_CC_COMPILER_FLAGS

# link to ws2_32 if on mingw
case $host_os in
    *mingw32)
        LDFLAGS="$LDFLAGS -lws2_32" ;;
esac

# add user C_EXTRA_FLAGS back
CFLAGS="$CFLAGS $USER_C_EXTRA_FLAGS"
OPTION_FLAGS="$USER_C_EXTRA_FLAGS $AM_CFLAGS"

CREATE_HEX_VERSION
AC_SUBST([AM_CPPFLAGS])
AC_SUBST([AM_CFLAGS])
AC_SUBST([AM_LDFLAGS])

# FINAL
AC_CONFIG_FILES([stamp-h], [echo timestamp > stamp-h])
AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([wolfssl/version.h])
AC_CONFIG_FILES([wolfssl/options.h])
#have options.h and version.h for autoconf fips tag and build
#if test "x$ENABLED_FIPS" = "xyes"
#then
#    AC_CONFIG_FILES([cyassl/version.h])
#    AC_CONFIG_FILES([cyassl/options.h])
#fi
AC_CONFIG_FILES([support/wolfssl.pc])
AC_CONFIG_FILES([rpm/spec])

AX_CREATE_GENERIC_CONFIG
AX_AM_JOBSERVER([yes])

AC_OUTPUT


# force make clean
echo "---"
echo "Running make clean..."
make clean >/dev/null 2>&1
# Touch files that may not be in repository
echo "Touching File..."
touch ctaocrypt/src/fips.c
touch ctaocrypt/src/fips_test.c
echo

# generate user options header 
echo "---"
echo "Generating user options header..."

OPTION_FILE="wolfssl/options.h"
#if
#OPTION_FILE+="cyassl/options.h"
#fi
rm -f $OPTION_FILE

echo "/* wolfssl options.h" > $OPTION_FILE 
echo " * generated from configure options" >> $OPTION_FILE
echo " *" >> $OPTION_FILE
echo " * Copyright (C) 2006-2015 wolfSSL Inc." >> $OPTION_FILE
echo " *" >> $OPTION_FILE
echo " * This file is part of wolfSSL. (formerly known as CyaSSL)" >> $OPTION_FILE
echo " *" >> $OPTION_FILE
echo " */" >> $OPTION_FILE

echo "" >> $OPTION_FILE 
echo "#pragma once" >> $OPTION_FILE 
echo "" >> $OPTION_FILE 
echo "#ifdef __cplusplus" >> $OPTION_FILE 
echo "extern \"C\" {" >> $OPTION_FILE 
echo "#endif" >> $OPTION_FILE 
echo "" >> $OPTION_FILE 

for option in $OPTION_FLAGS; do
    defonly=`echo $option | sed 's/-D//'`
    if test "$defonly" != "$option"
    then
        noequalsign=`echo $defonly | sed 's/=/ /'`
        if test "$noequalsign" = "NDEBUG" || test "$noequalsign" = "DEBUG"
        then
            echo "not outputing (N)DEBUG to $OPTION_FILE"
            continue
        fi

        # allow user to igonore system options
        ignoresys=no
        if [[[ $noequalsign == _* ]]] ;
        then
            ignoresys=yes
            echo "#ifndef WOLFSSL_OPTIONS_IGNORE_SYS" >> $OPTION_FILE
        fi

        noarg=`echo $defonly | sed 's/=.*//'`
        echo "#undef  $noarg" >> $OPTION_FILE
        echo "#define $noequalsign" >> $OPTION_FILE

        if test "$ignoresys" = "yes"
        then
            echo "#endif" >> $OPTION_FILE
        fi

        echo "" >> $OPTION_FILE
    else
        echo "option w/o begin -D is $option, not saving to $OPTION_FILE"
    fi
done

echo "" >> $OPTION_FILE 
echo "#ifdef __cplusplus" >> $OPTION_FILE 
echo "}" >> $OPTION_FILE 
echo "#endif" >> $OPTION_FILE 
echo "" >> $OPTION_FILE 
echo

#backwards compatability for those who have included options or version
touch cyassl/options.h
echo "/* cyassl options.h" > cyassl/options.h
echo " * generated from wolfssl/options.h" >> cyassl/options.h
echo " */" >> cyassl/options.h
echo ""
while read -r line
do
    echo "$line" >> cyassl/options.h
done < $OPTION_FILE

# output config summary
echo "---"
echo "Configuration summary for $PACKAGE_NAME version $VERSION"
echo ""
echo "   * Installation prefix:       $prefix"
echo "   * System type:               $host_vendor-$host_os"
echo "   * Host CPU:                  $host_cpu"
echo "   * C Compiler:                $CC"
echo "   * C Flags:                   $CFLAGS"
echo "   * C++ Compiler:              $CXX"
echo "   * C++ Flags:                 $CXXFLAGS"
echo "   * CPP Flags:                 $CPPFLAGS"
echo "   * LIB Flags:                 $LIB"
echo "   * Debug enabled:             $ax_enable_debug"
echo "   * Warnings as failure:       $ac_cv_warnings_as_errors"
echo "   * make -j:                   $enable_jobserver"
echo "   * VCS checkout:              $ac_cv_vcs_checkout"
echo 
echo "   Features "
echo "   * Single threaded:           $ENABLED_SINGLETHREADED"
echo "   * Filesystem:                $ENABLED_FILESYSTEM"
echo "   * OpenSSL Extra API:         $ENABLED_OPENSSLEXTRA"
echo "   * Max Strength Build:        $ENABLED_MAXSTRENGTH"
echo "   * fastmath:                  $ENABLED_FASTMATH"
echo "   * sniffer:                   $ENABLED_SNIFFER"
echo "   * snifftest:                 $ENABLED_SNIFFTEST"
echo "   * ARC4:                      $ENABLED_ARC4"
echo "   * AES:                       $ENABLED_AES"
echo "   * AES-NI:                    $ENABLED_AESNI"
echo "   * AES-GCM:                   $ENABLED_AESGCM"
echo "   * AES-CCM:                   $ENABLED_AESCCM"
echo "   * DES3:                      $ENABLED_DES3"
echo "   * Camellia:                  $ENABLED_CAMELLIA"
echo "   * NULL Cipher:               $ENABLED_NULL_CIPHER"
echo "   * MD5:                       $ENABLED_MD5"
echo "   * RIPEMD:                    $ENABLED_RIPEMD"
echo "   * SHA:                       $ENABLED_SHA"
echo "   * SHA-512:                   $ENABLED_SHA512"
echo "   * BLAKE2:                    $ENABLED_BLAKE2"
echo "   * keygen:                    $ENABLED_KEYGEN"
echo "   * certgen:                   $ENABLED_CERTGEN"
echo "   * certreq:                   $ENABLED_CERTREQ"
echo "   * HC-128:                    $ENABLED_HC128"
echo "   * RABBIT:                    $ENABLED_RABBIT"
echo "   * CHACHA:                    $ENABLED_CHACHA"
echo "   * Hash DRBG:                 $ENABLED_HASHDRBG"
echo "   * PWDBASED:                  $ENABLED_PWDBASED"
echo "   * HKDF:                      $ENABLED_HKDF"
echo "   * MD4:                       $ENABLED_MD4"
echo "   * PSK:                       $ENABLED_PSK"
echo "   * Poly1305:                  $ENABLED_POLY1305"
echo "   * LEANPSK:                   $ENABLED_LEANPSK"
echo "   * RSA:                       $ENABLED_RSA"
echo "   * DSA:                       $ENABLED_DSA"
echo "   * DH:                        $ENABLED_DH"
echo "   * ECC:                       $ENABLED_ECC"
echo "   * CURVE25519:                $ENABLED_CURVE25519"
echo "   * ED25519:                   $ENABLED_ED25519"
echo "   * FPECC:                     $ENABLED_FPECC"
echo "   * ECC_ENCRYPT:               $ENABLED_ECC_ENCRYPT"
echo "   * ASN:                       $ENABLED_ASN"
echo "   * Anonymous cipher:          $ENABLED_ANON"
echo "   * CODING:                    $ENABLED_CODING"
echo "   * MEMORY:                    $ENABLED_MEMORY"
echo "   * I/O POOL:                  $ENABLED_IOPOOL"
echo "   * ERROR_STRINGS:             $ENABLED_ERROR_STRINGS"
echo "   * DTLS:                      $ENABLED_DTLS"
echo "   * Old TLS Versions:          $ENABLED_OLD_TLS"
echo "   * OCSP:                      $ENABLED_OCSP"
echo "   * CRL:                       $ENABLED_CRL"
echo "   * CRL-MONITOR:               $ENABLED_CRL_MONITOR"
echo "   * Persistent session cache:  $ENABLED_SAVESESSION"
echo "   * Persistent cert    cache:  $ENABLED_SAVECERT"
echo "   * Atomic User Record Layer:  $ENABLED_ATOMICUSER"
echo "   * Public Key Callbacks:      $ENABLED_PKCALLBACKS"
echo "   * NTRU:                      $ENABLED_NTRU"
echo "   * SNI:                       $ENABLED_SNI"
echo "   * Maximum Fragment Length:   $ENABLED_MAX_FRAGMENT"
echo "   * Truncated HMAC:            $ENABLED_TRUNCATED_HMAC"
echo "   * Renegotiation Indication:  $ENABLED_RENEGOTIATION_INDICATION"
echo "   * Secure Renegotiation:      $ENABLED_SECURE_RENEGOTIATION"
echo "   * Supported Elliptic Curves: $ENABLED_SUPPORTED_CURVES"
echo "   * Session Ticket:            $ENABLED_SESSION_TICKET"
echo "   * All TLS Extensions:        $ENABLED_TLSX"
echo "   * PKCS#7                     $ENABLED_PKCS7"
echo "   * wolfSCEP                   $ENABLED_WOLFSCEP"
echo "   * Small Stack:               $ENABLED_SMALL_STACK"
echo "   * valgrind unit tests:       $ENABLED_VALGRIND"
echo "   * LIBZ:                      $ENABLED_LIBZ"
echo "   * Examples:                  $ENABLED_EXAMPLES"
echo ""
echo "---"

