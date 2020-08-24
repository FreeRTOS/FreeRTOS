# configure.ac
#
# Copyright (C) 2006-2020 wolfSSL Inc.
#
# This file is part of wolfSSL. (formerly known as CyaSSL)
#
#
AC_COPYRIGHT([Copyright (C) 2006-2020 wolfSSL Inc.])
AC_PREREQ([2.63])
AC_INIT([wolfssl],[4.5.0],[https://github.com/wolfssl/wolfssl/issues],[wolfssl],[https://www.wolfssl.com])
AC_CONFIG_AUX_DIR([build-aux])

# The following sets CFLAGS to empty if unset on command line.  We do not
# want the default "-g -O2" that AC_PROG_CC sets automatically.
: ${CFLAGS=""}

# Test ar for the "U" option. Should be checked before the libtool macros.
xxx_ar_flags=$(ar --help 2>&1)
AS_CASE([$xxx_ar_flags],[*'use actual timestamps and uids/gids'*],[: ${AR_FLAGS="Ucru"}])

AC_PROG_CC
AM_PROG_CC_C_O
AC_CANONICAL_HOST
AC_CONFIG_MACRO_DIR([m4])

AM_INIT_AUTOMAKE([1.11 -Wall -Werror -Wno-portability foreign tar-ustar subdir-objects no-define color-tests])
m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

AC_ARG_PROGRAM

AC_CONFIG_HEADERS([config.h:config.in])

LT_PREREQ([2.2])
LT_INIT([disable-static win32-dll])

#shared library versioning
WOLFSSL_LIBRARY_VERSION=26:0:2
#                        | | |
#                 +------+ | +---+
#                 |        |     |
#                current:revision:age
#                 |        |     |
#                 |        |     +- increment if interfaces have been added
#                 |        |        set to zero if interfaces have been removed
#                 |        |        or changed
#                 |        +- increment if source code has changed
#                 |           set to zero if current is incremented
#                 +- increment if interfaces have been added, removed or changed
AC_SUBST([WOLFSSL_LIBRARY_VERSION])

# Capture user C_EXTRA_FLAGS from configure line.
# Use of C_EXTRA_FLAGS is deprecated because CFLAGS was fixed but someone
# might still be using it.
CFLAGS="$CFLAGS $C_EXTRA_FLAGS $C_FLAGS"

gl_VISIBILITY
AS_IF([ test -n "$CFLAG_VISIBILITY" ], [
       AM_CFLAGS="$AM_CPPFLAGS $CFLAG_VISIBILITY"
       ])


# Moved these size of and type checks before the library checks.
# The library checks add the library to subsequent test compiles
# and in some rare cases, the networking check causes these sizeof
# checks to fail.
AC_CHECK_SIZEOF([long long])
AC_CHECK_SIZEOF([long])
AC_CHECK_SIZEOF([time_t])
AC_CHECK_TYPES([__uint128_t])
AC_CHECK_FUNCS([gethostbyname getaddrinfo gettimeofday gmtime_r inet_ntoa memset socket])
AC_CHECK_HEADERS([arpa/inet.h fcntl.h limits.h netdb.h netinet/in.h stddef.h sys/ioctl.h sys/socket.h sys/time.h errno.h])
AC_CHECK_LIB([network],[socket])
AC_C_BIGENDIAN

AC_PROG_INSTALL
AC_TYPE_SIZE_T
AC_TYPE_UINT8_T
AM_PROG_AS
LT_LIB_M

OPTIMIZE_CFLAGS="-Os"
OPTIMIZE_FAST_CFLAGS="-O2"
OPTIMIZE_HUGE_CFLAGS="-funroll-loops -DTFM_SMALL_SET -DTFM_HUGE_SET"
DEBUG_CFLAGS="-g -DDEBUG -DDEBUG_WOLFSSL"
LIB_ADD=
LIB_STATIC_ADD=

# Thread local storage
AX_TLS([thread_ls_on=yes],[thread_ls_on=no])
AS_IF([test "x$thread_ls_on" = "xyes"],[AM_CFLAGS="$AM_CFLAGS -DHAVE_THREAD_LS"])

# DEBUG
AX_DEBUG
AS_IF([test "$ax_enable_debug" = "yes"],
      [AM_CFLAGS="$DEBUG_CFLAGS $AM_CFLAGS"],
      [AM_CFLAGS="$AM_CFLAGS -DNDEBUG"])



# FIPS
AC_ARG_ENABLE([fips],
    [AS_HELP_STRING([--enable-fips],[Enable FIPS 140-2, Will NOT work w/o FIPS license (default: disabled)])],
    [ENABLED_FIPS=$enableval],
    [ENABLED_FIPS="no"])

AS_CASE([$ENABLED_FIPS],
    ["ready"],[
        ENABLED_FIPS="yes"
        FIPS_VERSION="v2"
        FIPS_READY="yes"
    ],
    ["v2"],[
        # FIPS v2
        ENABLED_FIPS="yes"
        FIPS_VERSION="v2"
    ],
    ["rand"],[
        # FIPS Rand
        ENABLED_FIPS="yes"
        FIPS_VERSION="rand"
    ],
    ["no"],[FIPS_VERSION="none"],
    [
        # FIPS v1
        ENABLED_FIPS="yes"
        FIPS_VERSION="v1"
    ])


# Distro build feature subset (Debian, Ubuntu, etc.)
AC_ARG_ENABLE([distro],
    [AS_HELP_STRING([--enable-distro],[Enable wolfSSL distro build (default: disabled)])],
    [ ENABLED_DISTRO=$enableval ],
    [ ENABLED_DISTRO=no ]
    )
if test "$ENABLED_DISTRO" = "yes"
then
    enable_shared=yes
    enable_static=yes
    enable_all=yes
fi


# ALL FEATURES
AC_ARG_ENABLE([all],
    [AS_HELP_STRING([--enable-all],[Enable all wolfSSL features, except SSLv3 (default: disabled)])],
    [ ENABLED_ALL=$enableval ],
    [ ENABLED_ALL=no ]
    )
if test "$ENABLED_ALL" = "yes"
then
    enable_dtls=yes
    if test "x$FIPS_VERSION" != "xv1"
    then
        enable_tls13=yes
        enable_rsapss=yes
    fi
    enable_openssh=yes
    enable_opensslextra=yes
    enable_opensslall=yes
    enable_savesession=yes
    enable_savecert=yes
    enable_atomicuser=yes
    enable_pkcallbacks=yes
    enable_aesgcm=yes
    enable_aesccm=yes
    enable_aesctr=yes
    enable_aesofb=yes
    enable_aescfb=yes
    enable_camellia=yes
    enable_ripemd=yes
    enable_sha512=yes
    enable_sha224=yes
    enable_sha3=yes
    enable_sessioncerts=yes
    enable_keygen=yes
    enable_certgen=yes
    enable_certreq=yes
    enable_certext=yes
    enable_sep=yes
    enable_hkdf=yes
    enable_dsa=yes
    enable_ecccustcurves=yes
    enable_compkey=yes
    enable_curve25519=yes
    enable_curve448=yes
    enable_ed25519=yes
    enable_fpecc=yes
    enable_eccencrypt=yes
    enable_psk=yes
    enable_idea=yes
    enable_cmac=yes
    enable_xts=yes
    enable_webserver=yes
    enable_hc128=yes
    enable_rabbit=yes
    enable_ocsp=yes
    enable_ocspstapling=yes
    enable_ocspstapling2=yes
    enable_crl=yes
    enable_crl_monitor=yes
    enable_sni=yes
    enable_maxfragment=yes
    enable_alpn=yes
    enable_truncatedhmac=yes
    enable_trusted_ca=yes
    enable_supportedcurves=yes
    enable_session_ticket=yes
    enable_tlsx=yes
    enable_pkcs7=yes
    enable_ssh=yes
    enable_scep=yes
    enable_srp=yes
    enable_certservice=yes
    enable_jni=yes
    enable_lighty=yes
    enable_haproxy=yes
    enable_stunnel=yes
    enable_nginx=yes
    enable_openvpn=yes
    enable_asio=yes
    enable_libwebsockets=yes
    enable_qt=yes
    enable_pwdbased=yes
    enable_aeskeywrap=yes
    enable_x963kdf=yes
    enable_scrypt=yes
    enable_indef=yes
    enable_enckeys=yes
    enable_hashflags=yes
    enable_dhdefaultparams=yes

    # Enable AES Decrypt, AES ECB, Alt Names, DER Load, Keep Certs, CRL IO with Timeout
    AM_CFLAGS="$AM_CFLAGS -DHAVE_AES_DECRYPT -DHAVE_AES_ECB -DWOLFSSL_ALT_NAMES -DWOLFSSL_DER_LOAD -DKEEP_OUR_CERT -DKEEP_PEER_CERT -DHAVE_CRL_IO -DHAVE_IO_TIMEOUT"

    # Enable DH const table speedups (eliminates `-lm` math lib dependency)
    AM_CFLAGS="$AM_CFLAGS -DHAVE_FFDHE_2048 -DHAVE_FFDHE_3072 -DFP_MAX_BITS=8192"

    # Enable ECC Key Gen / Import checks
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_VALIDATE_ECC_IMPORT -DWOLFSSL_VALIDATE_ECC_KEYGEN"

    # Enable multiple attribute additions such as DC
    AM_CFLAGS="-DWOLFSSL_MULTI_ATTRIB $AM_CFLAGS"
fi


# Support for forcing 32-bit mode
# To force 32-bit instructions use:
#   ./configure CFLAGS="-m32" LDFLAGS="-m32" && make
# The checks for sizeof long and long/long are run at the top of configure and require "-m32" to be set directly in the ./configure statement.
AC_ARG_ENABLE([32bit],
    [AS_HELP_STRING([--enable-32bit],[Enables 32-bit support (default: disabled)])],
    [ ENABLED_32BIT=$enableval ],
    [ ENABLED_32BIT=no ]
    )

# 16-bit compiler support
AC_ARG_ENABLE([16bit],
    [AS_HELP_STRING([--enable-16bit],[Enables 16-bit support (default: disabled)])],
    [ ENABLED_16BIT=$enableval ],
    [ ENABLED_16BIT=no ]
    )
if test "$ENABLED_16BIT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWC_16BIT_CPU"
fi



# Support for disabling all ASM
AC_ARG_ENABLE([asm],
    [AS_HELP_STRING([--enable-asm],[Enables option for assembly (default: enabled)])],
    [ ENABLED_ASM=$enableval ],
    [ ENABLED_ASM=yes ]
    )

if test "$ENABLED_ASM" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DTFM_NO_ASM -DWOLFSSL_NO_ASM"
fi


# SINGLE THREADED
AC_ARG_ENABLE([singlethreaded],
    [AS_HELP_STRING([--enable-singlethreaded],[Enable wolfSSL single threaded (default: disabled)])],
    [ ENABLED_SINGLETHREADED=$enableval ],
    [ ENABLED_SINGLETHREADED=no ])

AS_IF([ test "x$ENABLED_SINGLETHREADED" = "xno" ],[
       AX_PTHREAD([
                   AC_DEFINE([HAVE_PTHREAD], [1], [Define if you have POSIX threads libraries and header files.])
                   # If AX_PTHREAD is adding -Qunused-arguments, need to prepend with -Xcompiler libtool will use it. Newer
                   # versions of clang don't need the -Q flag when using pthreads.
                   AS_CASE([$PTHREAD_CFLAGS],[-Qunused-arguments*],[PTHREAD_CFLAGS="-Xcompiler $PTHREAD_CFLAGS"])
                   AM_CFLAGS="-D_POSIX_THREADS $AM_CFLAGS $PTHREAD_CFLAGS"
                   LIBS="$LIBS $PTHREAD_LIBS"
                   ],[
                      ENABLED_SINGLETHREADED=yes
                      ])
      ])

AS_IF([ test "x$ENABLED_SINGLETHREADED" = "xyes" ],[ AM_CFLAGS="-DSINGLE_THREADED $AM_CFLAGS" ])


# DTLS
AC_ARG_ENABLE([dtls],
    [AS_HELP_STRING([--enable-dtls],[Enable wolfSSL DTLS (default: disabled)])],
    [ ENABLED_DTLS=$enableval ],
    [ ENABLED_DTLS=no ]
    )
if test "$ENABLED_DTLS" = "yes"
then
  AM_CFLAGS="-DWOLFSSL_DTLS $AM_CFLAGS"
fi

# DTLS change MTU
AC_ARG_ENABLE([dtls-mtu],
    [AS_HELP_STRING([--enable-dtls-mtu],[Enable setting the MTU size for wolfSSL DTLS (default: disabled)])],
    [ ENABLED_DTLS_MTU=$enableval ],
    [ ENABLED_DTLS_MTU=no ]
    )
if test "$ENABLED_DTLS_MTU" = "yes"
then
  AM_CFLAGS="-DWOLFSSL_DTLS_MTU $AM_CFLAGS"
fi


# TLS v1.3 Draft 18 (Note: only final TLS v1.3 supported, here for backwards build compatibility)
AC_ARG_ENABLE([tls13-draft18],
    [AS_HELP_STRING([--enable-tls13-draft18],[Enable wolfSSL TLS v1.3 Draft 18 (default: disabled)])],
    [ ENABLED_TLS13_DRAFT18=$enableval ],
    [ ENABLED_TLS13_DRAFT18=no ]
    )

# TLS v1.3
AC_ARG_ENABLE([tls13],
    [AS_HELP_STRING([--enable-tls13],[Enable wolfSSL TLS v1.3 (default: enabled)])],
    [ ENABLED_TLS13=$enableval ],
    [ ENABLED_TLS13=yes ]
    )
if test "x$FIPS_VERSION" = "xv1"
then
    ENABLED_TLS13="no"
fi

# Post-handshake Authentication
AC_ARG_ENABLE([postauth],
    [AS_HELP_STRING([--enable-postauth],[Enable wolfSSL Post-handshake Authentication (default: disabled)])],
    [ ENABLED_TLS13_POST_AUTH=$enableval ],
    [ ENABLED_TLS13_POST_AUTH=no ]
    )
if test "$ENABLED_TLS13_POST_AUTH" = "yes"
then
    if test "x$ENABLED_TLS13" = "xno"
    then
        AC_MSG_ERROR([cannot enable postauth without enabling tls13.])
    fi
  AM_CFLAGS="-DWOLFSSL_POST_HANDSHAKE_AUTH $AM_CFLAGS"
fi


# Hello Retry Request Cookie
AC_ARG_ENABLE([hrrcookie],
    [AS_HELP_STRING([--enable-hrrcookie],[Enable the server to send Cookie Extension in HRR with state (default: disabled)])],
    [ ENABLED_SEND_HRR_COOKIE=$enableval ],
    [ ENABLED_SEND_HRR_COOKIE=no ]
    )
if test "$ENABLED_SEND_HRR_COOKIE" = "yes"
then
    if test "x$ENABLED_TLS13" = "xno"
    then
        AC_MSG_ERROR([cannot enable hrrcookie without enabling tls13.])
    fi
  AM_CFLAGS="-DWOLFSSL_SEND_HRR_COOKIE $AM_CFLAGS"
fi


# RNG
AC_ARG_ENABLE([rng],
    [AS_HELP_STRING([--enable-rng],[Enable compiling and using RNG (default: enabled)])],
    [ ENABLED_RNG=$enableval ],
    [ ENABLED_RNG=yes ]
    )

if test "$ENABLED_RNG" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DWC_NO_RNG"
fi


# DTLS-SCTP
AC_ARG_ENABLE([sctp],
    [AS_HELP_STRING([--enable-sctp],[Enable wolfSSL DTLS-SCTP support (default: disabled)])],
    [ENABLED_SCTP=$enableval],
    [ENABLED_SCTP=no])

AS_IF([test "x$ENABLED_SCTP" = "xyes"],
        [AC_MSG_CHECKING([for SCTP])
         AC_RUN_IFELSE(
            [AC_LANG_PROGRAM(
[[
#include <sys/socket.h>
#include <arpa/inet.h>
]],
[[int s = socket(AF_INET, SOCK_STREAM, IPPROTO_SCTP); if (s == -1) return 1;]])],
[AC_MSG_RESULT(yes)],
[AC_MSG_RESULT(no)
 AC_MSG_ERROR([SCTP not available, remove enable-sctp from configure])])
])


# DTLS-MULTICAST
AC_ARG_ENABLE([mcast],
    [AS_HELP_STRING([--enable-mcast],[Enable wolfSSL DTLS multicast support (default: disabled)])],
    [ENABLED_MCAST=$enableval],
    [ENABLED_MCAST=no])


# List of open source project defines using our openssl compatibility layer:
# openssh (--enable-openssh) WOLFSSL_OPENSSH
# openvpn (--enable-openvpn) WOLFSSL_OPENVPN
# nginix (--enable-nginx) WOLFSSL_NGINX
# haproxy (--enable-haproxy) WOLFSSL_HAPROXY
# wpa_supplicant (--enable-wpas) WOLFSSL_WPAS
# ssl fortress (--enable-fortress) FORTRESS
# ssl bump (--enable-bump)
# signal (--enable-signal)
# lighty (--enable-lighty) HAVE_LIGHTY
# stunnel (--enable-stunnel) HAVE_STUNNEL
# asio (--enable-asio) WOLFSSL_ASIO
# libwebsockets (--enable-libwebsockets) WOLFSSL_LIBWEBSOCKETS
# qt (--enable-qt) WOLFSSL_QT
# qt test (--enable-qt-test) WOLFSSL_QT_TEST
# HAVE_POCO_LIB
# WOLFSSL_MYSQL_COMPATIBLE
# web server (--enable-webserver) HAVE_WEBSERVER


# OpenSSH compatibility Build
AC_ARG_ENABLE([openssh],
    [AS_HELP_STRING([--enable-openssh],[Enable OpenSSH compatibility build (default: disabled)])],
    [ENABLED_OPENSSH=$enableval],
    [ENABLED_OPENSSH=no])

# OpenVPN compatibility Build
AC_ARG_ENABLE([openvpn],
    [AS_HELP_STRING([--enable-openvpn],[Enable OpenVPN compatibility build (default: disabled)])],
    [ENABLED_OPENVPN=$enableval],
    [ENABLED_OPENVPN=no])

# nginx compatibility build
AC_ARG_ENABLE([nginx],
    [AS_HELP_STRING([--enable-nginx],[Enable nginx (default: disabled)])],
    [ ENABLED_NGINX=$enableval ],
    [ ENABLED_NGINX=no ]
    )

# haproxy compatibility build
AC_ARG_ENABLE([haproxy],
    [AS_HELP_STRING([--enable-haproxy],[Enable haproxy (default: disabled)])],
    [ ENABLED_HAPROXY=$enableval ],
    [ ENABLED_HAPROXY=no ]
    )

# wpa_supplicant support
AC_ARG_ENABLE([wpas],
    [AS_HELP_STRING([--enable-wpas],[Enable wpa_supplicant support (default: disabled)])],
    [ ENABLED_WPAS=$enableval ],
    [ ENABLED_WPAS=no ]
    )

# wpa_supplicant support
AC_ARG_ENABLE([wpas-dpp],
    [AS_HELP_STRING([--enable-wpas-dpp],[Enable wpa_supplicant support with dpp (default: disabled)])],
    [ ENABLED_WPAS_DPP=$enableval ],
    [ ENABLED_WPAS_DPP=no ]
    )

if test "$ENABLED_WPAS_DPP" = "yes"
then
    ENABLED_WPAS="yes"
fi

# Fortress build
AC_ARG_ENABLE([fortress],
    [AS_HELP_STRING([--enable-fortress],[Enable SSL fortress build (default: disabled)])],
    [ ENABLED_FORTRESS=$enableval ],
    [ ENABLED_FORTRESS=no ]
    )

# libwebsockets Support
AC_ARG_ENABLE([libwebsockets],
    [AS_HELP_STRING([--enable-libwebsockets],[Enable libwebsockets (default: disabled)])],
    [ ENABLED_LIBWEBSOCKETS=$enableval ],
    [ ENABLED_LIBWEBSOCKETS=no ]
    )
if test "$ENABLED_LIBWEBSOCKETS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_LIBWEBSOCKETS -DHAVE_EX_DATA -DOPENSSL_NO_EC"
fi


if test "$ENABLED_OPENSSH" = "yes"
then
    ENABLED_FORTRESS="yes"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_OPENSSH -DHAVE_EX_DATA -DWOLFSSL_BASE16"
fi

#IP alternative name Support
AC_ARG_ENABLE([ip-alt-name],
    [AS_HELP_STRING([--enable-ip-alt-name],[Enable IP subject alternative name (default: disabled)])],
    [ ENABLE_IP_ALT_NAME=$enableval ],
    [ ENABLE_IP_ALT_NAME=no ]
    )

if test "$ENABLE_IP_ALT_NAME" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_IP_ALT_NAME"
fi

#Qt Support
AC_ARG_ENABLE([qt],
    [AS_HELP_STRING([--enable-qt],[Enable qt (default: disabled)])],
    [ ENABLED_QT=$enableval ],
    [ ENABLED_QT=no ]
    )

# ssl bump build
AC_ARG_ENABLE([bump],
    [AS_HELP_STRING([--enable-bump],[Enable SSL Bump build (default: disabled)])],
    [ ENABLED_BUMP=$enableval ],
    [ ENABLED_BUMP=no ]
    )

# SNIFFER
AC_ARG_ENABLE([sniffer],
   [AS_HELP_STRING([--enable-sniffer],[Enable wolfSSL sniffer support (default: disabled)])],
   [ ENABLED_SNIFFER=$enableval ],
   [ ENABLED_SNIFFER=no ]
   )

# signal compatibility build
AC_ARG_ENABLE([signal],
    [AS_HELP_STRING([--enable-signal],[Enable signal (default: disabled)])],
    [ ENABLED_SIGNAL=$enableval ],
    [ ENABLED_SIGNAL=no ]
    )

# OpenSSL Coexist
AC_ARG_ENABLE([opensslcoexist],
    [AS_HELP_STRING([--enable-opensslcoexist],[Enable coexistence of wolfssl/openssl (default: disabled)])],
    [ ENABLED_OPENSSLCOEXIST=$enableval ],
    [ ENABLED_OPENSSLCOEXIST=no ]
    )
if test "x$ENABLED_OPENSSLCOEXIST" = "xyes"
then
    # make sure old names are disabled
    enable_oldnames=no

    AM_CFLAGS="$AM_CFLAGS -DOPENSSL_COEXIST"
fi


# OPENSSL Compatibility ALL
AC_ARG_ENABLE([opensslall],
[AS_HELP_STRING([--enable-opensslall],[Enable all OpenSSL API, size++ (default: disabled)])],
[ ENABLED_OPENSSLALL=$enableval ],
[ ENABLED_OPENSSLALL=no ]
)
if test "$ENABLED_LIBWEBSOCKETS" = "yes" || test "$ENABLED_OPENVPN" = "yes" || test "$ENABLED_WPAS_DPP" = "yes"
then
    ENABLED_OPENSSLALL="yes"
fi

if test "$ENABLED_OPENSSLALL" = "yes"
then
AM_CFLAGS="-DOPENSSL_ALL -DWOLFSSL_EITHER_SIDE -DWC_RSA_NO_PADDING -DWC_RSA_PSS $AM_CFLAGS"
fi

# OPENSSL Extra Compatibility
AC_ARG_ENABLE([opensslextra],
    [AS_HELP_STRING([--enable-opensslextra],[Enable extra OpenSSL API, size+ (default: disabled)])],
    [ ENABLED_OPENSSLEXTRA=$enableval ],
    [ ENABLED_OPENSSLEXTRA=no ]
    )
if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_NGINX" = "yes" || test "$ENABLED_SIGNAL" = "yes" || test "$ENABLED_WPAS" = "yes" || test "$ENABLED_FORTRESS" = "yes" || test "$ENABLED_BUMP" = "yes" || test "$ENABLED_SNIFFER" = "yes" || test "$ENABLED_OPENSSLALL" = "yes" || test "$ENABLED_LIBWEBSOCKETS" = "yes"
then
    ENABLED_OPENSSLEXTRA="yes"
fi

if test "$ENABLED_OPENSSLEXTRA" = "yes" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
then
  AM_CFLAGS="-DOPENSSL_EXTRA -DWOLFSSL_ALWAYS_VERIFY_CB $AM_CFLAGS"
  AM_CFLAGS="-DWOLFSSL_VERIFY_CB_ALL_CERTS -DWOLFSSL_EXTRA_ALERTS $AM_CFLAGS"
  AM_CFLAGS="-DHAVE_EXT_CACHE $AM_CFLAGS"
fi

if test "$ENABLED_OPENSSLEXTRA" = "yes" && test "$ENABLED_SMALL" = "yes"
then
   AC_MSG_ERROR([cannot enable small and opensslextra, only one or the other.])
fi

if test "$ENABLED_OPENSSLEXTRA" = "x509small"
then
  AC_MSG_NOTICE([Enabling only a subset of X509 opensslextra])
  AM_CFLAGS="-DOPENSSL_EXTRA_X509_SMALL $AM_CFLAGS"
  AM_CFLAGS="-DWOLFSSL_EKU_OID -DWOLFSSL_MULTI_ATTRIB $AM_CFLAGS"
fi

# High Strength Build
AC_ARG_ENABLE([maxstrength],
    [AS_HELP_STRING([--enable-maxstrength],[Enable Max Strength build, allows TLSv1.2-AEAD-PFS ciphers only (default: disabled)])],
    [ENABLED_MAXSTRENGTH=$enableval],
    [ENABLED_MAXSTRENGTH=no])


# Harden, enable Timing Resistance and Blinding by default
AC_ARG_ENABLE([harden],
    [AS_HELP_STRING([--enable-harden],[Enable Hardened build, Enables Timing Resistance and Blinding (default: enabled)])],
    [ENABLED_HARDEN=$enableval],
    [ENABLED_HARDEN=yes])

if test "$ENABLED_HARDEN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DTFM_TIMING_RESISTANT -DECC_TIMING_RESISTANT"
    if test "$ENABLED_RNG" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DWC_RSA_BLINDING"
    fi
else
    AM_CFLAGS="$AM_CFLAGS -DWC_NO_HARDEN"
fi


# IPv6 Test Apps
AC_ARG_ENABLE([ipv6],
    [AS_HELP_STRING([--enable-ipv6],[Enable testing of IPV6 (default: disabled)])],
    [ ENABLED_IPV6=$enableval ],
    [ ENABLED_IPV6=no ]
    )

if test "$ENABLED_IPV6" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DTEST_IPV6 -DWOLFSSL_IPV6"
fi


if test "$ENABLED_WPAS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_SECRET_CALLBACK -DWOLFSSL_STATIC_RSA"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_PUBLIC_MP -DWOLFSSL_PUBLIC_ECC_ADD_DBL"
    AM_CFLAGS="$AM_CFLAGS -DATOMIC_USER -DHAVE_EX_DATA -DWOLFSSL_KEEP_PEER_CERT"
    AM_CFLAGS="$AM_CFLAGS -DHAVE_EXT_CACHE"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALWAYS_VERIFY_CB"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_DIRECT -DWOLFSSL_DER_LOAD"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_KEY_GEN -DWOLFSSL_DES_ECB"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_WPAS"
fi

if test "$ENABLED_WPAS" = "small"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALWAYS_VERIFY_CB"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALWAYS_KEEP_SNI"
    AM_CFLAGS="$AM_CFLAGS -DHAVE_EX_DATA"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_EITHER_SIDE"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_WPAS_SMALL"
fi

if test "$ENABLED_FORTRESS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DFORTRESS -DWOLFSSL_ALWAYS_VERIFY_CB -DWOLFSSL_AES_COUNTER -DWOLFSSL_AES_DIRECT -DWOLFSSL_DER_LOAD -DWOLFSSL_KEY_GEN"
fi


if test "$ENABLED_BUMP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DLARGE_STATIC_BUFFERS -DWOLFSSL_CERT_GEN -DWOLFSSL_KEY_GEN -DHUGE_SESSION_CACHE -DFP_MAX_BITS=8192 -DWOLFSSL_DER_LOAD -DWOLFSSL_ALT_NAMES -DWOLFSSL_TEST_CERT"
fi

ENABLED_SLOWMATH="yes"

# lean psk build
AC_ARG_ENABLE([leanpsk],
    [AS_HELP_STRING([--enable-leanpsk],[Enable Lean PSK build (default: disabled)])],
    [ ENABLED_LEANPSK=$enableval ],
    [ ENABLED_LEANPSK=no ]
    )

if test "$ENABLED_LEANPSK" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_LEANPSK -DWOLFSSL_STATIC_PSK -DHAVE_NULL_CIPHER -DSINGLE_THREADED -DNO_AES -DNO_FILESYSTEM -DNO_RABBIT -DNO_RSA -DNO_DSA -DNO_DH -DNO_CERTS -DNO_PWDBASED -DNO_MD4 -DNO_MD5 -DNO_ERROR_STRINGS -DNO_OLD_TLS -DNO_RC4 -DNO_WRITEV -DNO_DEV_RANDOM -DWOLFSSL_USER_IO -DNO_SHA"
    ENABLED_SLOWMATH="no"
    ENABLED_SINGLETHREADED="yes"
    enable_lowresource=yes
fi


# lean TLS build (TLS 1.2 client only (no client auth), ECC256, AES128 and SHA256 w/o Shamir)
AC_ARG_ENABLE([leantls],
    [AS_HELP_STRING([--enable-leantls],[Enable Lean TLS build (default: disabled)])],
    [ ENABLED_LEANTLS=$enableval ],
    [ ENABLED_LEANTLS=no ]
    )

if test "$ENABLED_LEANTLS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_LEANTLS -DNO_WRITEV -DHAVE_ECC -DTFM_ECC256 -DECC_USER_CURVES -DNO_WOLFSSL_SERVER -DNO_RABBIT -DNO_RSA -DNO_DSA -DNO_DH -DNO_PWDBASED -DNO_MD5 -DNO_ERROR_STRINGS -DNO_OLD_TLS -DNO_RC4 -DNO_SHA -DNO_PSK -DNO_WOLFSSL_MEMORY -DNO_WOLFSSL_CM_VERIFY"
    enable_lowresource=yes
fi


# low resource options to reduce flash and memory use
AC_ARG_ENABLE([lowresource],
    [AS_HELP_STRING([--enable-lowresource],[Enable low resource options for memory/flash (default: disabled)])],
    [ ENABLED_LOWRESOURCE=$enableval ],
    [ ENABLED_LOWRESOURCE=no ]
    )

if test "$ENABLED_LOWRESOURCE" = "yes"
then
    # low memory / flash flags
    AM_CFLAGS="$AM_CFLAGS -DNO_SESSION_CACHE -DRSA_LOW_MEM -DALT_ECC_SIZE -DGCM_SMALL -DCURVE25519_SMALL -DED25519_SMALL -DWOLFSSL_SMALL_CERT_VERIFY"

    # low flash flags
    AM_CFLAGS="$AM_CFLAGS -DUSE_SLOW_SHA -DUSE_SLOW_SHA256 -DUSE_SLOW_SHA512"
fi


# TITAN cache
AC_ARG_ENABLE([titancache],
    [AS_HELP_STRING([--enable-titancache],[Enable titan session cache (default: disabled)])],
    [ ENABLED_TITANCACHE=$enableval ],
    [ ENABLED_TITANCACHE=no ]
    )

if test "$ENABLED_TITANCACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DTITAN_SESSION_CACHE"
fi


# HUGE cache
AC_ARG_ENABLE([hugecache],
    [AS_HELP_STRING([--enable-hugecache],[Enable huge session cache (default: disabled)])],
    [ ENABLED_HUGECACHE=$enableval ],
    [ ENABLED_HUGECACHE=no ]
    )

if test "$ENABLED_HUGECACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHUGE_SESSION_CACHE"
fi


# big cache
AC_ARG_ENABLE([bigcache],
    [AS_HELP_STRING([--enable-bigcache],[Enable big session cache (default: disabled)])],
    [ ENABLED_BIGCACHE=$enableval ],
    [ ENABLED_BIGCACHE=no ]
    )

if test "$ENABLED_BIGCACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DBIG_SESSION_CACHE"
fi


# SMALL cache
AC_ARG_ENABLE([smallcache],
    [AS_HELP_STRING([--enable-smallcache],[Enable small session cache (default: disabled)])],
    [ ENABLED_SMALLCACHE=$enableval ],
    [ ENABLED_SMALLCACHE=no ]
    )

if test "$ENABLED_SMALLCACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DSMALL_SESSION_CACHE"
fi


# Persistent session cache
AC_ARG_ENABLE([savesession],
    [AS_HELP_STRING([--enable-savesession],[Enable persistent session cache (default: disabled)])],
    [ ENABLED_SAVESESSION=$enableval ],
    [ ENABLED_SAVESESSION=no ]
    )

if test "$ENABLED_SAVESESSION" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DPERSIST_SESSION_CACHE"
fi


# Persistent cert cache
AC_ARG_ENABLE([savecert],
    [AS_HELP_STRING([--enable-savecert],[Enable persistent cert cache (default: disabled)])],
    [ ENABLED_SAVECERT=$enableval ],
    [ ENABLED_SAVECERT=no ]
    )

if test "$ENABLED_SAVECERT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DPERSIST_CERT_CACHE"
fi


# Write duplicate WOLFSSL object
AC_ARG_ENABLE([writedup],
    [AS_HELP_STRING([--enable-writedup],[Enable write duplication of WOLFSSL objects (default: disabled)])],
    [ ENABLED_WRITEDUP=$enableval ],
    [ ENABLED_WRITEDUP=no ]
    )

if test "$ENABLED_WRITEDUP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_WRITE_DUP"
fi


# Atomic User Record Layer
AC_ARG_ENABLE([atomicuser],
    [AS_HELP_STRING([--enable-atomicuser],[Enable Atomic User Record Layer (default: disabled)])],
    [ ENABLED_ATOMICUSER=$enableval ],
    [ ENABLED_ATOMICUSER=no ]
    )

if test "$ENABLED_ATOMICUSER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DATOMIC_USER"
fi


# Public Key Callbacks
AC_ARG_ENABLE([pkcallbacks],
    [AS_HELP_STRING([--enable-pkcallbacks],[Enable Public Key Callbacks (default: disabled)])],
    [ ENABLED_PKCALLBACKS=$enableval ],
    [ ENABLED_PKCALLBACKS=no ]
    )

if test "$ENABLED_PKCALLBACKS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_PK_CALLBACKS"
fi


# Microchip/Atmel CryptoAuthLib
ENABLED_CRYPTOAUTHLIB="no"
trylibatcadir=""
AC_ARG_WITH([cryptoauthlib],
    [AS_HELP_STRING([--with-cryptoauthlib=PATH],[PATH to CryptoAuthLib install (default /usr/)])],
    [
        AC_MSG_CHECKING([for cryptoauthlib])
        CPPFLAGS="$CPPFLAGS -DWOLFSSL_ATECC508A"
        LIBS="$LIBS -lcryptoauth"

        AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <cryptoauthlib.h>]], [[ atcab_init(0); ]])],[ libatca_linked=yes ],[ libatca_linked=no ])

        if test "x$libatca_linked" = "xno" ; then
            if test "x$withval" != "xno" ; then
                trylibatcadir=$withval
            fi
            if test "x$withval" = "xyes" ; then
                trylibatcadir="/usr"
            fi

            LDFLAGS="$LDFLAGS -L$trylibatcadir/lib"
            CPPFLAGS="$CPPFLAGS -I$trylibatcadir/lib"

            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <cryptoauthlib.h>]], [[ atcab_init(0); ]])],[ libatca_linked=yes ],[ libatca_linked=no ])

            if test "x$libatca_linked" = "xno" ; then
                AC_MSG_ERROR([cryptoauthlib isn't found.
                If it's already installed, specify its path using --with-cryptoauthlib=/dir/])
            fi

            AM_LDFLAGS="$AM_LDFLAGS -L$trylibatcadir/lib"
            AM_CFLAGS="$AM_CFLAGS -I$trylibatcadir/lib"
            AC_MSG_RESULT([yes])
        else
            AC_MSG_RESULT([yes])
        fi

        ENABLED_CRYPTOAUTHLIB="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ATECC508A"
    ]
)


# sniffer doesn't work in maxstrength mode
if test "$ENABLED_SNIFFER" = "yes" && test "$ENABLED_MAXSTRENGTH" = "yes"
then
    AC_MSG_ERROR([cannot enable maxstrength in sniffer mode.])
fi

ENABLED_SNIFFTEST=no
AS_IF([ test "x$ENABLED_SNIFFER" = "xyes" ],
      [
          AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SNIFFER -DWOLFSSL_STATIC_EPHEMERAL"
          AC_CHECK_HEADERS([pcap/pcap.h],
              [ ENABLED_SNIFFTEST=yes ],
              [ AC_MSG_WARN([cannot enable sniffer test without having libpcap available.]) ]
          )
      ])


# AES-CBC
AC_ARG_ENABLE([aescbc],
    [AS_HELP_STRING([--enable-aescbc],[Enable wolfSSL AES-CBC support (default: enabled)])],
    [ ENABLED_AESCBC=$enableval ],
    [ ENABLED_AESCBC=yes ]
    )

if test "$ENABLED_AESCBC" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_AES_CBC"
fi

# leanpsk and leantls don't need gcm

# AES-GCM
AC_ARG_ENABLE([aesgcm],
    [AS_HELP_STRING([--enable-aesgcm],[Enable wolfSSL AES-GCM support (default: enabled)])],
    [ ENABLED_AESGCM=$enableval ],
    [ ENABLED_AESGCM=yes ]
    )

# leanpsk and leantls don't need gcm
if test "$ENABLED_LEANPSK" = "yes" || ( test "$ENABLED_LEANTLS" = "yes" &&
                                        test "$ENABLED_TLS13" = "no")
then
    ENABLED_AESGCM=no
fi

if test "$ENABLED_AESGCM" != "no"
then
    if test "$ENABLED_AESGCM" = "word32"
    then
        AM_CFLAGS="$AM_CFLAGS -DGCM_WORD32"
        ENABLED_AESGCM=yes
    fi

    if test "$ENABLED_AESGCM" = "small" || test "$ENABLED_LOWRESOURCE" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DGCM_SMALL"
        ENABLED_AESGCM=yes
    fi

    if test "$ENABLED_AESGCM" = "table"
    then
        AM_CFLAGS="$AM_CFLAGS -DGCM_TABLE"
        ENABLED_AESGCM=yes
    fi

    AM_CFLAGS="$AM_CFLAGS -DHAVE_AESGCM"
fi


# AES-CCM
AC_ARG_ENABLE([aesccm],
    [AS_HELP_STRING([--enable-aesccm],[Enable wolfSSL AES-CCM support (default: disabled)])],
    [ ENABLED_AESCCM=$enableval ],
    [ ENABLED_AESCCM=no ]
    )

if test "$ENABLED_AESCCM" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_AESCCM"
fi


# AES-CTR
AC_ARG_ENABLE([aesctr],
    [AS_HELP_STRING([--enable-aesctr],[Enable wolfSSL AES-CTR support (default: disabled)])],
    [ ENABLED_AESCTR=$enableval ],
    [ ENABLED_AESCTR=no ]
    )
if test "$ENABLED_OPENVPN" = "yes"
then
    ENABLED_AESCTR=yes
fi

if test "$ENABLED_AESCTR" = "yes"
then
    if test "x$ENABLED_FORTRESS" != "xyes"
    then
        # This is already implied by fortress build
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_COUNTER -DWOLFSSL_AES_DIRECT"
    fi
fi


# AES-OFB
AC_ARG_ENABLE([aesofb],
    [AS_HELP_STRING([--enable-aesofb],[Enable wolfSSL AES-OFB support (default: disabled)])],
    [ ENABLED_AESOFB=$enableval ],
    [ ENABLED_AESOFB=no ]
    )

if test "$ENABLED_AESOFB" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_OFB -DWOLFSSL_AES_DIRECT"
fi


# AES-CFB
AC_ARG_ENABLE([aescfb],
    [AS_HELP_STRING([--enable-aescfb],[Enable wolfSSL AES-CFB support (default: disabled)])],
    [ ENABLED_AESCFB=$enableval ],
    [ ENABLED_AESCFB=no ]
    )

if test "$ENABLED_AESCFB" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_CFB"
fi


# AES-ARM
AC_ARG_ENABLE([armasm],
    [AS_HELP_STRING([--enable-armasm],[Enable wolfSSL ARMv8 ASM support (default: disabled)])],
    [ ENABLED_ARMASM=$enableval ],
    [ ENABLED_ARMASM=no ]
    )
if test "$ENABLED_ARMASM" = "yes" && test "$ENABLED_ASM" = "yes"
then
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_ARMASM"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ARMASM -DWOLFSSL_NO_HASH_RAW"
    #Check if mcpu and mfpu values already set if not use default
    case $CPPFLAGS in
    *mcpu* | *mfpu*)
        break;; #Do not override user set values
    *)
        case $host_cpu in
        *aarch64*)
            # +crypto needed for hardware acceleration
            AM_CPPFLAGS="$AM_CPPFLAGS -mcpu=generic+crypto"
            # Include options.h
            AM_CCASFLAGS="$AM_CCASFLAGS -DEXTERNAL_OPTS_OPENVPN"

            # Check for and set -mstrict-align compiler flag
            # Used to set assumption that Aarch64 systems will not handle
            #   unaligned memory references. The flag -mstrict-align is needed
            #   on some compiler versions to avoid an invalid addressing mode
            #   error with  "m" constraint variables in the inline assembly AES
            #   code. Even though unaligned load/store access is permitted on
            #   normal memory with Cortex-A series boards with the exception
            #   being exclusive and ordered access.
            case $CPPFLAGS in
                *mstrict-align*)
                    break;; # already set by user
                *)
                    AM_CPPFLAGS="$AM_CPPFLAGS -mstrict-align"
                    AC_MSG_NOTICE([64bit ARMv8, setting -mstrict-align]);;
            esac
            AC_MSG_NOTICE([64bit ARMv8 found, setting mcpu to generic+crypto]);;
        *)
            AM_CPPFLAGS="$AM_CPPFLAGS -mfpu=crypto-neon-fp-armv8"
            # Include options.h
            AM_CCASFLAGS="$AM_CCASFLAGS -DEXTERNAL_OPTS_OPENVPN"
            AC_MSG_NOTICE([32bit ARMv8 found, setting mfpu to crypto-neon-fp-armv8]);;
        esac
    esac
fi


# Xilinx hardened crypto
AC_ARG_ENABLE([xilinx],
    [AS_HELP_STRING([--enable-xilinx],[Enable wolfSSL support for Xilinx hardened crypto(default: disabled)])],
    [ ENABLED_XILINX=$enableval ],
    [ ENABLED_XILINX=no ]
    )
if test "$ENABLED_XILINX" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_XILINX -DWOLFSSL_XILINX_CRYPT"
fi


# INTEL AES-NI
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

if test "$ENABLED_ASM" = "yes"
then
    if test "$ENABLED_AESNI" = "small"
    then
        AM_CFLAGS="$AM_CFLAGS -DAES_GCM_AESNI_NO_UNROLL"
        ENABLED_AESNI=yes
    fi

    if test "$ENABLED_AESNI" = "yes" || test "$ENABLED_INTELASM" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AESNI"
        if test "$GCC" = "yes"
        then
            # GCC needs these flags, icc doesn't
            # opt levels greater than 2 may cause problems on systems w/o aesni
            if test "$CC" != "icc"
            then
                AM_CFLAGS="$AM_CFLAGS -maes -msse4 -mpclmul"
            fi
        fi
        AS_IF([test "x$ENABLED_AESGCM" != "xno"],[AM_CCASFLAGS="$AM_CCASFLAGS -DHAVE_AESGCM"])
    fi

    if test "$ENABLED_INTELASM" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DHAVE_INTEL_RDSEED -DUSE_INTEL_SPEEDUP"
        ENABLED_AESNI=yes
    fi
fi

# INTEL RDRAND
AC_ARG_ENABLE([intelrand],
    [AS_HELP_STRING([--enable-intelrand],[Enable Intel rdrand as preferred RNG source (default: disabled)])],
    [ ENABLED_INTELRDRAND=$enableval ],
    [ ENABLED_INTELRDRAND=no ]
    )

if test "$ENABLED_INTELRDRAND" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_INTEL_RDRAND"
fi


# Linux af_alg
AC_ARG_ENABLE([afalg],
    [AS_HELP_STRING([--enable-afalg],[Enable Linux af_alg use for crypto (default: disabled)])],
    [ ENABLED_AFALG=$enableval ],
    [ ENABLED_AFALG=no ]
    )

if test "$ENABLED_AFALG" = "yes"
then
    if test "$ENABLED_AESCCM" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_DIRECT"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_HASH"
fi

if test "$ENABLED_AFALG" = "xilinx"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_XILINX -DWOLFSSL_AFALG_XILINX_AES"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_XILINX_SHA3 -DWOLFSSL_AFALG_XILINX_RSA"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_NOSHA3_224 -DWOLFSSL_NOSHA3_256 -DWOLFSSL_NOSHA3_512 -DWOLFSSL_NO_SHAKE256"
    ENABLED_AFALG="yes"
    ENABLED_XILINX="yes"
fi

if test "$ENABLED_AFALG" = "xilinx-aes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_XILINX -DWOLFSSL_AFALG_XILINX_AES"
    ENABLED_AFALG="yes"
    ENABLED_XILINX="yes"
fi

if test "$ENABLED_AFALG" = "xilinx-sha3"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_XILINX"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_XILINX_SHA3"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_NOSHA3_224 -DWOLFSSL_NOSHA3_256 -DWOLFSSL_NOSHA3_512 -DWOLFSSL_NO_SHAKE256"
    ENABLED_AFALG="yes"
    ENABLED_XILINX="yes"
fi

if test "$ENABLED_AFALG" = "xilinx-rsa"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_XILINX"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_XILINX_RSA"
    ENABLED_AFALG="yes"
    ENABLED_XILINX="yes"
fi


# Support for Linux dev/crypto calls
AC_ARG_ENABLE([devcrypto],
    [AS_HELP_STRING([--enable-devcrypto],[Enable Linux dev crypto calls: all | aes (all aes support) | hash (all hash algos) | cbc (aes-cbc only) (default: disabled)])],
    [ ENABLED_DEVCRYPTO=$enableval ],
    [ ENABLED_DEVCRYPTO=no ]
    )

if test "$ENABLED_DEVCRYPTO" = "yes" || test "$ENABLED_DEVCRYPTO" = "all"
then
    #enable all devcrypto supported algorithms
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_CBC"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_AES"
    if test "$ENABLED_AESCCM" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_DIRECT"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_HASH"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_NO_HASH_RAW"
    ENABLED_DEVCRYPTO=yes
fi
if test "$ENABLED_DEVCRYPTO" = "aes"
then
    #enable only AES-CBC algorithm support
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_AES"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_CBC"
    if test "$ENABLED_AESCCM" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_DIRECT"
    fi
    ENABLED_DEVCRYPTO=yes
fi
if test "$ENABLED_DEVCRYPTO" = "cbc"
then
    #enable only AES-CBC algorithm support
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_CBC"
    ENABLED_DEVCRYPTO=yes
fi
if test "$ENABLED_DEVCRYPTO" = "hash"
then
    #enable only hash algorithm support
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_HASH"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_NO_HASH_RAW"
    ENABLED_DEVCRYPTO=yes
fi


# Camellia
AC_ARG_ENABLE([camellia],
    [AS_HELP_STRING([--enable-camellia],[Enable wolfSSL Camellia support (default: disabled)])],
    [ ENABLED_CAMELLIA=$enableval ],
    [ ENABLED_CAMELLIA=no ]
    )

if test "$ENABLED_CAMELLIA" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CAMELLIA"
fi


# MD2
AC_ARG_ENABLE([md2],
    [AS_HELP_STRING([--enable-md2],[Enable wolfSSL MD2 support (default: disabled)])],
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


# NULL CIPHER
AC_ARG_ENABLE([nullcipher],
    [AS_HELP_STRING([--enable-nullcipher],[Enable wolfSSL NULL cipher support (default: disabled)])],
    [ ENABLED_NULL_CIPHER=$enableval ],
    [ ENABLED_NULL_CIPHER=no ]
    )

if test "$ENABLED_OPENSSH" = "yes"
then
    ENABLED_NULL_CIPHER="yes"
fi

if test "$ENABLED_NULL_CIPHER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_NULL_CIPHER"
fi

# RIPEMD
AC_ARG_ENABLE([ripemd],
    [AS_HELP_STRING([--enable-ripemd],[Enable wolfSSL RIPEMD-160 support (default: disabled)])],
    [ ENABLED_RIPEMD=$enableval ],
    [ ENABLED_RIPEMD=no ]
    )

if test "$ENABLED_OPENSSH" = "yes"
then
    ENABLED_RIPEMD="yes"
fi

if test "$ENABLED_RIPEMD" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_RIPEMD"
fi


# BLAKE2
AC_ARG_ENABLE([blake2],
    [AS_HELP_STRING([--enable-blake2],[Enable wolfSSL BLAKE2b support (default: disabled)])],
    [ ENABLED_BLAKE2=$enableval ],
    [ ENABLED_BLAKE2=no ]
    )

if test "$ENABLED_BLAKE2" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_BLAKE2 -DHAVE_BLAKE2B"
fi


AC_ARG_ENABLE([blake2s],
    [AS_HELP_STRING([--enable-blake2s],[Enable wolfSSL BLAKE2s support (default: disabled)])],
    [ ENABLED_BLAKE2S=$enableval ],
    [ ENABLED_BLAKE2S=Sno ]
    )

if test "$ENABLED_BLAKE2S" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_BLAKE2S"
    ENABLED_BLAKE2="yes"
fi


# SHA512
AC_ARG_ENABLE([sha512],
    [AS_HELP_STRING([--enable-sha512],[Enable wolfSSL SHA-512 support (default: enabled)])],
    [ ENABLED_SHA512=$enableval ],
    [ ENABLED_SHA512=yes ]
    )

# options that don't require sha512
if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes" || test "$ENABLED_32BIT" = "yes" || test "$ENABLED_16BIT" = "yes"
then
    ENABLED_SHA512="no"
fi

# options that require sha512
if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_WPAS" = "yes" || test "$ENABLED_FORTRESS" = "yes"
then
    ENABLED_SHA512="yes"
    ENABLED_SHA384="yes"
fi

if test "$ENABLED_SHA512" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA512"
fi


# SHA384
AC_ARG_ENABLE([sha384],
    [AS_HELP_STRING([--enable-sha384],[Enable wolfSSL SHA-384 support (default: enabled)])],
    [ ENABLED_SHA384=$enableval ],
    [ ENABLED_SHA384=yes ]
    )

# options that don't require sha384
if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes" || test "$ENABLED_32BIT" = "yes" || test "$ENABLED_16BIT" = "yes"
then
    ENABLED_SHA384="no"
fi

# options that require sha384
if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_WPAS" = "yes" || test "$ENABLED_FORTRESS" = "yes"
then
    ENABLED_SHA384="yes"
fi
if test "$ENABLED_SHA384" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA384"
fi


# SESSION CERTS
AC_ARG_ENABLE([sessioncerts],
    [AS_HELP_STRING([--enable-sessioncerts],[Enable session cert storing (default: disabled)])],
    [ ENABLED_SESSIONCERTS=$enableval ],
    [ ENABLED_SESSIONCERTS=no ]
    )

if test "x$ENABLED_NGINX" = "xyes" || test "x$ENABLED_OPENVPN" = "xyes"
then
    ENABLED_SESSIONCERTS=yes
fi
if test "$ENABLED_TLS13" = "yes" && test "$ENABLED_PSK" = "yes"
then
    ENABLED_SESSIONCERTS=yes
fi

if test "$ENABLED_SESSIONCERTS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DSESSION_CERTS"
fi


# KEY GENERATION
AC_ARG_ENABLE([keygen],
    [AS_HELP_STRING([--enable-keygen],[Enable key generation (default: disabled)])],
    [ ENABLED_KEYGEN=$enableval ],
    [ ENABLED_KEYGEN=no ]
    )

if test "$ENABLED_KEYGEN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_KEY_GEN"
fi


# CERT GENERATION
AC_ARG_ENABLE([certgen],
    [AS_HELP_STRING([--enable-certgen],[Enable cert generation (default: disabled)])],
    [ ENABLED_CERTGEN=$enableval ],
    [ ENABLED_CERTGEN=no ]
    )
if test "$ENABLED_OPENVPN" = "yes" || test "$ENABLED_OPENSSH" = "yes"
then
    ENABLED_CERTGEN=yes
fi

if test "$ENABLED_CERTGEN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN"
fi


# CERT REQUEST GENERATION
AC_ARG_ENABLE([certreq],
    [AS_HELP_STRING([--enable-certreq],[Enable cert request generation (default: disabled)])],
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


# CERT REQUEST EXTENSION
AC_ARG_ENABLE([certext],
    [AS_HELP_STRING([--enable-certext],[Enable cert request extensions (default: disabled)])],
    [ ENABLED_CERTEXT=$enableval ],
    [ ENABLED_CERTEXT=no ]
    )
if test "$ENABLED_OPENVPN" = "yes"
then
    ENABLED_CERTEXT=yes
fi

if test "$ENABLED_CERTEXT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_EXT"
fi


# DECODED CERT CACHE
AC_ARG_ENABLE([certgencache],
    [AS_HELP_STRING([--enable-certgencache],[Enable decoded cert caching (default: disabled)])],
    [ ENABLED_certgencache=$enableval ],
    [ ENABLED_certgencache=no ]
    )

if test "$ENABLED_certgencache" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN_CACHE"
fi


# SEP
AC_ARG_ENABLE([sep],
    [AS_HELP_STRING([--enable-sep],[Enable sep extensions (default: disabled)])],
    [ ENABLED_SEP=$enableval ],
    [ ENABLED_SEP=no ]
    )
if test "$ENABLED_SEP" = "yes"
then
  AM_CFLAGS="-DWOLFSSL_SEP -DKEEP_PEER_CERT $AM_CFLAGS"
fi


# HKDF
AC_ARG_ENABLE([hkdf],
    [AS_HELP_STRING([--enable-hkdf],[Enable HKDF (HMAC-KDF) support (default: disabled)])],
    [ ENABLED_HKDF=$enableval ],
    [ ENABLED_HKDF=no ]
    )
if test "$ENABLED_TLS13" = "yes"
then
  ENABLED_HKDF="yes"
fi
if test "$ENABLED_HKDF" = "yes"
then
  AM_CFLAGS="$AM_CFLAGS -DHAVE_HKDF"
fi

# X9.63 KDF
AC_ARG_ENABLE([x963kdf],
    [AS_HELP_STRING([--enable-x963kdf],[Enable X9.63 KDF support (default: disabled)])],
    [ ENABLED_X963KDF=$enableval ],
    [ ENABLED_X963KDF=no ]
    )
if test "$ENABLED_X963KDF" = "yes"
then
  AM_CFLAGS="$AM_CFLAGS -DHAVE_X963_KDF"
fi

# DSA
AC_ARG_ENABLE([dsa],
    [AS_HELP_STRING([--enable-dsa],[Enable DSA (default: disabled)])],
    [ ENABLED_DSA=$enableval ],
    [ ENABLED_DSA=no ]
    )

if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_OPENVPN" = "yes" || test "$ENABLED_NGINX" = "yes" || test "$ENABLED_WPAS" = "yes" || test "$ENABLED_QT" = "yes"
then
    ENABLED_DSA="yes"
fi

if test "$ENABLED_DSA" = "no" && test "$ENABLED_OPENSSH" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_DSA"
fi

# ECC Shamir
AC_ARG_ENABLE([eccshamir],
    [AS_HELP_STRING([--enable-eccshamir],[Enable ECC Shamir (default: enabled)])],
    [ ENABLED_ECC_SHAMIR=$enableval ],
    [ ENABLED_ECC_SHAMIR=yes ]
    )


# ECC
AC_ARG_ENABLE([ecc],
    [AS_HELP_STRING([--enable-ecc],[Enable ECC (default: enabled)])],
    [ ENABLED_ECC=$enableval ],
    [ ENABLED_ECC=yes ]
    )

# lean psk doesn't need ecc
if test "$ENABLED_LEANPSK" = "yes"
then
    ENABLED_ECC=no
fi

if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_NGINX" = "yes" || test "$ENABLED_SIGNAL" = "yes"
then
    ENABLED_ECC="yes"
fi

if test "$ENABLED_ECC" != "no"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC -DTFM_ECC256"
    if test "$ENABLED_ECC_SHAMIR" = "yes" && test "$ENABLED_LOWRESOURCE" = "no"
    then
        AM_CFLAGS="$AM_CFLAGS -DECC_SHAMIR"
    fi

    if test "$ENABLED_ECC" = "nonblock"
    then
        AM_CFLAGS="$AM_CFLAGS -DWC_ECC_NONBLOCK"
    fi
fi


# ECC Custom Curves
AC_ARG_ENABLE([ecccustcurves],
    [AS_HELP_STRING([--enable-ecccustcurves],[Enable ECC custom curves (default: disabled)])],
    [ ENABLED_ECCCUSTCURVES=$enableval ],
    [ ENABLED_ECCCUSTCURVES=no ]
    )

if test "$ENABLED_ECCCUSTCURVES" != "no"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CUSTOM_CURVES"

    # For distro, all or ecccustcurves=all builds, enable all curve types
    if test "$ENABLED_DISTRO" = "yes" || test "$ENABLED_ALL" = "yes" || test "$ENABLED_ECCCUSTCURVES" = "all"
    then
        # Enable ECC SECPR2, SECPR3, BRAINPOOL and KOBLITZ curves
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC_SECPR2 -DHAVE_ECC_SECPR3 -DHAVE_ECC_BRAINPOOL -DHAVE_ECC_KOBLITZ"

        # Enable ECC Cofactor support
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC_CDH"

        # If fastmath enabled and on x86 use speedups
        if test "x$ENABLED_FASTMATH" = "xyes" && test "$host_cpu" = "x86_64"
        then
            AM_CFLAGS="$AM_CFLAGS -DTFM_ECC192 -DTFM_ECC224 -DTFM_ECC256 -DTFM_ECC384 -DTFM_ECC521"
        fi
    fi
fi


# Compressed Key
AC_ARG_ENABLE([compkey],
    [AS_HELP_STRING([--enable-compkey],[Enable compressed keys support (default: disabled)])],
    [ ENABLED_COMPKEY=$enableval ],
    [ ENABLED_COMPKEY=no ]
    )

if test "$ENABLED_WPAS" = "yes"
then
    ENABLED_COMPKEY=yes
fi
if test "$ENABLED_COMPKEY" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_COMP_KEY"
fi


# for using memory optimization setting on both curve25519 and ed25519
ENABLED_CURVE25519_SMALL=no
ENABLED_ED25519_SMALL=no

# CURVE25519
AC_ARG_ENABLE([curve25519],
    [AS_HELP_STRING([--enable-curve25519],[Enable Curve25519 (default: disabled)])],
    [ ENABLED_CURVE25519=$enableval ],
    [ ENABLED_CURVE25519=no ]
    )


if test "$ENABLED_OPENSSH" = "yes"
then
    ENABLED_CURVE25519="yes"
fi

if test "$ENABLED_CURVE25519" != "no"
then
    if test "$ENABLED_CURVE25519" = "small" || test "$ENABLED_LOWRESOURCE" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DCURVE25519_SMALL"
        ENABLED_CURVE25519_SMALL=yes
        ENABLED_CURVE25519=yes
    fi

    if test "$ENABLED_CURVE25519" = "no128bit" || test "$ENABLED_32BIT" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_CURVED25519_128BIT"
        ENABLED_CURVE25519=yes
    fi

    AM_CFLAGS="$AM_CFLAGS -DHAVE_CURVE25519"
    ENABLED_FEMATH=yes
fi


# ED25519
AC_ARG_ENABLE([ed25519],
    [AS_HELP_STRING([--enable-ed25519],[Enable ED25519 (default: disabled)])],
    [ ENABLED_ED25519=$enableval ],
    [ ENABLED_ED25519=no ]
    )


if test "$ENABLED_OPENSSH" = "yes"
then
    ENABLED_ED25519="yes"
fi

if test "$ENABLED_ED25519" != "no" && test "$ENABLED_32BIT" = "no"
then
    if test "$ENABLED_ED25519" = "small" || test "$ENABLED_LOWRESOURCE" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DED25519_SMALL"
        ENABLED_ED25519_SMALL=yes
        ENABLED_CURVE25519_SMALL=yes
        ENABLED_ED25519=yes
    fi

    if test "$ENABLED_SHA512" = "no"
    then
        AC_MSG_ERROR([cannot enable ed25519 without enabling sha512.])
    fi
    ENABLED_FEMATH=yes
    ENABLED_GEMATH=yes
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ED25519"
fi


# for using memory optimization setting on both curve448 and ed448
ENABLED_CURVE448_SMALL=no
ENABLED_ED448_SMALL=no

# CURVE448
AC_ARG_ENABLE([curve448],
    [AS_HELP_STRING([--enable-curve448],[Enable Curve448 (default: disabled)])],
    [ ENABLED_CURVE448=$enableval ],
    [ ENABLED_CURVE448=no ]
    )

if test "$ENABLED_CURVE448" != "no"
then
    if test "$ENABLED_CURVE448" = "small" || test "$ENABLED_LOWRESOURCE" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DCURVE448_SMALL"
        ENABLED_CURVE448_SMALL=yes
        ENABLED_CURVE448=yes
    fi

    if test "$ENABLED_CURVE448" = "no128bit" || test "$ENABLED_32BIT" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_CURVED448_128BIT"
        ENABLED_CURVE448=yes
    fi

    AM_CFLAGS="$AM_CFLAGS -DHAVE_CURVE448"
    ENABLED_FE448=yes
fi

# ED448
AC_ARG_ENABLE([ed448],
    [AS_HELP_STRING([--enable-ed448],[Enable ED448 (default: disabled)])],
    [ ENABLED_ED448=$enableval ],
    [ ENABLED_ED448=no ]
    )

if test "$ENABLED_ED448" != "no" && test "$ENABLED_32BIT" = "no"
then
    if test "$ENABLED_ED448" = "small" || test "$ENABLED_LOWRESOURCE" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DED448_SMALL"
        ENABLED_ED448_SMALL=yes
        ENABLED_CURVE448_SMALL=yes
        ENABLED_ED448=yes
    fi

    if test "$ENABLED_SHA512" = "no"
    then
        AC_MSG_ERROR([cannot enable ed448 without enabling sha512.])
    fi
    ENABLED_FE448=yes
    ENABLED_GE448=yes
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ED448"

    # EdDSA448 requires SHAKE256 which requires SHA-3
    ENABLED_SHAKE3=yes
    ENABLED_SHAKE256=yes
fi



# FP ECC, Fixed Point cache ECC
AC_ARG_ENABLE([fpecc],
    [AS_HELP_STRING([--enable-fpecc],[Enable Fixed Point cache ECC (default: disabled)])],
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
    [AS_HELP_STRING([--enable-eccencrypt],[Enable ECC encrypt (default: disabled)])],
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
    [AS_HELP_STRING([--enable-psk],[Enable PSK (default: disabled)])],
    [ ENABLED_PSK=$enableval ],
    [ ENABLED_PSK=no ]
    )

# Single PSK identity
AC_ARG_ENABLE([psk-one-id],
    [AS_HELP_STRING([--enable-psk-one-id],[Enable PSK (default: disabled)])],
    [ ENABLED_PSK_ONE_ID=$enableval ],
    [ ENABLED_PSK_ONE_ID=no ]
    )
if test "$ENABLED_PSK_ONE_ID" = "yes"
then
    if test "$ENABLED_PSK" = "no"
    then
        ENABLED_PSK="yes"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_PSK_ONE_ID"
fi

# ERROR STRINGS
AC_ARG_ENABLE([errorstrings],
    [AS_HELP_STRING([--enable-errorstrings],[Enable error strings table (default: enabled)])],
    [ ENABLED_ERROR_STRINGS=$enableval ],
    [ ENABLED_ERROR_STRINGS=yes ]
    )

if test "$ENABLED_ERROR_STRINGS" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_ERROR_STRINGS"
else
    # turn off error strings if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_ERROR_STRINGS"
        ENABLED_ERROR_STRINGS=no
    fi
fi


# ERROR QUEUE
AC_ARG_ENABLE([errorqueue],
    [AS_HELP_STRING([--disable-errorqueue],[Disables adding nodes to error queue when compiled with OPENSSL_EXTRA (default: enabled)])],
    [ ENABLED_ERROR_QUEUE=$enableval ],
    [ ENABLED_ERROR_QUEUE=yes ]
    )

if test "$ENABLED_ERROR_QUEUE" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_ERROR_QUEUE"
fi


# OLD TLS
AC_ARG_ENABLE([oldtls],
    [AS_HELP_STRING([--enable-oldtls],[Enable old TLS versions < 1.2 (default: enabled)])],
    [ ENABLED_OLD_TLS=$enableval ],
    [ ENABLED_OLD_TLS=yes ]
    )

if test "$ENABLED_OLD_TLS" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_OLD_TLS"
else
    # turn off old if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_OLD_TLS"
        ENABLED_OLD_TLS=no
    fi
fi


# TLSv1.2
AC_ARG_ENABLE([tlsv12],
    [AS_HELP_STRING([--enable-tlsv12],[Enable TLS versions 1.2 (default: enabled)])],
    [ ENABLED_TLSV12=$enableval ],
    [ ENABLED_TLSV12=yes ]
    )

if test "$ENABLED_TLSV12" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_NO_TLS12 -DNO_OLD_TLS"
fi


# TLSv1.0
AC_ARG_ENABLE([tlsv10],
    [AS_HELP_STRING([--enable-tlsv10],[Enable old TLS versions 1.0 (default: disabled)])],
    [ ENABLED_TLSV10=$enableval ],
    [ ENABLED_TLSV10=no ]
    )

if test "$ENABLED_TLSV10" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALLOW_TLSV10"
fi


# SSLv3
AC_ARG_ENABLE([sslv3],
    [AS_HELP_STRING([--enable-sslv3],[Enable SSL version 3.0 (default: disabled)])],
    [ ENABLED_SSLV3=$enableval ],
    [ ENABLED_SSLV3=no]
    )

if test "x$ENABLED_HAPROXY" = "xyes" && test "x$ENABLED_ALL" = "xno"
then
    ENABLED_SSLV3="yes"
fi

if test "$ENABLED_SSLV3" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALLOW_SSLV3"
fi


# STACK SIZE info for examples
AC_ARG_ENABLE([stacksize],
    [AS_HELP_STRING([--enable-stacksize],[Enable stack size info on examples (default: disabled)])],
    [ ENABLED_STACKSIZE=$enableval ],
    [ ENABLED_STACKSIZE=no ]
    )

if test "$ENABLED_STACKSIZE" = "yes"
then
    AC_CHECK_FUNC([posix_memalign], [], [AC_MSG_ERROR(stacksize needs posix_memalign)])
    AC_CHECK_FUNC([pthread_attr_setstack], [], AC_CHECK_LIB([pthread],[pthread_attr_setstack]))
    AM_CFLAGS="$AM_CFLAGS -DHAVE_STACK_SIZE"
fi


# MEMORY
AC_ARG_ENABLE([memory],
    [AS_HELP_STRING([--enable-memory],[Enable memory callbacks (default: enabled)])],
    [ ENABLED_MEMORY=$enableval ],
    [ ENABLED_MEMORY=yes ]
    )

if test "$ENABLED_MEMORY" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_WOLFSSL_MEMORY"
else
    # turn off memory cb if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        # but don't turn on NO_WOLFSSL_MEMORY because using own
        ENABLED_MEMORY=no
    fi
fi


# MEMORY SIZE info
AC_ARG_ENABLE([trackmemory],
    [AS_HELP_STRING([--enable-trackmemory],[Enable memory use info on wolfCrypt and wolfSSL cleanup (default: disabled)])],
    [ ENABLED_TRACKMEMORY=$enableval ],
    [ ENABLED_TRACKMEMORY=no ]
    )

if test "$ENABLED_TRACKMEMORY" = "yes"
then
    if test "$ENABLED_MEMORY" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_TRACK_MEMORY"
    else
        AC_MSG_ERROR([trackmemory requires using wolfSSL memory (--enable-memory).])
    fi
fi

# MEMORY usage logging
AC_ARG_ENABLE([memorylog],
    [AS_HELP_STRING([--enable-memorylog],[Enable dynamic memory logging (default: disabled)])],
    [ ENABLED_MEMORYLOG=$enableval ],
    [ ENABLED_MEMORYLOG=no ]
    )

if test "$ENABLED_MEMORYLOG" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_MEMORY_LOG"
fi


# STACK usage logging
AC_ARG_ENABLE([stacklog],
    [AS_HELP_STRING([--enable-stacklog],[Enable stack logging (default: disabled)])],
    [ ENABLED_STACKLOG=$enableval ],
    [ ENABLED_STACKLOG=no ]
    )

if test "$ENABLED_STACKLOG" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_STACK_LOG -finstrument-functions"
fi

if test "$ENABLED_QT" = "yes"
then
    # Requires opensslextra and opensslall
    if test "x$ENABLED_OPENSSLALL" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLALL="yes"
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="$AM_CFLAGS -DOPENSSL_EXTRA -DOPENSSL_ALL -DHAVE_EX_DATA"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_QT -DSESSION_CERTS -DOPENSSL_NO_SSL2"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_KEY_GEN -DHAVE_EX_DATA"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CUSTOM_CURVES -DHAVE_ECC_SECPR2 -DHAVE_ECC_SECPR3 -DHAVE_ECC_BRAINPOOL -DHAVE_ECC_KOBLITZ"
    if test "x$ENABLED_ALL" = "xno"; then
        # Don't enable old SSL/TLS for --enable-all, which is used by distro
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALLOW_SSLV3 -DWOLFSSL_ALLOW_TLSV10"
    fi

    # Requires OCSP make sure on
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
    fi

    # Requires PSK make sure on
    if test "x$ENABLED_PSK" = "xno"
    then
       ENABLED_PSK="yes"
    fi

    # Requires RC4 make sure on
    if test "x$ENABLED_ARC4" = "xno"
    then
       ENABLED_ARC4="yes"
    fi

    if test "x$ENABLED_CERTEXT" = "xno"
    then
        ENABLED_CERTEXT="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_EXT"
    fi

    if test "x$ENABLED_CERTGEN" = "xno"
    then
        ENABLED_CERTGEN="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN"
    fi

    # requires oldnames disabled
    enable_oldnames=no
fi

AC_ARG_ENABLE([qt-test],
    [AS_HELP_STRING([--enable-qt-test],[Enable qt tests (default: disabled)])],
    [ ENABLED_QT_TEST=$enableval ],
    [ ENABLED_QT_TEST=no ]
    )

if test "$ENABLED_QT_TEST" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DOPENSSL_NO_SSL3 -DWOLFSSL_STATIC_RSA"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_STATIC_PSK"
fi

# RSA
AC_ARG_ENABLE([rsa],
    [AS_HELP_STRING([--enable-rsa],[Enable RSA (default: enabled)])],
    [ ENABLED_RSA=$enableval ],
    [ ENABLED_RSA=yes ]
    )

if test "$ENABLED_RSA" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_RSA"
else
    # turn off RSA if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_RSA"
        ENABLED_RSA=no
    fi
fi

AC_ARG_ENABLE([oaep],
    [AS_HELP_STRING([--enable-oaep],[Enable RSA OAEP (default: enabled)])],
    [ ENABLED_OAEP=$enableval ],
    [ ENABLED_OAEP=yes ]
    )

if test "$ENABLED_OAEP" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DWC_NO_RSA_OAEP"
fi

AC_ARG_ENABLE([rsapub],
    [AS_HELP_STRING([--enable-rsapub],[Enable RSA Public Only (default: disabled)])],
    [ ENABLED_RSAPUB=$enableval ],
    [ ENABLED_RSAPUB=no ]
    )

if test "$ENABLED_RSAPUB" = "yes"
then
    if test "$ENABLED_RSA" = "no"
    then
        ENABLED_RSA="yes"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_RSA_PUBLIC_ONLY"
fi

AC_ARG_ENABLE([rsavfy],
    [AS_HELP_STRING([--enable-rsavfy],[Enable RSA Verify Inline Only (default: disabled)])],
    [ ENABLED_RSAVFY=$enableval ],
    [ ENABLED_RSAVFY=no ]
    )

if test "$ENABLED_RSAVFY" = "yes"
then
    if test "$ENABLED_RSA" = "no"
    then
        ENABLED_RSA="yes"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_RSA_PUBLIC_ONLY -DWOLFSSL_RSA_VERIFY_ONLY"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_RSA_VERIFY_INLINE -DNO_SIG_WRAPPER"
fi


# RSA-PSS
AC_ARG_ENABLE([rsapss],
    [  --enable-rsapss         Enable RSA-PSS (default: disabled)],
    [ ENABLED_RSAPSS=$enableval ],
    [ ENABLED_RSAPSS=no ]
    )

if test "$ENABLED_RSA" = "no"
then
    ENABLED_RSAPSS="no"
else
    if test "$ENABLED_TLS13" = "yes"
    then
        ENABLED_RSAPSS="yes"
    fi
fi
if test "$ENABLED_RSAPSS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWC_RSA_PSS"
fi


# DH
AC_ARG_ENABLE([dh],
    [AS_HELP_STRING([--enable-dh],[Enable DH (default: enabled)])],
    [ ENABLED_DH=$enableval ],
    [ ENABLED_DH=yes ]
    )

if test "$ENABLED_OPENSSH" = "yes"
then
    ENABLED_DH="yes"
fi

if test "$ENABLED_DH" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_DH"
else
    # turn off DH if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_DH"
        ENABLED_DH=no
    fi
fi


# Anonymous
AC_ARG_ENABLE([anon],
    [AS_HELP_STRING([--enable-anon],[Enable Anonymous (default: disabled)])],
    [ ENABLED_ANON=$enableval ],
    [ ENABLED_ANON=no ]
    )

if test "x$ENABLED_WPAS" = "xyes"
then
    ENABLED_ANON=yes
fi
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
    [AS_HELP_STRING([--enable-asn],[Enable ASN (default: enabled)])],
    [ ENABLED_ASN=$enableval ],
    [ ENABLED_ASN=yes ]
    )

if test "$ENABLED_ASN" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_ASN -DNO_CERTS"
    if test "$ENABLED_DH" = "no" && test "$ENABLED_ECC" = "no"
    then
        # DH and ECC need bigint
        AM_CFLAGS="$AM_CFLAGS -DNO_BIG_INT"
    fi
else
    # turn off ASN if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_ASN -DNO_CERTS -DNO_BIG_INT"
        ENABLED_ASN=no
    else
        if test "$ENABLED_ASN" = "nocrypt"
        then
            AM_CFLAGS="$AM_CFLAGS -DNO_ASN_CRYPT"
            enable_pwdbased=no
        fi
    fi
fi

if test "$ENABLED_RSA" = "yes" && test "$ENABLED_RSAVFY" = "no" && test "$ENABLED_ASN" = "no"
then
    AC_MSG_ERROR([please disable rsa if disabling asn.])
fi

if test "$ENABLED_DSA" = "yes" && test "$ENABLED_ASN" = "no"
then
    AC_MSG_ERROR([please disable dsa if disabling asn.])
fi

# DH and ECC need bigint
if test "$ENABLED_ASN" = "no" && test "$ENABLED_DH" = "no" && test "$ENABLED_ECC" = "no" && test "$ENABLED_RSA" = "no"
then
    ENABLED_FASTMATH=no
    ENABLED_SLOWMATH=no
fi


# AES
AC_ARG_ENABLE([aes],
    [AS_HELP_STRING([--enable-aes],[Enable AES (default: enabled)])],
    [ ENABLED_AES=$enableval ],
    [ ENABLED_AES=yes ]
    )

if test "$ENABLED_AES" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_AES"
    if test "$ENABLED_FORTRESS" = "yes"
    then
        AC_MSG_ERROR([fortress requires aes])
    fi
    if test "$ENABLED_ECC_ENCRYPT" = "yes"
    then
        AC_MSG_ERROR([cannot enable eccencrypt and hkdf without aes.])
    fi
    if test "$ENABLED_AESGCM" = "yes"
    then
        AC_MSG_ERROR([AESGCM requires AES.])
    fi
    if test "$ENABLED_AESCCM" = "yes"
    then
        AC_MSG_ERROR([AESCCM requires AES.])
    fi
    if test "$ENABLED_AESCTR" = "yes"
    then
        AC_MSG_ERROR([AESCTR requires AES.])
    fi
else
    # turn off AES if leanpsk on
    if test "$ENABLED_LEANPSK" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_AES"
        ENABLED_AES=no
    fi
fi


# CODING
AC_ARG_ENABLE([coding],
    [AS_HELP_STRING([--enable-coding],[Enable Coding base 16/64 (default: enabled)])],
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


# Base64 Encode
BASE64ENCODE_DEFAULT=no
if test "$host_cpu" = "x86_64"
then
BASE64ENCODE_DEFAULT=yes
fi
AC_ARG_ENABLE([base64encode],
    [AS_HELP_STRING([--enable-base64encode],[Enable Base64 encoding (default: enabled on x86_64)])],
    [ ENABLED_BASE64ENCODE=$enableval ],
    [ ENABLED_BASE64ENCODE=$BASE64ENCODE_DEFAULT ]
    )
if test "$ENABLED_BASE64ENCODE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_BASE64_ENCODE"
fi


# Base16
AC_ARG_ENABLE([base16],
    [AS_HELP_STRING([--enable-base16],[Enable Base16 encoding/decoding (default: disabled)])],
    [ ENABLED_BASE16=$enableval ],
    [ ENABLED_BASE16=no ]
    )
if test "$ENABLED_BASE16" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_BASE16"
fi


# DES3
AC_ARG_ENABLE([des3],
    [AS_HELP_STRING([--enable-des3],[Enable DES3 (default: disabled)])],
    [ ENABLED_DES3=$enableval ],
    [ ENABLED_DES3=no ]
    )

if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_QT" = "yes" || test "$ENABLED_OPENVPN" = "yes"
then
    ENABLED_DES3="yes"
fi

# IDEA
AC_ARG_ENABLE([idea],
    [AS_HELP_STRING([--enable-idea],[Enable IDEA Cipher (default: disabled)])],
    [ ENABLED_IDEA=$enableval ],
    [ ENABLED_IDEA=no ]
    )

if test "x$ENABLED_IDEA" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_IDEA"
fi

# ARC4
AC_ARG_ENABLE([arc4],
    [AS_HELP_STRING([--enable-arc4],[Enable ARC4 (default: disabled)])],
    [ ENABLED_ARC4=$enableval ],
    [ ENABLED_ARC4=no ]
    )

if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_WPAS" = "yes"
then
    ENABLED_ARC4="yes"
fi

if test "$ENABLED_ARC4" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_RC4"
else
    # turn off ARC4 if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_RC4"
        ENABLED_ARC4=no
    fi
fi

# MD5
AC_ARG_ENABLE([md5],
    [AS_HELP_STRING([--enable-md5],[Enable MD5 (default: enabled)])],
    [ ENABLED_MD5=$enableval ],
    [ ENABLED_MD5=yes ]
    )

if test "$ENABLED_MD5" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_MD5 -DNO_OLD_TLS"
else
    # turn off MD5 if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_MD5 -DNO_OLD_TLS"
        ENABLED_MD5=no
    fi
fi


# SHA
AC_ARG_ENABLE([sha],
    [AS_HELP_STRING([--enable-sha],[Enable SHA (default: enabled)])],
    [ ENABLED_SHA=$enableval ],
    [ ENABLED_SHA=yes ]
    )

if test "$ENABLED_SHA" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_SHA -DNO_OLD_TLS"
else
    # turn off SHA if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_SHA -DNO_OLD_TLS"
        ENABLED_SHA=no
    fi
fi


# CMAC
AC_ARG_ENABLE([cmac],
    [AS_HELP_STRING([--enable-cmac],[Enable CMAC (default: disabled)])],
    [ ENABLED_CMAC=$enableval ],
    [ ENABLED_CMAC=no ]
    )

if test "$ENABLED_WPAS" = "yes"
then
    ENABLED_CMAC=yes
fi

AS_IF([test "x$ENABLED_CMAC" = "xyes"],
      [AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CMAC -DWOLFSSL_AES_DIRECT"])


# AES-XTS
AC_ARG_ENABLE([xts],
    [AS_HELP_STRING([--enable-xts],[Enable XTS (default: disabled)])],
    [ ENABLED_XTS=$enableval ],
    [ ENABLED_XTS=no ]
    )

AS_IF([test "x$ENABLED_XTS" = "xyes"],
      [AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_XTS -DWOLFSSL_AES_DIRECT"])


# Web Server Build
AC_ARG_ENABLE([webserver],
    [AS_HELP_STRING([--enable-webserver],[Enable Web Server (default: disabled)])],
    [ ENABLED_WEBSERVER=$enableval ],
    [ ENABLED_WEBSERVER=no ]
    )

if test "$ENABLED_WEBSERVER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_WEBSERVER"
fi

# Web Client Build (HTTP Client)
AC_ARG_ENABLE([webclient],
    [AS_HELP_STRING([--enable-webclient],[Enable Web Client (HTTP) (default: disabled)])],
    [ ENABLED_WEBCLIENT=$enableval ],
    [ ENABLED_WEBCLIENT=no ]
    )

if test "$ENABLED_WEBCLIENT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_HTTP_CLIENT"
fi


# HC128
AC_ARG_ENABLE([hc128],
    [AS_HELP_STRING([--enable-hc128],[Enable HC-128 (default: disabled)])],
    [ ENABLED_HC128=$enableval ],
    [ ENABLED_HC128=no ]
    )

if test "$ENABLED_HC128" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_HC128"
else
    AM_CFLAGS="$AM_CFLAGS -DHAVE_HC128"
fi


# RABBIT
AC_ARG_ENABLE([rabbit],
    [AS_HELP_STRING([--enable-rabbit],[Enable RABBIT (default: disabled)])],
    [ ENABLED_RABBIT=$enableval ],
    [ ENABLED_RABBIT=no ]
    )

if test "$ENABLED_RABBIT" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_RABBIT"
else
    AM_CFLAGS="$AM_CFLAGS -DHAVE_RABBIT"
fi


# FIPS
AS_CASE([$FIPS_VERSION],
    ["v2"],[
        AS_IF([test "x$FIPS_READY" = "xyes"],
            [AM_CFLAGS="$AM_CFLAGS -DHAVE_FIPS_VERSION=3"],
            [AM_CFLAGS="$AM_CFLAGS -DHAVE_FIPS_VERSION=2"])
        AM_CFLAGS="$AM_CFLAGS -DHAVE_FIPS -DWOLFSSL_KEY_GEN -DWOLFSSL_SHA224 -DWOLFSSL_AES_DIRECT -DHAVE_AES_ECB -DHAVE_ECC_CDH -DWC_RSA_NO_PADDING -DWOLFSSL_VALIDATE_FFC_IMPORT -DHAVE_FFDHE_Q"
        ENABLED_KEYGEN="yes"
        ENABLED_SHA224="yes"
        # Shake256 is a SHA-3 algorithm not in our FIPS algorithm list
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_NO_SHAKE256"
        AS_IF([test "x$ENABLED_AESCCM" != "xyes"],
              [ENABLED_AESCCM="yes"
               AM_CFLAGS="$AM_CFLAGS -DHAVE_AESCCM"])
        AS_IF([test "x$ENABLED_RSAPSS" != "xyes"],
              [ENABLED_RSAPSS="yes"
               AM_CFLAGS="$AM_CFLAGS -DWC_RSA_PSS"])
        AS_IF([test "x$ENABLED_ECC" != "xyes"],
              [ENABLED_ECC="yes"
               AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC -DTFM_ECC256 -DWOLFSSL_VALIDATE_ECC_IMPORT"
               AS_IF([test "x$ENABLED_ECC_SHAMIR" = "xyes"],
                     [AM_CFLAGS="$AM_CFLAGS -DECC_SHAMIR"])],
              [AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_VALIDATE_ECC_IMPORT"])
        AS_IF([test "x$ENABLED_AESCTR" != "xyes"],
              [ENABLED_AESCTR="yes"
               AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_COUNTER"])
        AS_IF([test "x$ENABLED_CMAC" != "xyes"],
              [ENABLED_CMAC="yes"
               AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CMAC"])
        AS_IF([test "x$ENABLED_HKDF" != "xyes"],
              [ENABLED_HKDF="yes"
               AM_CFLAGS="$AM_CFLAGS -DHAVE_HKDF"])
        AS_IF([test "x$ENABLED_INTELASM" = "xyes"],
              [AM_CFLAGS="$AM_CFLAGS -DFORCE_FAILURE_RDSEED"])
    ],
    ["rand"],[
        AM_CFLAGS="$AM_CFLAGS -DWOLFCRYPT_FIPS_RAND -DHAVE_FIPS -DHAVE_FIPS_VERSION=2"
    ],
    ["v1"],[
        AM_CFLAGS="$AM_CFLAGS -DHAVE_FIPS"
    ])

AS_IF([test "x$ENABLED_FIPS" = "xyes" && test "x$thread_ls_on" = "xno"],
    [AC_MSG_ERROR([FIPS requires Thread Local Storage])])

AS_IF([test "x$ENABLED_FIPS" = "xyes" && test "x$FIPS_VERSION" != "xrand"],
[
    # Force enable the prerequisites.
    AS_IF([test "x$ENABLED_SHA512" = "xno"],
        [ENABLED_SHA512="yes"; AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA512 -DWOLFSSL_SHA384"])
    AS_IF([test "x$ENABLED_AESGCM" = "xno"],
        [ENABLED_AESGCM="yes"; AM_CFLAGS="$AM_CFLAGS -DHAVE_AESGCM"])
    AS_IF([test "x$ENABLED_DES3" = "xno"],[ENABLED_DES3="yes"])
],
[
    AS_IF([test "x$ENABLED_FORTRESS" = "xyes"],[ENABLED_DES3="yes"])
])


# SELFTEST
AC_ARG_ENABLE([selftest],
    [AS_HELP_STRING([--enable-selftest],[Enable selftest, Will NOT work w/o CAVP selftest license (default: disabled)])],
    [ ENABLED_SELFTEST=$enableval ],
    [ ENABLED_SELFTEST="no" ]
    )

AS_CASE([$ENABLED_SELFTEST],
    ["v2"],[
        # selftest v2 (wolfCrypt 4.1.0)
        ENABLED_SELFTEST="yes"
        SELFTEST_VERSION="v2"
    ],
    ["no"],[SELFTEST_VERSION="none"],
    [
        # selftest v1 (wolfCrypt 3.14.2)
        ENABLED_SELFTEST="yes"
        SELFTEST_VERSION="v1"
    ])

AS_CASE([$SELFTEST_VERSION],
    ["v2"],[
        AM_CFLAGS="$AM_CFLAGS -DHAVE_SELFTEST -DHAVE_SELFTEST_VERSION=2"
    ],
    ["v1"],[
        AM_CFLAGS="$AM_CFLAGS -DHAVE_SELFTEST"
    ])


# set sha224 default
SHA224_DEFAULT=no
if test "$host_cpu" = "x86_64" || test "$host_cpu" = "aarch64"
then
    if test "x$ENABLED_AFALG" = "xno" && test "x$ENABLED_DEVCRYPTO" = "xno" && ( test "x$ENABLED_FIPS" = "xno" || test "x$FIPS_VERSION" = "xv2" )
    then
        SHA224_DEFAULT=yes
    fi
fi

# SHA224
AC_ARG_ENABLE([sha224],
    [AS_HELP_STRING([--enable-sha224],[Enable wolfSSL SHA-224 support (default: enabled on x86_64/aarch64)])],
    [ ENABLED_SHA224=$enableval ],
    [ ENABLED_SHA224=$SHA224_DEFAULT ]
    )

if test "$ENABLED_SHA224" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA224"
fi


# set sha3 default
SHA3_DEFAULT=no
if test "$host_cpu" = "x86_64" || test "$host_cpu" = "aarch64"
then
    if test "x$ENABLED_FIPS" = "xno" || test "x$FIPS_VERSION" = "xv2"
    then
        SHA3_DEFAULT=yes
    fi
fi

# SHA3
AC_ARG_ENABLE([sha3],
    [AS_HELP_STRING([--enable-sha3],[Enable wolfSSL SHA-3 support (default: enabled on x86_64/aarch64)])],
    [ ENABLED_SHA3=$enableval ],
    [ ENABLED_SHA3=$SHA3_DEFAULT ]
    )

if test "$ENABLED_SHA3" = "small"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA3_SMALL"
    ENABLED_SHA3="yes"
fi

if test "$ENABLED_SHA3" = "yes" && test "$ENABLED_32BIT" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHA3"
fi

# SHAKE256
AC_ARG_ENABLE([shake256],
    [AS_HELP_STRING([--enable-shake256],[Enable wolfSSL SHAKE256 support (default: enabled on x86_64/aarch64)])],
    [ ENABLED_SHAKE256=$enableval ],
    [ ENABLED_SHAKE256=$ENABLED_SHA3 ]
    )

if test "$ENABLED_SHAKE256" = "yes" || test "$ENABLED_SHAKE256" = "small"
then
    if test "$ENABLED_32BIT" = "no"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SHAKE256"
        if test "$ENABLED_SHA3" = "no"
        then
            AC_MSG_ERROR([Must have SHA-3 enabled: --enable-sha3])
        fi
    fi
fi

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

# leanpsk and leantls don't need poly1305
if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
then
    ENABLED_POLY1305=no
fi

if test "$ENABLED_POLY1305" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_POLY1305 -DHAVE_ONE_TIME_AUTH"
fi


# set CHACHA default
CHACHA_DEFAULT=yes

if test "x$ENABLED_FIPS" = "xyes"
then
CHACHA_DEFAULT=no
fi

# CHACHA
AC_ARG_ENABLE([chacha],
    [AS_HELP_STRING([--enable-chacha],[Enable CHACHA (default: enabled). Use `=noasm` to disable ASM AVX/AVX2 speedups])],
    [ ENABLED_CHACHA=$enableval ],
    [ ENABLED_CHACHA=$CHACHA_DEFAULT]
    )

# leanpsk and leantls don't need chacha
if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
then
    ENABLED_CHACHA=no
fi

if test "$ENABLED_CHACHA" = "noasm" || test "$ENABLED_ASM" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_CHACHA_ASM"
fi

if test "$ENABLED_CHACHA" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CHACHA"
fi


# Hash DRBG
AC_ARG_ENABLE([hashdrbg],
    [AS_HELP_STRING([--enable-hashdrbg],[Enable Hash DRBG support (default: enabled)])],
    [ ENABLED_HASHDRBG=$enableval ],
    [ ENABLED_HASHDRBG=yes ]
    )

if test "x$ENABLED_HASHDRBG" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_HASHDRBG"
else
    # turn on Hash DRBG if FIPS is on
    if test "x$ENABLED_FIPS" = "xyes"
    then
        AM_CFLAGS="$AM_CFLAGS -DHAVE_HASHDRBG"
        ENABLED_HASHDRBG=yes
    else
        AM_CFLAGS="$AM_CFLAGS -DWC_NO_HASHDRBG"
    fi
fi


# Filesystem Build
AC_ARG_ENABLE([filesystem],
    [AS_HELP_STRING([--enable-filesystem],[Enable Filesystem support (default: enabled)])],
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
    [AS_HELP_STRING([--enable-inline],[Enable inline functions (default: enabled)])],
    [ ENABLED_INLINE=$enableval ],
    [ ENABLED_INLINE=yes ]
    )

if test "$ENABLED_INLINE" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_INLINE"
fi


# OCSP
AC_ARG_ENABLE([ocsp],
    [AS_HELP_STRING([--enable-ocsp],[Enable OCSP (default: disabled)])],
    [ ENABLED_OCSP=$enableval ],
    [ ENABLED_OCSP=no ],
    )

if test "x$ENABLED_OPENSSLALL" = "xyes" || test "x$ENABLED_NGINX" = "xyes"
then
    ENABLED_OCSP=yes
fi

if test "$ENABLED_OCSP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
fi


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


# Certificate Status Request : a.k.a. OCSP Stapling
AC_ARG_ENABLE([ocspstapling],
    [AS_HELP_STRING([--enable-ocspstapling],[Enable OCSP Stapling (default: disabled)])],
    [ ENABLED_CERTIFICATE_STATUS_REQUEST=$enableval ],
    [ ENABLED_CERTIFICATE_STATUS_REQUEST=no ]
    )

if test "x$ENABLED_NGINX" = "xyes" || test "x$ENABLED_WPAS" = "xyes" || test "x$ENABLED_HAPROXY" = "xyes"
then
    ENABLED_CERTIFICATE_STATUS_REQUEST="yes"
fi

if test "x$ENABLED_CERTIFICATE_STATUS_REQUEST" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_CERTIFICATE_STATUS_REQUEST"

    # Requires OCSP make sure on
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
    fi
fi


# Certificate Status Request v2 : a.k.a. OCSP stapling v2
AC_ARG_ENABLE([ocspstapling2],
    [AS_HELP_STRING([--enable-ocspstapling2],[Enable OCSP Stapling v2 (default: disabled)])],
    [ ENABLED_CERTIFICATE_STATUS_REQUEST_V2=$enableval ],
    [ ENABLED_CERTIFICATE_STATUS_REQUEST_V2=no ]
    )

if test "x$ENABLED_NGINX" = "xyes" || test "x$ENABLED_WPAS" = "xyes" || test "x$ENABLED_HAPROXY" = "xyes"
then
    ENABLED_CERTIFICATE_STATUS_REQUEST_V2=yes
fi

if test "x$ENABLED_CERTIFICATE_STATUS_REQUEST_V2" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_CERTIFICATE_STATUS_REQUEST_V2"

    # Requires OCSP make sure on
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
    fi
fi


# CRL
AC_ARG_ENABLE([crl],
    [AS_HELP_STRING([--enable-crl],[Enable CRL (default: disabled)])],
    [ ENABLED_CRL=$enableval ],
    [ ENABLED_CRL=no ],
    )


if test "x$ENABLED_NGINX" = "xyes" || test "x$ENABLED_HAPROXY" = "xyes" || test "x$ENABLED_OPENVPN" = "xyes"
then
    ENABLED_CRL=yes
fi

if test "$ENABLED_CRL" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL"
fi


# CRL Monitor
AC_ARG_ENABLE([crl-monitor],
    [AS_HELP_STRING([--enable-crl-monitor],[Enable CRL Monitor (default: disabled)])],
    [ ENABLED_CRL_MONITOR=$enableval ],
    [ ENABLED_CRL_MONITOR=no ],
    )

if test "$ENABLED_CRL_MONITOR" = "yes"
then
    case $host_os in
    *linux* | *darwin* | *freebsd*)
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL_MONITOR" ;;
    *)
        if test "x$ENABLED_DISTRO" = "xyes" ; then
            ENABLED_CRL_MONITOR="no"
        else
            AC_MSG_ERROR( [crl monitor only allowed on linux, OS X, or freebsd])
        fi
        break;;
    esac
fi


# USER CRYPTO
ENABLED_USER_CRYPTO="no"
ENABLED_USER_RSA="no"
AC_DEFINE([BUILD_USER_RSA], [], [User RSA is being defined])
trycryptodir=""
AC_ARG_WITH([user-crypto],
    [AS_HELP_STRING([--with-user-crypto=PATH],[Path to USER_CRYPTO install (default /usr/local)])],
    [
        CPPFLAGS="$CPPFLAGS -DHAVE_USER_CRYPTO"
        LIBS="$LIBS -lusercrypto"

        if test "x$withval" != "xno" ; then
            trycryptodir=$withval
        fi
        if test "x$withval" = "xyes" ; then
            trycryptodir="/usr/local"
        fi

        LDFLAGS="$LDFLAGS -L$trycryptodir/lib"
        CPPFLAGS="$CPPFLAGS -I$trycryptodir/include"

        #Look for RSA Init function in usercrypto lib
        AC_CHECK_LIB([usercrypto], [wc_InitRsaKey], [user_rsa_linked=yes], [user_rsa_linked=no])

       if test "x$user_rsa_linked" = "xyes" ; then
            AC_MSG_NOTICE([User user_rsa.h being used])
            AM_CFLAGS="$AM_CFLAGS -DHAVE_USER_RSA"
            ENABLED_USER_RSA=yes
            ENABLED_USER_CRYPTO=yes
       fi


        #Display check and find result of link attempts
        AC_MSG_CHECKING([for USER_CRYPTO])
        if test "x$ENABLED_USER_CRYPTO" = "xno" ; then
            AC_MSG_RESULT([no])
            AC_MSG_ERROR([USER_CRYPTO not found. Either move to /usr/include and /usr/lib or
                    Specify its path using --with-user-crypto=/dir/])
        else
            AC_MSG_RESULT([yes])
            # Check if .la is available if not then rely on exported path
            AC_CHECK_FILE($trycryptodir/lib/libusercrypto.la, [LIB_ADD="$trycryptodir/lib/libusercrypto.la $LIB_ADD"], [LIB_ADD="-lusercrypto $LIB_ADD"])
            AM_LDFLAGS="$AM_LDFLAGS -L$trycryptodir/lib"
            AM_CFLAGS="$AM_CFLAGS -DHAVE_USER_CRYPTO"
        fi
    ]
)

if test "$ENABLED_USER_CRYPTO" = "yes" && test "$ENABLED_FIPS" = "yes"
then
    AC_MSG_ERROR([cannot enable user crypto and fips, user crypto posibility of using code in fips boundary.])
fi


# NTRU
ENABLED_NTRU="no"
tryntrudir=""
AC_ARG_WITH([ntru],
    [AS_HELP_STRING([--with-ntru=PATH],[Path to NTRU install (default /usr/)])],
    [
        AC_MSG_CHECKING([for NTRU])
        CPPFLAGS="$CPPFLAGS -DHAVE_NTRU -DHAVE_TLS_EXTENSIONS"
        LIBS="$LIBS -lntruencrypt"

        AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <libntruencrypt/ntru_crypto_drbg.h>]], [[ ntru_crypto_drbg_instantiate(0, 0, 0, 0, 0); ]])], [ ntru_linked=yes ],[ ntru_linked=no ])

        if test "x$ntru_linked" = "xno" ; then
            if test "x$withval" != "xno" ; then
                tryntrudir=$withval
            fi
            if test "x$withval" = "xyes" ; then
                tryntrudir="/usr"
            fi

            LDFLAGS="$AM_LDFLAGS $LDFLAGS -L$tryntrudir/lib"
            CPPFLAGS="$CPPFLAGS -I$tryntrudir/include"

            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <libntruencrypt/ntru_crypto_drbg.h>]], [[ ntru_crypto_drbg_instantiate(0, 0, 0, 0, 0); ]])], [ ntru_linked=yes ],[ ntru_linked=no ])

            if test "x$ntru_linked" = "xno" ; then
                AC_MSG_ERROR([NTRU isn't found.
                If it's already installed, specify its path using --with-ntru=/dir/])
            fi
            AC_MSG_RESULT([yes])
            AM_LDFLAGS="$AM_LDFLAGS -L$tryntrudir/lib"
        else
            AC_MSG_RESULT([yes])
        fi

        AM_CFLAGS="$AM_CFLAGS -DHAVE_NTRU -DHAVE_TLS_EXTENSIONS -DWOLFSSL_STATIC_RSA"
        ENABLED_NTRU="yes"
    ]
)


# QSH
AC_ARG_ENABLE([qsh],
    [AS_HELP_STRING([--enable-qsh],[Enable QSH (default: disabled)])],
    [ ENABLED_QSH=$enableval ],
    [ ENABLED_QSH=no ]
    )

if test "x$ENABLED_QSH" = "xyes"
then
    if test "x$ENABLED_NTRU" = "xno"
    then
        AC_MSG_ERROR([cannot enable qsh without NTRU])
    fi

    AM_CFLAGS="$AM_CFLAGS -DHAVE_QSH"
fi


# Whitewood netRandom client library
ENABLED_WNR="no"
trywnrdir=""
AC_ARG_WITH([wnr],
    [AS_HELP_STRING([--with-wnr=PATH],[Path to Whitewood netRandom install (default /usr/local)])],
    [
        AC_MSG_CHECKING([for Whitewood netRandom])
        CPPFLAGS="$CPPFLAGS -DHAVE_WNR"
        LIBS="$LIBS -lwnr"

        AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <wnr.h>]], [[ wnr_setup(0, 0); ]])], [ wnr_linked=yes ],[ wnr_linked=no ])

        if test "x$wnr_linked" = "xno" ; then
            if test "x$withval" != "xno" ; then
                trywnrdir=$withval
            fi
            if test "x$withval" = "xyes" ; then
                trywnrdir="/usr/local"
            fi

            LDFLAGS="$AM_LDFLAGS $LDFLAGS -L$trywnrdir/lib"
            CPPFLAGS="$CPPFLAGS -I$trywnrdir/include"

            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <wnr.h>]], [[ wnr_setup(0, 0); ]])], [ wnr_linked=yes ],[ wnr_linked=no ])

            if test "x$wnr_linked" = "xno" ; then
                AC_MSG_ERROR([Whitewood netRandom isn't found.
                If it's already installed, specify its path using --with-wnr=/dir/])
            fi
            AC_MSG_RESULT([yes])
            AM_LDFLAGS="$AM_LDFLAGS -L$trywnrdir/lib"
        else
            AC_MSG_RESULT([yes])
        fi

        AM_CFLAGS="$AM_CFLAGS -DHAVE_WNR"
        ENABLED_WNR="yes"
    ]
)


# SNI
AC_ARG_ENABLE([sni],
    [AS_HELP_STRING([--enable-sni],[Enable SNI (default: disabled)])],
    [ ENABLED_SNI=$enableval ],
    [ ENABLED_SNI=no ]
    )
if test "x$ENABLED_QT" = "xyes"
then
    ENABLED_SNI="yes"
fi

if test "x$ENABLED_SNI" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SNI"
fi

# Maximum Fragment Length
AC_ARG_ENABLE([maxfragment],
    [AS_HELP_STRING([--enable-maxfragment],[Enable Maximum Fragment Length (default: disabled)])],
    [ ENABLED_MAX_FRAGMENT=$enableval ],
    [ ENABLED_MAX_FRAGMENT=no ]
    )

# ALPN
AC_ARG_ENABLE([alpn],
    [AS_HELP_STRING([--enable-alpn],[Enable ALPN (default: disabled)])],
    [ ENABLED_ALPN=$enableval ],
    [ ENABLED_ALPN=no ]
    )

if test "x$ENABLED_ALPN" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_ALPN"
fi

# Maximum Fragment Length
if test "x$ENABLED_MAX_FRAGMENT" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_MAX_FRAGMENT"
fi

# Trusted CA Indication Extension
AC_ARG_ENABLE([trustedca],
    [AS_HELP_STRING([--enable-trustedca],[Enable Trusted CA Indication (default: disabled)])],
    [ ENABLED_TRUSTED_CA=$enableval ],[ ENABLED_TRUSTED_CA=no ])

AS_IF([test "x$ENABLED_TRUSTED_CA" = "xyes"],
      [AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_TRUSTED_CA"])

# Truncated HMAC
AC_ARG_ENABLE([truncatedhmac],
    [AS_HELP_STRING([--enable-truncatedhmac],[Enable Truncated HMAC (default: disabled)])],
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
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SECURE_RENEGOTIATION -DHAVE_SERVER_RENEGOTIATION_INFO"
fi

# Fallback SCSV
AC_ARG_ENABLE([fallback-scsv],
    [AS_HELP_STRING([--enable-fallback-scsv],[Enable Fallback SCSV (default: disabled)])],
    [ ENABLED_FALLBACK_SCSV=$enableval ],
    [ ENABLED_FALLBACK_SCSV=no ]
    )

if test "x$ENABLED_FALLBACK_SCSV" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_FALLBACK_SCSV"
fi

# Supported Elliptic Curves Extensions
AC_ARG_ENABLE([supportedcurves],
    [AS_HELP_STRING([--enable-supportedcurves],[Enable Supported Elliptic Curves (default: enabled)])],
    [ENABLED_SUPPORTED_CURVES=$enableval],
    [ENABLED_SUPPORTED_CURVES=yes])

if test "x$ENABLED_SUPPORTED_CURVES" = "xyes"
then
    AS_IF([test "x$ENABLED_ECC" = "xno" && test "x$ENABLED_CURVE25519" = "xno" && test "x$ENABLED_CURVE448" = "xno"],
          [ENABLED_SUPPORTED_CURVES=no],
          [AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SUPPORTED_CURVES"])
fi

# Diffie-Hellman
if test "$ENABLED_DH" = "yes"
then
    if test "$ENABLED_TLS13" = "yes" || test "$ENABLED_SUPPORTED_CURVES" = "yes"
    then
        AM_CFLAGS="-DHAVE_FFDHE_2048 $AM_CFLAGS"
    fi
fi

# FFDHE parameters only
AC_ARG_ENABLE([ffdhe-only],
    [AS_HELP_STRING([--enable-ffdhe-only],[Enable using only FFDHE in client (default: disabled)])],
    [ ENABLED_FFDHE_ONLY=$enableval ],
    [ ENABLED_FFDHE_ONLY=no ]
    )

if test "x$ENABLED_FFDHE_ONLY" = "xyes"
then
    if test "$ENABLED_DH" = "no"
    then
        AC_MSG_ERROR([FFDHE only support requires DH support])
    fi
    if test "$ENABLED_SUPPORTED_CURVES" = "no"
    then
        AC_MSG_ERROR([FFDHE only support requires Supported Curves extension])
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_REQUIRE_FFDHE"
fi

# TLS 1.3 Requires either ECC or (RSA/DH), or CURVE25519/ED25519 or CURVE448/ED448
if test "x$ENABLED_ECC" = "xno" && \
    (test "x$ENABLED_RSA" = "xno" || test "x$ENABLED_DH" = "xno") && \
    (test "x$ENABLED_CURVE25519" = "xno" || test "x$ENABLED_ED25519" = "xno") && \
    (test "x$ENABLED_CURVE448" = "xno" || test "x$ENABLED_ED448" = "xno")
then
    # disable TLS 1.3
    ENABLED_TLS13=no
fi
if test "$ENABLED_TLS13" = "yes"
then
    AM_CFLAGS="-DWOLFSSL_TLS13 -DHAVE_TLS_EXTENSIONS -DHAVE_SUPPORTED_CURVES $AM_CFLAGS"
fi


# Session Ticket Extension
AC_ARG_ENABLE([session-ticket],
    [AS_HELP_STRING([--enable-session-ticket],[Enable Session Ticket (default: disabled)])],
    [ ENABLED_SESSION_TICKET=$enableval ],
    [ ENABLED_SESSION_TICKET=no ]
    )

if test "x$ENABLED_NGINX" = "xyes" || test "$ENABLED_WPAS" != "no" || test "x$ENABLED_HAPROXY" = "xyes"
then
    ENABLED_SESSION_TICKET=yes
fi

if test "x$ENABLED_SESSION_TICKET" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SESSION_TICKET"
fi

# Extended Master Secret Extension
AC_ARG_ENABLE([extended-master],
    [AS_HELP_STRING([--enable-extended-master],[Enable Extended Master Secret (default: enabled)])],
    [ ENABLED_EXTENDED_MASTER=$enableval ],
    [ ENABLED_EXTENDED_MASTER=yes ]
    )

if test "x$ENABLED_EXTENDED_MASTER" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_EXTENDED_MASTER"
fi

# TLS Extensions
AC_ARG_ENABLE([tlsx],
    [AS_HELP_STRING([--enable-tlsx],[Enable all TLS Extensions (default: disabled)])],
    [ ENABLED_TLSX=$enableval ],
    [ ENABLED_TLSX=no ]
    )

if test "x$ENABLED_NGINX" = "xyes" || test "x$ENABLED_HAPROXY" = "xyes" || test "x$ENABLED_SIGNAL" = "xyes"
then
    ENABLED_TLSX=yes
fi

if test "x$ENABLED_TLSX" = "xyes"
then
    ENABLED_SNI=yes
    ENABLED_MAX_FRAGMENT=yes
    ENABLED_TRUNCATED_HMAC=yes
    ENABLED_ALPN=yes
    ENABLED_TRUSTED_CA=yes
    ENABLED_ENCRYPT_THEN_MAC=yes
    AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SNI -DHAVE_MAX_FRAGMENT -DHAVE_TRUNCATED_HMAC -DHAVE_ALPN -DHAVE_TRUSTED_CA"
    # Check the ECC supported curves prereq
    AS_IF([test "x$ENABLED_ECC" != "xno" || test "x$ENABLED_CURVE25519" = "xyes" || test "x$ENABLED_CURVE448" = "xyes" || test "x$ENABLED_TLS13" = "xyes"],
          [ENABLED_SUPPORTED_CURVES=yes
           AM_CFLAGS="$AM_CFLAGS -DHAVE_SUPPORTED_CURVES"])
fi

# Early Data handshake in TLS v1.3 and above
AC_ARG_ENABLE([earlydata],
    [AS_HELP_STRING([--enable-earlydata],[Enable Early Data handshake with wolfSSL TLS v1.3 (default: disabled)])],
    [ ENABLED_TLS13_EARLY_DATA=$enableval ],
    [ ENABLED_TLS13_EARLY_DATA=no ]
    )

if test "$ENABLED_TLS13_EARLY_DATA" = "group"
then
    ENABLED_TLS13_EARLY_DATA="yes"
    # Group EarlyData with ClientHello
    AM_CFLAGS="-DWOLFSSL_EARLY_DATA_GROUP $AM_CFLAGS"
fi
if test "$ENABLED_TLS13_EARLY_DATA" = "yes"
then
    if test "x$ENABLED_TLS13" = "xno"
    then
        AC_MSG_ERROR([cannot enable earlydata without enabling tls13.])
    fi
    if test "x$ENABLED_SESSION_TICKET" = "xno" && test "x$ENABLED_PSK" = "xno"
    then
        AC_MSG_ERROR([cannot enable earlydata without enabling session tickets and/or PSK.])
    fi
    AM_CFLAGS="-DWOLFSSL_EARLY_DATA $AM_CFLAGS"
fi

if test "$ENABLED_TLSV12" = "no" && test "$ENABLED_TLS13" = "yes" && test "x$ENABLED_SESSION_TICKET" = "xno"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_SESSION_CACHE"
fi


# PKCS7
AC_ARG_ENABLE([pkcs7],
    [AS_HELP_STRING([--enable-pkcs7],[Enable PKCS7 (default: disabled)])],
    [ ENABLED_PKCS7=$enableval ],
    [ ENABLED_PKCS7=no ],
    )


# wolfSSH Options
AC_ARG_ENABLE([ssh],
    [AS_HELP_STRING([--enable-ssh],[Enable wolfSSH options (default: disabled)])],
    [ ENABLED_WOLFSSH=$enableval ],
    [ ENABLED_WOLFSSH=no ]
    )

# Simple Certificate Enrollment Protocol (SCEP)
AC_ARG_ENABLE([scep],
    [AS_HELP_STRING([--enable-scep],[Enable wolfSCEP (default: disabled)])],
    [ ENABLED_WOLFSCEP=$enableval ],
    [ ENABLED_WOLFSCEP=no ]
    )


# Secure Remote Password
AC_ARG_ENABLE([srp],
    [AS_HELP_STRING([--enable-srp],[Enable Secure Remote Password (default: disabled)])],
    [ ENABLED_SRP=$enableval ],
    [ ENABLED_SRP=no ]
    )

if test "x$ENABLED_SRP" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFCRYPT_HAVE_SRP"
fi


# Indefinite length encoded BER message support
AC_ARG_ENABLE([indef],
    [AS_HELP_STRING([--enable-indef],[Enable parsing of indefinite length encoded msgs (default: disabled)])],
    [ ENABLED_BER_INDEF=$enableval ],
    [ ENABLED_BER_INDEF=no ]
    )

if test "x$ENABLED_BER_INDEF" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DASN_BER_TO_DER"
fi



# Small Stack - Cache on object
AC_ARG_ENABLE([smallstackcache],
    [AS_HELP_STRING([--enable-smallstackcache],[Enable Small Stack Usage Caching (default: disabled)])],
    [ ENABLED_SMALL_STACK_CACHE=$enableval ],
    [ ENABLED_SMALL_STACK_CACHE=no ]
    )

if test "x$ENABLED_SMALL_STACK_CACHE" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SMALL_STACK_CACHE"
fi

# Small Stack
AC_ARG_ENABLE([smallstack],
    [AS_HELP_STRING([--enable-smallstack],[Enable Small Stack Usage (default: disabled)])],
    [ ENABLED_SMALL_STACK=$enableval ],
    [ ENABLED_SMALL_STACK=no ]
    )

if test "x$ENABLED_SMALL_STACK_CACHE" = "xyes"
then
    ENABLED_SMALL_STACK=yes
fi
if test "x$ENABLED_SMALL_STACK" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SMALL_STACK"
fi


#valgrind
AC_ARG_ENABLE([valgrind],
    [AS_HELP_STRING([--enable-valgrind],[Enable valgrind for unit tests (default: disabled)])],
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


# Test certs, use internal cert functions for extra testing
AC_ARG_ENABLE([testcert],
    [AS_HELP_STRING([--enable-testcert],[Enable Test Cert (default: disabled)])],
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
    [AS_HELP_STRING([--enable-iopool],[Enable I/O Pool example (default: disabled)])],
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
    [AS_HELP_STRING([--enable-certservice],[Enable cert service (default: disabled)])],
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
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC -DTFM_ECC256"

        if test "$ENABLED_ECC_SHAMIR" = "yes"
        then
            AM_CFLAGS="$AM_CFLAGS -DECC_SHAMIR"
        fi
    fi
    if test "x$ENABLED_OPENSSLEXTRA" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAVE_CERT_SERVICE"
fi


# wolfSSL JNI
AC_ARG_ENABLE([jni],
    [AS_HELP_STRING([--enable-jni],[Enable wolfSSL JNI (default: disabled)])],
    [ ENABLED_JNI=$enableval ],
    [ ENABLED_JNI=no ]
    )
if test "$ENABLED_JNI" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_JNI -DHAVE_EX_DATA"

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
    if test "x$ENABLED_OPENSSLALL" = "xno"
    then
        ENABLED_OPENSSLALL="yes"
        AM_CFLAGS="$AM_CFLAGS -DOPENSSL_ALL"
    fi
    if test "x$ENABLED_CRL" = "xno"
    then
        ENABLED_CRL="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL"
    fi
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
    fi
    if test "x$ENABLED_CRL_MONITOR" = "xno" && test "x$ENABLED_DISTRO" = "xno"
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
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC -DTFM_ECC256"

        if test "$ENABLED_ECC_SHAMIR" = "yes"
        then
            AM_CFLAGS="$AM_CFLAGS -DECC_SHAMIR"
        fi
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
    if test "x$ENABLED_PSK" = "xno"
    then
        ENABLED_PSK="yes"
    fi
    if test "x$ENABLED_CERTEXT" = "xno"
    then
        ENABLED_CERTEXT="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_EXT"
    fi
    if test "x$ENABLED_CERTGEN" = "xno"
    then
        ENABLED_CERTGEN="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN"
    fi
    if test "x$ENABLED_SNI" = "xno"
    then
        ENABLED_SNI="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SNI"
    fi
    if test "x$ENABLED_ALPN" = "xno"
    then
        ENABLED_ALPN="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ALPN"
    fi
fi

# lighty Support
AC_ARG_ENABLE([lighty],
    [AS_HELP_STRING([--enable-lighty],[Enable lighttpd/lighty (default: disabled)])],
    [ ENABLED_LIGHTY=$enableval ],
    [ ENABLED_LIGHTY=no ]
    )
if test "$ENABLED_LIGHTY" = "yes"
then
    # Requires opensslextra make sure on
    if test "x$ENABLED_OPENSSLEXTRA" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
    fi
    AM_CFLAGS="$AM_CFLAGS -DHAVE_LIGHTY -DHAVE_WOLFSSL_SSL_H=1"
fi

if test "$ENABLED_NGINX" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_NGINX -DWOLFSSL_SIGNER_DER_CERT"
fi

if test "$ENABLED_HAPROXY" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAPROXY"
    # Requires opensslextra make sure on
    if test "x$ENABLED_OPENSSLEXTRA" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
    fi
fi

if test "$ENABLED_SIGNAL" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SIGNAL"
    # Requires opensslextra make sure on
    if test "x$ENABLED_OPENSSLEXTRA" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
    fi
fi

if test "$ENABLED_OPENVPN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DES_ECB -DHAVE_EX_DATA -DWOLFSSL_KEY_GEN -DWOLFSSL_OPENVPN"
fi


if test "$ENABLED_NGINX" = "yes"|| test "x$ENABLED_HAPROXY" = "xyes" || test "x$ENABLED_LIGHTY" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALWAYS_VERIFY_CB"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALWAYS_KEEP_SNI"
    AM_CFLAGS="$AM_CFLAGS -DKEEP_OUR_CERT -DKEEP_PEER_CERT"
    AM_CFLAGS="$AM_CFLAGS -DHAVE_EXT_CACHE -DHAVE_EX_DATA"
fi

if test "$ENABLED_OPENSSH" = "yes" || test "$ENABLED_WPAS" = "yes" || test "$ENABLED_QT" = "yes"
then
    ENABLED_ARC4="yes"
fi

if test "$ENABLED_ARC4" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_RC4"
else
    # turn off ARC4 if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_RC4"
        ENABLED_ARC4=no
    fi
fi

# Asio Support
AC_ARG_ENABLE([asio],
    [AS_HELP_STRING([--enable-asio],[Enable asio (default: disabled)])],
    [ ENABLED_ASIO=$enableval ],
    [ ENABLED_ASIO=no ]
    )
if test "$ENABLED_ASIO" = "yes"
then
    # Requires opensslextra and opensslall
    if test "x$ENABLED_OPENSSLALL" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLALL="yes"
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA -DOPENSSL_ALL $AM_CFLAGS"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ASIO -DASIO_USE_WOLFSSL -DWOLFSSL_KEY_GEN"
    AM_CFLAGS="$AM_CFLAGS -DBOOST_ASIO_USE_WOLFSSL -DHAVE_EX_DATA"
    AM_CFLAGS="$AM_CFLAGS -DSSL_TXT_TLSV1_2 -DSSL_TXT_TLSV1_1"
    AM_CFLAGS="$AM_CFLAGS -DOPENSSL_NO_SSL2 -DOPENSSL_NO_SSL3"
    if test "$ENABLED_TLSV10" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DSSL_TXT_TLSV1"
    fi

    # Requires OCSP make sure on
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
    fi
fi

# Apache HTTPD
AC_ARG_ENABLE([apachehttpd],
    [AS_HELP_STRING([--enable-apachehttpd],[Enable Apache httpd (default: disabled)])],
    [ ENABLED_APACHE_HTTPD=$enableval ],
    [ ENABLED_APACHE_HTTPD=no ]
    )
if test "$ENABLED_APACHE_HTTPD" = "yes"
then
    # Requires opensslextra and opensslall
    if test "x$ENABLED_OPENSSLALL" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLALL="yes"
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA -DOPENSSL_ALL $AM_CFLAGS"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_APACHE_HTTPD"
    AM_CFLAGS="$AM_CFLAGS -DOPENSSL_NO_SSL2 -DOPENSSL_NO_SSL3 -DOPENSSL_NO_COMP"
    AM_CFLAGS="$AM_CFLAGS -DHAVE_EX_DATA -DWOLFSSL_SIGNER_DER_CERT"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_EXT -DWOLFSSL_CERT_GEN"

    # Requires OCSP make sure on
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
    fi

    # Requires sessioncerts make sure on
    if test "x$ENABLED_SESSIONCERTS" = "xno"
    then
        ENABLED_SESSIONCERTS="yes"
        AM_CFLAGS="$AM_CFLAGS -DSESSION_CERTS"
    fi

    # Requires ALPN
    if test "x$ENABLED_ALPN" = "xno"
    then
        ENABLED_ALPN="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_ALPN"
    fi

    # Requires CRL
    if test "x$ENABLED_CRL" = "xno"
    then
        ENABLED_CRL="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL"
    fi

    # Requires Certificate Generation, Request and Extensions
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
    if test "x$ENABLED_CERTEXT" = "xno"
    then
        ENABLED_CERTEXT="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_EXT"
    fi

    # Requires Secure Renegotiation
    if test "x$ENABLED_SECURE_RENEGOTIATION" = "xno"
    then
        AM_CFLAGS="$AM_CFLAGS -DHAVE_SECURE_RENEGOTIATION -DHAVE_SERVER_RENEGOTIATION_INFO"
    fi
fi

# Encrypt-Then-Mac
AC_ARG_ENABLE([enc-then-mac],
    [AS_HELP_STRING([--enable-enc-then-mac],[Enable Encryptr-Then-Mac extension (default: enabled)])],
    [ ENABLED_ENCRYPT_THEN_MAC=$enableval ],
    [ ENABLED_ENCRYPT_THEN_MAC=yes ]
    )

if test "x$ENABLED_APACHE_HTTPD" = "xyes"
then
    ENABLED_ENCRYPT_THEN_MAC=no
fi

if test "x$ENABLED_TLSX" = "xyes"
then
    ENABLED_ENCRYPT_THEN_MAC=yes
fi

AS_IF([test "x$ENABLED_SNIFFER" = "xyes"],[ENABLED_ENCRYPT_THEN_MAC="no"])

if test "x$ENABLED_ENCRYPT_THEN_MAC" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ENCRYPT_THEN_MAC"
fi


# stunnel Support
AC_ARG_ENABLE([stunnel],
    [AS_HELP_STRING([--enable-stunnel],[Enable stunnel (default: disabled)])],
    [ ENABLED_STUNNEL=$enableval ],
    [ ENABLED_STUNNEL=no ]
    )
if test "$ENABLED_WPAS" = "yes"
then
    ENABLED_STUNNEL="yes"
fi
if test "$ENABLED_STUNNEL" = "yes"
then
    # Requires opensslextra make sure on
    if test "x$ENABLED_OPENSSLEXTRA" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
    fi

    # Requires OCSP make sure on
    if test "x$ENABLED_OCSP" = "xno"
    then
        ENABLED_OCSP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
    fi

    # Requires coding make sure on
    if test "x$ENABLED_CODING" = "xno"
    then
        ENABLED_CODING="yes"
    fi

    # Requires sessioncerts make sure on
    if test "x$ENABLED_SESSIONCERTS" = "xno"
    then
        ENABLED_SESSIONCERTS="yes"
        AM_CFLAGS="$AM_CFLAGS -DSESSION_CERTS"
    fi

    # Requires crls, make sure on
    if test "x$ENABLED_CRL" = "xno"
    then
        ENABLED_CRL="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL"
    fi

    # Requires DES3, make sure on
    if test "x$ENABLED_DES3" = "xno"
    then
        ENABLED_DES3="yes"
    fi

    # Requires tlsx, make sure on
    if test "x$ENABLED_TLSX" = "xno"
    then
        ENABLED_TLSX="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_TLS_EXTENSIONS -DHAVE_SNI -DHAVE_MAX_FRAGMENT -DHAVE_TRUNCATED_HMAC"

        # Check the ECC supported curves prereq
        AS_IF([test "x$ENABLED_ECC" != "xno" || test "x$ENABLED_CURVE25519" = "xyes"],
              [ENABLED_SUPPORTED_CURVES=yes
               AM_CFLAGS="$AM_CFLAGS -DHAVE_SUPPORTED_CURVES"])
    fi

    # Requires ecc make sure on
    if test "x$ENABLED_ECC" = "xno"
    then
        ENABLED_OPENSSLEXTRA="yes"
        ENABLED_ECC="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC -DTFM_ECC256"

        if test "$ENABLED_ECC_SHAMIR" = "yes"
        then
            AM_CFLAGS="$AM_CFLAGS -DECC_SHAMIR"
        fi
    fi

    # Requires wolfSSL_OBJ_txt2nid
    if test "x$ENABLED_CERTEXT" = "xno"
    then
        ENABLED_CERTEXT="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_EXT"
    fi

    # Requires certgen
    if test "x$ENABLED_CERTGEN" = "xno"
    then
        ENABLED_CERTGEN="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_GEN"
    fi

    AM_CFLAGS="$AM_CFLAGS -DHAVE_STUNNEL -DWOLFSSL_ALWAYS_VERIFY_CB"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ALWAYS_KEEP_SNI -DHAVE_EX_DATA"
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DES_ECB"
fi

if test "$ENABLED_PSK" = "no" && test "$ENABLED_LEANPSK" = "no" \
    && test "x$ENABLED_STUNNEL" = "xno"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_PSK"
fi

if test "$ENABLED_PSK" = "no" &&  \
    (test "$ENABLED_LEANPSK" = "yes" || test "x$ENABLED_STUNNEL" = "xyes")
then
    ENABLED_PSK=yes
fi

# MD4
AC_ARG_ENABLE([md4],
    [AS_HELP_STRING([--enable-md4],[Enable MD4 (default: disabled)])],
    [ ENABLED_MD4=$enableval ],
    [ ENABLED_MD4=no ]
    )


if test "$ENABLED_MD4" = "no"
then
    #turn on MD4 if using stunnel
    if test "x$ENABLED_STUNNEL" = "xyes"
    then
        ENABLED_MD4="yes"
    else
        AM_CFLAGS="$AM_CFLAGS -DNO_MD4"
    fi
fi


# Encrypted keys
AC_ARG_ENABLE([enckeys],
    [AS_HELP_STRING([--enable-enckeys],[Enable PEM encrypted private key support (default: disabled)])],
    [ ENABLED_ENCKEYS=$enableval ],
    [ ENABLED_ENCKEYS=no ]
    )

if test "$ENABLED_OPENSSLEXTRA" = "yes" || test "$ENABLED_WEBSERVER" = "yes" || test "$ENABLED_WPAS" != "no"
then
    ENABLED_ENCKEYS=yes
fi

if test "$ENABLED_ENCKEYS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ENCRYPTED_KEYS"
fi


# PWDBASED has to come after certservice since we want it on w/o explicit on
# PWDBASED
AC_ARG_ENABLE([pwdbased],
    [AS_HELP_STRING([--enable-pwdbased],[Enable PWDBASED (default: disabled)])],
    [ ENABLED_PWDBASED=$enableval ],
    [ ENABLED_PWDBASED=no ]
    )

if test "$ENABLED_PWDBASED" = "no"
then
    if test "$ENABLED_OPENSSLEXTRA" = "yes" || test "$ENABLED_OPENSSLALL" = "yes" || test "$ENABLED_WEBSERVER" = "yes" || test "$ENABLED_ENCKEYS" = "yes"
    then
        # opensslextra, opensslall, webserver, and enckeys needs pwdbased
        ENABLED_PWDBASED=yes
    else
        AM_CFLAGS="$AM_CFLAGS -DNO_PWDBASED"
    fi
fi


AC_ARG_ENABLE([scrypt],
    [AS_HELP_STRING([--enable-scrypt],[Enable SCRYPT (default: disabled)])],
    [ ENABLED_SCRYPT=$enableval ],
    [ ENABLED_SCRYPT=no ]
    )

if test "$ENABLED_SCRYPT" = "yes"
then
    if test "$ENABLED_PWDBASED" = "no"
    then
        AC_MSG_ERROR([cannot enable scrypt without enabling pwdbased.])
    fi
    AM_CFLAGS="$AM_CFLAGS -DHAVE_SCRYPT"
fi


# wolfCrypt Only Build
AC_ARG_ENABLE([cryptonly],
    [AS_HELP_STRING([--enable-cryptonly],[Enable wolfCrypt Only build (default: disabled)])],
    [ENABLED_CRYPTONLY=$enableval],
    [ENABLED_CRYPTONLY=no])

AS_IF([test "x$FIPS_VERSION" = "xrand"],[ENABLED_CRYPTONLY="yes"])

if test "$ENABLED_CRYPTONLY" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFCRYPT_ONLY"
fi

if test "x$ENABLED_CRYPTONLY" = "xno"
then
    if test "x$ENABLED_PSK" = "xno" && test "x$ENABLED_ASN" = "xno"
    then
        AC_MSG_ERROR([please enable psk if disabling asn.])
    fi

    if test "x$ENABLED_ECC" != "xno" && test "x$ENABLED_ASN" = "xno"
    then
        AC_MSG_ERROR([please disable ecc if disabling asn.])
    fi

    if test "$ENABLED_AFALG" = "yes"
    then
        # for TLS connections the intermediate hash needs to store buffer
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AFALG_HASH_KEEP"
    fi

    if test "$ENABLED_DEVCRYPTO" = "yes"
    then
        # for TLS connections the intermediate hash needs to store buffer
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_DEVCRYPTO_HASH_KEEP"
    fi
fi

# set fastmath default
FASTMATH_DEFAULT=no

if test "$host_cpu" = "x86_64" || test "$host_cpu" = "aarch64"
then
    FASTMATH_DEFAULT=yes
fi
if test "$ENABLED_SP_MATH" = "yes"
then
    FASTMATH_DEFAULT=no
fi

# fastmath
AC_ARG_ENABLE([fastmath],
    [AS_HELP_STRING([--enable-fastmath],[Enable fast math ops (default: enabled on x86_64/aarch64)])],
    [ ENABLED_FASTMATH=$enableval ],
    [ ENABLED_FASTMATH=$FASTMATH_DEFAULT]
    )

if test "x$ENABLED_FASTMATH" = "xyes"
then
    # turn off fastmth if leanpsk on or asn off (w/o DH and ECC)
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_ASN" = "no"
    then
        if test "$ENABLED_DH" = "no" && test "$ENABLED_ECC" = "no" && test "$ENABLED_RSA" = "no"
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
    [AS_HELP_STRING([--enable-fasthugemath],[Enable fast math + huge code (default: disabled)])],
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


# Enable Examples, used to disable examples
AC_ARG_ENABLE([examples],
    [AS_HELP_STRING([--enable-examples],[Enable Examples  (default: enabled)])],
    [ ENABLED_EXAMPLES=$enableval ],
    [ ENABLED_EXAMPLES=yes ]
    )

AS_IF([test "x$ENABLED_FILESYSTEM" = "xno"], [ENABLED_EXAMPLES="no"])
AS_IF([test "x$ENABLED_INLINE" = "xno"], [ENABLED_EXAMPLES="no"])
AS_IF([test "x$ENABLED_CRYPTONLY" = "xyes"], [ENABLED_EXAMPLES="no"])


# Enable wolfCrypt test and benchmark
AC_ARG_ENABLE([crypttests],
    [AS_HELP_STRING([--enable-crypttests],[Enable Crypt Bench/Test  (default: enabled)])],
    [ ENABLED_CRYPT_TESTS=$enableval ],
    [ ENABLED_CRYPT_TESTS=yes ]
    )


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

        if test "x$libz_linked" = "xno" ; then
            if test "x$withval" != "xno" ; then
                trylibzdir=$withval
            fi
            if test "x$withval" = "xyes" ; then
                trylibzdir="/usr"
            fi

            LDFLAGS="$LDFLAGS -L$trylibzdir/lib"
            CPPFLAGS="$CPPFLAGS -I$trylibzdir/include"

            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <zlib.h>]], [[ deflateInit(0, 8); ]])],[ libz_linked=yes ],[ libz_linked=no ])

            if test "x$libz_linked" = "xno" ; then
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


# PKCS#11
AC_ARG_ENABLE([pkcs11],
    [AS_HELP_STRING([--enable-pkcs11],[Enable pkcs11 access (default: disabled)])],
    [ ENABLED_PKCS11=$enableval ],
    [ ENABLED_PKCS11=no ]
    )

if test "x$ENABLED_PKCS11" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_PKCS11 -DHAVE_WOLF_BIGINT"
    LIBS="$LIBS -ldl"
fi


# PKCS#12
AC_ARG_ENABLE([pkcs12],
    [AS_HELP_STRING([--enable-pkcs12],[Enable pkcs12 (default: enabled)])],
    [ ENABLED_PKCS12=$enableval ],
    [ ENABLED_PKCS12=yes ]
    )

if test "x$ENABLED_PKCS12" = "xno"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_PKCS12"
fi


# cavium
trycaviumdir=""
AC_ARG_WITH([cavium],
    [  --with-cavium=PATH      PATH to cavium/software dir ],
    [
        AC_MSG_CHECKING([for cavium])
        CPPFLAGS="$CPPFLAGS -DHAVE_CAVIUM"
        LIB_ADD="-lrt $LIB_ADD"

        if test "x$withval" = "xyes" ; then
            AC_MSG_ERROR([need a PATH for --with-cavium])
        fi
        if test "x$withval" != "xno" ; then
            trycaviumdir=$withval
        fi

        LDFLAGS="$AM_LDFLAGS $trycaviumdir/api/cavium_common.o"
        CPPFLAGS="$CPPFLAGS -I$trycaviumdir/include"

        AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include "cavium_common.h"]], [[ CspShutdown(CAVIUM_DEV_ID); ]])],[ cavium_linked=yes ],[ cavium_linked=no ])

        if test "x$cavium_linked" = "xno" ; then
            AC_MSG_ERROR([cavium isn't found.
            If it's already installed, specify its path using --with-cavium=/dir/])
        else
            AM_CFLAGS="$AM_CFLAGS -DHAVE_CAVIUM"
        fi
        AC_MSG_RESULT([yes])
        enable_shared=no
        enable_static=yes
        ENABLED_CAVIUM=yes
    ],
    [ ENABLED_CAVIUM=no ]
)

# cavium V
trycaviumdir=""
AC_ARG_WITH([cavium-v],
    [  --with-cavium-v=PATH    PATH to Cavium V/software dir ],
    [
        AC_MSG_CHECKING([for cavium])
        AM_CFLAGS="$AM_CFLAGS -DHAVE_CAVIUM -DHAVE_CAVIUM_V"
        LIB_ADD="-lrt -lcrypto $LIB_ADD"

        if test "x$withval" = "xyes" ; then
            AC_MSG_ERROR([need a PATH for --with-cavium])
        fi
        if test "x$withval" != "xno" ; then
            trycaviumdir=$withval
        fi

        AC_CHECK_FILES([$trycaviumdir/lib/libnitrox.a], [AM_CPPFLAGS="-I$trycaviumdir/include $AM_CPPFLAGS"], [ENABLED_CAVIUM_V=no])
        LIB_STATIC_ADD="$trycaviumdir/lib/libnitrox.a $LIB_STATIC_ADD"

        if test "$ENABLED_CAVIUM_V" = "no"; then
            AC_MSG_ERROR([Could not find Nitrox library])
        fi

        enable_shared=no
        enable_static=yes
        enable_opensslextra=yes

        ENABLED_CAVIUM=yes
        ENABLED_CAVIUM_V=yes
    ],
    [
        ENABLED_CAVIUM_=no
        ENABLED_CAVIUM_V=no
    ]
)


# Cavium Octeon
OCTEON_ROOT=""
: ${OCTEON_OBJ="obj-octeon2"}
: ${OCTEON_HOST="standalone"}

AC_ARG_WITH([octeon-sync],
    [AS_HELP_STRING([--with-octeon-sync=PATH],[PATH to Cavium Octeon SDK dir (sync)])],
    [
        AC_MSG_CHECKING([for octeon])

        if test "x$withval" = "xyes" ; then
            AC_MSG_ERROR([need a PATH for --with-octeon])
        fi
        if test "x$withval" != "xno" ; then
            OCTEON_ROOT=$withval
        fi

        AM_CFLAGS="$AM_CFLAGS -DHAVE_CAVIUM_OCTEON_SYNC"
        AM_CFLAGS="$AM_CFLAGS -DOCTEON_MODEL=$OCTEON_MODEL"
        AM_CFLAGS="$AM_CFLAGS -I$OCTEON_ROOT/executive"
        AS_CASE([$OCTEON_HOST],['linux'],[AM_CFLAGS="$AM_CFLAGS -DCVMX_BUILD_FOR_LINUX_HOST"])

        #-I$OCTEON_ROOT/target/include
        AM_LDFLAGS="$AM_LDFLAGS -lrt -Xlinker -T -Xlinker $OCTEON_ROOT/executive/cvmx-shared-linux.ld"
        AM_LDFLAGS="$AM_LDFLAGS -L$OCTEON_ROOT/executive/$OCTEON_OBJ -lcvmx -lfdt"

        enable_shared=no
        enable_static=yes

        ENABLED_OCTEON_SYNC=yes
        AC_MSG_RESULT([yes])
    ],
    [ENABLED_OCTEON_SYNC=no]
)


# Intel QuickAssist
QAT_DIR=""
BUILD_INTEL_QAT_VERSION=2

AC_ARG_WITH([intelqa],
    [AS_HELP_STRING([--with-intelqa=PATH],[PATH to Intel QuickAssist (QAT) driver dir])],
    [ENABLED_INTEL_QA=yes; QAT_DIR=$withval],
    [ENABLED_INTEL_QA=no])

AC_ARG_WITH([intelqa-sync],
    [AS_HELP_STRING([--with-intelqa-sync=PATH],[PATH to Intel QuickAssist (QAT) driver dir (sync)])],
    [ENABLED_INTEL_QA_SYNC=yes; QAT_DIR=$withval],
    [ENABLED_INTEL_QA_SYNC=no])

AS_IF([test "x$ENABLED_INTEL_QA" = "xyes" && test "x$ENABLED_INTEL_QA_SYNC" = "xyes"],
    [AC_MSG_ERROR([Both Intel QA Async and Sync are selected, only select one.])])

AS_IF([test "x$ENABLED_INTEL_QA" = "xyes" || test "x$ENABLED_INTEL_QA_SYNC" = "xyes"],
    [AC_MSG_CHECKING([for intelqa])
     AS_IF([test "x$ENABLED_INTEL_QA" = "xyes"],
           [AM_CPPFLAGS="$AM_CPPFLAGS -DHAVE_INTEL_QA -DDO_CRYPTO -DUSER_SPACE"; intelqa_opt=""],
           [AM_CPPFLAGS="$AM_CPPFLAGS -DHAVE_INTEL_QA_SYNC -DQAT_USE_POLLING_THREAD -DO_CRYPTO -DUSER_SPACE"; intelqa_opt="-sync"])
     OLD_LIBS="$LIBS"
     OLD_CPPFLAGS="$CPPFLAGS"

     AS_IF([test "x$QAT_DIR" = "xyes"],[AC_MSG_ERROR([need a PATH for --with-intelqa$intelqa_opt])])

     AM_CPPFLAGS="$AM_CPPFLAGS -I$QAT_DIR/quickassist/include -I$QAT_DIR/quickassist/include/lac -I$QAT_DIR/quickassist/utilities/osal/include \
         -I$QAT_DIR/quickassist/utilities/osal/src/linux/user_space/include -I$QAT_DIR/quickassist/lookaside/access_layer/include \
         -I$QAT_DIR/quickassist/lookaside/access_layer/src/common/include -I$srcdir/wolfssl -I$srcdir/wolfssl/wolfcrypt/port/intel \
         -I$QAT_DIR/quickassist/utilities/libusdm_drv"
     CPPFLAGS="$AM_CPPFLAGS"

     LDFLAGS="$LDFLAGS -L$QAT_DIR/build"
     LIBS="$LIBS -lqat_s -lusdm_drv_s"

     AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include "cpa_cy_common.h"]],[[Cpa16U count = 0; cpaCyGetNumInstances(&count);]])],[intelqa_linked=yes],[intelqa_linked=no])

     AS_IF([test "x$intelqa_linked" = "xno"],
           [# Try old QAT driver libraries
            LIBS="$OLD_LIBS -licp_qa_al_s"
            AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include "cpa_cy_common.h"]],[[Cpa16U count = 0; cpaCyGetNumInstances(&count);]])],[intelqa_linked=yes],[intelqa_linked=no])
            AS_IF([test "x$intelqa_linked" = "xno"],
                [AC_MSG_ERROR([Intel QuickAssist not found. If it's already installed, specify its path using --with-intelqa$intelqa_opt=/dir/])],
                [BUILD_INTEL_QAT_VERSION=1])
           ])

     AC_MSG_RESULT([yes])

     AS_IF([test "x$BUILD_INTEL_QAT_VERSION" = "x1"],
        [LIB_ADD="-ladf_proxy -losal -lrt $LIB_ADD"],
        [LIB_ADD="-losal -lrt $LIB_ADD"])
     CPPFLAGS="$OLD_CPPFLAGS"
])


# Single Precision maths implementation
AC_ARG_ENABLE([sp],
    [AS_HELP_STRING([--enable-sp],[Enable Single Precision maths implementation (default: disabled)])],
    [ ENABLED_SP=$enableval ],
    [ ENABLED_SP=no ],
    )

ENABLED_SP_RSA=no
ENABLED_SP_DH=no
ENABLED_SP_FF_2048=no
ENABLED_SP_FF_3072=no
ENABLED_SP_FF_4096=no
ENABLED_SP_ECC=no
ENABLED_SP_EC_256=no
ENABLED_SP_EC_384=no
ENABLED_SP_NO_MALLOC=no
ENABLED_SP_NONBLOCK=no
for v in `echo $ENABLED_SP | tr "," " "`
do
  case $v in
  small)
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_2048=yes
    ENABLED_SP_FF_3072=yes
    ENABLED_SP_ECC=yes
    ENABLED_SP_SMALL=yes
    ENABLED_SP_EC_256=yes
    if test "$host_cpu" = "x86_64"; then
      ENABLED_SP_FF_4096=yes
      ENABLED_SP_EC_384=yes
    fi
    ;;

  yes)
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_2048=yes
    ENABLED_SP_FF_3072=yes
    ENABLED_SP_ECC=yes
    ENABLED_SP_EC_256=yes
    if test "$host_cpu" = "x86_64"; then
      ENABLED_SP_FF_4096=yes
      ENABLED_SP_EC_384=yes
    fi
    ;;

  no)
    ;;

  smallec256 | smallp256 | small256)
    ENABLED_SP_ECC=yes
    ENABLED_SP_SMALL=yes
    ENABLED_SP_EC_256=yes
    ;;
  ec256 | p256 | 256)
    ENABLED_SP_ECC=yes
    ENABLED_SP_EC_256=yes
    ;;
  smallec384 | smallp384 | small384)
    ENABLED_SP_ECC=yes
    ENABLED_SP_SMALL=yes
    ENABLED_SP_EC_384=yes
    ;;
  ec384 | p384 | 384)
    ENABLED_SP_ECC=yes
    ENABLED_SP_EC_384=yes
    ;;

  small2048)
    ENABLED_SP_SMALL=yes
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_2048=yes
    ;;
  2048)
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_2048=yes
    ;;
  smallrsa2048)
    ENABLED_SP_SMALL=yes
    ENABLED_SP_RSA=yes
    ENABLED_SP_FF_2048=yes
    ;;
  rsa2048)
    ENABLED_SP_RSA=yes
    ENABLED_SP_FF_2048=yes
    ;;

  small3072)
    ENABLED_SP_SMALL=yes
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_3072=yes
    ;;
  3072)
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_3072=yes
    ;;
  smallrsa3072)
    ENABLED_SP_SMALL=yes
    ENABLED_SP_RSA=yes
    ENABLED_SP_FF_3072=yes
    ;;
  rsa3072)
    ENABLED_SP_RSA=yes
    ENABLED_SP_FF_3072=yes
    ;;

  small4096)
    ENABLED_SP_SMALL=yes
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_4096=yes
    ;;
  4096 | +4096)
    ENABLED_SP_RSA=yes
    ENABLED_SP_DH=yes
    ENABLED_SP_FF_4096=yes
    ;;
  smallrsa4096)
    ENABLED_SP_SMALL=yes
    ENABLED_SP_RSA=yes
    ENABLED_SP_FF_4096=yes
    ;;
  rsa4096)
    ENABLED_SP_RSA=yes
    ENABLED_SP_FF_4096=yes
    ;;

  nomalloc)
    ENABLED_SP_NO_MALLOC=yes
    ;;

  nonblock)
    # Requires small and no malloc
    ENABLED_SP_NONBLOCK=yes
    ENABLED_SP_NO_MALLOC=yes
    ENABLED_SP_SMALL=yes
    ;;

  *)
    AC_MSG_ERROR([Invalid choice of Single Precision length in bits [256, 2048, 3072]: $ENABLED_SP.])
    break;;
  esac
done

ENABLED_SP=no
if test "$ENABLED_RSA" = "yes" && test "$ENABLED_SP_RSA" = "yes"; then
    ENABLED_SP=yes
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAVE_SP_RSA"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_HAVE_SP_RSA"
fi
if test "$ENABLED_DH" = "yes" && test "$ENABLED_SP_DH" = "yes"; then
    ENABLED_SP=yes
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAVE_SP_DH"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_HAVE_SP_DH"
fi
if test "$ENABLED_SP_RSA" = "yes" || test "$ENABLED_SP_DH" = "yes"; then
    if test "$ENABLED_SP_FF_2048" = "no"; then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_NO_2048"
        AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_NO_2048"
    fi
    if test "$ENABLED_SP_FF_3072" = "no"; then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_NO_3072"
        AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_NO_3072"
    fi
    if test "$ENABLED_SP_FF_4096" = "yes"; then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_4096"
        AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_4096"
    fi
fi
if test "$ENABLED_ECC" != "no" && test "$ENABLED_SP_ECC" = "yes"; then
    ENABLED_SP=yes
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAVE_SP_ECC"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_HAVE_SP_ECC"
    if test "$ENABLED_SP_EC_256" = "no"; then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_NO_256"
        AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_NO_256"
    fi
    if test "$ENABLED_SP_EC_384" = "yes"; then
        AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC384 -DWOLFSSL_SP_384"
        AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_384"
    fi
fi
if test "$ENABLED_SP_SMALL" = "yes"; then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_SMALL"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_SMALL"
fi
if test "$ENABLED_SP_NO_MALLOC" = "yes"; then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_NO_MALLOC"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_NO_MALLOC"
fi
if test "$ENABLED_SP_NONBLOCK" = "yes"; then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_NONBLOCK"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_NONBLOCK"
fi


AC_ARG_ENABLE([sp-asm],
    [AS_HELP_STRING([--enable-sp-asm],[Enable Single Precision assembly implementation (default: disabled)])],
    [ ENABLED_SP_ASM=$enableval ],
    [ ENABLED_SP_ASM=no ],
    )
if test "$ENABLED_SP_ASM" = "yes"; then
  if test "$ENABLED_SP" = "no"; then
    AC_MSG_ERROR([Must have SP enabled: --enable-sp])
  fi
  if test "$ENABLED_SP_NONBLOCK" = "yes"; then
    AC_MSG_ERROR([SP non-blocking not supported with sp-asm])
  fi
  if test "$ENABLED_ASM" = "no"; then
    AC_MSG_ERROR([Assembly code turned off])
  fi

  AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_ASM"
  AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_ASM"
  case $host_cpu in
  *aarch64*)
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_ARM64_ASM"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_ARM64_ASM"
    ENABLED_SP_ARM64_ASM=yes
    ;;
  *arm*)
    if test $host_alias = "thumb"; then
      AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_ARM_THUMB_ASM -mthumb -march=armv6"
      AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_ARM_THUMB_ASM"
      ENABLED_SP_ARM_THUMB_ASM=yes
    else
      if test $host_alias = "cortex"; then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_ARM_CORTEX_M_ASM -mcpu=cortex-r5"
        AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_ARM_CORTEX_M_ASM"
        ENABLED_SP_ARM_CORTEX_ASM=yes
      else
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_ARM32_ASM"
        AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_ARM32_ASM"
        ENABLED_SP_ARM32_ASM=yes
      fi
    fi
    ;;
  *x86_64*)
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_X86_64_ASM"
    AM_CCASFLAGS="$AM_CCASFLAGS -DWOLFSSL_SP_X86_64_ASM"
    ENABLED_SP_X86_64_ASM=yes
    ;;
  *)
    AC_MSG_ERROR([ASM not available for CPU. Supported CPUs: x86_64, aarch64, arm])
    ;;
  esac
fi

AC_ARG_ENABLE([sp-math],
    [AS_HELP_STRING([--enable-sp-math],[Enable Single Precision math implementation only (default: disabled)])],
    [ ENABLED_SP_MATH=$enableval ],
    [ ENABLED_SP_MATH=no ],
    )
if test "$ENABLED_SP_MATH" = "yes"; then
    if test "$ENABLED_SP" = "no"; then
        AC_MSG_ERROR([Must have SP enabled: --enable-sp])
    fi
    if test "$ENABLED_ECCCUSTCURVES" = "yes"; then
        AC_MSG_ERROR([Cannot use single precision math and custom curves])
    fi
    if test "$ENABLED_OPENSSLEXTRA" = "yes"; then
        AC_MSG_ERROR([Cannot use single precision math and OpenSSL extra])
    fi
    if test "$ENABLED_DSA" = "yes"; then
        AC_MSG_ERROR([Cannot use single precision math and DSA])
    fi
    if test "$ENABLED_SRP" = "yes"; then
        AC_MSG_ERROR([Cannot use single precision math and SRP])
    fi
    if test "$ENABLED_SP_RSA" = "no" && test "$ENABLED_RSA" = "yes"; then
        AC_MSG_ERROR([Cannot use RSA single precision only math and RSA])
    fi
    if test "$ENABLED_SP_DH" = "no" && test "$ENABLED_DH" = "yes"; then
        AC_MSG_ERROR([Cannot use DH single precision only math and DH])
    fi

    ENABLED_FASTMATH="no"
    ENABLED_SLOWMATH="no"
fi
if test "$ENABLED_SP_MATH" = "yes"; then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SP_MATH"
fi


# Fast RSA using Intel IPP
ippdir="${srcdir}/IPP"
ipplib="lib" # if autoconf guesses 32bit system changes lib directory
fastRSA_found=no
abs_path=`pwd`

# set up variables used
IPPLIBS=
IPPHEADERS=
IPPLINK=

AC_ARG_ENABLE([fast-rsa],
    [AS_HELP_STRING([--enable-fast-rsa],[Enable RSA using Intel IPP (default: disabled)])],
    [ ENABLED_FAST_RSA=$enableval ],
    [ ENABLED_FAST_RSA=no ],
    )

# Fast RSA does not support RSA-PSS
if test "$ENABLED_RSAPSS" = "yes"; then
    ENABLED_FAST_RSA=no
fi

if test "$ENABLED_USER_RSA" = "no" && test "$ENABLED_FIPS" = "no"; then

    if test "$ac_cv_sizeof_long" = "4" && test "$ac_cv_sizeof_long_long" = "8"; then
        ipplib="lib_32" # 32 bit OS detected
    fi

#   Use static IPP Libraries
if test "$enable_shared" = "no" && test "$ENABLED_FAST_RSA" = "yes"; then
    case $host_os in
    *darwin*)
        ipplib="$ipplib/mac_static"
        AC_MSG_ERROR([Issue with static linking to libippcp.a on Mac.
                Dynamic IPP libraries supported on Mac])
        break;;

    *linux*)
        ipplib="$ipplib/linux_static"
        break;;
    *)
        ENABLED_FAST_RSA=no
    esac

    AC_CHECK_FILES([$srcdir/IPP/$ipplib/libippcore.a $srcdir/IPP/$ipplib/libippcp.a], [], [ENABLED_FAST_RSA=no])
    AC_CHECK_FILES([$srcdir/IPP/include/ipp.h $srcdir/IPP/include/ippcp.h], [AM_CPPFLAGS="-I$srcdir/IPP/include $AM_CPPFLAGS"], [ENABLED_FAST_RSA=no])
    LIB_STATIC_ADD="$srcdir/IPP/$ipplib/libippcp.a $srcdir/IPP/$ipplib/libippcore.a $LIB_STATIC_ADD"
    if test "$ENABLED_FAST_RSA" = "no"; then
        AC_MSG_ERROR([Could not find fast rsa libraries])
    fi
else

#   Check for and use bundled IPP libraries
if test "$ENABLED_FAST_RSA" = "yes"; then
    AC_MSG_NOTICE([Using local IPP crypto library])

    AC_CHECK_FILES([$abs_path/IPP/include/ippcp.h],
    [
        # build and default locations on linux and mac
        STORE_LDFLAGS=${LDFLAGS}
        STORE_CPPFLAGS=${CPPFLAGS}

        # using LDFLAGS instead of AM_ temporarily to test link to library
        LDFLAGS="-L$ippdir/$ipplib -lippcp -lippcore"
        CPPFLAGS="-I$ippdir/include"
        AC_CHECK_HEADERS([ippcp.h], [AC_CHECK_LIB([ippcp], [ippsRSAEncrypt_PKCSv15], [fastRSA_found=yes], [fastRSA_found=no])], [fastRSA_found=no])
        name="$ippdir/$ipplib/libippcp"
        case $host_os in
        *darwin*)
            # check file existence and conditionally set variables
            AC_CHECK_FILES([$abs_path/IPP/$ipplib/libippcp.dylib], [
            IPPLIBS="${name}.dylib ${name}-9.0.dylib ${name}e9-9.0.dylib ${name}g9-9.0.dylib ${name}h9-9.0.dylib ${name}k0-9.0.dylib ${name}l9-9.0.dylib ${name}n8-9.0.dylib ${name}p8-9.0.dylib ${name}s8-9.0.dylib ${name}y8-9.0.dylib IPP/lib/libippcore.dylib IPP/lib/libippcore-9.0.dylib"
            IPPLINK="mkdir -p src/.libs && ln -f ${name}.dylib src/.libs/libippcp.dylib && ln -f ${srcdir}/${name}-9.0.dylib src/.libs/libippcp-9.0.dylib && ln -f ${srcdir}/${name}e9-9.0.dylib src/.libs/libippcpe9-9.0.dylib && ln -f ${srcdir}/${name}g9-9.0.dylib src/.libs/libippcpg9-9.0.dylib && ln -f ${srcdir}/${name}h9-9.0.dylib src/.libs/libippcph9-9.0.dylib && ln -f ${srcdir}/${name}k0-9.0.dylib src/.libs/libippcpk0-9.0.dylib && ln -f ${srcdir}/${name}l9-9.0.dylib src/.libs/libippcpl9-9.0.dylib && ln -f ${srcdir}/${name}n8-9.0.dylib src/.libs/libippcpn8-9.0.dylib && ln -f ${srcdir}/${name}p8-9.0.dylib src/.libs/libippcpp8-9.0.dylib && ln -f ${srcdir}/${name}s8-9.0.dylib src/.libs/libippcps8-9.0.dylib && ln -f ${srcdir}/${name}y8-9.0.dylib src/.libs/libippcpy8-9.0.dylib && ln -f ${srcdir}/IPP/lib/libippcore.dylib src/.libs/libippcore.dylib && ln -f ${srcdir}/IPP/lib/libippcore-9.0.dylib src/.libs/libippcore-9.0.dylib"
            ], [fastRSA_found=no])
            break;;

        *linux*)
            # check file existence and conditionally set variables
            AC_CHECK_FILES([$abs_path/IPP/$ipplib/libippcp.so.9.0], [
            if test "$ac_cv_sizeof_long" = "4" && test "$ac_cv_sizeof_long_long" = "8"; then
                IPPLIBS="${name}.so.9.0 ${name}g9.so.9.0 ${name}h9.so.9.0 ${name}p8.so.9.0 ${name}px.so.9.0 ${name}s8.so.9.0 ${name}.so ${name}w7.so.9.0 IPP/$ipplib/libippcore.so IPP/$ipplib/libippcore.so.9.0"
                IPPLINK="mkdir -p src/.libs && ln -f ${name}.so.9.0 src/.libs/libippcp.so.9.0 && ln -f ${name}g9.so.9.0 src/.libs/libippcpg9.so.9.0 && ln -f ${name}h9.so.9.0 src/.libs/libippcph9.so.9.0 && ln -f ${name}p8.so.9.0 src/.libs/libippcpp8.so.9.0 && ln -f ${name}px.so.9.0 src/.libs/libippcppx.so.9.0 && ln -f ${name}s8.so.9.0 src/.libs/libippcps8.so.9.0 && ln -f ${name}.so src/.libs/libippcp.so && ln -f ${name}w7.so.9.0 src/.libs/libippcpw7.so.9.0 && ln -f IPP/$ipplib/libippcore.so src/.libs/libippcore.so && ln -f IPP/$ipplib/libippcore.so.9.0 src/.libs/libippcore.so.9.0"
                else
                IPPLIBS="${name}.so.9.0 ${name}e9.so.9.0 ${name}k0.so.9.0 ${name}l9.so.9.0 ${name}m7.so.9.0 ${name}mx.so.9.0 ${name}.so ${name}n8.so.9.0 ${name}y8.so.9.0 IPP/lib/libippcore.so IPP/lib/libippcore.so.9.0"
                IPPLINK="mkdir -p src/.libs && ln -f ${name}.so.9.0 src/.libs/libippcp.so.9.0 && ln -f ${name}e9.so.9.0 src/.libs/libippcpe9.so.9.0 && ln -f ${name}k0.so.9.0 src/.libs/libippcpk0.so.9.0 && ln -f ${name}l9.so.9.0 src/.libs/libippcpl9.so.9.0 && ln -f ${name}m7.so.9.0 src/.libs/libippcpm7.so.9.0 && ln -f ${name}mx.so.9.0 src/.libs/libippcpmx.so.9.0 && ln -f ${name}.so src/.libs/libippcp.so && ln -f ${name}n8.so.9.0 src/.libs/libippcpn8.so.9.0 && ln -f ${name}y8.so.9.0 src/.libs/libippcpy8.so.9.0 && ln -f IPP/lib/libippcore.so src/.libs/libippcore.so && ln -f IPP/lib/libippcore.so.9.0 src/.libs/libippcore.so.9.0"
            fi
            ], [fastRSA_found=no])
            break;;
        *)
            fastRSA_found=no
        esac

        if test "$fastRSA_found" = "yes"; then
            # was succesfull so add tested LDFLAGS to AM_ flags
            AM_LDFLAGS="${AM_LDFLAGS} ${LDFLAGS}"
            AM_CPPFLAGS="${AM_CPPFLAGS} ${CPPFLAGS}"
            IPPHEADERS="${srcdir}/IPP/include/*.h"
        fi

        # restore LDFLAGS to user set
        LDFLAGS=${STORE_LDFLAGS}
        CPPFLAGS=${STORE_CPPFLAGS}
    ], [fastRSA_found=no])
fi

# Don't cache the result so it can be checked
AS_UNSET([ac_cv_header_ippcp_h])
AS_UNSET([ac_cv_header_ipp_h])
AS_UNSET([ac_cv_lib_ippcp_ippsRSAEncrypt_PKCSv15]);

#   Check link and see if user has pre-existing IPP Libraries if not using local
if test "$ENABLED_FAST_RSA" = "yes" && test "$fastRSA_found" = "no"; then
    AC_MSG_NOTICE([Checking if IPP crypto library installed])
    AC_CHECK_HEADER([ippcp.h], [AC_CHECK_LIB([ippcp], [ippsRSAEncrypt_PKCSv15],
        [
            fastRSA_found=yes
            AM_LDFLAGS="${AM_LDFLAGS} -lippcore -lippcp"
        ], [ fastRSA_found=no])
    ], [fastRSA_found=no])

    # Error out on not finding libraries
    if test "$fastRSA_found" = "no"; then
        AC_MSG_ERROR([Could not find fast rsa libraries])
    fi
fi
fi # end of if for shared library
else # if user rsa is set than do not use fast rsa option
    if test "$ENABLED_FAST_RSA" = "yes"; then
        AC_MSG_ERROR([Could not use fast rsa libraries with user crypto or fips])
    fi
fi # end of if for user rsa crypto or fips

#   End result of checking for IPP Libraries
AC_MSG_CHECKING([for fast RSA])
if test "$ENABLED_FAST_RSA" = "yes"; then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_FAST_RSA -DHAVE_USER_RSA"
    # add in user crypto header that uses Intel IPP
    AM_CPPFLAGS="$AM_CPPFLAGS -I$srcdir/wolfcrypt/user-crypto/include"
    if test "$enable_shared" = "yes"; then
        LIBS="$LIBS -lippcore -lippcp"
        LIB_ADD="-lippcp -lippcore $LIB_ADD"
    else
        LIB_ADD="$srcdir/IPP/$ipplib/libippcp.a $srcdir/IPP/$ipplib/libippcore.a $LIB_ADD"
    fi
    AC_MSG_RESULT([yes])
else
    AC_MSG_RESULT([no])
fi

AC_SUBST([IPPLIBS])
AC_SUBST([IPPHEADERS])
AC_SUBST([IPPLINK])


# static memory use
AC_ARG_ENABLE([staticmemory],
    [AS_HELP_STRING([--enable-staticmemory],[Enable static memory use (default: disabled)])],
    [ ENABLED_STATICMEMORY=$enableval ],
    [ ENABLED_STATICMEMORY=no ]
    )

if test "x$ENABLED_STATICMEMORY" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_STATIC_MEMORY"
    if test "x$ENABLED_FASTMATH" = "xno"
    then
        AC_MSG_ERROR([please use --enable-fastmath if enabling staticmemory.])
    fi
    if test "$ENABLED_LOWRESOURCE" = "yes" && test "$ENABLED_RSA" = "no"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_STATIC_MEMORY_SMALL"
    fi
fi


# microchip api
AC_ARG_ENABLE([mcapi],
    [AS_HELP_STRING([--enable-mcapi],[Enable Microchip API (default: disabled)])],
    [ ENABLED_MCAPI=$enableval ],
    [ ENABLED_MCAPI=no ]
    )

if test "$ENABLED_MCAPI" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_MCAPI"
    if test "x$ENABLED_AESCTR" != "xyes"
    then
        # These flags are already implied by --enable-aesctr
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_AES_COUNTER -DWOLFSSL_AES_DIRECT"
    fi
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


# Asynchronous Crypto
AC_ARG_ENABLE([asynccrypt],
    [AS_HELP_STRING([--enable-asynccrypt],[Enable Asynchronous Crypto (default: disabled)])],
    [ ENABLED_ASYNCCRYPT=$enableval ],
    [ ENABLED_ASYNCCRYPT=no ]
    )

if test "$ENABLED_ASYNCCRYPT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ASYNC_CRYPT -DHAVE_WOLF_EVENT -DHAVE_WOLF_BIGINT -DWOLFSSL_NO_HASH_RAW"

    # if no async hardware then use simulator for testing
    if test "x$ENABLED_CAVIUM" = "xno" && test "x$ENABLED_INTEL_QA" = "xno"
    then
        # Async threading is Linux specific
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_ASYNC_CRYPT_TEST"
    fi
fi


# check for async if using Intel QuckAssist or Cavium
if test "x$ENABLED_INTEL_QA" = "xyes" || test "x$ENABLED_CAVIUM" = "xyes" ; then
    if test "x$ENABLED_ASYNCCRYPT" = "xno" ; then
        AC_MSG_ERROR([Please enable asynchronous support using --enable-asynccrypt])
    fi
fi


# Asynchronous threading
AC_ARG_ENABLE([asyncthreads],
    [AS_HELP_STRING([--enable-asyncthreads],[Enable Asynchronous Threading (default: enabled)])],
    [ ENABLED_ASYNCTHREADS=$enableval ],
    [ ENABLED_ASYNCTHREADS=yes ]
    )

if test "$ENABLED_ASYNCCRYPT" = "yes" && test "$ENABLED_ASYNCTHREADS" = "yes"
then
    AX_PTHREAD([ENABLED_ASYNCTHREADS=yes],[ENABLED_ASYNCTHREADS=no])
else
    ENABLED_ASYNCTHREADS=no
fi

if test "$ENABLED_ASYNCTHREADS" = "yes"
then
    LIB_ADD="-lpthread $LIB_ADD"
    AM_CFLAGS="$AM_CFLAGS -D_GNU_SOURCE"
else
    AM_CFLAGS="$AM_CFLAGS -DWC_NO_ASYNC_THREADING"
fi


# cryptodev is old name, replaced with cryptocb
AC_ARG_ENABLE([cryptodev],
    [AS_HELP_STRING([--enable-cryptodev],[DEPRECATED, use cryptocb instead])],
    [ ENABLED_CRYPTOCB=$enableval ],[ ENABLED_CRYPTOCB=no ])

# Support for crypto callbacks
AC_ARG_ENABLE([cryptocb],
    [AS_HELP_STRING([--enable-cryptocb],[Enable crypto callbacks (default: disabled)])],
    [ ENABLED_CRYPTOCB=$enableval ],
    [ ENABLED_CRYPTOCB=no ]
    )

if test "x$ENABLED_PKCS11" = "xyes"
then
    ENABLED_CRYPTOCB=yes
fi
if test "$ENABLED_CRYPTOCB" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLF_CRYPTO_CB"
fi


# Session Export
AC_ARG_ENABLE([sessionexport],
    [AS_HELP_STRING([--enable-sessionexport],[Enable export and import of sessions (default: disabled)])],
    [ ENABLED_SESSIONEXPORT=$enableval ],
    [ ENABLED_SESSIONEXPORT=no ]
    )

if test "$ENABLED_SESSIONEXPORT" = "yes" ||
   test "$ENABLED_SESSIONEXPORT" = "nopeer"
then
    if test "$ENABLED_DTLS" = "no"
    then
        AC_MSG_ERROR([Only DTLS supported with session export])
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SESSION_EXPORT"

    if test "$ENABLED_SESSIONEXPORT" = "nopeer"
    then
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_SESSION_EXPORT_NOPEER"
    fi
fi


# AES key wrap
AC_ARG_ENABLE([aeskeywrap],
    [AS_HELP_STRING([--enable-aeskeywrap],[Enable AES key wrap support (default: disabled)])],
    [ ENABLED_AESKEYWRAP=$enableval ],
    [ ENABLED_AESKEYWRAP=no ]
    )

if test "$ENABLED_WPAS" = "yes" && test "$ENABLED_FIPS" = "no"
then
    ENABLED_AESKEYWRAP="yes"
fi

if test "$ENABLED_AESKEYWRAP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_AES_KEYWRAP -DWOLFSSL_AES_DIRECT"
fi


# Old name support for backwards compatibility
AC_ARG_ENABLE([oldnames],
    [AS_HELP_STRING([--enable-oldnames],[Keep backwards compat with old names (default: enabled)])],
    [ ENABLED_OLDNAMES=$enableval ],
    [ ENABLED_OLDNAMES=yes ]
    )

if test "x$ENABLED_OLDNAMES" = "xno" && test "x$ENABLED_OPENSSLCOEXIST" = "xno"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_OLD_RNGNAME -DNO_OLD_WC_NAMES -DNO_OLD_SSL_NAMES"
    AM_CFLAGS="$AM_CFLAGS -DNO_OLD_SHA_NAMES"
fi


# Memory Tests
AC_ARG_ENABLE([memtest],
    [AS_HELP_STRING([--enable-memtest],[Memory testing option, for internal use (default: disabled)])],
    [ ENABLED_MEMTEST=$enableval ],
    [ ENABLED_MEMTEST=no ]
    )

if test "x$ENABLED_MEMTEST" != "xno"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_TRACK_MEMORY -DWOLFSSL_DEBUG_MEMORY -DWOLFSSL_FORCE_MALLOC_FAIL_TEST"
fi


# Enable hash flags support
# Hash flags are useful for runtime options such as SHA3 KECCAK256 selection
AC_ARG_ENABLE([hashflags],
    [AS_HELP_STRING([--enable-hashflags],[Enable support for hash flags (default: disabled)])],
    [ ENABLED_HASHFLAGS=$enableval ],
    [ ENABLED_HASHFLAGS=no ]
    )

if test "x$ENABLED_HASHFLAGS" != "xno"
then
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HASH_FLAGS"
fi

# Support for enabling setting default DH parameters in
AC_ARG_ENABLE([defaultdhparams],
    [AS_HELP_STRING([--enable-dhdefaultparams],[Enables option for default dh parameters (default: disabled)])],
    [ ENABLED_DHDEFAULTPARAMS=$enableval ],
    [ ENABLED_DHDEFAULTPARAMS=no ]
    )
if test "$ENABLED_DHDEFAULTPARAMS" = "yes" || test "$ENABLED_QT" = "no"
then
    ENABLED_DHDEFAULTPARAMS=yes
    AM_CFLAGS="$AM_CFLAGS -DHAVE_DH_DEFAULT_PARAMS"
fi

# User Settings
AC_ARG_ENABLE([usersettings],
    [AS_HELP_STRING([--enable-usersettings],[Use your own user_settings.h and do not add Makefile CFLAGS (default: disabled)])],
    [ ENABLED_USERSETTINGS=$enableval ],
    [ ENABLED_USERSETTINGS=no ]
    )


# Default optimization CFLAGS enable
AC_ARG_ENABLE([optflags],
    [AS_HELP_STRING([--enable-optflags],[Enable default optimization CFLAGS for the compiler (default: enabled)])],
    [ ENABLED_OPTFLAGS=$enableval ],
    [ ENABLED_OPTFLAGS=yes ]
    )


# check if should run the trusted peer certs test
# (for now checking both C_FLAGS and C_EXTRA_FLAGS)
AS_CASE(["$CFLAGS $CPPFLAGS"],[*'WOLFSSL_TRUST_PEER_CERT'*],[ENABLED_TRUSTED_PEER_CERT=yes])


# dertermine if we have key validation mechanism
if test "x$ENABLED_ECC" != "xno" || test "x$ENABLED_RSA" = "xyes"
then
    if test "x$ENABLED_ASN" = "xyes"
    then
        ENABLED_PKI="yes"
    fi
fi


# When building for wolfRand, strip out all options to disable everything.
AS_IF([test "x$ENABLED_FIPS" = "xyes" && test "x$FIPS_VERSION" = "xrand"],
[NEW_AM_CFLAGS="-DNO_AES -DNO_DH -DNO_ASN -DNO_RSA -DNO_SHA -DNO_MD5 -DNO_BIG_INT"
for v in $AM_CFLAGS
do
  case $v in
-DHAVE_FFDHE_2048 | -DTFM_TIMING_RESISTANT | -DECC_TIMING_RESISTANT | \
-DWC_RSA_BLINDING | -DHAVE_AESGCM | -DWOLFSSL_SHA512 | -DWOLFSSL_SHA384 | \
-DHAVE_ECC | -DTFM_ECC256 | -DECC_SHAMIR | -DHAVE_TLS_EXTENSIONS | \
-DHAVE_SUPPORTED_CURVES | -DHAVE_EXTENDED_MASTER | -DUSE_FAST_MATH)
    AS_ECHO(["ignoring $v"])
    ;;
  *)
    NEW_AM_CFLAGS="$NEW_AM_CFLAGS $v"
    ;;
  esac
done
AM_CFLAGS=$NEW_AM_CFLAGS])


################################################################################
# Check for build-type conflicts                                               #
################################################################################

AS_IF([test "x$ENABLED_MAXSTRENGTH" = "xyes" && \
       test "x$ENABLED_LEANPSK" = "xyes"],
      [AC_MSG_ERROR([Cannot use Max Strength and Lean PSK at the same time.])])

AS_IF([test "x$ENABLED_OCSP" = "xyes" && \
       test "x$ENABLED_ASN" = "xno"],
      [AC_MSG_ERROR([please enable asn if enabling ocsp.])])

AS_IF([test "x$ENABLED_OCSP" = "xyes" && \
       test "x$ENABLED_RSA" = "xno" && \
       test "x$ENABLED_ECC" = "xno"],
      [AC_MSG_ERROR([please enable rsa or ecc if enabling ocsp.])])

# Sync Intel QA and Sync Cavium Octeon require the crypto callback
AS_IF([test "x$ENABLED_INTEL_QA_SYNC" = "xyes" || test "x$ENABLED_OCTEON_SYNC" = "xyes"],
        [AS_IF([test "x$ENABLED_CRYPTOCB" = "xno"],
         [AC_MSG_ERROR([please enable the crypto callback support using --enable-cryptocb])])])

# checks for pkcs7 needed enables
AS_IF([test "x$ENABLED_PKCS7" = "xyes" && \
       test "x$ENABLED_RSA" = "xno" && \
       test "x$ENABLED_ECC" = "xno"],
      [AC_MSG_ERROR([please enable ecc or rsa if enabling pkcs7.])])

AS_IF([test "x$ENABLED_PKCS7" = "xyes" && \
       test "x$ENABLED_SHA" = "xno"],
      [AC_MSG_ERROR([please enable sha if enabling pkcs7.])])

AS_IF([test "x$ENABLED_PKCS7" = "xyes" && \
       test "x$ENABLED_AES" = "xno" && \
       test "x$ENABLED_DES3" = "xno"],
      [AC_MSG_ERROR([please enable either AES or 3DES if enabling pkcs7.])])

AS_IF([test "x$ENABLED_WOLFSCEP" = "xyes" && \
       test "x$ENABLED_AES" = "xno" && \
       test "x$ENABLED_DES3" = "xno"],
      [AC_MSG_ERROR([please enable either AES or 3DES if enabling scep.])])

AS_IF([test "x$ENABLED_LEANTLS" = "xyes" && \
       test "x$ENABLED_ECC" = "xno"],
      [AC_MSG_ERROR([please enable ecc if enabling leantls.])])

AS_IF([test "x$ENABLED_SNIFFER" = "xyes" && \
       test "x$ENABLED_RSA" = "xno" && \
       test "x$ENABLED_ECC" = "xno"],
      [AC_MSG_ERROR([please enable ecc or rsa if enabling sniffer.])])

# Lean TLS forces off prereqs of SCEP.
AS_IF([test "x$ENABLED_SCEP" = "xyes" && \
       test "x$ENABLED_LEANTLS" = "xyes"],
      [AC_MSG_ERROR([Cannot use SCEP and Lean TLS at the same time.])])

# CMAC currently requires AES.
AS_IF([test "x$ENABLED_CMAC" = "xyes" && \
       test "x$ENABLED_AES" = "xno"],
      [AC_MSG_ERROR([cannot use CMAC without AES.])])

################################################################################
# Update CFLAGS based on options                                               #
################################################################################

AS_IF([test "x$ENABLED_MCAPI" = "xyes"],
      [AS_IF([test "x$ENABLED_DES3" = "xno"],[ENABLED_DES3="yes"])])

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
    if test "x$ENABLED_CERTEXT" = "xno"
    then
        ENABLED_CERTEXT="yes"
        AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_CERT_EXT"
    fi
    if test "x$ENABLED_PKCS7" = "xno"
    then
        ENABLED_PKCS7="yes"
    fi
    AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_HAVE_WOLFSCEP"
fi
#if test "$ENABLED_SP_MATH" = "yes" && test "$ENABLED_KEYGEN" = "yes"; then
#    AC_MSG_ERROR([Cannot use single precision math and key generation])
#fi

if test "x$ENABLED_PKCS7" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_PKCS7"
    # Enable prereqs if not already enabled
    if test "x$ENABLED_AESKEYWRAP" = "xno"
    then
        ENABLED_AESKEYWRAP="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_AES_KEYWRAP -DWOLFSSL_AES_DIRECT"
    fi
    if test "x$ENABLED_X963KDF" = "xno" && test "$ENABLED_ECC" != "no"
    then
        ENABLED_X963KDF="yes"
        AM_CFLAGS="$AM_CFLAGS -DHAVE_X963_KDF"
    fi
fi

if test "x$ENABLED_DES3" = "xno"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_DES3"
else
    # turn off DES3 if leanpsk or leantls on
    if test "$ENABLED_LEANPSK" = "yes" || test "$ENABLED_LEANTLS" = "yes"
    then
        AM_CFLAGS="$AM_CFLAGS -DNO_DES3"
        ENABLED_DES3=no
    fi
fi


AS_IF([test "x$ENABLED_MAXSTRENGTH" = "xyes"],
      [AM_CFLAGS="$AM_CFLAGS -DWOLFSSL_MAX_STRENGTH"])

AS_IF([test "x$ENABLED_MAXSTRENGTH" = "xyes" && \
       test "x$ENABLED_OLD_TLS" = "xyes"],
      [AM_CFLAGS="$AM_CFLAGS -DNO_OLD_TLS"
       ENABLED_OLD_TLS=no])

AS_IF([test "x$ENABLED_MAXSTRENGTH" = "xyes" && \
       test "x$ENABLED_SSLV3" = "xyes"],
      [AC_MSG_ERROR([Cannot use Max Strength and SSLv3 at the same time.])])

AS_IF([test "x$ENABLED_SCTP" = "xyes"],
      [AM_CFLAGS="-DWOLFSSL_SCTP $AM_CFLAGS"])

AS_IF([test "x$ENABLED_MCAST" = "xyes"],
      [AM_CFLAGS="-DWOLFSSL_MULTICAST $AM_CFLAGS"])

# WOLFSSL_AFALG does not support SHA224 yet
AS_IF([(test "x$ENABLED_AFALG" = "xyes") && (test "x$ENABLED_SHA224" = "xyes")],
      [AC_MSG_ERROR([--enable-sha224 with --enable-afalg not yet supported])])

# WOLFSSL_DEVCRYPTO does not support SHA224 yet
AS_IF([(test "x$ENABLED_DEVCRYPTO" = "xyes") && (test "x$ENABLED_SHA224" = "xyes")],
      [AC_MSG_ERROR([--enable-sha224 with --enable-devcrypto not yet supported])])

# SCTP and Multicast require DTLS
AS_IF([(test "x$ENABLED_DTLS" = "xno") && \
        (test "x$ENABLED_SCTP" = "xyes" || test "x$ENABLED_MCAST" = "xyes")],
      [AM_CFLAGS="-DWOLFSSL_DTLS $AM_CFLAGS"
       ENABLED_DTLS=yes])

# Multicast requires the null cipher
AS_IF([test "x$ENABLED_NULL_CIPHER" = "xno" && \
        test "x$ENABLED_MCAST" = "xyes"],
      [AM_CFLAGS="-DHAVE_NULL_CIPHER $AM_CFLAGS"
       ENABLED_NULL_CIPHER=yes])

# wolfSSH and WPA Supplicant both need Public MP, only enable once.
# This will let you know if you enabled wolfSSH but have any of the prereqs
# disabled. Some of these options, disabling them adds things to the FLAGS and
# you need to check and add items in two places depending on the option.
AS_IF([test "x$ENABLED_WOLFSSH" = "xyes"],
      [AS_IF([test "x$ENABLED_WPAS" = "xno"],[AM_CFLAGS="-DWOLFSSL_PUBLIC_MP $AM_CFLAGS"])
       AS_IF([test "x$ENABLED_AESGCM" = "xno"],[AC_MSG_ERROR([cannot enable wolfSSH with AES-GCM disabled])])
       AS_IF([test "x$ENABLED_ECC" = "xno"],[AC_MSG_ERROR([cannot enable wolfSSH with ECC disabled])])
       AS_IF([test "x$ENABLED_SHA" = "xno"],[AC_MSG_ERROR([cannot enable wolfSSH with SHA-1 disabled])])
       AS_IF([test "x$ENABLED_SHA512" = "xno"],[AC_MSG_ERROR([cannot enable wolfSSH with SHA-512/384 disabled])])
      ])

if test "x$ENABLED_OPENSSLCOEXIST" = "xyes"; then
    if test "x$ENABLED_OPENSSLALL" = "xyes"; then
        AC_MSG_ERROR([Cannot use --enable-opensslcoexist with --enable-opensslall])
    fi
    if test "x$ENABLED_OPENSSLEXTRA" = "xyes"; then
        AC_MSG_ERROR([Cannot use --enable-opensslcoexist with --enable-opensslextra])
    fi
fi
################################################################################

# USER SETTINGS
if test "x$ENABLED_USERSETTINGS" = "xyes"
then
    # Replace all options and just use WOLFSSL_USER_SETTINGS
    AM_CFLAGS="-DWOLFSSL_USER_SETTINGS"
fi

# OPTIMIZE FLAGS
# For distro disable custom build options that interfere with symbol generation
if test "$GCC" = "yes" && test "$ENABLED_DISTRO" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -Wall -Wno-unused"
    if test "$ax_enable_debug" = "no"
    then
    AS_IF([test "x$ENABLED_OPTFLAGS" = "xyes"], [
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
    ])
    fi
fi

# ICC command line warning for non supported warning flags
if test "$CC" = "icc"
then
    AM_CFLAGS="$AM_CFLAGS -wd10006"
fi

# Expose HAVE___UINT128_T to options flags"
if test "$ac_cv_type___uint128_t" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE___UINT128_T=1"
fi


LIB_SOCKET_NSL
AX_HARDEN_CC_COMPILER_FLAGS

# if mingw then link to ws2_32 for sockets
case $host_os in
    mingw*)
        LDFLAGS="$LDFLAGS -lws2_32"
        if test "$enable_shared" = "yes"
        then
            AC_DEFINE([WOLFSSL_DLL], [1], [Use __declspec(dllexport) when building library])
            if test "$enable_static" = "yes"
            then
                MINGW_LIB_WARNING="yes"
            fi
        fi ;;
esac


# The following AM_CONDITIONAL statements set flags for use in the Makefiles.
# Some of these affect build targets and objects, some trigger different
# test scripts for make check.
AM_CONDITIONAL([BUILD_DISTRO],[test "x$ENABLED_DISTRO" = "xyes"])
AM_CONDITIONAL([BUILD_ALL],[test "x$ENABLED_ALL" = "xyes"])
AM_CONDITIONAL([BUILD_TLS13],[test "x$ENABLED_TLS13" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_RNG],[test "x$ENABLED_RNG" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SCTP],[test "x$ENABLED_SCTP" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_MCAST],[test "x$ENABLED_MCAST" = "xyes"])
AM_CONDITIONAL([BUILD_IPV6],[test "x$ENABLED_IPV6" = "xyes"])
AM_CONDITIONAL([BUILD_LEANPSK],[test "x$ENABLED_LEANPSK" = "xyes"])
AM_CONDITIONAL([BUILD_LEANTLS],[test "x$ENABLED_LEANTLS" = "xyes"])
AM_CONDITIONAL([BUILD_LOWMEM],[test "x$ENABLED_LOWRESOURCE" = "xyes"])
AM_CONDITIONAL([BUILD_PKCALLBACKS],  [ test "x$ENABLED_PKCALLBACKS" = "xyes"])
AM_CONDITIONAL([BUILD_CRYPTOAUTHLIB],[test "x$ENABLED_CRYPTOAUTHLIB" = "xyes"])
AM_CONDITIONAL([BUILD_SNIFFER],  [ test "x$ENABLED_SNIFFER"   = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SNIFFTEST],[ test "x$ENABLED_SNIFFTEST" = "xyes"])
AM_CONDITIONAL([BUILD_AESGCM],[test "x$ENABLED_AESGCM" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_AESCCM],[test "x$ENABLED_AESCCM" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_ARMASM],[test "x$ENABLED_ARMASM" = "xyes"])
AM_CONDITIONAL([BUILD_XILINX],[test "x$ENABLED_XILINX" = "xyes"])
AM_CONDITIONAL([BUILD_AESNI],[test "x$ENABLED_AESNI" = "xyes"])
AM_CONDITIONAL([BUILD_INTELASM],[test "x$ENABLED_INTELASM" = "xyes"])
AM_CONDITIONAL([BUILD_AFALG],[test "x$ENABLED_AFALG" = "xyes"])
AM_CONDITIONAL([BUILD_DEVCRYPTO],[test "x$ENABLED_DEVCRYPTO" = "xyes"])
AM_CONDITIONAL([BUILD_CAMELLIA],[test "x$ENABLED_CAMELLIA" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_MD2],[test "x$ENABLED_MD2" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_RIPEMD],[test "x$ENABLED_RIPEMD" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_BLAKE2],[test "x$ENABLED_BLAKE2" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_BLAKE2S],[test "x$ENABLED_BLAKE2S" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SHA512],[test "x$ENABLED_SHA512" = "xyes" || test "x$ENABLED_SHA384" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_DSA],[test "x$ENABLED_DSA" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_ECC],[test "x$ENABLED_ECC" != "xno" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_ED25519],[test "x$ENABLED_ED25519" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_ED25519_SMALL],[test "x$ENABLED_ED25519_SMALL" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_FEMATH], [test "x$ENABLED_FEMATH" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_GEMATH], [test "x$ENABLED_GEMATH" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CURVE25519],[test "x$ENABLED_CURVE25519" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CURVE25519_SMALL],[test "x$ENABLED_CURVE25519_SMALL" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_ED448],[test "x$ENABLED_ED448" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_ED448_SMALL],[test "x$ENABLED_ED448_SMALL" = "xyes"])
AM_CONDITIONAL([BUILD_FE448], [test "x$ENABLED_FE448" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_GE448], [test "x$ENABLED_GE448" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CURVE448],[test "x$ENABLED_CURVE448" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CURVE448_SMALL],[test "x$ENABLED_CURVE448_SMALL" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_MEMORY],[test "x$ENABLED_MEMORY" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_RSA],[test "x$ENABLED_RSA" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_DH],[test "x$ENABLED_DH" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_ASN],[test "x$ENABLED_ASN" != "xno" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_AES],[test "x$ENABLED_AES" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CODING],[test "x$ENABLED_CODING" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_IDEA],[test "x$ENABLED_IDEA" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_RC4],[test "x$ENABLED_ARC4" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_MD5],[test "x$ENABLED_MD5" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SHA],[test "x$ENABLED_SHA" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_HC128],[test "x$ENABLED_HC128" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_RABBIT],[test "x$ENABLED_RABBIT" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_FIPS],[test "x$ENABLED_FIPS" = "xyes"])
AM_CONDITIONAL([BUILD_FIPS_V1],[test "x$FIPS_VERSION" = "xv1"])
AM_CONDITIONAL([BUILD_FIPS_V2],[test "x$FIPS_VERSION" = "xv2"])
AM_CONDITIONAL([BUILD_FIPS_RAND],[test "x$FIPS_VERSION" = "xrand"])
AM_CONDITIONAL([BUILD_CMAC],[test "x$ENABLED_CMAC" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SELFTEST],[test "x$ENABLED_SELFTEST" = "xyes"])
AM_CONDITIONAL([BUILD_SHA224],[test "x$ENABLED_SHA224" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SHA3],[test "x$ENABLED_SHA3" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_POLY1305],[test "x$ENABLED_POLY1305" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CHACHA],[test "x$ENABLED_CHACHA" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_INLINE],[test "x$ENABLED_INLINE" = "xyes"])
AM_CONDITIONAL([BUILD_OCSP],[test "x$ENABLED_OCSP" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_OCSP_STAPLING],[test "x$ENABLED_CERTIFICATE_STATUS_REQUEST" = "xyes"])
AM_CONDITIONAL([BUILD_OCSP_STAPLING_V2],[test "x$ENABLED_CERTIFICATE_STATUS_REQUEST_V2" = "xyes"])
AM_CONDITIONAL([BUILD_CRL],[test "x$ENABLED_CRL" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CRL_MONITOR],[test "x$ENABLED_CRL_MONITOR" = "xyes"])
AM_CONDITIONAL([BUILD_USER_RSA],[test "x$ENABLED_USER_RSA" = "xyes"] )
AM_CONDITIONAL([BUILD_USER_CRYPTO],[test "x$ENABLED_USER_CRYPTO" = "xyes"])
AM_CONDITIONAL([BUILD_NTRU],[test "x$ENABLED_NTRU" = "xyes"])
AM_CONDITIONAL([BUILD_WNR],[test "x$ENABLED_WNR" = "xyes"])
AM_CONDITIONAL([BUILD_SRP],[test "x$ENABLED_SRP" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([USE_VALGRIND],[test "x$ENABLED_VALGRIND" = "xyes"])
AM_CONDITIONAL([BUILD_MD4],[test "x$ENABLED_MD4" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_PWDBASED],[test "x$ENABLED_PWDBASED" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SCRYPT],[test "x$ENABLED_SCRYPT" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CRYPTONLY],[test "x$ENABLED_CRYPTONLY" = "xyes" && test "x$ENABLED_OPENSSLEXTRA" = "xno"])
AM_CONDITIONAL([BUILD_FASTMATH],[test "x$ENABLED_FASTMATH" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SLOWMATH],[test "x$ENABLED_SLOWMATH" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_EXAMPLE_SERVERS],[test "x$ENABLED_EXAMPLES" = "xyes" && test "x$ENABLED_LEANTLS" = "xno"])
AM_CONDITIONAL([BUILD_EXAMPLE_CLIENTS],[test "x$ENABLED_EXAMPLES" = "xyes"])
AM_CONDITIONAL([BUILD_TESTS],[test "x$ENABLED_EXAMPLES" = "xyes" && test "x$ENABLED_LEANTLS" = "xno"])
AM_CONDITIONAL([BUILD_THREADED_EXAMPLES],[test "x$ENABLED_SINGLETHREADED" = "xno" && test "x$ENABLED_EXAMPLES" = "xyes" && test "x$ENABLED_LEANTLS" = "xno"])
AM_CONDITIONAL([BUILD_WOLFCRYPT_TESTS],[test "x$ENABLED_CRYPT_TESTS" = "xyes"])
AM_CONDITIONAL([BUILD_LIBZ],[test "x$ENABLED_LIBZ" = "xyes"])
AM_CONDITIONAL([BUILD_PKCS11],[test "x$ENABLED_PKCS11" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_PKCS12],[test "x$ENABLED_PKCS12" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_CAVIUM],[test "x$ENABLED_CAVIUM" = "xyes"])
AM_CONDITIONAL([BUILD_CAVIUM_V],[test "x$ENABLED_CAVIUM_V" = "xyes"])
AM_CONDITIONAL([BUILD_OCTEON_SYNC],[test "x$ENABLED_OCTEON_SYNC" = "xyes"])
AM_CONDITIONAL([BUILD_INTEL_QA],[test "x$ENABLED_INTEL_QA" = "xyes"])
AM_CONDITIONAL([BUILD_INTEL_QA_SYNC],[test "x$ENABLED_INTEL_QA_SYNC" = "xyes"])
AM_CONDITIONAL([BUILD_SP],[test "x$ENABLED_SP" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SP_C],[(test "x$ENABLED_SP" = "xyes" && test "x$ENABLED_SP_ASM" = "xno") || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SP_ARM64],[test "x$ENABLED_SP_ARM64_ASM" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SP_ARM32],[test "x$ENABLED_SP_ARM32_ASM" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SP_ARM_THUMB],[test "x$ENABLED_SP_ARM_THUMB_ASM" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SP_ARM_CORTEX],[test "x$ENABLED_SP_ARM_CORTEX_ASM" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SP_X86_64],[test "x$ENABLED_SP_X86_64_ASM" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_SP_INT],[test "x$ENABLED_SP_MATH" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_FAST_RSA],[test "x$ENABLED_FAST_RSA" = "xyes"])
AM_CONDITIONAL([BUILD_MCAPI],[test "x$ENABLED_MCAPI" = "xyes"])
AM_CONDITIONAL([BUILD_ASYNCCRYPT],[test "x$ENABLED_ASYNCCRYPT" = "xyes"])
AM_CONDITIONAL([BUILD_WOLFEVENT],[test "x$ENABLED_ASYNCCRYPT" = "xyes"])
AM_CONDITIONAL([BUILD_CRYPTOCB],[test "x$ENABLED_CRYPTOCB" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_PSK],[test "x$ENABLED_PSK" = "xyes"])
AM_CONDITIONAL([BUILD_TRUST_PEER_CERT],[test "x$ENABLED_TRUSTED_PEER_CERT" = "xyes"])
AM_CONDITIONAL([BUILD_PKI],[test "x$ENABLED_PKI" = "xyes"])
AM_CONDITIONAL([BUILD_DES3],[test "x$ENABLED_DES3" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_PKCS7],[test "x$ENABLED_PKCS7" = "xyes" || test "x$ENABLED_USERSETTINGS" = "xyes"])
AM_CONDITIONAL([BUILD_HASHFLAGS],[test "x$ENABLED_HASHFLAGS" = "xyes"])


CREATE_HEX_VERSION
AC_SUBST([AM_CPPFLAGS])
AC_SUBST([AM_CFLAGS])
AC_SUBST([AM_LDFLAGS])
AC_SUBST([AM_CCASFLAGS])
AC_SUBST([LIB_ADD])
AC_SUBST([LIB_STATIC_ADD])

# FINAL
AC_CONFIG_FILES([stamp-h], [echo timestamp > stamp-h])
AC_CONFIG_FILES([Makefile wolfssl/version.h wolfssl/options.h cyassl/options.h support/wolfssl.pc rpm/spec])

AX_CREATE_GENERIC_CONFIG
AX_AM_JOBSERVER([yes])

AC_OUTPUT


# force make clean
echo "---"
echo "Running make clean..."
make clean >/dev/null 2>&1

# generate user options header
echo "---"
echo "Generating user options header..."

OPTION_FILE="wolfssl/options.h"
rm -f $OPTION_FILE

echo "/* wolfssl options.h" > $OPTION_FILE
echo " * generated from configure options" >> $OPTION_FILE
echo " *" >> $OPTION_FILE
echo " * Copyright (C) 2006-2020 wolfSSL Inc." >> $OPTION_FILE
echo " *" >> $OPTION_FILE
echo " * This file is part of wolfSSL. (formerly known as CyaSSL)" >> $OPTION_FILE
echo " *" >> $OPTION_FILE
echo " */" >> $OPTION_FILE

echo "" >> $OPTION_FILE
echo "#ifndef WOLFSSL_OPTIONS_H" >> $OPTION_FILE
echo "#define WOLFSSL_OPTIONS_H" >> $OPTION_FILE
echo "" >> $OPTION_FILE
echo "" >> $OPTION_FILE
echo "#ifdef __cplusplus" >> $OPTION_FILE
echo "extern \"C\" {" >> $OPTION_FILE
echo "#endif" >> $OPTION_FILE
echo "" >> $OPTION_FILE

for option in $CPPFLAGS $AM_CPPFLAGS $CFLAGS $AM_CFLAGS; do
    defonly=`echo $option | sed 's/^-D//'`
    if test "$defonly" != "$option"
    then
        noequalsign=`echo $defonly | sed 's/=/ /'`
        if test "$noequalsign" = "NDEBUG" || test "$noequalsign" = "DEBUG"
        then
            echo "not outputting (N)DEBUG to $OPTION_FILE"
            continue
        fi

        # allow user to ignore system options
        ignoresys=$(echo "$noequalsign" | grep '^_.*')
        if test -n "$ignoresys"
        then
            echo "#ifndef WOLFSSL_OPTIONS_IGNORE_SYS" >> $OPTION_FILE
        fi

        noarg=`echo $defonly | sed 's/=.*//'`
        echo "#undef  $noarg" >> $OPTION_FILE
        echo "#define $noequalsign" >> $OPTION_FILE

        if test -n "$ignoresys"
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
echo "" >> $OPTION_FILE
echo "#endif /* WOLFSSL_OPTIONS_H */" >> $OPTION_FILE
echo "" >> $OPTION_FILE
echo

#backwards compatibility for those who have included options or version
touch cyassl/options.h
echo "/* cyassl options.h" > cyassl/options.h
echo " * generated from wolfssl/options.h" >> cyassl/options.h
echo " */" >> cyassl/options.h
echo ""
while read -r line
do
    echo "$line" >> cyassl/options.h
done < $OPTION_FILE

# switch ifdef protection in cyassl/option.h to CYASSL_OPTONS_H, remove bak
sed -i.bak 's/WOLFSSL_OPTIONS_H/CYASSL_OPTIONS_H/g' cyassl/options.h

# workaround for mingw sed that may get "Permission denied" trying to preserver permissions
case $host_os in
    mingw*)
        chmod u+w cyassl/options.h ;;
esac

rm cyassl/options.h.bak


# output config summary
echo "---"
echo "Configuration summary for $PACKAGE_NAME version $VERSION"
echo ""
echo "   * Installation prefix:        $prefix"
echo "   * System type:                $host_vendor-$host_os"
echo "   * Host CPU:                   $host_cpu"
echo "   * C Compiler:                 $CC"
echo "   * C Flags:                    $CFLAGS"
echo "   * C++ Compiler:               $CXX"
echo "   * C++ Flags:                  $CXXFLAGS"
echo "   * CPP Flags:                  $CPPFLAGS"
echo "   * CCAS Flags:                 $CCASFLAGS"
echo "   * LIB Flags:                  $LIB"
echo "   * Debug enabled:              $ax_enable_debug"
echo "   * Coverage enabled:           $ax_enable_coverage"
echo "   * Warnings as failure:        $ac_cv_warnings_as_errors"
echo "   * make -j:                    $enable_jobserver"
echo "   * VCS checkout:               $ac_cv_vcs_checkout"
echo
echo "   Features "
echo "   * Single threaded:            $ENABLED_SINGLETHREADED"
echo "   * Filesystem:                 $ENABLED_FILESYSTEM"
echo "   * OpenSSH Build:              $ENABLED_OPENSSH"
echo "   * OpenSSL Extra API:          $ENABLED_OPENSSLEXTRA"
echo "   * OpenSSL Coexist:            $ENABLED_OPENSSLCOEXIST"
echo "   * Old Names:                  $ENABLED_OLDNAMES"
echo "   * Max Strength Build:         $ENABLED_MAXSTRENGTH"
echo "   * Distro Build:               $ENABLED_DISTRO"
echo "   * fastmath:                   $ENABLED_FASTMATH"
echo "   * Assembly Allowed:           $ENABLED_ASM"
echo "   * sniffer:                    $ENABLED_SNIFFER"
echo "   * snifftest:                  $ENABLED_SNIFFTEST"
echo "   * ARC4:                       $ENABLED_ARC4"
echo "   * AES:                        $ENABLED_AES"
echo "   * AES-NI:                     $ENABLED_AESNI"
echo "   * AES-CBC:                    $ENABLED_AESCBC"
echo "   * AES-GCM:                    $ENABLED_AESGCM"
echo "   * AES-CCM:                    $ENABLED_AESCCM"
echo "   * AES-CTR:                    $ENABLED_AESCTR"
echo "   * DES3:                       $ENABLED_DES3"
echo "   * IDEA:                       $ENABLED_IDEA"
echo "   * Camellia:                   $ENABLED_CAMELLIA"
echo "   * NULL Cipher:                $ENABLED_NULL_CIPHER"
echo "   * MD5:                        $ENABLED_MD5"
echo "   * RIPEMD:                     $ENABLED_RIPEMD"
echo "   * SHA:                        $ENABLED_SHA"
echo "   * SHA-224:                    $ENABLED_SHA224"
echo "   * SHA-384:                    $ENABLED_SHA384"
echo "   * SHA-512:                    $ENABLED_SHA512"
echo "   * SHA3:                       $ENABLED_SHA3"
echo "   * SHAKE256:                   $ENABLED_SHAKE256"
echo "   * BLAKE2:                     $ENABLED_BLAKE2"
echo "   * CMAC:                       $ENABLED_CMAC"
echo "   * keygen:                     $ENABLED_KEYGEN"
echo "   * certgen:                    $ENABLED_CERTGEN"
echo "   * certreq:                    $ENABLED_CERTREQ"
echo "   * certext:                    $ENABLED_CERTEXT"
echo "   * certgencache:               $ENABLED_certgencache"
echo "   * HC-128:                     $ENABLED_HC128"
echo "   * RABBIT:                     $ENABLED_RABBIT"
echo "   * CHACHA:                     $ENABLED_CHACHA"
echo "   * Hash DRBG:                  $ENABLED_HASHDRBG"
echo "   * PWDBASED:                   $ENABLED_PWDBASED"
echo "   * scrypt:                     $ENABLED_SCRYPT"
echo "   * wolfCrypt Only:             $ENABLED_CRYPTONLY"
echo "   * HKDF:                       $ENABLED_HKDF"
echo "   * X9.63 KDF:                  $ENABLED_X963KDF"
echo "   * MD4:                        $ENABLED_MD4"
echo "   * PSK:                        $ENABLED_PSK"
echo "   * Poly1305:                   $ENABLED_POLY1305"
echo "   * LEANPSK:                    $ENABLED_LEANPSK"
echo "   * LEANTLS:                    $ENABLED_LEANTLS"
echo "   * RSA:                        $ENABLED_RSA"
echo "   * RSA-PSS:                    $ENABLED_RSAPSS"
echo "   * DSA:                        $ENABLED_DSA"
echo "   * DH:                         $ENABLED_DH"
echo "   * DH Default Parameters:      $ENABLED_DHDEFAULTPARAMS"
echo "   * ECC:                        $ENABLED_ECC"
echo "   * ECC Custom Curves           $ENABLED_ECCCUSTCURVES"
echo "   * CURVE25519:                 $ENABLED_CURVE25519"
echo "   * ED25519:                    $ENABLED_ED25519"
echo "   * CURVE448:                   $ENABLED_CURVE448"
echo "   * ED448:                      $ENABLED_ED448"
echo "   * FPECC:                      $ENABLED_FPECC"
echo "   * ECC_ENCRYPT:                $ENABLED_ECC_ENCRYPT"
echo "   * ASN:                        $ENABLED_ASN"
echo "   * Anonymous cipher:           $ENABLED_ANON"
echo "   * CODING:                     $ENABLED_CODING"
echo "   * MEMORY:                     $ENABLED_MEMORY"
echo "   * I/O POOL:                   $ENABLED_IOPOOL"
echo "   * LIGHTY:                     $ENABLED_LIGHTY"
echo "   * HAPROXY:                    $ENABLED_HAPROXY"
echo "   * STUNNEL:                    $ENABLED_STUNNEL"
echo "   * Apache httpd:               $ENABLED_APACHE_HTTPD"
echo "   * NGINX:                      $ENABLED_NGINX"
echo "   * ASIO:                       $ENABLED_ASIO"
echo "   * LIBWEBSOCKETS:              $ENABLED_LIBWEBSOCKETS"
echo "   * Qt                          $ENABLED_QT"
echo "   * Qt Unit Testing             $ENABLED_QT_TEST"
echo "   * SIGNAL:                     $ENABLED_SIGNAL"
echo "   * ERROR_STRINGS:              $ENABLED_ERROR_STRINGS"
echo "   * DTLS:                       $ENABLED_DTLS"
echo "   * SCTP:                       $ENABLED_SCTP"
echo "   * Indefinite Length:          $ENABLED_BER_INDEF"
echo "   * Multicast:                  $ENABLED_MCAST"
echo "   * SSL v3.0 (Old):             $ENABLED_SSLV3"
echo "   * TLS v1.0 (Old):             $ENABLED_TLSV10"
echo "   * TLS v1.1 (Old):             $ENABLED_OLD_TLS"
echo "   * TLS v1.2:                   $ENABLED_TLSV12"
echo "   * TLS v1.3:                   $ENABLED_TLS13"
echo "   * Post-handshake Auth:        $ENABLED_TLS13_POST_AUTH"
echo "   * Early Data:                 $ENABLED_TLS13_EARLY_DATA"
echo "   * Send State in HRR Cookie:   $ENABLED_SEND_HRR_COOKIE"
echo "   * OCSP:                       $ENABLED_OCSP"
echo "   * OCSP Stapling:              $ENABLED_CERTIFICATE_STATUS_REQUEST"
echo "   * OCSP Stapling v2:           $ENABLED_CERTIFICATE_STATUS_REQUEST_V2"
echo "   * CRL:                        $ENABLED_CRL"
echo "   * CRL-MONITOR:                $ENABLED_CRL_MONITOR"
echo "   * Persistent session cache:   $ENABLED_SAVESESSION"
echo "   * Persistent cert    cache:   $ENABLED_SAVECERT"
echo "   * Atomic User Record Layer:   $ENABLED_ATOMICUSER"
echo "   * Public Key Callbacks:       $ENABLED_PKCALLBACKS"
echo "   * NTRU:                       $ENABLED_NTRU"
echo "   * QSH:                        $ENABLED_QSH"
echo "   * Whitewood netRandom:        $ENABLED_WNR"
echo "   * Server Name Indication:     $ENABLED_SNI"
echo "   * ALPN:                       $ENABLED_ALPN"
echo "   * Maximum Fragment Length:    $ENABLED_MAX_FRAGMENT"
echo "   * Trusted CA Indication:      $ENABLED_TRUSTED_CA"
echo "   * Truncated HMAC:             $ENABLED_TRUNCATED_HMAC"
echo "   * Supported Elliptic Curves:  $ENABLED_SUPPORTED_CURVES"
echo "   * FFDHE only in client:       $ENABLED_FFDHE_ONLY"
echo "   * Session Ticket:             $ENABLED_SESSION_TICKET"
echo "   * Extended Master Secret:     $ENABLED_EXTENDED_MASTER"
echo "   * Renegotiation Indication:   $ENABLED_RENEGOTIATION_INDICATION"
echo "   * Secure Renegotiation:       $ENABLED_SECURE_RENEGOTIATION"
echo "   * Fallback SCSV:              $ENABLED_FALLBACK_SCSV"
echo "   * All TLS Extensions:         $ENABLED_TLSX"
echo "   * PKCS#7                      $ENABLED_PKCS7"
echo "   * wolfSSH                     $ENABLED_WOLFSSH"
echo "   * wolfSCEP                    $ENABLED_WOLFSCEP"
echo "   * Secure Remote Password      $ENABLED_SRP"
echo "   * Small Stack:                $ENABLED_SMALL_STACK"
echo "   * valgrind unit tests:        $ENABLED_VALGRIND"
echo "   * LIBZ:                       $ENABLED_LIBZ"
echo "   * Examples:                   $ENABLED_EXAMPLES"
echo "   * User Crypto:                $ENABLED_USER_CRYPTO"
echo "   * Fast RSA:                   $ENABLED_FAST_RSA"
echo "   * Single Precision:           $ENABLED_SP"
echo "   * Async Crypto:               $ENABLED_ASYNCCRYPT"
echo "   * PKCS#11:                    $ENABLED_PKCS11"
echo "   * PKCS#12:                    $ENABLED_PKCS12"
echo "   * Cavium Nitox:               $ENABLED_CAVIUM"
echo "   * Cavium Octeon (Sync):       $ENABLED_OCTEON_SYNC"
echo "   * Intel Quick Assist:         $ENABLED_INTEL_QA"
echo "   * ARM ASM:                    $ENABLED_ARMASM"
echo "   * AES Key Wrap:               $ENABLED_AESKEYWRAP"
echo "   * Write duplicate:            $ENABLED_WRITEDUP"
echo "   * Xilinx Hardware Acc.:       $ENABLED_XILINX"
echo "   * Inline Code:                $ENABLED_INLINE"
echo "   * Linux AF_ALG:               $ENABLED_AFALG"
echo "   * Linux devcrypto:            $ENABLED_DEVCRYPTO"
echo "   * Crypto callbacks:           $ENABLED_CRYPTOCB"
echo ""
echo "---"

################################################################################
# Show warnings at bottom so they are noticed
################################################################################

if test "$ENABLED_ASYNCCRYPT" = "yes"
then
    AC_MSG_WARN([Make sure real async files are loaded. Contact wolfSSL for details on using the asynccrypt option.])
fi

# MinGW static vs shared library
# Reference URL from libtool for MinGW is located at
# http://www.gnu.org/software/libtool/manual/libtool.html#Cygwin-to-MinGW-Cross
# this allows for not even having dllimport/dllexport on functions
# with recent libtools, only requiring it with global variables.
#
# The following warning is displayed here because if not using "contemporary GNU
# tools" there is the possibility of export/import issues.
# wolfSSL uses __declspec(dllexport) and "contemporary GNU tools" handle the
# case where both static and shared libraries are built.
#
# More can be found about the MinGW linker at
# https://sourceware.org/binutils/docs/ld/WIN32.html
if test "$MINGW_LIB_WARNING" = "yes"
then
    AC_MSG_WARN([Building with shared and static library at the same time on this system may cause export/import problems when using non contemporary GNU tools.])
fi

