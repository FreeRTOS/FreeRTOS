# configure.ac
#
# Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
#
# This file is part of CyaSSL.
#
#

AC_INIT([cyassl],[2.3.0],[http://www.yassl.com])

AC_CONFIG_AUX_DIR(config)

AC_CANONICAL_TARGET

AM_INIT_AUTOMAKE(-Wall -Werror -Wno-portability foreign tar-ustar subdir-objects)

AC_CANONICAL_HOST
AC_CANONICAL_BUILD

AC_PREREQ([2.61])

AC_CONFIG_MACRO_DIR(m4)

AC_CONFIG_HEADERS([config.h:config.in])dnl Keep filename to 8.3 for MS-DOS.


#shared library versioning
CYASSL_LIBRARY_VERSION=3:1:0
#                      | | |
#               +------+ | +---+
#               |        |     |
#              current:revision:age
#               |        |     |
#               |        |     +- increment if interfaces have been added
#               |        |        set to zero if interfaces have been removed
#                        |        or changed
#               |        +- increment if source code has changed
#               |           set to zero if current is incremented
#               +- increment if interfaces have been added, removed or changed
AC_SUBST(CYASSL_LIBRARY_VERSION)

# Make sure configure doesn't add to CFLAGS
CFLAGS="$CFLAGS $C_EXTRA_FLAGS"

LT_INIT([win32-dll])
LT_LANG([C++])
LT_LANG([C])
gl_VISIBILITY

m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

AC_CHECK_FUNCS([gethostbyname])
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
AC_CHECK_HEADERS(errno.h)
AC_CHECK_LIB(network,socket)
AC_CHECK_SIZEOF(long long, 8)
AC_CHECK_SIZEOF(long, 4)
AC_C_BIGENDIAN
AC_DISABLE_STATIC
AC_DISABLE_STATIC
AC_FUNC_MALLOC
AC_FUNC_MKTIME
AC_FUNC_REALLOC

AC_PROG_CC
AC_PROG_CC_C_O
AC_PROG_CXX
AC_PROG_INSTALL
LT_INIT
AC_TYPE_SIZE_T
AC_TYPE_UINT8_T
AM_PROG_AS
AM_PROG_CC_C_O
LT_LIB_M

OPTIMIZE_CFLAGS="-Os -fomit-frame-pointer"
OPTIMIZE_FAST_CFLAGS="-O3 -fomit-frame-pointer"
OPTIMIZE_HUGE_CFLAGS="-funroll-loops -DTFM_SMALL_SET"
DEBUG_CFLAGS="-g -DDEBUG -DDEBUG_CYASSL"


# DEBUG
AC_ARG_ENABLE(debug,
    [  --enable-debug          Enable CyaSSL debugging support (default: disabled)],
    [ ENABLED_DEBUG=$enableval ],
    [ ENABLED_DEBUG=no ]
    )
if test "$ENABLED_DEBUG" = "yes"
then
  # Full debug. Very slow in some cases
  AM_CFLAGS="$DEBUG_CFLAGS $AM_CFLAGS"
else
  # Optimized version. No debug
  AM_CFLAGS="$AM_CFLAGS -DNDEBUG"
fi


# SMALL BUILD
AC_ARG_ENABLE(small,
    [  --enable-small          Enable smallest build (default: disabled)],
    [ ENABLED_SMALL=$enableval ],
    [ ENABLED_SMALL=no ]
    )
if test "$ENABLED_SMALL" = "yes"
then
  # make small no tls build with smallest cipher
  # if you only want server or client you can define NO_CYASSL_SERVER or
  # NO_CYASSL_CLIENT but then some of the examples and testsuite won't build
  # note that TLS needs HMAC
  AM_CFLAGS="-DNO_TLS -DNO_HMAC -DNO_AES -DNO_DES3 -DNO_SHA256 -DNO_ERROR_STRINGS -DNO_RABBIT -DNO_PSK -DNO_DSA -DNO_DH -DNO_PWDBASED $AM_CFLAGS" 
fi


# SINGLE THREADED
AC_ARG_ENABLE(singleThreaded,
    [  --enable-singleThreaded Enable CyaSSL single threaded (default: disabled)],
    [ ENABLED_SINGLETHREADED=$enableval ],
    [ ENABLED_SINGLETHREADED=no ]
    )
if test "$ENABLED_SINGLETHREADED" = "yes"
then
  AM_CFLAGS="-DSINGLE_THREADED $AM_CFLAGS"
fi


# DTLS
AC_ARG_ENABLE(dtls,
    [  --enable-dtls           Enable CyaSSL DTLS (default: disabled)],
    [ ENABLED_DTLS=$enableval ],
    [ ENABLED_DTLS=no ]
    )
if test "$ENABLED_DTLS" = "yes"
then
  AM_CFLAGS="-DCYASSL_DTLS $AM_CFLAGS"
fi


# OPENSSL Extra Compatibility
AC_ARG_ENABLE(opensslExtra,
    [  --enable-opensslExtra   Enable extra OpenSSL API, size+ (default: disabled)],
    [ ENABLED_OPENSSLEXTRA=$enableval ],
    [ ENABLED_OPENSSLEXTRA=no ]
    )
if test "$ENABLED_OPENSSLEXTRA" = "yes"
then
  AM_CFLAGS="-DOPENSSL_EXTRA $AM_CFLAGS"
fi

if test "$ENABLED_OPENSSLEXTRA" = "yes" && test "$ENABLED_SMALL" = "yes"
then
    AC_MSG_ERROR([cannot enable small and opensslExtra, only one or the other.])
fi


# IPv6 Test Apps
AC_ARG_ENABLE(ipv6,
    [  --enable-ipv6           Enable testing of IPV6 (default: disabled)],
    [ ENABLED_IPV6=$enableval ],
    [ ENABLED_IPV6=no ]
    )

if test "$ENABLED_IPV6" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DTEST_IPV6"
fi


# Fortress build 
AC_ARG_ENABLE(fortress,
    [  --enable-fortress       Enable SSL fortress build (default: disabled)],
    [ ENABLED_FORTRESS=$enableval ],
    [ ENABLED_FORTRESS=no ]
    )

if test "$ENABLED_FORTRESS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DFORTRESS -DOPENSSL_EXTRA -DCYASSL_DES_ECB -DCYASSL_AES_COUNTER -DCYASSL_AES_DIRECT -DCYASSL_DER_LOAD -DCYASSL_SHA512 -DCYASSL_SHA384 -DCYASSL_KEY_GEN"
fi


# ssl bump build 
AC_ARG_ENABLE(bump,
    [  --enable-bump           Enable SSL Bump build (default: disabled)],
    [ ENABLED_BUMP=$enableval ],
    [ ENABLED_BUMP=no ]
    )

if test "$ENABLED_BUMP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DLARGE_STATIC_BUFFERS -DCYASSL_CERT_GEN -DCYASSL_KEY_GEN -DHUGE_SESSION_CACHE -DOPENSSL_EXTRA -DFP_MAX_BITS=8192 -DCYASSL_DER_LOAD -DCYASSL_ALT_NAMES -DCYASSL_TEST_CERT"
fi

# fastmath
AC_ARG_ENABLE(fastmath,
    [  --enable-fastmath       Enable fast math for BigInts (default: disabled)],
    [ ENABLED_FASTMATH=$enableval ],
    [ ENABLED_FASTMATH=no ]
    )

if test "x$ENABLED_FASTMATH" = "xyes"
then
    AM_CFLAGS="$AM_CFLAGS -DUSE_FAST_MATH"
fi


# fast HUGE math
AC_ARG_ENABLE(fasthugemath,
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
fi

AM_CONDITIONAL([BUILD_FASTMATH], [test "x$ENABLED_FASTMATH" = "xyes"])


# big cache
AC_ARG_ENABLE(bigcache,
    [  --enable-bigcache       Enable big session cache (default: disabled)],
    [ ENABLED_BIGCACHE=$enableval ],
    [ ENABLED_BIGCACHE=no ]
    )

if test "$ENABLED_BIGCACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DBIG_SESSION_CACHE"
fi


# HUGE cache
AC_ARG_ENABLE(hugecache,
    [  --enable-hugecache      Enable huge session cache (default: disabled)],
    [ ENABLED_HUGECACHE=$enableval ],
    [ ENABLED_HUGECACHE=no ]
    )

if test "$ENABLED_HUGECACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHUGE_SESSION_CACHE"
fi


# SMALL cache
AC_ARG_ENABLE(smallcache,
    [  --enable-smallcache     Enable small session cache (default: disabled)],
    [ ENABLED_SMALLCACHE=$enableval ],
    [ ENABLED_SMALLCACHE=no ]
    )

if test "$ENABLED_SMALLCACHE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DSMALL_SESSION_CACHE"
fi


# SNIFFER
AC_ARG_ENABLE(sniffer,
    [  --enable-sniffer        Enable CyaSSL sniffer support (default: disabled)],
    [ ENABLED_SNIFFER=$enableval ],
    [ ENABLED_SNIFFER=no ]
    )

if test "$ENABLED_SNIFFER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_SNIFFER -DOPENSSL_EXTRA"
fi

AM_CONDITIONAL([BUILD_SNIFFER], [test "x$ENABLED_SNIFFER" = "xyes"])

# AES-GCM
AC_ARG_ENABLE(aesgcm,
    [  --enable-aesgcm         Enable CyaSSL AES-GCM support (default: disabled)],
    [ ENABLED_AESGCM=$enableval ],
    [ ENABLED_AESGCM=no ]
    )

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
    AM_CFLAGS="$AM_CFLAGS -DHAVE_AESGCM -DCYASSL_SHA384 -DCYASSL_SHA512"
fi

AM_CONDITIONAL([BUILD_AESGCM], [test "x$ENABLED_AESGCM" = "xyes"])

# AES-NI
AC_ARG_ENABLE(aesni,
    [  --enable-aesni          Enable CyaSSL AES-NI support (default: disabled)],
    [ ENABLED_AESNI=$enableval ],
    [ ENABLED_AESNI=no ]
    )

if test "$ENABLED_AESNI" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_AESNI"
    if test "$GCC" = "yes"
    then
        # GCC needs these flags, icc doesn't
        AM_CFLAGS="$AM_CFLAGS -maes -msse4"
    fi
fi

AM_CONDITIONAL([BUILD_AESNI], [test "x$ENABLED_AESNI" = "xyes"])


# MD2
AC_ARG_ENABLE(md2,
    [  --enable-md2            Enable CyaSSL MD2 support (default: disabled)],
    [ ENABLED_MD2=$enableval ],
    [ ENABLED_MD2=no ]
    )

if test "$ENABLED_BUMP" = "yes"
then
    ENABLED_MD2="yes"
fi

if test "$ENABLED_MD2" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_MD2"
fi

AM_CONDITIONAL([BUILD_MD2], [test "x$ENABLED_MD2" = "xyes"])


# RIPEMD
AC_ARG_ENABLE(ripemd,
    [  --enable-ripemd         Enable CyaSSL RIPEMD-160 support (default: disabled)],
    [ ENABLED_RIPEMD=$enableval ],
    [ ENABLED_RIPEMD=no ]
    )

if test "$ENABLED_RIPEMD" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_RIPEMD"
fi

AM_CONDITIONAL([BUILD_RIPEMD], [test "x$ENABLED_RIPEMD" = "xyes"])


# SHA512
AC_ARG_ENABLE(sha512,
    [  --enable-sha512         Enable CyaSSL SHA-512 support (default: disabled)],
    [ ENABLED_SHA512=$enableval ],
    [ ENABLED_SHA512=no ]
    )

if test "$ENABLED_SHA512" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_SHA512"
fi

if test "$ENABLED_FORTRESS" = "yes"
then
    ENABLED_SHA512="yes"
fi

if test "$ENABLED_AESGCM" = "yes"
then
    ENABLED_SHA512="yes"
fi


AM_CONDITIONAL([BUILD_SHA512], [test "x$ENABLED_SHA512" = "xyes"])


# SESSION CERTS
AC_ARG_ENABLE(sessioncerts,
    [  --enable-sessioncerts   Enable session cert storing (default: disabled)],
    [ ENABLED_SESSIONCERTS=$enableval ],
    [ ENABLED_SESSIONCERTS=no ]
    )

if test "$ENABLED_SESSIONCERTS" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DSESSION_CERTS"
fi


# KEY GENERATION
AC_ARG_ENABLE(keygen,
    [  --enable-keygen         Enable key generation (default: disabled)],
    [ ENABLED_KEYGEN=$enableval ],
    [ ENABLED_KEYGEN=no ]
    )

if test "$ENABLED_KEYGEN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_KEY_GEN"
fi


# CERT GENERATION
AC_ARG_ENABLE(certgen,
    [  --enable-certgen        Enable cert generation (default: disabled)],
    [ ENABLED_CERTGEN=$enableval ],
    [ ENABLED_CERTGEN=no ]
    )

if test "$ENABLED_CERTGEN" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_CERT_GEN"
fi


# HC128 
AC_ARG_ENABLE(hc128,
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


# PSK 
AC_ARG_ENABLE(psk,
    [  --enable-psk            Enable PSK (default: disabled)],
    [ ENABLED_PSK=$enableval ],
    [ ENABLED_PSK=no ]
    )

if test "$ENABLED_PSK" = "no"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_PSK"
fi


# Web Server Build 
AC_ARG_ENABLE(webServer,
    [  --enable-webServer      Enable Web Server (default: disabled)],
    [ ENABLED_WEBSERVER=$enableval ],
    [ ENABLED_WEBSERVER=no ]
    )

if test "$ENABLED_WEBSERVER" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_WEBSERVER"
fi


# No Filesystem Build 
AC_ARG_ENABLE(noFilesystem,
    [  --enable-noFilesystem   Enable No Filesystem (default: disabled)],
    [ ENABLED_NOFILESYSTEM=$enableval ],
    [ ENABLED_NOFILESYSTEM=no ]
    )

if test "$ENABLED_NOFILESYSTEM" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_FILESYSTEM"
fi


# No inline Build 
AC_ARG_ENABLE(noInline,
    [  --enable-noInline       Enable No inline (default: disabled)],
    [ ENABLED_NOINLINE=$enableval ],
    [ ENABLED_NOINLINE=no ]
    )

if test "$ENABLED_NOINLINE" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DNO_INLINE"
fi

AM_CONDITIONAL([BUILD_NOINLINE], [test "x$ENABLED_NOINLINE" = "xyes"])


# ECC 
AC_ARG_ENABLE(ecc,
    [  --enable-ecc            Enable ECC (default: disabled)],
    [ ENABLED_ECC=$enableval ],
    [ ENABLED_ECC=no ]
    )

if test "$ENABLED_ECC" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_ECC"
fi

AM_CONDITIONAL([BUILD_ECC], [test "x$ENABLED_ECC" = "xyes"])


if test "$ENABLED_ECC" = "yes" && test "$ENABLED_SMALL" = "yes"
then
    AC_MSG_ERROR([cannot enable ecc and small, ecc requires TLS which small turns off.]) 
fi


# OCSP
AC_ARG_ENABLE(ocsp,
    [  --enable-ocsp           Enable OCSP (default: disabled)],
    [ ENABLED_OCSP=$enableval ],
    [ ENABLED_OCSP=no ],
    )

if test "$ENABLED_OCSP" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_OCSP"
fi

AM_CONDITIONAL([BUILD_OCSP], [test "x$ENABLED_OCSP" = "xyes"])


# CRL 
AC_ARG_ENABLE(crl,
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
AC_ARG_ENABLE(crl-monitor,
    [  --enable-crl-monitor    Enable CRL Monitor (default: disabled)],
    [ ENABLED_CRL_MONITOR=$enableval ],
    [ ENABLED_CRL_MONITOR=no ],
    )

if test "$ENABLED_CRL_MONITOR" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_CRL_MONITOR"
fi

AM_CONDITIONAL([BUILD_CRL_MONITOR], [test "x$ENABLED_CRL_MONITOR" = "xyes"])


# NTRU
ntruHome=`pwd`/NTRU_algorithm
ntruInclude=$ntruHome/cryptolib
ntruLib=$ntruHome
AC_ARG_ENABLE(ntru,
    [  --enable-ntru           Enable NTRU (default: disabled)],
    [ ENABLED_NTRU=$enableval ],
    [ ENABLED_NTRU=no ]
    )

if test "$ENABLED_NTRU" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DHAVE_NTRU -I$ntruInclude"
    AM_LDFLAGS="$AM_LDFLAGS -L$ntruLib"
    LIBS="$LIBS -lntru_encrypt"
fi

AM_CONDITIONAL([BUILD_NTRU], [test "x$ENABLED_NTRU" = "xyes"])

if test "$ENABLED_NTRU" = "yes" && test "$ENABLED_SMALL" = "yes"
then
    AC_MSG_ERROR([cannot enable ntru and small, ntru requires TLS which small turns off.]) 
fi


# Test certs, use internal cert functions for extra testing 
AC_ARG_ENABLE(testcert,
    [  --enable-testcert       Enable Test Cert (default: disabled)],
    [ ENABLED_TESTCERT=$enableval ],
    [ ENABLED_TESTCERT=no ]
    )

if test "$ENABLED_TESTCERT" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -DCYASSL_TEST_CERT"
fi


# LIBZ
trylibzdir=""
AC_ARG_WITH(libz,
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

    ]
)


# OPTIMIZE FLAGS
if test "$GCC" = "yes"
then
    AM_CFLAGS="$AM_CFLAGS -Wall -Wno-unused"
    if test "$ENABLED_DEBUG" = "no"
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

AX_PTHREAD([
            AC_DEFINE([HAVE_PTHREAD], [1], [Define if you have POSIX threads libraries and header files.])
            ],
            [
             AC_DEFINE([HAVE_PTHREAD], [0], [Define if you have POSIX threads libraries and header files.])
             ])

LIB_SOCKET_NSL

dnl Various GCC warnings that should never fire for release quality code
GCCWARNINGS="-Wall -fno-strict-aliasing -W -Wfloat-equal -Wundef          \
  -Wpointer-arith -Wstrict-prototypes -Wmissing-prototypes                \
  -Wwrite-strings -Wredundant-decls -Wchar-subscripts -Wcomment           \
  -Wformat=2 -Wwrite-strings -Wmissing-declarations -Wredundant-decls     \
  -Wnested-externs -Wbad-function-cast -Wswitch-enum -Winit-self          \
  -Wmissing-field-initializers -Wdeclaration-after-statement              \
  -Wold-style-definition -Waddress -Wmissing-noreturn -Wnormalized=id     \
  -Woverride-init -Wstrict-overflow=1 -Wextra -Wstack-protector -Wformat  \
  -Wformat-security -Wpointer-sign -Wshadow -Wswitch-default"

case "$host_os" in
  *linux*)
GCCWARNINGS="$GCCWARNINGS -Warray-bounds"
  ;;
esac

AC_ARG_ENABLE(gcc-lots-o-warnings,
AS_HELP_STRING(--enable-gcc-lots-o-warnings, Enable lots of gcc warnings (default: disabled)),
[if test x$enableval = xyes; then
    AM_CFLAGS="$AM_CFLAGS $GCCWARNINGS"
fi])

AC_ARG_ENABLE(gcc-hardening,
AS_HELP_STRING(--enable-gcc-hardening, Enable compiler security checks (default: disabled)),
[if test x$enableval = xyes; then
    AM_CFLAGS="$AM_CFLAGS -D_FORTIFY_SOURCE=2 -fstack-protector-all"
    AM_CFLAGS="$AM_CFLAGS -fwrapv -fPIE -Wstack-protector"
    AM_CFLAGS="$AM_CFLAGS --param ssp-buffer-size=1"
    LDFLAGS="$LDFLAGS -pie"
fi])

dnl Linker hardening options
dnl Currently these options are ELF specific - you can't use this with MacOSX
AC_ARG_ENABLE(linker-hardening,
AS_HELP_STRING(--enable-linker-hardening, Enable linker security fixups (default: disabled)),
[if test x$enableval = xyes; then
    LDFLAGS="$LDFLAGS -z relro -z now"
fi])

CREATE_HEX_VERSION
AM_CFLAGS="$AM_CFLAGS $CFLAG_VISIBILITY"
AC_SUBST(AM_CFLAGS)
AC_SUBST(AM_LDFLAGS)

# FINAL
AC_CONFIG_FILES([stamp-h], [echo timestamp > stamp-h])
AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([cyassl/version.h])
AC_CONFIG_FILES([support/libcyassl.pc])

AC_OUTPUT

