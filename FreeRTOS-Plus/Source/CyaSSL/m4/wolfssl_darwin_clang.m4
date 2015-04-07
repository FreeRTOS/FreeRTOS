# ===========================================================================
#
# SYNOPSIS
#
#   WOLFSSL_DARWIN_USING_CLANG
#
# DESCRIPTION
#
#   With the advent of Apple Xcode v5.0, the old tool sets are missing from
#   the distribution. The provided "gcc" executable wrapper accepts the
#   "-pthread" flag, and passes it to the underlying "clang" which chokes
#   on it. This script checks the version of the gcc executable to see if
#   it reports it is really "clang".
#
#   The value is placed in the wolfssl_darwin_clang variable.
#
# LICENSE
#
#   Copyright (c) 2013 John Safranek <john@wolfssl.com>
#
#   Copying and distribution of this file, with or without modification, are
#   permitted in any medium without royalty provided the copyright notice
#   and this notice are preserved. This file is offered as-is, without any
#   warranty.

#serial 1

AC_DEFUN([WOLFSSL_DARWIN_USING_CLANG],
        [
            if test x"$CC" = xclang; then
                wolfssl_darwin_clang=yes
            elif test x"$CC" = x || test x"$CC" = xgcc; then
                if /usr/bin/gcc -v 2>&1 | grep 'clang' >/dev/null 2>&1; then
                    wolfssl_darwin_clang=yes
                fi
            fi
        ])
