# -*- coding: utf-8 -*-
#
# build_ffi.py
#
# Copyright (C) 2006-2020 wolfSSL Inc.
#
# This file is part of wolfSSL.
#
# wolfSSL is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# wolfSSL is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
#/

# pylint: disable=missing-docstring, invalid-name

from cffi import FFI

ffi = FFI()

ffi.set_source(
    "wolfssl._ffi",
    """
    #include <wolfssl/options.h>
    #include <wolfssl/ssl.h>

    void wolfSSL_Free(void *ptr, void* heap, int type);
    """,
    include_dirs=["/usr/local/include"],
    library_dirs=["/usr/local/lib"],
    libraries=["wolfssl"],
)

ffi.cdef(
    """
    typedef unsigned char byte;
    typedef unsigned int  word32;

    void  wolfSSL_Free(void*, void*, int);

    void* wolfSSLv23_server_method(void);
    void* wolfSSLv23_client_method(void);
    void* wolfTLSv1_2_server_method(void);
    void* wolfTLSv1_2_client_method(void);

    void* wolfSSL_CTX_new(void*);
    void  wolfSSL_CTX_free(void*);

    void wolfSSL_CTX_set_verify(void*, int, void*);
    int  wolfSSL_CTX_set_cipher_list(void*, const char*);
    int  wolfSSL_CTX_use_PrivateKey_file(void*, const char*, int);
    int  wolfSSL_CTX_load_verify_locations(void*, const char*, const char*);
    int  wolfSSL_CTX_load_verify_buffer(void*, const unsigned char*, long, int);
    int  wolfSSL_CTX_use_certificate_chain_file(void*, const char *);
    int  wolfSSL_CTX_UseSupportedCurve(void*, short);


    void* wolfSSL_new(void*);
    void  wolfSSL_free(void*);

    int wolfSSL_set_fd(void*, int);
    int wolfSSL_get_error(void*, int);
    int wolfSSL_negotiate(void*);
    int wolfSSL_write(void*, const void*, int);
    int wolfSSL_read(void*, void*, int);
    int wolfSSL_shutdown(void*);
    """
)

if __name__ == "__main__":
    ffi.compile(verbose=1)
