/* ssl-dummy.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ssl.h>
#include <cyassl/internal.h>
#include <cyassl/error-ssl.h>
#include <cyassl/ctaocrypt/coding.h>

Signer* GetCA(void* vp, byte* hash) 
{ 
    Signer*s ;
    return  s ;
}

int CyaSSL_dtls(CYASSL* ssl)
{
    return ssl->options.dtls;
}

int CyaSSL_get_using_nonblock(CYASSL* ssl)
{
    CYASSL_ENTER("CyaSSL_get_using_nonblock");
    CYASSL_LEAVE("CyaSSL_get_using_nonblock", ssl->options.usingNonblock);
    return ssl->options.usingNonblock;
}

Signer* GetCAByName(void* vp, byte* hash)
{
    Signer * ca ;
    return(ca) ;
}
