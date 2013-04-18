/* sniffer.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
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
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


#ifndef CYASSL_SNIFFER_H
#define CYASSL_SNIFFER_H

#include <cyassl/ctaocrypt/settings.h>

#ifdef _WIN32
    #ifdef SSL_SNIFFER_EXPORTS
        #define SSL_SNIFFER_API __declspec(dllexport)
    #else
        #define SSL_SNIFFER_API __declspec(dllimport)
    #endif
#else
    #define SSL_SNIFFER_API
#endif /* _WIN32 */


#ifdef __cplusplus
    extern "C" {
#endif


CYASSL_API 
SSL_SNIFFER_API int ssl_SetPrivateKey(const char* address, int port,
                                      const char* keyFile, int keyType,
                                      const char* password, char* error);

CYASSL_API 
SSL_SNIFFER_API int ssl_DecodePacket(const unsigned char* packet, int length,
                                     unsigned char* data, char* error);

CYASSL_API 
SSL_SNIFFER_API int ssl_Trace(const char* traceFile, char* error);
        
        
CYASSL_API void ssl_InitSniffer(void);
        
CYASSL_API void ssl_FreeSniffer(void);

        
/* ssl_SetPrivateKey keyTypes */
enum {
    FILETYPE_PEM = 1,
    FILETYPE_DER = 2,
};


#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* CyaSSL_SNIFFER_H */

