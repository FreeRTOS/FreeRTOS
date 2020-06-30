/*
 * FreeRTOS Utils V1.1.3
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* FreeRTOS includes. */

/**
 * @file iot_pki_utils.h
 * @brief Helper functions for PKCS #11
 */
#include "FreeRTOS.h"
#include "iot_pki_utils.h"

/* CRT includes. */
#include <stdio.h>
#include <string.h>

#define FAILURE    ( -1 )

/*-----------------------------------------------------------*/

/* Convert the EC signature from DER encoded to PKCS #11 format. */
/* @[declare pkcs11_utils_pkipkcs11signaturetombedtlssignature] */
BaseType_t PKI_mbedTLSSignatureToPkcs11Signature( uint8_t * pxSignaturePKCS,
                                                  const uint8_t * pxMbedSignature )
{
    BaseType_t xReturn = 0;
    const uint8_t * pxNextLength;
    uint8_t ucSigComponentLength;

    if( ( pxSignaturePKCS == NULL ) || ( pxMbedSignature == NULL ) )
    {
        xReturn = FAILURE;
    }

    if( xReturn == 0 )
    {
        /* The signature has the format
         * SEQUENCE LENGTH (of entire rest of signature)
         *      INTEGER LENGTH  (of R component)
         *      INTEGER LENGTH  (of S component)
         */

        /* The 4th byte contains the length of the R component */
        ucSigComponentLength = pxMbedSignature[ 3 ];

        /* The new signature will be 64 bytes long (32 bytes for R, 32 bytes for S).
         * Zero this buffer out in case a component is shorter than 32 bytes. */
        ( void ) memset( pxSignaturePKCS, 0, 64 );

        /********* R Component. *********/

        /* R components are represented by mbedTLS as 33 bytes when the first bit is zero to avoid any sign confusion. */
        if( ucSigComponentLength == 33UL )
        {
            /* Chop off the leading zero.  The first 4 bytes were SEQUENCE, LENGTH, INTEGER, LENGTH, 0x00 padding.  */
            ( void ) memcpy( pxSignaturePKCS, &pxMbedSignature[ 5 ], 32 );
            /* SEQUENCE, LENGTH, INTEGER, LENGTH, leading zero, R, S's integer tag */
            pxNextLength = pxMbedSignature + 5 + 32 + 1;
        }
        else
        {
            /* The R component is 32 bytes or less.  Copy so that it is properly represented as a 32 byte value,
             * leaving leading 0 pads at beginning if necessary. */
            ( void ) memcpy( &pxSignaturePKCS[ 32UL - ucSigComponentLength ], /* If the R component is less than 32 bytes, leave the leading zeros. */
                             &pxMbedSignature[ 4 ],                           /* SEQUENCE, LENGTH, INTEGER, LENGTH, (R component begins as the 5th byte) */
                             ucSigComponentLength );
            pxNextLength = pxMbedSignature + 4 + ucSigComponentLength + 1;    /* Move the pointer to get rid of
                                                                               * SEQUENCE, LENGTH, INTEGER, LENGTH, R Component, S integer tag. */
        }

        /********** S Component. ***********/

        /* Now pxNextLength is pointing to the length of the S component. */
        ucSigComponentLength = pxNextLength[ 0 ];

        if( ucSigComponentLength == 33UL )
        {
            ( void ) memcpy( &pxSignaturePKCS[ 32 ],
                             &pxNextLength[ 2 ], /*LENGTH (of S component), 0x00 padding, S component is 3rd byte - we want to skip the leading zero. */
                             32 );
        }
        else
        {
            /* The S component is 32 bytes or less.  Copy so that it is properly represented as a 32 byte value,
             * leaving leading 0 pads at beginning if necessary. */
            ( void ) memcpy( &pxSignaturePKCS[ 64UL - ucSigComponentLength ],
                             &pxNextLength[ 1 ],
                             ucSigComponentLength );
        }
    }

    return xReturn;
}
/* @[declare pkcs11_utils_pkipkcs11signaturetombedtlssignature] */
/*-----------------------------------------------------------*/


/* Convert an EC signature from PKCS #11 format to DER encoded. */
/* @[declare pkcs11_utils_pkimbedtlssignaturetopkcs11signature] */
BaseType_t PKI_pkcs11SignatureTombedTLSSignature( uint8_t * pucSig,
                                                  size_t * pxSigLen )
{
    BaseType_t xReturn = 0;
    uint8_t * pucSigPtr;
    uint8_t ucTemp[ 64 ] = { 0 }; /* A temporary buffer for the pre-formatted signature. */

    if( ( pucSig == NULL ) || ( pxSigLen == NULL ) )
    {
        xReturn = FAILURE;
    }

    if( xReturn == 0 )
    {
        ( void ) memcpy( ucTemp, pucSig, 64 );


        /* The ASN.1 encoded signature has the format
         * SEQUENCE LENGTH (of entire rest of signature)
         *      INTEGER LENGTH  (of R component)
         *      INTEGER LENGTH  (of S component)
         *
         * and a signature coming out of PKCS #11 C_Sign will have the format
         * R[32] + S[32]
         */

        pucSig[ 0 ] = 0x30; /* Sequence. */
        pucSig[ 1 ] = 0x44; /* The minimum length the signature could be. */
        pucSig[ 2 ] = 0x02; /* Integer. */

        /*************** R Component. *******************/

        /* If the first bit is one, pre-append a 00 byte.
         * This prevents the number from being interpreted as negative. */
        if( ( ucTemp[ 0 ] & 0x80UL ) == 0x80UL )
        {
            pucSig[ 1 ]++;                               /* Increment the length of the structure to account for the 0x00 pad. */
            pucSig[ 3 ] = 0x21;                          /* Increment the length of the R value to account for the 0x00 pad. */
            pucSig[ 4 ] = 0x0;                           /* Write the 0x00 pad. */
            ( void ) memcpy( &pucSig[ 5 ], ucTemp, 32 ); /* Copy the 32-byte R value. */
            pucSigPtr = pucSig + 33;                     /* Increment the pointer to compensate for padded R length.    */
        }
        else
        {
            pucSig[ 3 ] = 0x20;                          /* R length with be 32 bytes. */
            ( void ) memcpy( &pucSig[ 4 ], ucTemp, 32 ); /* Copy 32 bytes of R into the signature buffer. */
            pucSigPtr = pucSig + 32;                     /* Increment the pointer for 32 byte R length. */
        }

        pucSigPtr += 4;        /* Increment the pointer to offset the SEQUENCE, LENGTH, R-INTEGER, LENGTH. */
        pucSigPtr[ 0 ] = 0x02; /* INTEGER tag for S. */
        pucSigPtr += 1;        /* Increment over S INTEGER tag. */

        /******************* S Component. ****************/

        /* If the first bit is one, pre-append a 00 byte.
         * This prevents the number from being interpreted as negative. */
        if( ( ucTemp[ 32 ] & 0x80UL ) == 0x80UL )
        {
            pucSig[ 1 ]++;                                   /* Increment the length of the structure to account for the 0x00 pad. */
            pucSigPtr[ 0 ] = 0x21;                           /* Increment the length of the S value to account for the 0x00 pad. */
            pucSigPtr[ 1 ] = 0x00;                           /* Write the 0x00 pad. */
            pucSigPtr += 2;                                  /* pucSigPtr was pointing at the S-length.  Increment by 2 to hop over length and 0 padding. */

            ( void ) memcpy( pucSigPtr, &ucTemp[ 32 ], 32 ); /* Copy the S value. */
        }
        else
        {
            pucSigPtr[ 0 ] = 0x20;                           /* S length will be 32 bytes. */
            pucSigPtr++;                                     /* Hop pointer over the length byte. */
            ( void ) memcpy( pucSigPtr, &ucTemp[ 32 ], 32 ); /* Copy the S value. */
        }

        /* The total signature length is the length of the R and S integers plus 2 bytes for
         * the SEQUENCE and LENGTH wrapping the entire struct. */
        *pxSigLen = pucSig[ 1 ] + 2UL;
    }

    return xReturn;
}
/* @[declare pkcs11_utils_pkimbedtlssignaturetopkcs11signature] */
