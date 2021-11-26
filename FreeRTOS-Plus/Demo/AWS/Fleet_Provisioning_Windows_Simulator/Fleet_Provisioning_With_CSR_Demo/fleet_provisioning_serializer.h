/*
 * AWS IoT Device SDK for Embedded C 202108.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/**
 * This file declares functions for serializing and parsing CBOR encoded Fleet
 * Provisioning API payloads.
 */

/* Standard includes. */
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

/**
 * @brief Creates the request payload to be published to the
 * CreateCertificateFromCsr API in order to request a certificate from AWS IoT
 * for the included Certificate Signing Request (CSR).
 *
 * @param[in] pBuffer Buffer into which to write the publish request payload.
 * @param[in] bufferLength Length of #pBuffer.
 * @param[in] pCsr The CSR to include in the request payload.
 * @param[in] csrLength The length of #pCsr.
 * @param[out] pOutLengthWritten The length of the publish request payload.
 */
bool generateCsrRequest( uint8_t * pBuffer,
                         size_t bufferLength,
                         const char * pCsr,
                         size_t csrLength,
                         size_t * pOutLengthWritten );

/**
 * @brief Creates the request payload to be published to the RegisterThing API
 * in order to activate the provisioned certificate and receive a Thing name.
 *
 * @param[in] pBuffer Buffer into which to write the publish request payload.
 * @param[in] bufferLength Length of #buffer.
 * @param[in] pCertificateOwnershipToken The certificate's certificate
 * ownership token.
 * @param[in] certificateOwnershipTokenLength Length of
 * #certificateOwnershipToken.
 * @param[out] pOutLengthWritten The length of the publish request payload.
 */
bool generateRegisterThingRequest( uint8_t * pBuffer,
                                   size_t bufferLength,
                                   const char * pCertificateOwnershipToken,
                                   size_t certificateOwnershipTokenLength,
                                   const char * pSerial,
                                   size_t serialLength,
                                   size_t * pOutLengthWritten );

/**
 * @brief Extracts the certificate, certificate ID, and certificate ownership
 * token from a CreateCertificateFromCsr accepted response. These are copied
 * to the provided buffers so that they can outlive the data in the response
 * buffer and as CBOR strings may be chunked.
 *
 * @param[in] pResponse The response payload.
 * @param[in] length Length of #pResponse.
 * @param[in] pCertificateBuffer The buffer to which to write the certificate.
 * @param[in,out] pCertificateBufferLength The length of #pCertificateBuffer.
 * The length written is output here.
 * @param[in] pCertificateIdBuffer The buffer to which to write the certificate
 * ID.
 * @param[in,out] pCertificateIdBufferLength The length of
 * #pCertificateIdBuffer. The length written is output here.
 * @param[in] pOwnershipTokenBuffer The buffer to which to write the
 * certificate ownership token.
 * @param[in,out] pOwnershipTokenBufferLength The length of
 * #pOwnershipTokenBuffer. The length written is output here.
 */
bool parseCsrResponse( const uint8_t * pResponse,
                       size_t length,
                       char * pCertificateBuffer,
                       size_t * pCertificateBufferLength,
                       char * pCertificateIdBuffer,
                       size_t * pCertificateIdBufferLength,
                       char * pOwnershipTokenBuffer,
                       size_t * pOwnershipTokenBufferLength );

/**
 * @brief Extracts the Thing name from a RegisterThing accepted response.
 *
 * @param[in] pResponse The response document.
 * @param[in] length Length of #pResponse.
 * @param[in] pThingNameBuffer The buffer to which to write the Thing name.
 * @param[in,out] pThingNameBufferLength The length of #pThingNameBuffer. The
 * written length is output here.
 */
bool parseRegisterThingResponse( const uint8_t * pResponse,
                                 size_t length,
                                 char * pThingNameBuffer,
                                 size_t * pThingNameBufferLength );
