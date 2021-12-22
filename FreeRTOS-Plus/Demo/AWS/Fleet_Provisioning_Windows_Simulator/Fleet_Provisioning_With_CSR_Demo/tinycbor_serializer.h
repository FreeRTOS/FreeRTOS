/*
 * FreeRTOS V202112.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
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
 * @param[in] pucBuffer Buffer into which to write the publish request payload.
 * @param[in] xBufferLength Length of #pucBuffer.
 * @param[in] pcCsr The CSR to include in the request payload.
 * @param[in] xCsrLength The length of #pcCsr.
 * @param[out] pxOutLengthWritten The length of the publish request payload.
 */
bool xGenerateCsrRequest( uint8_t * pucBuffer,
                          size_t xBufferLength,
                          const char * pcCsr,
                          size_t xCsrLength,
                          size_t * pxOutLengthWritten );

/**
 * @brief Creates the request payload to be published to the RegisterThing API
 * in order to activate the provisioned certificate and receive a Thing name.
 *
 * @param[in] pucBuffer Buffer into which to write the publish request payload.
 * @param[in] xBufferLength Length of #buffer.
 * @param[in] pcCertificateOwnershipToken The certificate's certificate
 * ownership token.
 * @param[in] xCertificateOwnershipTokenLength Length of
 * #certificateOwnershipToken.
 * @param[out] pxOutLengthWritten The length of the publish request payload.
 */
bool xGenerateRegisterThingRequest( uint8_t * pucBuffer,
                                    size_t xBufferLength,
                                    const char * pcCertificateOwnershipToken,
                                    size_t xCertificateOwnershipTokenLength,
                                    const char * pcSerial,
                                    size_t xSerialLength,
                                    size_t * pxOutLengthWritten );

/**
 * @brief Extracts the certificate, certificate ID, and certificate ownership
 * token from a CreateCertificateFromCsr accepted response. These are copied
 * to the provided buffers so that they can outlive the data in the response
 * buffer and as CBOR strings may be chunked.
 *
 * @param[in] pucResponse The response payload.
 * @param[in] xLength Length of #pucResponse.
 * @param[in] pcCertificateBuffer The buffer to which to write the certificate.
 * @param[in,out] pxCertificateBufferLength The length of #pcCertificateBuffer.
 * The length written is output here.
 * @param[in] pcCertificateIdBuffer The buffer to which to write the certificate
 * ID.
 * @param[in,out] pxCertificateIdBufferLength The length of
 * #pcCertificateIdBuffer. The length written is output here.
 * @param[in] pcOwnershipTokenBuffer The buffer to which to write the
 * certificate ownership token.
 * @param[in,out] pxOwnershipTokenBufferLength The length of
 * #pcOwnershipTokenBuffer. The length written is output here.
 */
bool xParseCsrResponse( const uint8_t * pucResponse,
                        size_t xLength,
                        char * pcCertificateBuffer,
                        size_t * pxCertificateBufferLength,
                        char * pcCertificateIdBuffer,
                        size_t * pxCertificateIdBufferLength,
                        char * pcOwnershipTokenBuffer,
                        size_t * pxOwnershipTokenBufferLength );

/**
 * @brief Extracts the Thing name from a RegisterThing accepted response.
 *
 * @param[in] pucResponse The response document.
 * @param[in] xLength Length of #pucResponse.
 * @param[in] pcThingNameBuffer The buffer to which to write the Thing name.
 * @param[in,out] pxThingNameBufferLength The length of #pcThingNameBuffer. The
 * written length is output here.
 */
bool xParseRegisterThingResponse( const uint8_t * pucResponse,
                                  size_t xLength,
                                  char * pcThingNameBuffer,
                                  size_t * pxThingNameBufferLength );
