/*
 * AWS IoT Device SDK for Embedded C 202108.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

#ifndef PKCS11_OPERATIONS_H_
#define PKCS11_OPERATIONS_H_

/* Standard includes. */
#include <stdlib.h>
#include <stdbool.h>

/* corePKCS11 include. */
#include "core_pkcs11.h"

/**
 * @brief Loads the claim credentials into the PKCS #11 module. Claim
 * credentials are used in "Provisioning by Claim" workflow of Fleet
 * Provisioning feature of AWS IoT Core. For more information, refer to the
 * [AWS documentation](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html#claim-based)
 *
 * Note: This function is for demonstration purposes, and the claim credentials
 * should be securely stored in production devices. For example, the
 * shared claim credentials could be loaded into a secure element on the devices
 * in your fleet at the time of manufacturing.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[in] pClaimCertPath Path to the claim certificate.
 * @param[in] pClaimCertLabel PKCS #11 label for the claim certificate.
 * @param[in] pClaimPrivKeyPath Path to the claim private key.
 * @param[in] pClaimPrivKeyLabel PKCS #11 label for the claim private key.
 *
 * @return True on success.
 */
bool loadClaimCredentials( CK_SESSION_HANDLE p11Session,
                           const char * pClaimCertPath,
                           const char * pClaimCertLabel,
                           const char * pClaimPrivKeyPath,
                           const char * pClaimPrivKeyLabel );

/**
 * @brief Generate a new public-private key pair in the PKCS #11 module, and
 * generate a certificate signing request (CSR) for them.
 *
 * This device-generated private key and CSR can be used with the
 * CreateCertificateFromCsr API of the the Fleet Provisioning feature of AWS IoT
 * Core in order to provision a unique client certificate.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[in] pPrivKeyLabel PKCS #11 label for the private key.
 * @param[in] pPubKeyLabel PKCS #11 label for the public key.
 * @param[out] pCsrBuffer The buffer to write the CSR to.
 * @param[in] csrBufferLength Length of #pCsrBuffer.
 * @param[out] pOutCsrLength The length of the written CSR.
 *
 * @return True on success.
 */
bool generateKeyAndCsr( CK_SESSION_HANDLE p11Session,
                        const char * pPrivKeyLabel,
                        const char * pPubKeyLabel,
                        char * pCsrBuffer,
                        size_t csrBufferLength,
                        size_t * pOutCsrLength );

/**
 * @brief Save the device client certificate into the PKCS #11 module.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[in] pCertificate The certificate to save.
 * @param[in] pLabel PKCS #11 label for the certificate.
 * @param[in] certificateLength Length of #pCertificate.
 *
 * @return True on success.
 */
bool loadCertificate( CK_SESSION_HANDLE p11Session,
                      const char * pCertificate,
                      const char * pLabel,
                      size_t certificateLength );

/**
 * @brief Close the PKCS #11 session.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 *
 * @return True on success.
 */
bool pkcs11CloseSession( CK_SESSION_HANDLE p11Session );

#endif /* ifndef PKCS11_OPERATIONS_H_ */
