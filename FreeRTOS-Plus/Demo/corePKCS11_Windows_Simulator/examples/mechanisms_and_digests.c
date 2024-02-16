/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include "stdio.h"

/* PKCS #11 includes. */
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"
#include "pkcs11.h"

/* Demo includes. */
#include "demo_helpers.h"
#include "pkcs11_demos.h"

/**
 * This function details what Cryptoki mechanisms are, how to query a slot's
 * support for them, and how to use those mechanisms to generate a hash of a buffer.
 * This can then be used as a message digest.
 *
 * http://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html
 * please consult the standard for more information.
 *
 * The standard has grouped the functions presented in this demo as:
 * Slot and token management functions.
 * Message digesting functions.
 *
 */
void vPKCS11MechanismsAndDigestDemo( void )
{
    /*
     * This demo builds upon the demo found in "management_and_rng.c". It borrows
     * code and terminology defined and explained, and it is recommended to complete
     * the "management and rng" demo before this one.
     */
    configPRINTF( ( "\r\nStarting PKCS #11 Mechanisms and Digest Demo.\r\n" ) );

    CK_SESSION_HANDLE hSession = CK_INVALID_HANDLE;
    CK_SLOT_ID * pxSlotId = 0;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_ULONG ulIndex = 0;
    CK_RV xResult = CKR_OK;

    /* The PKCS #11 standard defines a mechanism to be a "A process for
     * implementing a cryptographic operation." For example the SHA-256 algorithm
     * will be the mechanism used in this demo to perform a digest (hash operation).
     *
     * The mechanism types are defined in "pkcs11t.h", and are prefixed CKM_, to
     * provide a portable way to identify mechanisms.
     */
    CK_MECHANISM_TYPE xMechanismType = 0;

    /* This variable is not directly used, but is instantiated for demonstration
     * purposes.
     */
    ( void ) xMechanismType;

    /* The CK_MECHANISM_INFO allows the application to retrieve the minimum and
     * maximum key sizes supported by the mechanism (could be in bits or bytes).
     * The structure also has a flags field, that is populated with bit flags
     * for what features the mechanism supports.
     */
    CK_MECHANISM_INFO MechanismInfo = { 0 };

    /* The CK_MECHANISM type contains the mechanism type, as well as a pointer
     * for mechanism parameters and a CK_ULONG indicating the length of the
     * parameters.
     */
    CK_MECHANISM xDigestMechanism = { 0 };

    /* The digest will return a hash of the known SHA-256 hash size, 32 bytes.
     * Please see this page for further explanation of the SHA-256 hash.
     * https://en.wikipedia.org/wiki/SHA-2
     */
    CK_BYTE xDigestResult[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_ULONG ulDigestLength = pkcs11SHA256_DIGEST_LENGTH;

    CK_BYTE pxKnownMessage[] = "Hello world!";

    vStart( &hSession, &pxSlotId );
    xResult = C_GetFunctionList( &pxFunctionList );
    configASSERT( CKR_OK == xResult );
    configASSERT( pxFunctionList->C_GetMechanismInfo != NULL );
    configASSERT( pxFunctionList->C_DigestInit != NULL );
    configASSERT( pxFunctionList->C_DigestUpdate != NULL );
    configASSERT( pxFunctionList->C_DigestFinal != NULL );

    /*************************** RSA Capabilities ***************************/
    xResult = pxFunctionList->C_GetMechanismInfo( pxSlotId[ 0 ],
                                                  CKM_RSA_PKCS,
                                                  &MechanismInfo );
    configASSERT( CKR_OK == xResult );

    /* Check to see if the slot supports signing. This capability is important
     * because we want to use the Cryptoki API to sign messages, without directly
     * accessing the private key. This concept will be explained further in the
     * "sign_verify.c" demo, but for now we will just check that the slot has the
     * capabilities we need. See https://en.wikipedia.org/wiki/Public-key_cryptography
     * for more information regarding private keys and public keys.
     */
    if( 0 != ( CKF_SIGN & MechanismInfo.flags ) )
    {
        configPRINTF( ( "This Cryptoki library supports signing messages with RSA" \
                        " private keys.\r\n" ) );
    }
    else
    {
        configPRINTF( ( "This Cryptoki library does not support signing messages" \
                        " with RSA private keys.\r\n" ) );
    }

    /* This Cryptoki library assumes that RSA private keys are 2048 bit . */
    configASSERT( MechanismInfo.ulMaxKeySize >= pkcs11RSA_2048_MODULUS_BITS );
    configASSERT( MechanismInfo.ulMinKeySize <= pkcs11RSA_2048_MODULUS_BITS );

    /* Check for pre-padded signature verification support, this feature will
     * be used in the "sign_verify.c" demo.
     */
    xResult = pxFunctionList->C_GetMechanismInfo( pxSlotId[ 0 ],
                                                  CKM_RSA_X_509,
                                                  &MechanismInfo );

    /* If this fails, the slot is not able to verify the signature using
     * a RSA public key. Please see https://en.wikipedia.org/wiki/Public_key_infrastructure
     * for more information regarding PKI (Public Key Infrastructure).
     */
    if( 0 != ( CKF_VERIFY & MechanismInfo.flags ) )
    {
        configPRINTF( ( "This Cryptoki library supports verifying messages with RSA" \
                        " public keys.\r\n" ) );
    }
    else
    {
        configPRINTF( ( "This Cryptoki library does not support verifying messages" \
                        " with RSA public keys.\r\n" ) );
    }

    /* This Cryptoki library assumes that RSA public keys are 2048 bit . */
    configASSERT( MechanismInfo.ulMaxKeySize >= pkcs11RSA_2048_MODULUS_BITS );
    configASSERT( MechanismInfo.ulMinKeySize <= pkcs11RSA_2048_MODULUS_BITS );

    /*************************** ECDSA Capabilities ***************************/
    xResult = pxFunctionList->C_GetMechanismInfo( pxSlotId[ 0 ],
                                                  CKM_ECDSA,
                                                  &MechanismInfo );
    configASSERT( CKR_OK == xResult );

    if( 0 != ( CKF_SIGN & MechanismInfo.flags ) )
    {
        configPRINTF( ( "This Cryptoki library supports signing messages with" \
                        " ECDSA private keys.\r\n" ) );
    }
    else
    {
        configPRINTF( ( "This Cryptoki library does not support signing messages" \
                        " with ECDSA private keys.\r\n" ) );
    }

    if( 0 != ( CKF_VERIFY & MechanismInfo.flags ) )
    {
        configPRINTF( ( "This Cryptoki library supports verifying messages with" \
                        " ECDSA public keys.\r\n" ) );
    }
    else
    {
        configPRINTF( ( "This Cryptoki library does not support verifying" \
                        " messages with ECDSA public keys.\r\n" ) );
    }

    configASSERT( MechanismInfo.ulMaxKeySize >= pkcs11ECDSA_P256_KEY_BITS );
    configASSERT( MechanismInfo.ulMinKeySize <= pkcs11ECDSA_P256_KEY_BITS );

    /************************** Digest Capabilities **************************/
    xResult = pxFunctionList->C_GetMechanismInfo( pxSlotId[ 0 ],
                                                  CKM_SHA256,
                                                  &MechanismInfo );
    configASSERT( CKR_OK == xResult );

    if( 0 != ( CKF_DIGEST & MechanismInfo.flags ) )
    {
        configPRINTF( ( "The Cryptoki library supports the " \
                        "SHA-256 algorithm.\r\n" ) );
    }
    else
    {
        configPRINTF( ( "The Cryptoki library doesn't support the " \
                        "SHA-256 algorithm.\r\n" ) );
    }

    /***************************** Buffer Digest *****************************/
    /* Hash with SHA256 mechanism. */
    xDigestMechanism.mechanism = CKM_SHA256;

    /* Initializes the digest operation and sets what mechanism will be used
     * for the digest. */
    xResult = pxFunctionList->C_DigestInit( hSession,
                                            &xDigestMechanism );
    configASSERT( CKR_OK == xResult );


    /* Pass a pointer to the buffer of bytes to be hashed, and it's size. */
    xResult = pxFunctionList->C_DigestUpdate( hSession,
                                              pxKnownMessage,
                                              /* Strip NULL Terminator. */
                                              sizeof( pxKnownMessage ) - 1 );
    configASSERT( CKR_OK == xResult );

    /* Retrieve the digest buffer. Since the mechanism is a SHA-256 algorithm,
     * the size will always be 32 bytes. If the size cannot be known ahead of time,
     * a NULL value to the second parameter pDigest, will set the third parameter,
     * pulDigestLen to the number of required bytes. */
    xResult = pxFunctionList->C_DigestFinal( hSession,
                                             xDigestResult,
                                             &ulDigestLength );
    configASSERT( CKR_OK == xResult );

    /* This will now print out the digest of the known message. You can compare
     * the hash generated by the Cryptoki library in a UNIX shell by using the
     * command '$ echo -n "{pxKnownMessage}" | shasum -a 256'
     * this command should generate the same hash. */
    configPRINTF( ( "Known message: %s\r\n", ( char * ) pxKnownMessage ) );
    configPRINTF( ( "Hash of known message using SHA256:\r\n" ) );

    for( ulIndex = 0; ulIndex < ulDigestLength; ulIndex++ )
    {
        configPRINTF( ( "%x", xDigestResult[ ulIndex ] ) );
    }

    configPRINTF( ( "\r\n" ) );

    configPRINTF( ( "Finished PKCS #11 Mechanisms and Digest Demo.\r\n" ) );
    vEnd( hSession, pxSlotId );
}
