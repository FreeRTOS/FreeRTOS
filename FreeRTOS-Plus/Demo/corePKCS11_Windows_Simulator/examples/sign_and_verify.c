/*
 * FreeRTOS V202012.00
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard include. */
#include "stdio.h"

/* PKCS #11 includes. */
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"
#include "pkcs11.h"
#include "core_pki_utils.h"

/* Demo includes. */
#include "demo_helpers.h"
#include "pkcs11_demos.h"

/**
 * This function details how to use the PKCS #11 "Sign and Verify" functions to 
 * create and interact with digital signatures.
 * The functions described are all defined in 
 * http://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html 
 * please consult the standard for more information regarding these functions.
 *
 * The standard has grouped the functions presented in this demo as:
 * Object Management Functions
 * Signing and MACing Functions 
 */
void vPKCS11SignVerifyDemo( void )
{
    /* This demo will use the generated private and public key from the 
     * "objects.c" demo and use them to sign and verify the integrity of a 
     * message digest. This demo will use concepts from all the other demos,
     * and is recommended be done last. 
     *
     * The intention of this demo is how to use PKCS #11's Crypotki API to do
     * these signature operations, not to explain when and why they should be
     * used. For a deeper understanding of that please read:
     * https://en.wikipedia.org/wiki/Public_key_infrastructure
     * https://en.wikipedia.org/wiki/Transport_Layer_Security
     * https://en.wikipedia.org/wiki/Digital_signature
     */
    configPRINTF( ( "\r\nStarting PKCS #11 Sign and Verify Demo.\r\n" ) );

    /* Helper / previously explained variables. */
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE hSession = CK_INVALID_HANDLE;
    CK_SLOT_ID * pxSlotId = NULL;
    CK_ULONG ulSlotCount = 0;
    CK_ULONG ulIndex = 0;
    CK_OBJECT_HANDLE xPrivateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPublicKeyHandle = CK_INVALID_HANDLE;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_BYTE * pxDerPublicKey = NULL;
    CK_ULONG ulDerPublicKeyLength = 0;

    /* Digest variables. See "mechanisms_and_digests" for an explanation. */
    CK_BYTE pxKnownMessage[] = { "Hello world" };
    CK_BYTE xDigestResult[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_ULONG ulDigestLength = pkcs11SHA256_DIGEST_LENGTH;
    CK_MECHANISM xDigestMechanism = { 0 };

    /* Signing variables. */
    /* The ECDSA mechanism will be used to sign the message digest. */
    CK_MECHANISM xMechanism = { CKM_ECDSA, NULL, 0 };

    /* This signature buffer will be used to store the signature created by the 
     * private key. (64 bytes). We pad it with an extra 8 bytes so it can be
     * converted to an ASN.1 encoding. */
    CK_BYTE xSignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH + 8 ] = { 0 };
    CK_ULONG xSignatureLength = sizeof( xSignature );

    /* Ensure the Cryptoki library has the necessary functions implemented. */
    xResult = C_GetFunctionList( &pxFunctionList );
    configASSERT( xResult == CKR_OK );
    configASSERT( pxFunctionList->C_SignInit != NULL );
    configASSERT( pxFunctionList->C_Sign != NULL );
    configASSERT( pxFunctionList->C_FindObjectsInit != NULL );
    configASSERT( pxFunctionList->C_FindObjects != NULL );
    configASSERT( pxFunctionList->C_FindObjectsFinal != NULL );
    configASSERT( pxFunctionList->C_Login != NULL );
    configASSERT( pxFunctionList->C_InitToken != NULL );
    configASSERT( pxFunctionList->C_GetTokenInfo != NULL );

    /* Instead of using the vStart helper, we will  use the "core_pkcs11.h" 
     * functions that help wrap around some common PKCS #11 use cases. 
     *
     * This function will:
     * Initialize the PKCS #11 module if it is not already.
     * Initialize a PKCS #11 session. 
     */
    xResult = xInitializePkcs11Session( &hSession ); 
    configASSERT( xResult == CKR_OK );
    configASSERT( hSession != CK_INVALID_HANDLE );
    
    /* This function will:
     * Initialize the PKCS #11 module if it is not already.
     * Initialize the token to be used. 
     *
     * Note: By default this function will always initialize the token in the 
     * first slot in the slot list. If it desired to use a different slot, it
     * is necessary to modify the implementation of this function to use a 
     * different slot. */
    xResult = xInitializePkcs11Token(); 
    configASSERT( xResult == CKR_OK );
 
    /* This function will:
     * Query the Cryptoki library for the total number of slots. Malloc an array
     * of slots. Then the pxSlotId and ulSlotCount variables will be updated to 
     * point to the slot array, and the total slot count. 
     */
    xResult = xGetSlotList( &pxSlotId, &ulSlotCount );
    configASSERT( xResult == CKR_OK );
    configASSERT( ulSlotCount != 0 );
    configASSERT( pxSlotId != NULL );

    /***************************** Find Objects *****************************/

    /* This function will:
     * Find an object, given it's label.
     *
     * This is done using the FindObjects group of functions defined as
     * "Object Management Functions" in PKCS #11.
     *
     * This will acquire the object handle for the private key created in the
     * "objects.c" demo.
     */
    xResult = xFindObjectWithLabelAndClass( hSession, 
            pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, 
            sizeof( pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS ) - 1UL, 
            CKO_PRIVATE_KEY,
            &xPrivateKeyHandle );
    configASSERT( xResult == CKR_OK );
    configASSERT( xPrivateKeyHandle != CK_INVALID_HANDLE );

    /* Acquire the object handle for the public key created in the "objects.c" 
     * demo. */
    xResult = xFindObjectWithLabelAndClass( hSession, 
            pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS, 
            sizeof( pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS ) - 1UL, 
            CKO_PRIVATE_KEY,
            &xPublicKeyHandle );
    configASSERT( xResult == CKR_OK );
    configASSERT( xPublicKeyHandle != CK_INVALID_HANDLE );

    /***************************** Buffer Digest *****************************/
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

    /* Retrieve the digest buffer length. When passing in a NULL pointer as the 
     * second argument, instead of a point to a buffer, this will signal the
     * Cryptoki library to fill the third parameter with the required amount of 
     * bytes to store the resulting digest.
     */
    xResult = pxFunctionList->C_DigestFinal( hSession,
                                             NULL,
                                             &ulDigestLength );
    configASSERT( CKR_OK == xResult );
    /* Since the length of a SHA-256 digest is known, we made an assumption and
     * allocated the buffer originally with the known length. Assert to make sure
     * we queried the length we expected. */
    configASSERT( pkcs11SHA256_DIGEST_LENGTH == ulDigestLength );

    /* Now that ulDigestLength contains the required byte length, retrieve the 
     * digest buffer.
     */
    xResult = pxFunctionList->C_DigestFinal( hSession,
                                             xDigestResult,
                                             &ulDigestLength );
    configASSERT( CKR_OK == xResult );

    /********************************* Sign **********************************/

    configPRINTF( ( "Signing known message:\r\n %s\r\n", 
                ( char * ) pxKnownMessage ) );

    /* Initializes the sign operation and sets what mechanism will be used
     * for signing the message digest. Specify what object handle to use for this
     * operation, in this case the private key object handle. */
    xResult = pxFunctionList->C_SignInit( hSession, 
            &xMechanism, 
            xPrivateKeyHandle );
    configASSERT( xResult == CKR_OK );

    /* Sign the message digest that was created with the C_Digest series of 
     * functions. A signature will be created using the private key specified in
     * C_SignInit and put in the byte buffer xSignature. */
    xResult = pxFunctionList->C_Sign( hSession, 
            xDigestResult, 
            pkcs11SHA256_DIGEST_LENGTH, 
            xSignature, 
            &xSignatureLength );
    configASSERT( xResult == CKR_OK );
    configASSERT( xSignatureLength == pkcs11ECDSA_P256_SIGNATURE_LENGTH );


    /********************************* Verify **********************************/
    /* Verify the signature created by C_Sign. First we will verify that the 
     * same Cryptoki library was able to trust itself.
     *
     * C_VerifyInit will begin the verify operation, by specifying what mechanism
     * to use (CKM_ECDSA, the same as the sign operation) and then specifying
     * which public key handle to use.
     */
    xResult = pxFunctionList->C_VerifyInit( hSession, 
            &xMechanism, 
            xPublicKeyHandle );
    configASSERT( xResult == CKR_OK );

    /* Given the signature and it's length, the Cryptoki will use the public key
     * to verify that the signature was created by the corresponding private key. 
     * If C_Verify returns CKR_OK, it means that the sender of the message has 
     * the same private key as the private key that was used to generate the 
     * public key, and we can trust that the message we received was from that 
     * sender.
     *
     * Note that we are not using the actual message, but the digest that we 
     * created earlier of the message, for the verification.
     */
    xResult = pxFunctionList->C_Verify( hSession, 
            xDigestResult, 
            pkcs11SHA256_DIGEST_LENGTH, 
            xSignature, 
            xSignatureLength );

    if( xResult == CKR_OK )
    {
        configPRINTF( ( "The signature of the digest was verified with the" \
                    " public key and can be trusted.\r\n" ) );
    }
    else
    {
        configPRINTF( ( "Unable to verify the signature with the given public" \
                    " key, the message cannot be trusted.\r\n" ) );
    }

    /* Export public key as hex bytes and print the hex representation of the
     * public key. 
     *
     * We need to export the public key so that it can be used by a different 
     * device to verify messages signed by the private key of the device that
     * generated the key pair.
     *
     * To do this, we will output the hex representation of the public key.
     * Then create an empty text file called "DevicePublicKeyAsciiHex.txt".
     *
     * Copy and paste the hex value of the public key into this text file.
     *
     * Then we will need to convert the text file to binary using the xxd tool.
     *
     * xxd will take a text file that contains hex data and output a binary of
     * the hex in the file. See "$ man xxd" for more information about xxd.
     *
     * Copy the below command into the terminal.
     * "$ xxd -r -ps DevicePublicKeyAsciiHex.txt DevicePublicKeyDer.bin"
     *
     * Now that we have the binary encoding of the public key, we will convert 
     * it to PEM using OpenSSL.  
     *
     * The following command will create a PEM file of the public key called 
     * "public_key.pem"
     *
     * "$ openssl ec -inform der -in DevicePublicKeyDer.bin -pubin -pubout -outform pem -out public_key.pem"
     * 
     * Now we can use the extracted public key to verify the signature of the 
     * device's private key.
     *
     * WARNING: Running the object generation demo will create a new key pair,
     * and make it necessary to redo these steps!
     *
     */
    configPRINTF( ( "Verifying with public key.\r\n" ) );
    vExportPublicKey( hSession,
                      xPublicKeyHandle,
                      &pxDerPublicKey,
                      &ulDerPublicKeyLength );
    vWriteHexBytesToConsole( "Public Key in Hex Format",
                             pxDerPublicKey,
                             ulDerPublicKeyLength );

    /* This utility function converts the PKCS #11 signature into an ASN.1 
     * encoded binary der signature. This is necessary so we can export the 
     * signature and verify it with OpenSSL, otherwise OpenSSL will not be able
     * to parse the buffer.
     *
     * See https://en.wikipedia.org/wiki/ASN.1 for more information about the 
     * ASN.1 encoding format.
     */
    PKI_pkcs11SignatureTombedTLSSignature( xSignature, ( size_t * ) &xSignatureLength );


    /* The following loop will output the signature in hex. 
     *
     * In order to get the signature exported in binary form copy the output
     * of the loop, and paste it to an empty text file. 
     *
     * Then we will need to convert the text file to binary using the xxd tool.
     *
     * The following commands outline this process.
     * Write buffer to signature.txt
     * xxd will take a text file that contains hex data and output a binary of
     * the hex in the file. See "$ man xxd" for more information about xxd.
     *
     * Copy the below command into the terminal.
     * "$ xxd -r -ps signature.txt signature.bin"
     *
     * Next, we need to copy the original message that the Cryptoki library 
     * signed, the following shell command will create the message without any 
     * newlines, so the messages are similar. 
     *
     * The contents of the echo command can be replaced with whatever data was 
     * in the known message, but the example uses "Hello world" to make it easier
     * for copy and pasting.
     *
     * "$ echo -n "Hello world" > msg.txt"
     *
     * Now we will use OpenSSL to verify that the signature we created can be 
     * trusted by another device using the public key we created and then 
     * extracted earlier.
     *
     * "$ openssl dgst -sha256 -verify public_key.pem -signature signature.bin msg.txt"
     * This command should output "Verified OK" and we then know we can trust 
     * the sender of the message!
     */
    configPRINTF( ( "Created signature: \r\n" ) );
    for( ulIndex = 0; ulIndex < xSignatureLength; ulIndex++ )
    {
        configPRINTF( ( "%02x", xSignature[ ulIndex ] ) );
    }
    configPRINTF( ( "\r\n" ) );

    configPRINTF( ( "Finished PKCS #11 Sign and Verify Demo.\r\n" ) );
}
