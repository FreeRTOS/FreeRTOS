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

/* Demo include. */
#include "pkcs11_demos.h"

/**
 * This function details how to use the PKCS #11 "Management" functions to
 * manage the internal state machine of the PKCS #11 implementation. These
 * functions are all defined in
 * http://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html
 * please consult the standard for more information regarding these functions.
 *
 * The standard has grouped the functions presented in this demo as:
 * General Purpose Functions
 * Slot and Token Management Functions
 * Session Management Functions
 * Random Number Generation Functions
 */
void vPKCS11ManagementAndRNGDemo( void )
{
    /* We will use the terminology as defined in the standard, Cryptoki is in
     * reference to the Cryptographic Token Interface defined in the PKCS #11
     * standard. An implementation of Cryptoki is referred to as a
     * "Cryptoki library". */
    configPRINTF( ( "\r\nStarting PKCS #11 Management and Random Number Generation" \
                    " Demo.\r\n" ) );

    /* CK_RV is the return type for a Cryptoki function. Generally the underlying
     * type is a CK_ULONG, it can also be a CKR_VENDOR_DEFINED type. */
    CK_RV xResult = CKR_OK;

    /* The CK_FUNCTION_LIST is a structure that contains the Cryptoki version
     * and a function pointer to each function in the Cryptoki API. If the
     * function pointer is NULL it is unimplemented. */
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;

    /* This Cryptoki library does not implement any initialization arguments. At the time of
     * writing this demo, the purpose of these optional arguments is to provide
     * function pointers for mutex operations. */
    CK_C_INITIALIZE_ARGS xInitArgs = { 0 };

    /* A slot ID is an integer that defines a slot. The Cryptoki definition of
     * a slot is "A logical reader that potentially contains a token."
     *
     * Essentially it is an abstraction for accessing the token. The reason for
     * this is Some tokens are a physical "card' that needs to be inserted into
     * a slot for the device to read.
     *
     * A concrete example of a slot could be a USB Hardware Security Module (HSM),
     * which generally appears as a singular slot, and abstracts it's internal "token".
     *
     * Some implementations have multiple slots mapped to a single token, or maps
     * a slot per token. */
    CK_SLOT_ID * pxSlotId = NULL;

    /* A session is defined to be "The logical connection between an application
     * and a token."
     *
     * The session can either be private or public, and differentiates
     * your application from the other users of the token. */
    CK_SESSION_HANDLE hSession = CK_INVALID_HANDLE;

    /* Helper variables. */
    CK_BYTE xRandomData[ 10 ] = { 0 };
    uint32_t ulIndex = 0;
    CK_ULONG xSlotCount = 0;

    /* We use the function list returned by C_GetFunctionList to see what functions
     * the Cryptoki library supports. We use asserts to ensure that all the
     * functionality needed in this demo is available. */
    xResult = C_GetFunctionList( &pxFunctionList );
    configASSERT( xResult == CKR_OK );
    configASSERT( pxFunctionList != NULL );
    configASSERT( pxFunctionList->C_Initialize != NULL );
    configASSERT( pxFunctionList->C_GetSlotList != NULL );
    configASSERT( pxFunctionList->C_OpenSession != NULL );
    configASSERT( pxFunctionList->C_Login != NULL );
    configASSERT( pxFunctionList->C_GenerateRandom != NULL );
    configASSERT( pxFunctionList->C_CloseSession != NULL );
    configASSERT( pxFunctionList->C_Finalize != NULL );

    configPRINTF( ( "Cryptoki Major Version: %lu Minor Version %lu\r\n",
                    pxFunctionList->version.major,
                    pxFunctionList->version.minor ) );

    /* C_Initialize will initialize the Cryptoki library and the hardware it
     * abstracts. */
    xResult = pxFunctionList->C_Initialize( &xInitArgs );
    configASSERT( xResult == CKR_OK );

    /* C_GetSlotList will retrieve an array of CK_SLOT_IDs.
     * This Cryptoki library does not implement slots, but it is important to
     * highlight how Cryptoki can be used to interface with real hardware.
     *
     * By setting the first argument "tokenPresent" to true, we only retrieve
     * slots that have a token. If the second argument "pSlotList" is NULL, the
     * third argument "pulCount" will be modified to contain the total slots. */
    xResult = pxFunctionList->C_GetSlotList( CK_TRUE,
                                             NULL,
                                             &xSlotCount );
    configASSERT( xResult == CKR_OK );

    /* Since C_GetSlotList does not allocate the memory itself for getting a list
     * of CK_SLOT_ID, we allocate one for it to populate with the list of
     * slot ids. */
    pxSlotId = pvPortMalloc( sizeof( CK_SLOT_ID ) * ( xSlotCount ) );
    configASSERT( pxSlotId != NULL );

    /* Now since pSlotList is not NULL, C_GetSlotList will populate it with the
     * available slots. */
    xResult = pxFunctionList->C_GetSlotList( CK_TRUE,
                                             pxSlotId,
                                             &xSlotCount );
    configASSERT( xResult == CKR_OK );

    /* Since this Cryptoki library does not actually implement the concept of slots,
     * but we will use the first available slot, so the demo code conforms to
     * Cryptoki.
     *
     * C_OpenSession will establish a session between the application and
     * the token and we can then use the returned CK_SESSION_HANDLE for
     * cryptographic operations with the token.
     *
     * For legacy reasons, Cryptoki demands that the CKF_SERIAL_SESSION bit
     * is always set. */
    xResult = pxFunctionList->C_OpenSession( pxSlotId[ 0 ],
                                             CKF_SERIAL_SESSION | CKF_RW_SESSION,
                                             NULL, /* Application defined pointer. */
                                             NULL, /* Callback function. */
                                             &hSession );
    configASSERT( xResult == CKR_OK );


    /* C_Login is called to log the user in to the token. The login status is
     * shared between sessions, so logging in once is sufficient for all the sessions
     * tied to the token. Most of the behavior for C_Login is defined by the token
     * so it may be necessary to modify calls to C_Login when switching to a different
     * Cryptoki library or token.
     *
     * This Cryptoki library does not implement C_Login, and only defines the function
     * for compatibility reasons.
     */
    xResult = pxFunctionList->C_Login( hSession,
                                       CKU_USER,
                                       ( CK_UTF8CHAR_PTR ) configPKCS11_DEFAULT_USER_PIN,
                                       sizeof( configPKCS11_DEFAULT_USER_PIN ) - 1UL );
    configASSERT( xResult == CKR_OK );

    /* C_GenerateRandom generates random or pseudo random data. As arguments it
     * takes the application session, and a pointer to a byte buffer, as well as
     * the length of the byte buffer. Then it will fill this buffer with random
     * bytes. */
    xResult = pxFunctionList->C_GenerateRandom( hSession,
                                                xRandomData,
                                                sizeof( xRandomData ) );
    configASSERT( xResult == CKR_OK );

    for( ulIndex = 0; ulIndex < sizeof( xRandomData ); ulIndex++ )
    {
        configPRINTF( ( "Generated random number: %x\r\n", xRandomData[ ulIndex ] ) );
    }

    /* C_CloseSession closes the session that was established between the
     * application and the token. This will clean up the resources that maintained
     * the link between the application and the token. If the application wishes
     * to use the token again, it will need to open a new session. */
    xResult = pxFunctionList->C_CloseSession( hSession );
    configASSERT( xResult == CKR_OK );

    /* C_Finalize signals to the Cryptoki library that the application is done
     * using it. It should always be the last call to the Cryptoki library.
     * NULL should always be passed as the argument, as the parameter is currently
     * just reserved for future revisions.
     *
     * Calling this function in a multi threaded environment can lead to undefined
     * behavior if other threads are accessing the Cryptoki library. */
    xResult = pxFunctionList->C_Finalize( NULL );
    configASSERT( xResult == CKR_OK );

    configPRINTF( ( "Finished PKCS #11 Management and Random Number Generation" \
                    " Demo.\r\n" ) );

    vPortFree( pxSlotId );
}
