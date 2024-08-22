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

#define ensure_memory_is_valid( px, length )    ( px != NULL ) && __CPROVER_w_ok( ( px ), length )

/* Implementation of safe malloc which returns NULL if the requested size is 0.
 * Warning: The behavior of malloc(0) is platform dependent.
 * It is possible for malloc(0) to return an address without allocating memory.*/
void * safeMalloc( size_t xWantedSize )
{
    return nondet_bool() ? malloc( xWantedSize ) : NULL;
}

/* Memory assignment for FreeRTOS_Socket_t */
FreeRTOS_Socket_t * ensure_FreeRTOS_Socket_t_is_allocated()
{
    FreeRTOS_Socket_t * pxSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) );

    if( ensure_memory_is_valid( pxSocket, sizeof( FreeRTOS_Socket_t ) ) )
    {
        pxSocket->u.xTCP.rxStream = safeMalloc( sizeof( StreamBuffer_t ) );
        pxSocket->u.xTCP.txStream = safeMalloc( sizeof( StreamBuffer_t ) );
        pxSocket->u.xTCP.pxPeerSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) );
    }

    return pxSocket;
}

/* Memory assignment for FreeRTOS_Network_Buffer */
NetworkBufferDescriptor_t * ensure_FreeRTOS_NetworkBuffer_is_allocated()
{
    return safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
}
