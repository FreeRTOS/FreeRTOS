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
