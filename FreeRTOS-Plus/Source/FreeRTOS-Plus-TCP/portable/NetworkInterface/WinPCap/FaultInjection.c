#define xBUFFER_CACHE_SIZE           10
#define xMAX_FAULT_INJECTION_RATE    15
#define xMIN_FAULT_INJECTION_RATE    3
#define xNUM_FAULT_TYPES             1

static NetworkBufferDescriptor_t * xNetworkBufferCache[ xBUFFER_CACHE_SIZE ] = { 0 };

#define xFAULT_LOG_SIZE    2048
uint32_t ulInjectedFault[ xFAULT_LOG_SIZE ];
uint32_t ulFaultLogIndex = 0;

static BaseType_t prvCachePacket( NetworkBufferDescriptor_t * pxNetworkBufferIn )
{
    BaseType_t x, xReturn = pdFALSE;

    for( x = 0; x < xBUFFER_CACHE_SIZE; x++ )
    {
        if( xNetworkBufferCache[ x ] == NULL )
        {
            xNetworkBufferCache[ x ] = pxNetworkBufferIn;
            xReturn = pdTRUE;
            break;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static NetworkBufferDescriptor_t * prvGetCachedPacket( void )
{
    BaseType_t x;
    NetworkBufferDescriptor_t * pxReturn = NULL;

    for( x = ( xBUFFER_CACHE_SIZE - 1 ); x >= 0; x-- )
    {
        if( xNetworkBufferCache[ x ] != NULL )
        {
            pxReturn = xNetworkBufferCache[ x ];
            xNetworkBufferCache[ x ] = NULL;
            break;
        }
    }

    return pxReturn;
}
/*-----------------------------------------------------------*/

static NetworkBufferDescriptor_t * prvDuplicatePacket( NetworkBufferDescriptor_t * pxOriginalPacket,
                                                       const uint8_t * pucPacketData )
{
    NetworkBufferDescriptor_t * pxReturn;

    /* Obtain a new descriptor. */
    pxReturn = pxGetNetworkBufferWithDescriptor( pxOriginalPacket->xDataLength, 0 );

    if( pxReturn != NULL )
    {
        /* Copy in the packet data. */
        pxReturn->xDataLength = pxOriginalPacket->xDataLength;
        memcpy( pxReturn->pucEthernetBuffer, pucPacketData, pxOriginalPacket->xDataLength );
    }

    return pxReturn;
}
/*-----------------------------------------------------------*/

static NetworkBufferDescriptor_t * prvRxFaultInjection( NetworkBufferDescriptor_t * pxNetworkBufferIn,
                                                        const uint8_t * pucPacketData )
{
    static uint32_t ulCallCount = 0, ulNextFaultCallCount = 0;
    NetworkBufferDescriptor_t * pxReturn = pxNetworkBufferIn;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    uint32_t ulFault;

    return pxNetworkBufferIn;

    ulCallCount++;

    if( ulCallCount > ulNextFaultCallCount )
    {
        xApplicationGetRandomNumber( &( ulNextFaultCallCount ) );
        ulNextFaultCallCount = ulNextFaultCallCount % xMAX_FAULT_INJECTION_RATE;

        if( ulNextFaultCallCount < xMIN_FAULT_INJECTION_RATE )
        {
            ulNextFaultCallCount = xMIN_FAULT_INJECTION_RATE;
        }

        ulCallCount = 0;

        xApplicationGetRandomNumber( &( ulFault ) );
        ulFault = ulFault % xNUM_FAULT_TYPES;

        if( ulFaultLogIndex < xFAULT_LOG_SIZE )
        {
            ulInjectedFault[ ulFaultLogIndex ] = ulFault;
            ulFaultLogIndex++;
        }

        switch( ulFault )
        {
            case 0:
                /* Just drop the packet. */
                vReleaseNetworkBufferAndDescriptor( pxNetworkBufferIn );
                pxReturn = NULL;
                break;

            case 1:

                /* Store the packet in the cache for later. */
                if( prvCachePacket( pxNetworkBufferIn ) == pdTRUE )
                {
                    /* The packet may get sent later, it is not being sent
                     * now. */
                    pxReturn = NULL;
                }

                break;

            case 2:
                /* Send a cached packet. */
                pxReturn = prvGetCachedPacket();

                if( pxReturn != NULL )
                {
                    /* A cached packet was obtained so drop the original
                     * packet. */
                    vReleaseNetworkBufferAndDescriptor( pxNetworkBufferIn );
                }
                else
                {
                    /* Could not obtain a packet from the cache so just return
                     * the packet that was passed in. */
                    pxReturn = pxNetworkBufferIn;
                }

                break;

            case 4:

                /* Send a duplicate of the packet right away. */
                pxReturn = prvDuplicatePacket( pxNetworkBufferIn, pucPacketData );

                /* Send the original packet to the stack. */
                xRxEvent.pvData = ( void * ) pxNetworkBufferIn;

                if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
                {
                    vReleaseNetworkBufferAndDescriptor( pxNetworkBufferIn );
                }

                break;

            case 5:

                /* Send both a cached packet and the current packet. */
                xRxEvent.pvData = ( void * ) prvGetCachedPacket();

                if( xRxEvent.pvData != NULL )
                {
                    if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
                    {
                        vReleaseNetworkBufferAndDescriptor( pxNetworkBufferIn );
                    }
                }

                break;

            case 6:
            case 7:
            case 8:

                /* Store the packet in the cache for later. */
                if( prvCachePacket( pxNetworkBufferIn ) == pdTRUE )
                {
                    /* The packet may get sent later, it is not being sent
                     * now. */
                    pxReturn = NULL;
                }

                break;
        }
    }

    return pxReturn;
}
/*-----------------------------------------------------------*/
