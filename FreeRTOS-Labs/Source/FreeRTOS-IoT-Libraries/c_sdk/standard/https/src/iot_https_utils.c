/*
 * Amazon FreeRTOS HTTPS Client V1.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * @file iot_https_utils.c
 * @brief Implements functions for HTTPS Client library utilities.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* iot_https_includes */
#include "iot_https_utils.h"
#include "http_parser.h"
#include "private/iot_https_internal.h"

/*-----------------------------------------------------------*/

IotHttpsReturnCode_t IotHttpsClient_GetUrlPath( const char * pUrl,
                                                size_t urlLen,
                                                const char ** pPath,
                                                size_t * pPathLen )
{
    /* http-parser status. Initialized to 0 to signify success. */
    int parserStatus = 0;
    struct http_parser_url urlParser;
    IotHttpsReturnCode_t returnStatus = IOT_HTTPS_OK;

    /* Sets all members in urlParser to 0. */
    http_parser_url_init( &urlParser );

    if( ( pUrl == NULL ) || ( pPath == NULL ) || ( pPathLen == NULL ) )
    {
        IotLogError( "NULL parameter passed to IotHttpsClient_GetUrlPath()." );
        returnStatus = IOT_HTTPS_INVALID_PARAMETER;
    }

    if( returnStatus == IOT_HTTPS_OK )
    {
        parserStatus = http_parser_parse_url( pUrl, urlLen, 0, &urlParser );

        if( parserStatus != 0 )
        {
            IotLogError( "Error parsing the input URL %.*s. Error code: %d.", urlLen, pUrl, parserStatus );
            returnStatus = IOT_HTTPS_PARSING_ERROR;
        }
    }

    if( returnStatus == IOT_HTTPS_OK )
    {
        *pPathLen = ( size_t ) ( urlParser.field_data[ UF_PATH ].len );

        if( *pPathLen == 0 )
        {
            returnStatus = IOT_HTTPS_NOT_FOUND;
            *pPath = NULL;
        }
        else
        {
            *pPath = &pUrl[ urlParser.field_data[ UF_PATH ].off ];
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

IotHttpsReturnCode_t IotHttpsClient_GetUrlAddress( const char * pUrl,
                                                   size_t urlLen,
                                                   const char ** pAddress,
                                                   size_t * pAddressLen )
{
    /* http-parser status. Initialized to 0 to signify success. */
    int parserStatus = 0;
    struct http_parser_url urlParser;
    IotHttpsReturnCode_t returnStatus = IOT_HTTPS_OK;

    /* Sets all members in urlParser to 0. */
    http_parser_url_init( &urlParser );

    if( ( pUrl == NULL ) || ( pAddress == NULL ) || ( pAddressLen == NULL ) )
    {
        IotLogError( "NULL parameter passed to IotHttpsClient_GetUrlAddress()." );
        returnStatus = IOT_HTTPS_INVALID_PARAMETER;
    }

    if( returnStatus == IOT_HTTPS_OK )
    {
        parserStatus = http_parser_parse_url( pUrl, urlLen, 0, &urlParser );

        if( parserStatus != 0 )
        {
            IotLogError( "Error parsing the input URL %.*s. Error code: %d.", urlLen, pUrl, parserStatus );
            returnStatus = IOT_HTTPS_PARSING_ERROR;
        }
    }

    if( returnStatus == IOT_HTTPS_OK )
    {
        *pAddressLen = ( size_t ) ( urlParser.field_data[ UF_HOST ].len );

        if( *pAddressLen == 0 )
        {
            returnStatus = IOT_HTTPS_NOT_FOUND;
            *pAddress = NULL;
        }
        else
        {
            *pAddress = &pUrl[ urlParser.field_data[ UF_HOST ].off ];
        }
    }

    return returnStatus;
}
