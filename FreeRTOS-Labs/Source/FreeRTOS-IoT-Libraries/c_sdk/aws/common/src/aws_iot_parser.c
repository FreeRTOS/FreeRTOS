/*
 * AWS IoT Common V1.0.0
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
 */

/**
 * @file aws_iot_parser.c
 * @brief Parses topics for Thing Name and status.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* AWS IoT include. */
#include "aws_iot.h"

/* Error handling include. */
#include "iot_error.h"

/* AWS Parser include. */
#include "aws_iot_doc_parser.h"

/**
 * @brief Minimum allowed topic length for an AWS IoT status topic.
 *
 * Topics must contain at least:
 * - The common prefix
 * - The suffix "/accepted" or "/rejected"
 * - 1 character for the Thing Name
 * - 2 characters for the operation name and the enclosing slashes
 */
#define MINIMUM_TOPIC_NAME_LENGTH                   \
    ( uint16_t ) ( AWS_IOT_TOPIC_PREFIX_LENGTH +    \
                   AWS_IOT_ACCEPTED_SUFFIX_LENGTH + \
                   1 + 2 )

/**
 * @brief The longest client token accepted by AWS IoT service, per AWS IoT
 * service limits.
 */
#define MAX_CLIENT_TOKEN_LENGTH    ( 64 )

/*-----------------------------------------------------------*/

bool AwsIot_GetClientToken( const char * pJsonDocument,
                            size_t jsonDocumentLength,
                            const char ** pClientToken,
                            size_t * pClientTokenLength )
{
    /* Extract the client token from the JSON document. */
    bool status = AwsIotDocParser_FindValue( pJsonDocument,
                                             jsonDocumentLength,
                                             AWS_IOT_CLIENT_TOKEN_KEY,
                                             AWS_IOT_CLIENT_TOKEN_KEY_LENGTH,
                                             pClientToken,
                                             pClientTokenLength );

    if( status == true )
    {
        /* Check that the length of the client token is valid. */
        if( ( *pClientTokenLength < 2 ) ||
            ( *pClientTokenLength > MAX_CLIENT_TOKEN_LENGTH ) )
        {
            status = false;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool AwsIot_ParseThingName( const char * pTopicName,
                            uint16_t topicNameLength,
                            const char ** pThingName,
                            size_t * pThingNameLength )
{
    IOT_FUNCTION_ENTRY( bool, true );
    const char * pThingNameStart = NULL;
    size_t thingNameLength = 0;

    /* Check that the topic name is at least as long as the minimum allowed. */
    if( topicNameLength < MINIMUM_TOPIC_NAME_LENGTH )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Check that the given topic starts with the common prefix. */
    if( strncmp( AWS_IOT_TOPIC_PREFIX,
                 pTopicName,
                 AWS_IOT_TOPIC_PREFIX_LENGTH ) != 0 )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* The Thing Name starts immediately after the topic prefix. */
    pThingNameStart = pTopicName + AWS_IOT_TOPIC_PREFIX_LENGTH;

    /* Calculate the length of the Thing Name, which is terminated with a '/'. */
    while( ( thingNameLength + AWS_IOT_TOPIC_PREFIX_LENGTH < ( size_t ) topicNameLength ) &&
           ( pThingNameStart[ thingNameLength ] != '/' ) )
    {
        thingNameLength++;
    }

    /* The end of the topic name was reached without finding a '/'. The topic
     * name is invalid. */
    if( thingNameLength + AWS_IOT_TOPIC_PREFIX_LENGTH >= ( size_t ) topicNameLength )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Set the output parameters. */
    *pThingName = pThingNameStart;
    *pThingNameLength = thingNameLength;

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotStatus_t AwsIot_ParseStatus( const char * pTopicName,
                                   uint16_t topicNameLength )
{
    IOT_FUNCTION_ENTRY( AwsIotStatus_t, AWS_IOT_UNKNOWN );
    const char * pSuffixStart = NULL;

    /* Both 'accepted' and  'rejected' topics are of the same length
     * The below is a defensive check at run time to ensure that.
     */
    Iot_DefaultAssert( AWS_IOT_ACCEPTED_SUFFIX_LENGTH == AWS_IOT_REJECTED_SUFFIX_LENGTH );

    /* Check that the status topic name is at least as long as the
     * "accepted" suffix. This length check will be good for rejected also
     * as both are of 8 characters in length. */
    if( topicNameLength > AWS_IOT_ACCEPTED_SUFFIX_LENGTH )
    {
        /* Calculate where the "accepted" suffix should start. */
        pSuffixStart = pTopicName + topicNameLength - AWS_IOT_ACCEPTED_SUFFIX_LENGTH;

        /* Check if the end of the status topic name is "/accepted". */
        if( strncmp( pSuffixStart,
                     AWS_IOT_ACCEPTED_SUFFIX,
                     AWS_IOT_ACCEPTED_SUFFIX_LENGTH ) == 0 )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ACCEPTED );
        }

        /* Check if the end of the status topic name is "/rejected". */
        if( strncmp( pSuffixStart,
                     AWS_IOT_REJECTED_SUFFIX,
                     AWS_IOT_REJECTED_SUFFIX_LENGTH ) == 0 )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_REJECTED );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/
