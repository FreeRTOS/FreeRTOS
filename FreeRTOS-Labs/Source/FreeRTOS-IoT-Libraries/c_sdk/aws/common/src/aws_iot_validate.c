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
 * @file aws_iot_validate.c
 * @brief Validates Thing Names and other parameters to AWS IoT.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* AWS IoT include. */
#include "aws_iot.h"

/* Error handling include. */
#include "iot_error.h"

/*-----------------------------------------------------------*/

bool AwsIot_ValidateThingName( const char * pThingName,
                               size_t thingNameLength )
{
    IOT_FUNCTION_ENTRY( bool, true );

    if( pThingName == NULL )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    if( thingNameLength == 0 )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    if( thingNameLength > AWS_IOT_MAX_THING_NAME_LENGTH )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/
