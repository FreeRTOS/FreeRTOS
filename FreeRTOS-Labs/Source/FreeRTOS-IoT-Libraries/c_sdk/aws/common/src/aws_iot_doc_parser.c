/*
 * AWS IoT Common V1.0.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_doc_parser.c
 * @brief Implements the functions in aws_iot_doc_parser.h
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* JSON utilities include. */
#include "aws_iot_doc_parser.h"

#define IS_QUOTE( str, idx ) \
    ( ( str )[ ( idx ) ] == '"' && ( ( idx ) == 0 || ( str )[ ( idx ) - 1 ] != '\\' ) )
#define IS_WHITESPACE( str, idx ) \
    ( ( str )[ ( idx ) ] == ' ' || ( str )[ ( idx ) ] == '\n' || ( str )[ ( idx ) ] == '\r' || ( str )[ ( idx ) ] == '\t' )

/*-----------------------------------------------------------*/

bool AwsIotDocParser_FindValue( const char * pAwsIotJsonDocument,
                                size_t awsIotJsonDocumentLength,
                                const char * pAwsIotJsonKey,
                                size_t awsIotJsonKeyLength,
                                const char ** pAwsIotJsonValue,
                                size_t * pAwsIotJsonValueLength )
{
    size_t i = 0;
    size_t jsonValueLength = 0;
    char openCharacter = '\0', closeCharacter = '\0';
    int nestingLevel = 0;
    bool isWithinQuotes = false;

    /* Validate all the arguments.*/
    if( ( pAwsIotJsonDocument == NULL ) || ( pAwsIotJsonKey == NULL ) ||
        ( awsIotJsonDocumentLength == 0 ) || ( awsIotJsonKeyLength == 0 ) )
    {
        return false;
    }

    /* Ensure the JSON document is long enough to contain the key/value pair. At
     * the very least, a JSON key/value pair must contain the key and the 6
     * characters {":""} */
    if( awsIotJsonDocumentLength < awsIotJsonKeyLength + 6 )
    {
        return false;
    }

    /* Search the characters in the JSON document for the key. The end of the JSON
     * document does not have to be searched once too few characters remain to hold a
     * value. */
    while( i < awsIotJsonDocumentLength - awsIotJsonKeyLength - 3 )
    {
        /* If the first character in the key is found and there's an unescaped double
         * quote after the key length, do a string compare for the key. */
        if( ( IS_QUOTE( pAwsIotJsonDocument, i ) ) &&
            ( IS_QUOTE( pAwsIotJsonDocument, i + 1 + awsIotJsonKeyLength ) ) &&
            ( pAwsIotJsonDocument[ i + 1 ] == pAwsIotJsonKey[ 0 ] ) &&
            ( strncmp( pAwsIotJsonDocument + i + 1,
                       pAwsIotJsonKey,
                       awsIotJsonKeyLength ) == 0 ) )
        {
            /* Key found; this is a potential match. */

            /* Skip the characters in the JSON key and closing double quote. */
            /* While loop guarantees that i < awsIotJsonDocumentLength - 1 */
            i += awsIotJsonKeyLength + 2;

            /* Skip all whitespace characters between the closing " and the : */
            while( IS_WHITESPACE( pAwsIotJsonDocument, i ) )
            {
                i++;

                /* If the end of the document is reached, this isn't a match. */
                if( i >= awsIotJsonDocumentLength )
                {
                    return false;
                }
            }

            /* The character immediately following a key (and any whitespace) must be a :
             * If it's another character, then this string is a JSON value; skip it. */
            if( pAwsIotJsonDocument[ i ] != ':' )
            {
                continue;
            }
            else
            {
                /* Skip the : */
                i++;
            }

            /* If the end of the document is reached, this isn't a match. */
            if( i >= awsIotJsonDocumentLength )
            {
                return false;
            }

            /* Skip all whitespace characters between : and the first character in the value. */
            while( IS_WHITESPACE( pAwsIotJsonDocument, i ) )
            {
                i++;

                /* If the end of the document is reached, this isn't a match. */
                if( i >= awsIotJsonDocumentLength )
                {
                    return false;
                }
            }

            /* Value found. Set the output parameter. */
            if( pAwsIotJsonValue != NULL )
            {
                *pAwsIotJsonValue = pAwsIotJsonDocument + i;
            }

            /* Calculate the value's length. */
            switch( pAwsIotJsonDocument[ i ] )
            {
                /* Calculate length of a JSON string. */
                case '\"':
                    /* Include the length of the opening and closing double quotes. */
                    jsonValueLength = 2;

                    /* Skip the opening double quote. */
                    i++;

                    /* If the end of the document is reached, this isn't a match. */
                    if( i >= awsIotJsonDocumentLength )
                    {
                        return false;
                    }

                    /* Add the length of all characters in the JSON string. */
                    while( pAwsIotJsonDocument[ i ] != '\"' )
                    {
                        /* Ignore escaped double quotes. */
                        if( ( pAwsIotJsonDocument[ i ] == '\\' ) &&
                            ( i + 1 < awsIotJsonDocumentLength ) &&
                            ( pAwsIotJsonDocument[ i + 1 ] == '\"' ) )
                        {
                            /* Skip the characters \" */
                            i += 2;
                            jsonValueLength += 2;
                        }
                        else
                        {
                            /* Add the length of a single character. */
                            i++;
                            jsonValueLength++;
                        }

                        /* If the end of the document is reached, this isn't a match. */
                        if( i >= awsIotJsonDocumentLength )
                        {
                            return false;
                        }
                    }

                    break;

                /* Set the matching opening and closing characters of a JSON object or array.
                 * The length calculation is performed below. */
                case '{':
                    openCharacter = '{';
                    closeCharacter = '}';
                    break;

                case '[':
                    openCharacter = '[';
                    closeCharacter = ']';
                    break;

                /* Calculate the length of a JSON primitive. */
                default:

                    /* Skip the characters in the JSON value. The JSON value ends with a , or } */
                    while( pAwsIotJsonDocument[ i ] != ',' &&
                           pAwsIotJsonDocument[ i ] != '}' )
                    {
                        /* Any whitespace before a , or } means the JSON document is invalid. */
                        if( IS_WHITESPACE( pAwsIotJsonDocument, i ) )
                        {
                            return false;
                        }

                        i++;
                        jsonValueLength++;

                        /* If the end of the document is reached, this isn't a match. */
                        if( i >= awsIotJsonDocumentLength )
                        {
                            return false;
                        }
                    }

                    break;
            }

            /* Calculate the length of a JSON object or array. */
            if( ( openCharacter != '\0' ) && ( closeCharacter != '\0' ) )
            {
                /* Include the length of the opening and closing characters. */
                jsonValueLength = 2;

                /* Skip the opening character. */
                i++;

                /* If the end of the document is reached, this isn't a match. */
                if( i >= awsIotJsonDocumentLength )
                {
                    return false;
                }

                /* Add the length of all characters in the JSON object or array. This
                 * includes the length of nested objects. */
                while( pAwsIotJsonDocument[ i ] != closeCharacter ||
                       ( pAwsIotJsonDocument[ i ] == closeCharacter && ( nestingLevel != 0 || isWithinQuotes ) ) )
                {
                    /* Check if its a quote so as to avoid considering the
                     * nested levels for opening and closing characters within
                     * quotes.
                     */
                    if( IS_QUOTE( pAwsIotJsonDocument, i ) )
                    {
                        /*Toggle the flag*/
                        isWithinQuotes = !isWithinQuotes;
                    }

                    /* Calculate the nesting levels only if not in quotes. */
                    if( !isWithinQuotes )
                    {
                        /* An opening character starts a nested object. */
                        if( pAwsIotJsonDocument[ i ] == openCharacter )
                        {
                            nestingLevel++;
                        }
                        /* A closing character ends a nested object. */
                        else if( pAwsIotJsonDocument[ i ] == closeCharacter )
                        {
                            nestingLevel--;
                        }
                    }

                    i++;
                    jsonValueLength++;

                    /* If the end of the document is reached, this isn't a match. */
                    if( i >= awsIotJsonDocumentLength )
                    {
                        return false;
                    }
                }
            }

            /* JSON value length calculated; set the output parameter. */
            if( pAwsIotJsonValueLength != NULL )
            {
                *pAwsIotJsonValueLength = jsonValueLength;
            }

            return true;
        }

        i++;
    }

    return false;
}

/*-----------------------------------------------------------*/
