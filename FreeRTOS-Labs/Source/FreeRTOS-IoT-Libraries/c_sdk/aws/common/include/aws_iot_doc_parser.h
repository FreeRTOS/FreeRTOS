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
 * @file aws_iot_doc_parser.h
 * @brief Parser for AWS IoT Services Documents. This is a JSON parser
 * specifically designed to process and retrieve a value from a AWS IoT JSON
 * document, used in AWS IoT libraries such as Shadow and Jobs. Given a key and
 * a JSON document, AwsIotDocParser_FindValue() will find the first occurrence
 * of the key and return its respective value. The design goal of this parser
 * is to be light weight and to be of low memory footprint. However, it does
 * not check the correctness of the JSON documents. Hence, this parser is not
 * meant to be used for general purpose JSON parsing.
 */

#ifndef AWS_IOT_DOC_PARSER_H_
#define AWS_IOT_DOC_PARSER_H_

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>

/**
 * @brief Find a value for a key from a AWS IoT service JSON document.
 *
 * @warning The parsing will not check for the correctness of the JSON document.
 * It is designed to be light weight and to be of low memory footprint rather
 * than checking for the correctness of the JSON document. Hence this is not
 * meant to be used for a general purpose JSON parsing. This is recommended to
 * be used only with mutually authenticated AWS IoT services such as Shadow and
 * Jobs where the document will always be a well formatted JSON.
 *
 * @param[in] pAwsIotJsonDocument Pointer to AWS IoT Service JSON document.
 * @param[in] awsIotJsonDocumentLength Length of AWS IoT Service JSON document.
 * @param[in] pAwsIotJsonKey JSON key for finding the associated value.
 * @param[in] awsIotJsonKeyLength Length of the JSON key.
 * @param[out] pAwsIotJsonValue Pointer to the pointer of value found.
 * @param[out] pAwsIotJsonValueLength Pointer to the length of the value found.
 *
 * @returns `true` if a value is found, `false` if a value cannot be found. If
 * returns `false`, the values in out pointers will not be valid.
 */
bool AwsIotDocParser_FindValue( const char * pAwsIotJsonDocument,
                                size_t awsIotJsonDocumentLength,
                                const char * pAwsIotJsonKey,
                                size_t awsIotJsonKeyLength,
                                const char ** pAwsIotJsonValue,
                                size_t * pAwsIotJsonValueLength );

#endif /* ifndef AWS_IOT_DOC_PARSER_H_ */
