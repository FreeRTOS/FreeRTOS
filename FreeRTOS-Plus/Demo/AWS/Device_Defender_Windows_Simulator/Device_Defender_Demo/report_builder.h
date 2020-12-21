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

#ifndef REPORT_BUILDER_H_
#define REPORT_BUILDER_H_

/* Metrics collector. */
#include "metrics_collector.h"

/**
 * @brief Return codes from report builder APIs.
 */
typedef enum
{
    eReportBuilderSuccess = 0,
    eReportBuilderBadParameter,
    eReportBuilderBufferTooSmall
} eReportBuilderStatus;

/**
 * @brief Represents metrics to be included in the report.
 */
typedef struct ReportMetrics
{
    NetworkStats_t * pxNetworkStats;
    uint16_t * pusOpenTcpPortsArray;
    uint32_t ulOpenTcpPortsArrayLength;
    uint16_t * pusOpenUdpPortsArray;
    uint32_t ulOpenUdpPortsArrayLength;
    Connection_t * pxEstablishedConnectionsArray;
    uint32_t ulEstablishedConnectionsArrayLength;
} ReportMetrics_t;

/**
 * @brief Generate a report in the format expected by the AWS IoT Device Defender
 * Service.
 *
 * @param[in] pcBuffer The buffer to write the report into.
 * @param[in] ulBufferLength The length of the buffer.
 * @param[in] pxMetrics Metrics to write in the generated report.
 * @param[in] ulMajorReportVersion Major version of the report.
 * @param[in] ulMinorReportVersion Minor version of the report.
 * @param[in] ulReportId Value to be used as the ulReportId in the generated report.
 * @param[out] pulOutReprotLength The length of the generated report.
 *
 * @return #ReportBuilderSuccess if the report is successfully generated;
 * #ReportBuilderBadParameter if invalid parameters are passed;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full report.
 */
eReportBuilderStatus eGenerateJsonReport( char * pcBuffer,
                                          uint32_t ulBufferLength,
                                          const ReportMetrics_t * pxMetrics,
                                          uint32_t ulMajorReportVersion,
                                          uint32_t ulMinorReportVersion,
                                          uint32_t ulReportId,
                                          uint32_t * pulOutReportLength );

#endif /* ifndef REPORT_BUILDER_H_ */
