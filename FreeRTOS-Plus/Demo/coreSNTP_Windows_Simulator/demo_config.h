/*
 * FreeRTOS V202104.00
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef DEMO_CONFIG_H
#define DEMO_CONFIG_H

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Include logging header files and define logging macros in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for DEMO.
 * 3. Include the header file "logging_stack.h", if logging is enabled for DEMO.
 */

#include "logging_levels.h"

/* Logging configuration for the Demo. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "SNTPDemo"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_DEBUG
#endif

/* Prototype for the function used to print to console on Windows simulator
 * of FreeRTOS.
 * The function prints to the console before the network is connected;
 * then a UDP port after the network has connected. */
extern void vLoggingPrintf( const char * pcFormatString,
                            ... );

/* Map the SdkLog macro to the logging function to enable logging
 * on Windows simulator. */
#ifndef SdkLog
    #define SdkLog( message )    vLoggingPrintf message
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief The desired accuracy (in milliseconds) of system clock in relation with internet time.
 * In other words, this is the maximum tolerance desired for clock drift in the system.
 */
#define democonfigDESIRED_CLOCK_ACCURACY_MS     ( 1000 )

/**
 * @brief The system clock tolerance (in parts per million) that represents the rate of clock
 * drift of the system. The rate can be viewed as the system clock drift that occurs as milliseconds
 * per second.
 *
 * @note In systems with a HW oscillator based clock, the frequency tolerance can be obtained from the
 * hardware specification of the clock oscillator.
 * @note This demo DOES NOT use a hardware clock oscillator as it runs on Windows Simulator. The configuration
 * ONLY provides the user to view the impact of the settings for "Clock Tolerance" and "Desired
 * Clock Accuracy" configurations on the calculated "SNTP polling period".
 */
#define democonfigSYSTEM_CLOCK_TOLERANCE_PPM    ( 32000 )

/**
 * @brief The set of time servers, in decreasing order of priority, for configuring the SNTP client.
 * The servers SHOULD be listed as comma-separated list of strings. For example, the following
 * can be a configuration used:
 *
 * #define democonfigLIST_OF_TIME_SERVERS          "0.pool.ntp.org", "1.pool.ntp.org"
 */
#define democonfigLIST_OF_TIME_SERVERS          "time.cloudflare.com", "pool.ntp.org"

/**
 * @brief The year to bake in the demo application for initializing the system clock with.
 * The demo initializes the system clock time for the starting second of the 1st Janurary of
 * the configured year. So for example, with a configuration of year 2021, the demo will
 * initialize the system clock time as 1st January 2021 00h:00m:00s.
 *
 * @note The coreSNTP library REQUIRES that the client system time is within ~68 years of internet
 * time. Thus, for systems that do not have an Real-Time Clock module, this demo shows how
 * a starting time can be baked in the device firmware to keep the starting time of the system
 * close to actual time on the first boot-up of device.
 * For such systems without Real-Time Clock module, all device boot ups from subsequent device resets
 * or power cycles can continue to carry close to correct time by EITHER
 *  * (RECOMMENDED) Saving the most recent time in non-volatile memory
 *     OR
 *  * Using the same firmware baked-in starting time of device for every boot-up.
 */
#define democonfigSYSTEM_START_YEAR             ( 2021 )

/**
 * @brief The timeout (in milliseconds) for the time response to a time request made to a
 * time server.
 */
#define democonfigSERVER_RESPONSE_TIMEOUT_MS    ( 5000 )

/**
 * @brief Set the stack size of the main demo task.
 *
 * In the Windows port, this stack only holds a structure. The actual
 * stack is created by an operating system thread.
 */
#define democonfigDEMO_STACKSIZE                configMINIMAL_STACK_SIZE

#endif /* DEMO_CONFIG_H */
