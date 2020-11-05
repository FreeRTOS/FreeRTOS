/*
 * AWS IoT Device Shadow v1.0.1
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
 */

/**
 * @file shadow_config.h
 * @brief Values for the configuration macros for the Shadow library.
 */

#ifndef SHADOW_CONFIG_H_
#define SHADOW_CONFIG_H_

/* The macro definition for SHADOW_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the Shadow library without the custom config
 * file shadow_config.h.
 *
 * Without the custom config, the Shadow library builds with
 * default values of config macros defined in shadow_config_defaults.h file.
 *
 * If a custom config is provided, then SHADOW_DO_NOT_USE_CUSTOM_CONFIG should not
 * be defined.
 */
#ifdef DOXYGEN
    #define SHADOW_DO_NOT_USE_CUSTOM_CONFIG
#endif

/**
 * @brief Macro that is called in the Shadow library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the Shadow library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the Shadow library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to shadow_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the Shadow library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the Shadow library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the Shadow library, this macro should be mapped to the
 * application-specific logging implementation that supports warning logging.
 *
 * @note This logging macro is called in the Shadow library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to shadow_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the Shadow library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the Shadow library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the Shadow library, this macro should be mapped to the
 * application-specific logging implementation that supports info logging.
 *
 * @note This logging macro is called in the Shadow library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to shadow_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the Shadow library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the Shadow library for logging "Debug" level
 * messages.
 *
 * To enable debug level logging from Shadow library, this macro should be mapped to the
 * application-specific logging implementation that supports debug logging.
 *
 * @note This logging macro is called in the Shadow library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to shadow_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the Shadow library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

#endif /* ifndef SHADOW_CONFIG_H_ */
