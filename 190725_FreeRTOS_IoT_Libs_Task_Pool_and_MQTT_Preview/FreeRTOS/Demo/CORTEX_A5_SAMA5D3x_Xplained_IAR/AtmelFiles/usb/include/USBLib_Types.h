/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file
 *  Definitions for USB Lib compiling.
 */

#ifndef USBLIB_TYPES_H
#define USBLIB_TYPES_H
/*----------------------------------------------------------------------------
 *         Includes
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Defines
 *----------------------------------------------------------------------------*/

/* Define WEAK attribute */
#ifndef WEAK
#if defined   ( __CC_ARM   )
    #define WEAK __attribute__ ((weak))
#elif defined ( __ICCARM__ )
    #define WEAK __weak
#elif defined (  __GNUC__  )
    #define WEAK __attribute__ ((weak))
#endif
#endif

/** USB status ReturnCode */
typedef enum _USBRC {
    USBRC_OK = 0,      /**< Operation was successful */
    USBRC_SUCCESS = 0, /**< Operation was successful */
    /* Bool codes */
    USBRC_FALSE = 0,   /**< As boolean TRUE */
    USBRC_TRUE  = 1,   /**< As boolean FALSE */
    /* Error codes */    
    USBRC_BUSY,        /**< EP/Device is already busy */
    USBRC_ABORTED,     /**< Operation aborted due to error or stall */
    USBRC_CANCELED,    /**< Operation canceled by user */
    USBRC_RESET,       /**< Operation aborted due to init/reset/un-configure */
    USBRC_PARTIAL_DONE,/**< Part of operation successfully done */
    USBRC_FINISHED,    /**< All operation successfully done and terminate */

    USBRC_PARAM_ERR,   /**< Failed due to parameter error */
    USBRC_STATE_ERR,   /**< Failed due to state error */
    USBRC_ERROR,       /**< General error */

    USBRC_SW_NOT_SUPPORTED = 0xFD, /**< Failed due to SW not supported */
    USBRC_HW_NOT_SUPPORTED = 0xFE  /**< Failed due to HW not supported */
} USBRC;
 
#endif /* #define USBLIB_TYPES_H */

