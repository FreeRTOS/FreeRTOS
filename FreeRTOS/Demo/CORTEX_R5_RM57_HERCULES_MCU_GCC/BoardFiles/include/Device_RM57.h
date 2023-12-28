/**********************************************************************************************************************
 *  FILE DESCRIPTION
 *  -------------------------------------------------------------------------------------------------------------------
 *         File:  Device_RM57.c
 *      Project:  Tms570_TIFEEDriver
 *       Module:  TIFEEDriver
 *    Generator:  None
 *
 *  Description:  This file defines the number of sectors.
 *---------------------------------------------------------------------------------------------------------------------
 * Author:  Vishwanath Reddy
 *---------------------------------------------------------------------------------------------------------------------
 * Revision History
 *---------------------------------------------------------------------------------------------------------------------
 * Version        Date         Author               Change ID        Description
 *---------------------------------------------------------------------------------------------------------------------
 * 01.15.00          06Jun2014    Vishwanath Reddy                Initial Version.
 *********************************************************************************************************************/

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/*********************************************************************************************************************
 * INCLUDES
 *********************************************************************************************************************/

#ifndef DEVICE_RM57_H
    #define DEVICE_RM57_H

    /** @def DEVICE_CONFIGURATION_VERSION
     *   @brief Device Configuration Version
     *
     *   @note Indicates the current version of the device files
     */
    #define DEVICE_CONFIGURATION_VERSION \
        0U /* Indicates the current version of the device files */

    /** @def DEVICE_NUMBER_OF_FLASH_BANKS
     *   @brief Number of Flash Banks
     *
     *   @note Defines the number of Flash Banks on the device
     */
    #define DEVICE_NUMBER_OF_FLASH_BANKS \
        1U /* Defines the number of Flash Banks on the device */

    /** @def DEVICE_BANK_MAX_NUMBER_OF_SECTORS
     *   @brief Maximum number of Sectors
     *
     *   @note Defines the maxium number of sectors in all banks
     */
    #define DEVICE_BANK_MAX_NUMBER_OF_SECTORS \
        32U /* Defines the maxium number of sectors in all banks */

    /** @def DEVICE_BANK1_NUMBER_OF_SECTORS
     *   @brief Number of Sectors
     *
     *   @note Defines the number of sectors in bank1
     */
    #define DEVICE_BANK1_NUMBER_OF_SECTORS \
        32U /* Defines the number of sectors in bank1 */

    /** @def DEVICE_NUMBER_OF_READ_CYCLE_THRESHOLDS
     *   @brief Number of Sectors
     *
     *   @note Defines the number of Read Cycle Thresholds
     */
    #define DEVICE_NUMBER_OF_READ_CYCLE_THRESHOLDS \
        4U /* Defines the number of Read Cycle Thresholds */

    /* Include Files */
    #ifndef _PLATFORM_TYPES_H_
        #define _PLATFORM_TYPES_H_
    #endif
    #ifndef _L2FMC
        #define _L2FMC
    #endif
    #include "F021.h"
    #include "hal_stdtypes.h"
    #include "Device_types.h"

#endif /* DEVICE_RM57_H */

/* End of File */
