/**********************************************************************************************************************
 *  FILE DESCRIPTION
 *  -------------------------------------------------------------------------------------------------------------------
 *         File:  Device_types.h
 *      Project:  Tms570_TIFEEDriver
 *       Module:  TIFEEDriver
 *    Generator:  None
 *
 *  Description:  This file defines the structures.
 *---------------------------------------------------------------------------------------------------------------------
 * Author:  Vishwanath Reddy
 *---------------------------------------------------------------------------------------------------------------------
 * Revision History
 *---------------------------------------------------------------------------------------------------------------------
 * Version        Date         Author               Change ID        Description
 *---------------------------------------------------------------------------------------------------------------------
 * 01.15.00		  06Jun2014    Vishwanath Reddy                     Initial Version.
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

#ifndef DEVICE_TYPES_H
    #define DEVICE_TYPES_H

    #include "hal_stdtypes.h"

/* Enum to describe the type of error handling on the device */
typedef enum
{
    Device_ErrorHandlingNone,   /* Device has no error handling */
    Device_ErrorHandlingParity, /* Device has parity error handling */
    Device_ErrorHandlingEcc     /* Device has ECC error handling */
} Device_FlashErrorCorrectionProcessType;

/* Enum to describe the ARM core on the device*/
typedef enum
{
    Device_CoreNone, /* To indicate that the device has a single core */
    Device_Arm7,     /* To indicate that the device has a ARM7 core	*/
    Device_CortexR4, /* To indicate that the device has a CortexR4 core */
    Device_CortexM3  /* To indicate that the device has a CortexM3 core */
} Device_ArmCoreType;

/* Structure defines an individual sector within a bank */
typedef struct
{
    Fapi_FlashSectorType Device_Sector; /* Sector number */
    uint32 Device_SectorStartAddress;   /* Starting address of the sector */
    uint32 Device_SectorLength;         /* Length of the sector */
    uint32 Device_MaxWriteCycles;       /* Number of cycles the sector is rated for */
    uint32 Device_EccAddress;
    uint32 Device_EccLength;
} Device_SectorType;

/* Structure defines an individual bank */
typedef struct
{
    Fapi_FmcRegistersType * Device_ControlRegister;
    Fapi_FlashBankType Device_Core; /* Core number for this bank */
    Device_SectorType Device_SectorInfo[ DEVICE_BANK_MAX_NUMBER_OF_SECTORS ]; /* Array of
                                                                                 the
                                                                                 Sectors
                                                                                 within a
                                                                                 bank */
} Device_BankType;

/* Structure defines the Flash structure of the device */
typedef struct
{
    uint8 Device_DeviceName[ 12 ]; /* Device name */
    uint32 Device_EngineeringId;   /* Device Engineering ID */
    Device_FlashErrorCorrectionProcessType
        Device_FlashErrorHandlingProcessInfo; /* Indicates
                                                 which
                                                 type
                                                 of bit
                                                 Error
                                                 handling
                                                 is on
                                                 the
                                                 device
                                               */
    Device_ArmCoreType Device_MasterCore; /* Indicates the Master core type on the device
                                           */
    boolean Device_SupportsInterrupts;    /* Indicates if the device supports Flash
                                             interrupts for processing Flash */
    uint32 Device_NominalWriteTime; /* Nominal time for one write command operation in uS
                                     */
    uint32 Device_MaximumWriteTime; /* Maximum time for one write command operation in uS
                                     */
    Device_BankType Device_BankInfo[ DEVICE_NUMBER_OF_FLASH_BANKS ]; /* Array of Banks on
                                                                        the device */
} Device_FlashType;

#endif /* DEVICE_TYPES_H */

/* End of File */
