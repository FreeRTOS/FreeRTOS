/**********************************************************************************************************************
 *  FILE DESCRIPTION
 *  -------------------------------------------------------------------------------------------------------------------
 *         File:  ti_fee.h
 *      Project:  Tms570_TIFEEDriver
 *       Module:  TIFEEDriver
 *    Generator:  None
 *
 *  Description:  This file implements the TI FEE Api.
 *---------------------------------------------------------------------------------------------------------------------
 * Author:  Vishwanath Reddy
 *---------------------------------------------------------------------------------------------------------------------
 * Revision History
 *---------------------------------------------------------------------------------------------------------------------
 * Version        Date         Author               Change ID        Description
 *---------------------------------------------------------------------------------------------------------------------
 * 00.01.00       31Aug2012    Vishwanath Reddy     0000000000000    Initial Version
 * 00.01.01       29Oct2012    Vishwanath Reddy     0000000000000    Changes for
 *implementing Error Recovery 00.01.02       30Nov2012    Vishwanath Reddy SDOCM00097786
 *Misra Fixes, Memory segmentation changes. 00.01.03       14Jan2013    Vishwanath Reddy
 *SDOCM00098510    Changes as requested by Vector. 00.01.04		  12Feb2012	   Vishwanath
 *Reddy     SDOCM00099152    Integration issues fix. 00.01.05		  04Mar2013 Vishwanath
 *Reddy     SDOCM00099152    Added Deleting a block feature, bug fixes. 00.01.06
 *11Mar2013	   Vishwanath Reddy     SDOCM00099152    Added feature : copying of
 *unconfigured blocks. 00.01.07		  15Mar2013	   Vishwanath Reddy     SDOCM00099152
 *Added feature : Number of 8 bytes writes, fixed issue with copy blocks. 00.01.08
 *05Apr2013	   Vishwanath Reddy     SDOCM00099152    Added feature : CRC check for
 *unconfigured  blocks, Main function modified to complete writes as fast as possible,
 *Added Non polling mode support. 00.01.09		  19Apr2013	   Vishwanath Reddy
 *SDOCM00099152    Warning removal, Added feature comparision of data during write.
 * 00.01.10       11Jun2013	   Vishwanath Reddy     SDOCM00101845	 Updated version
 *information. 00.01.11       05Jul2013	   Vishwanath Reddy     SDOCM00101643	 Updated
 *version information. 01.12.00		  13Dec2013    Vishwanath Reddy     SDOCM00105412
 *Traceability tags added. MISRA C fixes.	Version info corrected. 01.13.00 30Dec2013
 *Vishwanath Reddy     0000000000000	 Undated version info for  SDOCM00107976 and
 *SDOCM00105795. 01.13.01       19May2014	   Vishwanath Reddy     0000000000000
 *Updated version info for  SDOCM00107913 and SDOCM00107622. 01.13.02       12Jun2014
 *Vishwanath Reddy     0000000000000	 Updated version info for SDOCM00108238 01.14.00
 *26Mar2014    Vishwanath Reddy                      Update version info for
 *SDOCM00107161. 01.15.00		  06Jun2014    Vishwanath Reddy Support for Conqueror.
 * 01.16.00		  15Jul2014    Vishwanath Reddy     SDOCM00112141    Remove  MISRA
 *warnings. 01.16.01		  12Sep2014	   Vishwanath Reddy     SDOCM00112930 Prototype
 *for TI_Fee_SuspendResumeErase added. TI_Fee_EraseCommandType enum added. extern added
 *for TI_Fee_bEraseSuspended. 01.17.00		  15Oct2014    Vishwanath Reddy SDOCM00113379
 *RAM Optimization changes. 01.17.01		  30Oct2014    Vishwanath Reddy SDOCM00113536
 *Support for TMS570LS07xx,TMS570LS09xx, TMS570LS05xx, RM44Lx. 01.17.02		  26Dec2014
 *Vishwanath Reddy     SDOCM00114102    FLEE Errata Fix. SDOCM00114104    Change ALL 1's
 *OK check condition. Updated version info. Added new macros. SDOCM00114423	 Add new enum
 *TI_Fee_DeviceType. Add new variable TI_Fee_MaxSectors and prototype
 *TI_FeeInternal_PopulateStructures. 01.18.00		  12Oct2015    Vishwanath Reddy
 *SDOCM00119455    Update version history. Update ti_fee_util.c file for the bugfix "If
 *morethan one data set is config- ured, then a valid block may get invalidated if
 *                                                                   multiple valid blocks
 *are present in FEE memory. 01.18.01		  17Nov2015    Vishwanath Reddy SDOCM00120161
 *Update version history. In TI_FeeInternal_FeeManager, do not change the state to
 *IDLE,after completing the copy operation. 01.18.02		  05Feb2016    Vishwanath
 *Reddy     SDOCM00121158    Update version history. Add a call of
 *TI_FeeInternal_PollFlashStatus() before reading data from FEE bank in
 *                                                                   TI_FeeInternal_UpdateBlockOffsetArray(),
 *                                                                   TI_Fee_WriteAsync(),TI_Fee_WriteSync(),
 *                                                                   TI_Fee_ReadSync(),
 *TI_Fee_Read() 01.18.03       30June2016   Vishwanath Reddy     SDOCM00122388    Update
 *patch version TI_FEE_SW_PATCH_VERSION. TI_FEE_FLASH_CRC_ENABLE is renamed to
 *                                                                   TI_FEE_FLASH_CHECKSUM_ENABLE.
 *                                                  SDOCM00122429    In ti_fee_types.h,
 *add error when endianess is not defined. 01.19.00       08Augu2016   Vishwanath Reddy
 *SDOCM00122592    Update patch version TI_FEE_MINOR_VERSION. Code for using partially
 *ersed sector is now removed. Bugfix for FEE reading from unimplemented memory space.
 * 01.19.01       12Augu2016   Vishwanath Reddy     SDOCM00122543    Update patch version
 *TI_FEE_MINOR_VERSION. Synchronous write API modified to avoid copy of already copied
 *block. 01.19.02       25Janu2017   Vishwanath Reddy     SDOCM00122832    Update patch
 *version TI_FEE_MINOR_VERSION. Format API modified to erase all configured VS.
 *                                                  SDOCM00122833    In API
 *TI_Fee_ErrorRecovery, added polling for flash status before calling TI_Fee_Init.
 * 01.19.03       15May2017    Prathap Srinivasan   SDOCM00122917    Added
 *TI_Fee_bIsMainFunctionCalled Global Variable. 01.19.04		  05Dec2017    Prathap
 *Srinivasan   HERCULES_SW-5082 Update version history.
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

#ifndef TI_FEE_H
    #define TI_FEE_H

    /**********************************************************************************************************************
     * INCLUDES
     *********************************************************************************************************************/
    #include "hal_stdtypes.h"
    #include "fee_interface.h"
    #include "ti_fee_types.h"
    #include "ti_fee_cfg.h"

    /**********************************************************************************************************************
     *  GLOBAL CONSTANT MACROS
     *********************************************************************************************************************/
    /* Fee Published Information */
    #define TI_FEE_MAJOR_VERSION          3U
    #define TI_FEE_MINOR_VERSION          0U
    #define TI_FEE_PATCH_VERSION          2U
    #define TI_FEE_SW_MAJOR_VERSION       1U
    #define TI_FEE_SW_MINOR_VERSION       19U
    #define TI_FEE_SW_PATCH_VERSION       4U

    #define TI_FEE_VIRTUAL_SECTOR_VERSION 1U

    /* Virtual sector states */
    #define ActiveVSHi                    0x0000FFFFU
    #define ActiveVSLo                    0x00000000U
    #define CopyVSHi                      0xFFFFFFFFU
    #define CopyVSLo                      0x00000000U
    #define EmptyVSHi                     0xFFFFFFFFU
    #define EmptyVSLo                     0x0000FFFFU
    #define InvalidVSHi                   0xFFFFFFFFU
    #define InvalidVSLo                   0xFFFFFFFFU
    #define ReadyforEraseVSHi             0x00000000U
    #define ReadyforEraseVSLo             0x00000000U

    /* Data Block states*/
    #define EmptyBlockHi                  0xFFFFFFFFU
    #define EmptyBlockLo                  0xFFFFFFFFU
    #define StartProgramBlockHi           0xFFFF0000U
    #define StartProgramBlockLo           0xFFFFFFFFU
    #define ValidBlockHi                  0x00000000U
    #define ValidBlockLo                  0xFFFFFFFFU
    #define InvalidBlockHi                0x00000000U
    #define InvalidBlockLo                0xFFFF0000U
    #define CorruptBlockHi                0x00000000U
    #define CorruptBlockLo                0x00000000U

    #define FEE_BANK                      0U

    /* Enable/Disable FEE sectors */
    #define FEE_DISABLE_SECTORS_31_00     0x00000000U
    #define FEE_DISABLE_SECTORS_63_32     0x00000000U
    #define FEE_ENABLE_SECTORS_31_00      0xFFFFFFFFU
    #define FEE_ENABLE_SECTORS_63_32      0xFFFFFFFFU

/**********************************************************************************************************************
 *  GLOBAL DATA TYPES AND STRUCTURES
 *********************************************************************************************************************/
/* Structures used */
/* Enum to describe the Fee Status types */
typedef enum
{
    TI_FEE_OK = 0U,   /* Function returned no error */
    TI_FEE_ERROR = 1U /* Function returned an error */
} TI_Fee_StatusType;

/* Enum to describe the Virtual Sector State */
typedef enum
{
    VsState_Invalid = 1U,
    VsState_Empty = 2U,
    VsState_Copy = 3U,
    VsState_Active = 4U,
    VsState_ReadyForErase = 5U
} VirtualSectorStatesType;

/* Enum to describe the Block State */
typedef enum
{
    Block_StartProg = 1U,
    Block_Valid = 2U,
    Block_Invalid = 3U
} BlockStatesType;

/* Enum for error trpes */
typedef enum
{
    Error_Nil = 0U,
    Error_TwoActiveVS = 1U,
    Error_TwoCopyVS = 2U,
    Error_SetupStateMachine = 3U,
    Error_CopyButNoActiveVS = 4U,
    Error_NoActiveVS = 5U,
    Error_BlockInvalid = 6U,
    Error_NullDataPtr = 7U,
    Error_NoFreeVS = 8U,
    Error_InvalidVirtualSectorParameter = 9U,
    Error_ExceedSectorOnBank = 10U,
    Error_EraseVS = 11U,
    Error_BlockOffsetGtBlockSize = 12U,
    Error_LengthParam = 13U,
    Error_FeeUninit = 14U,
    Error_Suspend = 15U,
    Error_InvalidBlockIndex = 16U,
    Error_NoErase = 17U,
    Error_CurrentAddress = 18U,
    Error_Exceed_No_Of_DataSets = 19U
} TI_Fee_ErrorCodeType;

typedef enum
{
    Suspend_Erase = 0U,
    Resume_Erase
} TI_Fee_EraseCommandType;

/* Enum to describe the Device types */
typedef enum
{
    CHAMPION = 0U, /* Function returned no error */
    ARCHER = 1U    /* Function returned an error */
} TI_Fee_DeviceType;

typedef uint32 TI_Fee_AddressType; /* Used for defining variables to indicate number of
                                    * bytes for address offset */
typedef uint32 TI_Fee_LengthType;  /* Used for defining variables to indicate number of
                                    * bytes per read/write/erase */
typedef TI_Fee_ErrorCodeType Fee_ErrorCodeType;

/* Structure used when defining virtual sectors */
/* The following error checks need to be performed: */
/* Virtual Sector definitions are not allowed to overlap */
/* Virtual Sector definition is at least twice the size in bytes of the total size of all
 * defined blocks */
/* We will need to define a formula to indicate if the number of write cycles indicated in
 * the block definitions */
/* is possible in the defined Virtual Sector. */
/* Ending sector cannot be less than Starting sector */
typedef struct
{
    uint16 FeeVirtualSectorNumber; /* Virtual Sector's Number - 0 and 0xFFFF values are
                                      not allowed*/
                                   /* Minimum 1, Maximum 4 */
    uint16 FeeFlashBank;           /* Flash Bank to use for virtual sector. */

    /* As we do not allow Flash EEPROM Emulation in Bank 0,
     * 0 is not a valid option */
    /* Defaultvalue 1, Minimum 1, Maxiumum 7 */
    Fapi_FlashSectorType FeeStartSector; /* Defines the Starting Sector inthe Bank for
                                            this VirtualSector*/
    Fapi_FlashSectorType FeeEndSector;   /* Defines the Ending Sector inthe Bank for this
                                            Virtual Sector */

    /* Start and End sectors can be the same, which indicates only
     * one sector */
    /* is the entire virtual sector. */
    /* Values are based on the FLASH_SECT enum */

    /* Defaultvalue and Min is the same sector defined as the starting
     * sector */
    /* Max values are based onthe device definition file being used.*/
} Fee_VirtualSectorConfigType;

/* Structure used when defining blocks */
typedef struct
{
    uint16 FeeBlockNumber;    /* Block's Number - 0 and 0xFFFF values are not allowed */
                              /* Start 1, Next: Number of Blocks + 1, Min 1, Max 0xFFFE */
    uint16 FeeBlockSize;      /* Block's Size - Actual number of bits used is reduced */
                              /* by number of bits used for dataset. */
                              /* Default 8, Min 1, Max (2^(16-# of Dataset Bits))-1 */
    boolean FeeImmediateData; /* Indicates if the block is used for immediate data */
                              /* Default: False */
    uint32 FeeNumberOfWriteCycles; /* Number of write cycles this block requires */

    /* Default: 0, but this will not be a valid number.
     * Force customer to select a value */
    /* Min 1, Max (2^32)-1 */
    uint8 FeeDeviceIndex;      /* Device Index - This will always be 0 */
                               /* Fixed value: 0 */
    uint8 FeeNumberOfDataSets; /* Number of DataSets for the Block */
                               /* Default value: 1 */
    uint8 FeeEEPNumber;
} Fee_BlockConfigType;

/* Structure used for Global variables */
typedef struct
{
    TI_Fee_AddressType Fee_oFlashNextAddress;   /* The next Flash Address to write to */
    TI_Fee_AddressType Fee_oCopyCurrentAddress; /* Indicates the Address within the Active
                                                 * VS which will be copied to Copy VS */
    TI_Fee_AddressType Fee_oCopyNextAddress; /* Indicates the Address within the Copy VS
                                              * to which the data from Active VS will be
                                              * copied to */
    TI_Fee_AddressType Fee_u32nextwriteaddress; /* Indicates the next free Address within
                                                 * the curent VS to which the data will be
                                                 * written */
    TI_Fee_AddressType Fee_oVirtualSectorStartAddress; /* Start Address of the current
                                                          Virtual Sector */
    TI_Fee_AddressType Fee_oVirtualSectorEndAddress; /* End Address of the current Virtual
                                                        Sector */
    TI_Fee_AddressType Fee_oCopyVirtualSectorAddress; /* Start Address of the Copy Virtual
                                                         Address */
    TI_Fee_AddressType Fee_oCurrentStartAddress; /* Start Address of the Previous Block */
    TI_Fee_AddressType Fee_oCurrentBlockHeader;  /* Start Address of the Block which is
                                                  * being currently  written*/
    TI_Fee_AddressType Fee_oWriteAddress;     /* Address within the VS where data is to be
                                                 written */
    TI_Fee_AddressType Fee_oCopyWriteAddress; /* Address within the VS where data is to be
                                                 copied */
    TI_Fee_AddressType Fee_oActiveVirtualSectorAddress; /* Start Address of the Active VS
                                                         */
    TI_Fee_AddressType Fee_oBlankFailAddress; /* Address of first non-blank location */
    TI_Fee_AddressType Fee_oActiveVirtualSectorStartAddress; /* Start Address of the
                                                                active VS */
    TI_Fee_AddressType Fee_oActiveVirtualSectorEndAddress; /* End Address of the active VS
                                                            */
    TI_Fee_AddressType Fee_oCopyVirtualSectorStartAddress; /* Start Address of the Copy VS
                                                            */
    TI_Fee_AddressType Fee_oCopyVirtualSectorEndAddress; /* End Address of the Copy VS */
    TI_Fee_AddressType Fee_u32nextActiveVSwriteaddress; /* Next write address in Active VS
                                                         */
    TI_Fee_AddressType Fee_u32nextCopyVSwriteaddress; /* Next write address in Copy VS */
    uint16 Fee_u16CopyBlockSize; /* Indicates the size of current block in bytes which is
                                  * been copied from Active to Copy VS */
    uint8 Fee_u8VirtualSectorStart; /* Index of the Start Sector of the VS */
    uint8 Fee_u8VirtualSectorEnd;   /* Index of the End Sector of the VS */
    uint32 Fee_au32VirtualSectorStateValue[ TI_FEE_VIRTUAL_SECTOR_OVERHEAD
                                            >> 2U ]; /* Array to store the Virtual
                                                      * Sector Header and
                                                      * Information record */
    uint8 Fee_au8VirtualSectorState[ TI_FEE_NUMBER_OF_VIRTUAL_SECTORS ]; /* Stores the
                                                                          * state of each
                                                                          * Virtual sector
                                                                          */
    uint32 Fee_au32VirtualSectorEraseCount[ TI_FEE_NUMBER_OF_VIRTUAL_SECTORS ]; /* Array
                                                                                 * to
                                                                                 * store
                                                                                 * the
                                                                                 * erase
                                                                                 * count
                                                                                 * of each
                                                                                 * Virtual
                                                                                 * Sector*/
    uint16 Fee_au16BlockOffset[ TI_FEE_TOTAL_BLOCKS_DATASETS ]; /* Array to store within
                                                                   the VS */
    uint32 Fee_au32BlockHeader[ TI_FEE_BLOCK_OVERHEAD >> 2U ]; /* Array to store the Block
                                                                  Header value */
    uint8 Fee_au8BlockCopyStatus[ TI_FEE_TOTAL_BLOCKS_DATASETS ]; /* Array to storeblock
                                                                     copy status */
    uint8 Fee_u8InternalVirtualSectorStart; /* Indicates internal VS start index */
    uint8 Fee_u8InternalVirtualSectorEnd;   /* Indicates internal VS end index */
    TI_FeeModuleStatusType Fee_ModuleState; /* Indicates the state of the FEE module */
    TI_FeeJobResultType Fee_u16JobResult; /* Stores the Job Result of the current command
                                           */
    TI_Fee_StatusType Fee_oStatus;        /* Indicates the status of FEE */
    TI_Fee_ErrorCodeType Fee_Error;       /* Indicates the Error code */
    uint16 Fee_u16CopyBlockNumber; /* Block number which is currently being copied */
    uint16 Fee_u16BlockIndex;      /* Index of the Current Block */
    uint16 Fee_u16BlockCopyIndex;  /* Index of the Block being copied from Copy to Active
                                      VS */
    uint16 Fee_u16DataSetIndex;    /* Index of the Current DataSet */
    uint16 Fee_u16ArrayIndex;      /* Index of the Current DataSet */
    uint16 Fee_u16BlockSize;       /* Size of the current block in bytes */
    uint16 Fee_u16BlockSizeinBlockHeader; /* Size of the current block. Used to write into
                                             Block Header */
    uint16 Fee_u16BlockNumberinBlockHeader; /* Number of the current block. Used to write
                                               into Block Header */
    uint8 Fee_u8ActiveVirtualSector; /* Indicates the FeeVirtualSectorNumber for the
                                        Active VS */
    uint8 Fee_u8CopyVirtualSector; /* Indicates the FeeVirtualSectorNumber for the Copy VS
                                    */
    uint32 Fee_u32InternalEraseQueue; /* Indicates which VS can be erased when the FEE is
                                       * in BusyInternal State*/
    uint8 Fee_u8WriteCopyVSHeader; /* Indicates the number of bytes of the Copy VS Header
                                    * being written */
    uint8 Fee_u8WriteCount; /* Indicates the number of bytes of the Block Header being
                             * written */
    uint8 * Fee_pu8ReadDataBuffer; /* Pointer to read data */
    uint8 * Fee_pu8ReadAddress;    /* Pointer to read address */
    uint8 * Fee_pu8Data;           /* Pointer to the next data to be written to the VS */
    uint8 * Fee_pu8CopyData;       /* Pointer to the next data to be copied to the VS */
    uint8 * Fee_pu8DataStart;      /* Pointer to the first data to be written to the VS */
    boolean Fee_bInvalidWriteBit;  /* Indicates whether the block is
                                    * written/invalidated/erased  for the first time */
    boolean Fee_bWriteData; /* Indicates that there is data which is pending to be written
                             * to the Block */
    boolean Fee_bWriteBlockHeader; /* Indicates whether the Block Header has been written
                                      or not */
    boolean bWriteFirstTime; /* Indicates if the block is being written first time */
    boolean Fee_bFindNextVirtualSector; /* Indicates if there is aneed to find next free
                                           VS */
    boolean Fee_bWriteVSHeader;     /* Indicates if block header needs to be written */
    boolean Fee_bWriteStartProgram; /* Indicates if start program block header needs to be
                                       written */
    boolean Fee_bWritePartialBlockHeader; /* Indicates if start program block header needs
                                             to be written */
    #if( TI_FEE_NUMBER_OF_UNCONFIGUREDBLOCKSTOCOPY != 0U )
    uint16 Fee_au16UnConfiguredBlockAddress
        [ TI_FEE_NUMBER_OF_UNCONFIGUREDBLOCKSTOCOPY ]; /* Indicates
                                                        * number of unconfigured blocks to
                                                        * copy */
    uint8 Fee_au8UnConfiguredBlockCopyStatus
        [ TI_FEE_NUMBER_OF_UNCONFIGUREDBLOCKSTOCOPY ]; /* Array to store block
                                                        * copy status */
    #endif
} TI_Fee_GlobalVarsType;

/**********************************************************************************************************************
 * EXTERN Declarations
 *********************************************************************************************************************/
/*  Fee Global Variables */
extern const Fee_BlockConfigType Fee_BlockConfiguration[ TI_FEE_NUMBER_OF_BLOCKS ];
    #if( TI_FEE_GENERATE_DEVICEANDVIRTUALSECTORSTRUC == STD_OFF )
extern const Fee_VirtualSectorConfigType
    Fee_VirtualSectorConfiguration[ TI_FEE_NUMBER_OF_VIRTUAL_SECTORS ];
extern const Device_FlashType Device_FlashDevice;
    #endif
    #if( TI_FEE_GENERATE_DEVICEANDVIRTUALSECTORSTRUC == STD_ON )
extern Fee_VirtualSectorConfigType
    Fee_VirtualSectorConfiguration[ TI_FEE_NUMBER_OF_VIRTUAL_SECTORS ];
extern Device_FlashType Device_FlashDevice;
extern uint8 TI_Fee_MaxSectors;
    #endif
extern TI_Fee_GlobalVarsType TI_Fee_GlobalVariables[ TI_FEE_NUMBER_OF_EEPS ];
extern TI_Fee_StatusWordType_UN TI_Fee_oStatusWord[ TI_FEE_NUMBER_OF_EEPS ];
    #if( TI_FEE_FLASH_CHECKSUM_ENABLE == STD_ON )
extern uint32 TI_Fee_u32FletcherChecksum;
    #endif
extern uint32 TI_Fee_u32BlockEraseCount;
extern uint8 TI_Fee_u8DataSets;
extern uint8 TI_Fee_u8DeviceIndex;
extern uint32 TI_Fee_u32ActCpyVS;
extern uint8 TI_Fee_u8ErrEraseVS;
    #if( TI_FEE_NUMBER_OF_UNCONFIGUREDBLOCKSTOCOPY != 0U )
extern uint16 TI_Fee_u16NumberOfUnconfiguredBlocks[ TI_FEE_NUMBER_OF_EEPS ];
    #endif
    #if( TI_FEE_FLASH_ERROR_CORRECTION_HANDLING == TI_Fee_Fix )
extern boolean Fee_bDoubleBitError;
extern boolean Fee_bSingleBitError;
    #endif
    #if( TI_FEE_NUMBER_OF_EEPS == 2U )
extern TI_Fee_StatusWordType_UN TI_Fee_oStatusWord_Global;
    #endif
extern boolean TI_Fee_FapiInitCalled;
extern boolean TI_Fee_bEraseSuspended;
extern boolean TI_Fee_bIsMainFunctionCalled;

/**********************************************************************************************************************
 *  GLOBAL FUNCTION PROTOTYPES
 *********************************************************************************************************************/
/*  Interface Functions */
extern void TI_Fee_Cancel( uint8 u8EEPIndex );
extern Std_ReturnType TI_Fee_EraseImmediateBlock( uint16 BlockNumber );
extern TI_FeeModuleStatusType TI_Fee_GetStatus( uint8 u8EEPIndex );
extern void TI_Fee_GetVersionInfo( Std_VersionInfoType * VersionInfoPtr );
extern void TI_Fee_Init( void );
extern Std_ReturnType TI_Fee_InvalidateBlock( uint16 BlockNumber );
extern Std_ReturnType TI_Fee_Read( uint16 BlockNumber,
                                   uint16 BlockOffset,
                                   uint8 * DataBufferPtr,
                                   uint16 Length );
extern Std_ReturnType TI_Fee_WriteAsync( uint16 BlockNumber, uint8 * DataBufferPtr );
extern void TI_Fee_MainFunction( void );
extern TI_Fee_ErrorCodeType TI_FeeErrorCode( uint8 u8EEPIndex );
extern void TI_Fee_ErrorRecovery( TI_Fee_ErrorCodeType ErrorCode, uint8 u8VirtualSector );
extern TI_FeeJobResultType TI_Fee_GetJobResult( uint8 u8EEPIndex );
extern void TI_Fee_SuspendResumeErase( TI_Fee_EraseCommandType Command );

    #if( TI_FEE_FLASH_ERROR_CORRECTION_HANDLING == TI_Fee_Fix )
extern void TI_Fee_ErrorHookSingleBitError( void );
extern void TI_Fee_ErrorHookDoubleBitError( void );
    #endif

    #if( TI_FEE_DRIVER == 1U )
extern Std_ReturnType TI_Fee_WriteSync( uint16 BlockNumber, uint8 * DataBufferPtr );
extern Std_ReturnType TI_Fee_Shutdown( void );
extern boolean TI_Fee_Format( uint32 u32FormatKey );
extern Std_ReturnType TI_Fee_ReadSync( uint16 BlockNumber,
                                       uint16 BlockOffset,
                                       uint8 * DataBufferPtr,
                                       uint16 Length );
    #endif

/*  TI Fee Internal Functions */
TI_Fee_AddressType TI_FeeInternal_GetNextFlashAddress( uint8 u8EEPIndex );
TI_Fee_AddressType TI_FeeInternal_AlignAddressForECC( TI_Fee_AddressType oAddress );
TI_Fee_AddressType TI_FeeInternal_GetCurrentBlockAddress( uint16 BlockNumber,
                                                          uint16 DataSetNumber,
                                                          uint8 u8EEPIndex );
/*SAFETYMCUSW 61 X MR:1.4,5.1 <APPROVED> "Reason -
 * TI_FeeInternal_GetVirtualSectorParameter name is required here."*/
uint32 TI_FeeInternal_GetVirtualSectorParameter( Fapi_FlashSectorType oSector,
                                                 uint16 u16Bank,
                                                 boolean VirtualSectorInfo,
                                                 uint8 u8EEPIndex );
uint32 TI_FeeInternal_PollFlashStatus( void );
uint16 TI_FeeInternal_GetBlockSize( uint16 BlockIndex );
uint16 TI_FeeInternal_GetBlockIndex( uint16 BlockNumber );
uint16 TI_FeeInternal_GetDataSetIndex( uint16 BlockNumber );
uint16 TI_FeeInternal_GetBlockNumber( uint16 BlockNumber );
uint8 TI_FeeInternal_FindNextVirtualSector( uint8 u8EEPIndex );
uint8 TI_FeeInternal_WriteDataF021( boolean bCopy,
                                    uint16 u16WriteSize,
                                    uint8 u8EEPIndex );
boolean TI_FeeInternal_BlankCheck( uint32 u32StartAddress,
                                   uint32 u32EndAddress,
                                   uint16 u16Bank,
                                   uint8 u8EEPIndex );
Std_ReturnType TI_FeeInternal_CheckReadParameters( uint32 u32BlockSize,
                                                   uint16 BlockOffset,
                                                   const uint8 * DataBufferPtr,
                                                   uint16 Length,
                                                   uint8 u8EEPIndex );
Std_ReturnType TI_FeeInternal_CheckModuleState( uint8 u8EEPIndex );
Std_ReturnType TI_FeeInternal_InvalidateErase( uint16 BlockNumber );
TI_Fee_StatusType TI_FeeInternal_FeeManager( uint8 u8EEPIndex );
void TI_FeeInternal_WriteVirtualSectorHeader( uint8 FeeVirtualSectorNumber,
                                              VirtualSectorStatesType VsState,
                                              uint8 u8EEPIndex );
/*SAFETYMCUSW 61 X MR:1.4,5.1 <APPROVED> "Reason -  TI_FeeInternal_GetVirtualSectorIndex
 * name is required here."*/
void TI_FeeInternal_GetVirtualSectorIndex( Fapi_FlashSectorType oSectorStart,
                                           Fapi_FlashSectorType oSectorEnd,
                                           uint16 u16Bank,
                                           boolean bOperation,
                                           uint8 u8EEPIndex );
void TI_FeeInternal_WritePreviousBlockHeader( boolean bWrite, uint8 u8EEPIndex );
void TI_FeeInternal_WriteBlockHeader( boolean bWrite,
                                      uint8 u8EEPIndex,
                                      uint16 Fee_BlockSize_u16,
                                      uint16 u16BlockNumber );
void TI_FeeInternal_SetClearCopyBlockState( uint8 u8EEPIndex, boolean bSetClear );
void TI_FeeInternal_SanityCheck( uint16 BlockSize, uint8 u8EEPIndex );
void TI_FeeInternal_StartProgramBlock( uint8 u8EEPIndex );
void TI_FeeInternal_UpdateBlockOffsetArray( uint8 u8EEPIndex,
                                            boolean bActCpyVS,
                                            uint8 u8VirtualSector );
void TI_FeeInternal_WriteInitialize( TI_Fee_AddressType oFlashNextAddress,
                                     uint8 * DataBufferPtr,
                                     uint8 u8EEPIndex );
void TI_FeeInternal_CheckForError( uint8 u8EEPIndex );
void TI_FeeInternal_EnableRequiredFlashSector( uint32 u32VirtualSectorStartAddress );
uint16 TI_FeeInternal_GetArrayIndex( uint16 BlockNumber,
                                     uint16 DataSetNumber,
                                     uint8 u8EEPIndex,
                                     boolean bCallContext );
    #if( TI_FEE_FLASH_CHECKSUM_ENABLE == STD_ON )
uint32 TI_FeeInternal_Fletcher16( uint8 const * pu8data, uint16 u16Length );
    #endif
    #if( TI_FEE_GENERATE_DEVICEANDVIRTUALSECTORSTRUC == STD_ON )
void TI_FeeInternal_PopulateStructures( TI_Fee_DeviceType DeviceType );
    #endif
#endif /* TI_FEE_H */

/**********************************************************************************************************************
 *  END OF FILE: ti_fee.h
 *********************************************************************************************************************/
