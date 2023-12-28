/**********************************************************************************************************************
 *  FILE DESCRIPTION
 *
 -------------------------------------------------------------------------------------------------------------------
 *         File:  fee_interface.h
 *      Project:  Tms570_TIFEEDriver
 *       Module:  FEE Driver
 *    Generator:  None
 *
 *  Description:  This file is interfce between Autosar FEE and TI FEE.
 *---------------------------------------------------------------------------------------------------------------------
 * Author:  Vishwanath Reddy
 *---------------------------------------------------------------------------------------------------------------------
 * Revision History
 *---------------------------------------------------------------------------------------------------------------------
 * Version        Date         Author               Change ID        Description
 *---------------------------------------------------------------------------------------------------------------------
 * 00.01.00       07Sept2012    Vishwanath Reddy     0000000000000    Initial Version
 * 00.01.01       14Sept2012    Vishwanath Reddy     0000000000000    Review changes
 * 00.01.02       30Nov2012     Vishwanath Reddy     SDOCM00097786    Misra Fixes, Memory
 segmentation changes.
 * 00.01.03       14Jan2013     Vishwanath Reddy     SDOCM00098510    Changes as requested
 by Vector.
 * 00.01.06		  11Mar2013	     Vishwanath Reddy     SDOCM00099152    Added feature :
 copying of unconfigured blocks.
 * 00.01.07		  15Mar2013	     Vishwanath Reddy     SDOCM00099152    Added feature :
 Number of 8 bytes writes, fixed issue with copy blocks.
 * 00.01.08		  05Apr2013	    Vishwanath Reddy     SDOCM00099152    Added feature :CRC
 check for unconfigured blocks, Main function modified to complete writes as fast as
 possible, Added Non polling mode support.
 * 01.12.00		  13Dec2013     Vishwanath Reddy     SDOCM00105412    Traceability tags
 added.
 *                                                                    MISRA C fixes.
 * 01.21.00		  15Oct2014     Vishwanath Reddy     SDOCM00113379    RAM Optimization
 changes. Added mew ,acro
 * TI_FEE_TOTAL_BLOCKS_DATASETS
 * 01.22.00		  26Dec2014     Vishwanath Reddy     SDOCM00114423    Following new macros
 added.
 * TI_FEE_VIRTUALSECTOR_SIZE,
 * TI_FEE_PHYSICALSECTOR_SIZE,
 * TI_FEE_GENERATE_DEVICEANDVIRTUALSECTORSTRUC.
 * 01.23.00		  12Oct2015     Vishwanath Reddy     SDOCM00119455    Update version
 history.
 * 01.23.01		  17Nov2015     Vishwanath Reddy     SDOCM00120161    Updated version
 history.
 * 01.23.02		  10Mar2016     Vishwanath Reddy     SDOCM00121622    Updated version
 history.
 * 01.23.03       04Aug2016     Vishwanath Reddy     SDOCM00122571    Update patch version
 FEE_SW_PATCH_VERSION.
 * 01.23.04		  12Aug2016     Vishwanath Reddy     SDOCM00122592
 TI_FEE_CHECK_BANK7_ACCESS is always turned on.
 *                                                                    FEE_FLASH_CRC_ENABLE
 is renamed to
 * FEE_FLASH_CHECKSUM_ENABLE.
 *                                                                    New macro
 FEE_USEPARTIALERASEDSECTOR added.
 * 01.23.05		  05Dec2017     Prathap Srinivasan   HERCULES_SW-5082 Update version
 history for AUTOSAR FEE
 *                                                                    (This corresponds to
 TI FEE 1.19.04.)
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

#ifndef FEE_INTERFACE_H
    #define FEE_INTERFACE_H

    #include "ti_fee_cfg.h"

    #if( TI_FEE_DRIVER == 0U ) /* Include following macros only in Autosar Context */
        #include "fee_cfg.h"
        #include "nvm.h"

        #define Fee_None                                                                 \
            0x00U /* Take no action on single bit errors, (respond with corrected data), \
                   */
    /* return error for uncorrectable error reads (multi bit errors for ECC or parity
     * failures). */
    /* For devices with no ECC (they may have parity or not) the only valid option is
     * none. */
        #define Fee_Fix                                                                 \
            0x01U /* single bit "zero" error will be fixed by reprogramming, single bit \
                     "one" error */
    /* will be fixed by marking the current entry as invalid and copying the data to a new
     * entry,*/
    /* return error for uncorrectable error reads (multi bit errors for ECC or parity
     * failures). */

        #define TI_Fee_None                                                              \
            0x00U /* Take no action on single bit errors, (respond with corrected data), \
                   */
    /* return error for uncorrectable error reads(multibit errors for ECC or parity
     * failures)*/
    /* For devices with no ECC (they may have parity or not) the only valid option is
     * none. */
        #define TI_Fee_Fix                                                              \
            0x01U /* single bit "zero" error will be fixed by reprogramming, single bit \
                     "one" error */
    /* will be fixed by marking the current entry as invalid and copying the data to a new
       entry, */
    /* return error for uncorrectable error reads (multi bit errors for ECC or parity
       failures)*/

        #if( FEE_FLASH_ERROR_CORRECTION_HANDLING == Fee_Fix )
            /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - TI_Fee_Fix is a symbolic
             * constant."*/
            #define TI_FEE_FLASH_ERROR_CORRECTION_HANDLING TI_Fee_Fix
        #else
            /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - TI_Fee_None is a symbolic
             * constant."*/
            #define TI_FEE_FLASH_ERROR_CORRECTION_HANDLING TI_Fee_None
        #endif

        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_MAXIMUM_BLOCKING_TIME is a
         * symbolic constant"*/
        #define TI_FEE_MAXIMUM_BLOCKING_TIME         FEE_MAXIMUM_BLOCKING_TIME
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_OPERATING_FREQUENCY is a
         * symbolic constant."*/
        #define TI_FEE_OPERATING_FREQUENCY           FEE_OPERATING_FREQUENCY
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_FLASH_ERROR_CORRECTION_ENABLE
         * is a symbolic constant."*/
        #define TI_FEE_FLASH_ERROR_CORRECTION_ENABLE FEE_FLASH_ERROR_CORRECTION_ENABLE
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_FLASH_CHECKSUM_ENABLE is a
         * symbolic constant."*/
        #define TI_FEE_FLASH_CHECKSUM_ENABLE         FEE_FLASH_CHECKSUM_ENABLE
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_FLASH_WRITECOUNTER_SAVE is a
         * symbolic constant."*/
        #define TI_FEE_FLASH_WRITECOUNTER_SAVE       FEE_FLASH_WRITECOUNTER_SAVE
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - NVM_DATASET_SELECTION_BITS is a
         * symbolic constant."*/
        #define TI_FEE_DATASELECT_BITS               NVM_DATASET_SELECTION_BITS
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_NUMBER_OF_EEPS is a symbolic
         * constant."*/
        #define TI_FEE_NUMBER_OF_EEPS                FEE_NUMBER_OF_EEPS
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_INDEX is a symbolic
         * constant."*/
        #define TI_FEE_INDEX                         FEE_INDEX
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_PAGE_OVERHEAD is a symbolic
         * constant."*/
        #define TI_FEE_PAGE_OVERHEAD                 FEE_PAGE_OVERHEAD
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_BLOCK_OVERHEAD is a symbolic
         * constant."*/
        #define TI_FEE_BLOCK_OVERHEAD                FEE_BLOCK_OVERHEAD
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_VIRTUAL_PAGE_SIZE is a
         * symbolic constant."*/
        #define TI_FEE_VIRTUAL_PAGE_SIZE             FEE_VIRTUAL_PAGE_SIZE
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_VIRTUAL_SECTOR_OVERHEAD is a
         * symbolic constant."*/
        #define TI_FEE_VIRTUAL_SECTOR_OVERHEAD       FEE_VIRTUAL_SECTOR_OVERHEAD
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason -
         * FEE_NUMBER_OF_UNCONFIGUREDBLOCKSTOCOPY is a symbolic constant."*/
        #define TI_FEE_NUMBER_OF_UNCONFIGUREDBLOCKSTOCOPY \
            FEE_NUMBER_OF_UNCONFIGUREDBLOCKSTOCOPY
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_NUMBER_OF_EIGHTBYTEWRITES is a
         * symbolic constant."*/
        #define TI_FEE_NUMBER_OF_EIGHTBYTEWRITES  FEE_NUMBER_OF_EIGHTBYTEWRITES
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_NVM_JOB_END_NOTIFICATION is a
         * symbolic constant."*/
        #define TI_FEE_NVM_JOB_END_NOTIFICATION   FEE_NVM_JOB_END_NOTIFICATION
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_NVM_JOB_ERROR_NOTIFICATION is
         * a symbolic constant."*/
        #define TI_FEE_NVM_JOB_ERROR_NOTIFICATION FEE_NVM_JOB_ERROR_NOTIFICATION
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_POLLING_MODE is a symbolic
         * constant."*/
        #define TI_FEE_POLLING_MODE               FEE_POLLING_MODE
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_CHECK_BANK7_ACCESS is a
         * symbolic constant."*/
        #ifndef FEE_CHECK_BANK7_ACCESS
            #define TI_FEE_CHECK_BANK7_ACCESS STD_ON
        #else
            /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_CHECK_BANK7_ACCESS is a
             * symbolic constant."*/
            #define TI_FEE_CHECK_BANK7_ACCESS STD_ON
        #endif
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_TOTAL_BLOCKS_DATASETS is a
         * symbolic constant."*/
        #define TI_FEE_TOTAL_BLOCKS_DATASETS FEE_TOTAL_BLOCKS_DATASETS
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_VIRTUALSECTOR_SIZE is a
         * symbolic constant."*/
        #define TI_FEE_VIRTUALSECTOR_SIZE    FEE_VIRTUALSECTOR_SIZE
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_PHYSICALSECTOR_SIZE is a
         * symbolic constant."*/
        #define TI_FEE_PHYSICALSECTOR_SIZE   FEE_PHYSICALSECTOR_SIZE
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason -
         * FEE_GENERATE_DEVICEANDVIRTUALSECTORSTRUC is a symbolic constant."*/
        #define TI_FEE_GENERATE_DEVICEANDVIRTUALSECTORSTRUC \
            FEE_GENERATE_DEVICEANDVIRTUALSECTORSTRUC
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_USEPARTIALERASEDSECTOR is a
         * symbolic constant."*/
        #define TI_FEE_USEPARTIALERASEDSECTOR         FEE_USEPARTIALERASEDSECTOR

        /*----------------------------------------------------------------------------*/
        /* Virtual Sector Configuration                                               */

        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_NUMBER_OF_VIRTUAL_SECTORS is a
         * symbolic constant."*/
        /*SAFETYMCUSW 61 X MR:1.4,5.1 <APPROVED> "Reason - Similar Identifier name is
         * required here."*/
        #define TI_FEE_NUMBER_OF_VIRTUAL_SECTORS      FEE_NUMBER_OF_VIRTUAL_SECTORS
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_NUMBER_OF_VIRTUAL_SECTORS_EEP1
         * is a symbolic constant."*/
        /*SAFETYMCUSW 384 S MR:1.4,5.1 <APPROVED> "Reason - Similar Identifier name is
         * required here."*/
        /*SAFETYMCUSW 61 X MR:1.4,5.1 <APPROVED> "Reason - Similar Identifier name is
         * required here."*/
        #define TI_FEE_NUMBER_OF_VIRTUAL_SECTORS_EEP1 FEE_NUMBER_OF_VIRTUAL_SECTORS_EEP1

        /*----------------------------------------------------------------------------*/
        /* Block Configuration                                                        */
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - FEE_NUMBER_OF_BLOCKS is a symbolic
         * constant."*/
        #define TI_FEE_NUMBER_OF_BLOCKS               FEE_NUMBER_OF_BLOCKS
        /*SAFETYMCUSW 79 S MR:19.4 <APPROVED> "Reason - TI_FEE_VARIABLE_DATASETS is a
         * symbolic constant."*/
        #define TI_FEE_VARIABLE_DATASETS              STD_ON

    #endif /* TI_FEE_DRIVER */

#endif /* FEE_INTERFACE_H */
/**********************************************************************************************************************
 *  END OF FILE: fee_interface.h
 *********************************************************************************************************************/
