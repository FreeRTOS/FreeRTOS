/**********************************************************************************************************************
 *  FILE DESCRIPTION
 *  -------------------------------------------------------------------------------------------------------------------
 *         File:  ti_fee_types.h
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
 * 03.00.00       31Aug2012    Vishwanath Reddy     0000000000000    Initial Version
 * 00.01.00       31Aug2012    Vishwanath Reddy     0000000000000    Initial Version
 * 00.01.02       30Nov2012    Vishwanath Reddy     SDOCM00097786    Misra Fixes, Memory
 *segmentation changes. 01.12.00		  13Dec2013    Vishwanath Reddy     SDOCM00105412
 *MISRA C fixes. 01.15.00		  06Jun2014    Vishwanath Reddy Support for LC Varients.
 * 01.16.00		  15Jul2014    Vishwanath Reddy     SDOCM00112141    Remove  MISRA
 *warnings. 01.18.00		  12Oct2015    Vishwanath Reddy     SDOCM00119455    Update
 *version history.
 * 01.18.01		  17Nov2015    Vishwanath Reddy     SDOCM00120161    Update version
 *history.
 * 01.18.02		  05Feb2016    Vishwanath Reddy     SDOCM00121158    Update version
 *history. 01.18.03       30June2016   Vishwanath Reddy     SDOCM00122388    Update
 *version history. SDOCM00122429    Added error when endianess is not defined. 01.19.00
 *08Augu2016   Vishwanath Reddy     SDOCM00122592    Update version history. 01.19.01
 *12Augu2016   Vishwanath Reddy     SDOCM00122543    Update version history. 01.19.03
 *15May2017    Prathap Srinivasan   SDOCM00122917    Update version history. 01.19.04
 *05Dec2017    Prathap Srinivasan   HERCULES_SW-5082 Update version history.
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

#ifndef TI_FEE_TYPES_H
    #define TI_FEE_TYPES_H

    /**********************************************************************************************************************
     * INCLUDES
     *********************************************************************************************************************/
    #include "Device_header.h"

    #ifndef TI_Fee_None
        #define TI_Fee_None                                                             \
            0x00U /*Take no action on single bit errors, (respond with corrected data), \
                   */
    /*return error for uncorrectable error reads (multibit errors for ECC or parity
     * failures)*/
    /*For devices with no ECC (they may have parity or not) the only valid option is none.
     */
    #endif

    #ifndef TI_Fee_Fix
        #define TI_Fee_Fix 0x01U /* single bit error will be fixed by reprogramming */

    /* return previous valid data for uncorrectable error reads (multi bit errors for ECC
     * or parity failures). */
    #endif

    #if !defined( _LITTLE_ENDIAN ) && !defined( _BIG_ENDIAN )
        #error "Target Endianess is not defined. Include F021 header files and library."
    #endif

/*SAFETYMCUSW 74 S MR:18.4 <APPROVED> "Reason - union declaration is necessary here."*/
typedef union
{
    uint16 Fee_u16StatusWord;
    #ifdef _BIG_ENDIAN
    struct
    {
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Reserved        : 5U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Erase           : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 ReadSync        : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 ProgramFailed   : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Read            : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 WriteSync       : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 WriteAsync      : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 EraseImmediate  : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 InvalidateBlock : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Copy            : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Initialized     : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 SingleBitError  : 1U;
    } Fee_StatusWordType_ST;
    #endif /* ifdef _BIG_ENDIAN */
    #ifdef _LITTLE_ENDIAN
    struct
    {
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 SingleBitError  : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Initialized     : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Copy            : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 InvalidateBlock : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 EraseImmediate  : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 WriteAsync      : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 WriteSync       : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Read            : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 ProgramFailed   : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 ReadSync        : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Erase           : 1U;
        /*SAFETYMCUSW 42 S MR:3.5 <APPROVED> "Reason - Bit field declaration is necessary
         * here."*/
        /*SAFETYMCUSW 73 S MR:6.4 <APPROVED> "Reason - Bit field is declared as
         * unsigned."*/
        uint16 Reserved        : 5U;
    } Fee_StatusWordType_ST;
    #endif /* ifdef _LITTLE_ENDIAN */
} TI_Fee_StatusWordType_UN;

typedef enum
{
    UNINIT,
    IDLE,
    /*SAFETYMCUSW 91 S MR:5.2,5.6,5.7 <APPROVED> "Reason - BUSY in F021 is a member of
     * structure."*/
    BUSY,
    BUSY_INTERNAL
} TI_FeeModuleStatusType;

typedef enum
{
    JOB_OK,
    JOB_FAILED,
    JOB_PENDING,
    JOB_CANCELLED,
    BLOCK_INCONSISTENT,
    BLOCK_INVALID
} TI_FeeJobResultType;

#endif /* TI_FEE_TYPES_H */

/**********************************************************************************************************************
 *  END OF FILE: ti_fee_types.h
 *********************************************************************************************************************/
