/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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
 
/**
*  \file
*
*  Definitions and function prototype for smc module
*/

#ifndef _SMC_
#define _SMC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/
typedef union _SmcStatus {
    uint8_t BStatus;
    struct _SmcStatusBits {
        uint8_t smcSts:1,    /**< NAND Flash Controller Status */
                xfrDone:1,   /**< NFC Data Transfer Terminated */
                cmdDone:1,   /**< Command Done */
                rbEdge: 1,   /**< Ready/Busy Line 3 Edge Detected*/
           hammingReady:1;   /**< Hamming ecc ready */
    } bStatus;
} SmcStatus;

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/
/*
 * NFC definitions
 */

/** Base address of NFC SRAM */
#define NFC_SRAM_BASE_ADDRESS 0x100000
/** Base address for NFC Address Command */
#define NFC_CMD_BASE_ADDR     0x90000000


/* -------- NFCADDR_CMD : NFC Address Command -------- */
#define NFCADDR_CMD_CMD1      (0xFFu <<  2) /* Command Register Value for Cycle 1 */
#define NFCADDR_CMD_CMD2      (0xFFu << 10) /* Command Register Value for Cycle 2 */
#define NFCADDR_CMD_VCMD2     (0x1u << 18)  /* Valid Cycle 2 Command */
#define NFCADDR_CMD_ACYCLE    (0x7u << 19)  /* Number of Address required for the current command */
#define   NFCADDR_CMD_ACYCLE_NONE    (0x0u << 19) /* No address cycle */
#define   NFCADDR_CMD_ACYCLE_ONE     (0x1u << 19) /* One address cycle */
#define   NFCADDR_CMD_ACYCLE_TWO     (0x2u << 19) /* Two address cycles */
#define   NFCADDR_CMD_ACYCLE_THREE   (0x3u << 19) /* Three address cycles */
#define   NFCADDR_CMD_ACYCLE_FOUR    (0x4u << 19) /* Four address cycles */
#define   NFCADDR_CMD_ACYCLE_FIVE    (0x5u << 19) /* Five address cycles */
#define NFCADDR_CMD_CSID      (0x7u << 22)  /* Chip Select Identifier */
#define   NFCADDR_CMD_CSID_0                    (0x0u << 22) /* CS0 */
#define   NFCADDR_CMD_CSID_1                    (0x1u << 22) /* CS1 */
#define   NFCADDR_CMD_CSID_2                    (0x2u << 22) /* CS2 */
#define   NFCADDR_CMD_CSID_3                    (0x3u << 22) /* CS3 */
#define   NFCADDR_CMD_CSID_4                    (0x4u << 22) /* CS4 */
#define   NFCADDR_CMD_CSID_5                    (0x5u << 22) /* CS5 */
#define   NFCADDR_CMD_CSID_6                    (0x6u << 22) /* CS6 */
#define   NFCADDR_CMD_CSID_7                    (0x7u << 22) /* CS7 */
#define NFCADDR_CMD_DATAEN   (0x1u << 25)  /* NFC Data Enable */
#define NFCADDR_CMD_DATADIS  (0x0u << 25)  /* NFC Data disable */
#define NFCADDR_CMD_NFCRD    (0x0u << 26)  /* NFC Read Enable */
#define NFCADDR_CMD_NFCWR    (0x1u << 26)  /* NFC Write Enable */
#define NFCADDR_CMD_NFCCMD   (0x1u << 27)  /* NFC Command Enable */

/*
 * ECC definitions (Hsiao Code Errors)
 */

/** A single bit was incorrect but has been recovered. */
#define Hsiao_ERROR_SINGLEBIT         1

/** The original code has been corrupted. */
#define Hsiao_ERROR_ECC               2

/** Multiple bits are incorrect in the data and they cannot be corrected. */
#define Hsiao_ERROR_MULTIPLEBITS      3

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/*
 * NFC functions
 */

extern void SMC_NFC_Configure(uint32_t mode);
extern void SMC_NFC_Reset(void);
extern void SMC_NFC_EnableNfc(void);
extern void SMC_NFC_EnableSpareRead(void);
extern void SMC_NFC_DisableSpareRead(void);
extern void SMC_NFC_EnableSpareWrite(void);
extern void SMC_NFC_DisableSpareWrite(void);
extern uint8_t SMC_NFC_isSpareRead(void);
extern uint8_t SMC_NFC_isSpareWrite(void);
extern uint8_t SMC_NFC_isTransferComplete(void);
extern uint8_t SMC_NFC_isReadyBusy(void);
extern uint8_t SMC_NFC_isNfcBusy(void);
extern uint32_t SMC_NFC_GetStatus(void);

extern void SMC_NFC_SendCommand(uint32_t cmd, uint32_t addressCycle, uint32_t cycle0);
extern void SMC_NFC_Wait_CommandDone(void);
extern void SMC_NFC_Wait_XfrDone(void);
extern void SMC_NFC_Wait_RBbusy(void);
extern void SMC_NFC_Wait_HammingReady(void);

extern void SMC_ECC_Configure(uint32_t type, uint32_t pageSize);
extern uint32_t SMC_ECC_GetCorrectoinType(void);
extern uint8_t SMC_ECC_GetStatus(uint8_t eccNumber);

extern void SMC_ECC_GetValue(uint32_t *ecc);
extern void SMC_ECC_GetEccParity(uint32_t pageDataSize, uint8_t *code, uint8_t busWidth);
extern uint8_t SMC_ECC_VerifyHsiao(uint8_t *data, uint32_t size, const uint8_t *originalCode, const uint8_t *verifyCode, uint8_t busWidth);
#endif /* #ifndef _SMC_ */

