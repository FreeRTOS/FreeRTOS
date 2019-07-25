/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

#ifndef _HSMC_
#define _HSMC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdbool.h>
#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Macros
 *----------------------------------------------------------------------------*/

#define hsmc_nfc_configure(mode)       {HSMC->HSMC_CFG = mode ;}
#define hsmc_nfc_enable()              {HSMC->HSMC_CTRL |= HSMC_CTRL_NFCEN;}
#define hsmc_nfc_disable()             {HSMC->HSMC_CTRL |= HSMC_CTRL_NFCDIS;}
#define hsmc_nfc_get_status()          {HSMC->HSMC_SR;}

#define hsmc_nfc_enable_spare_read()   {HSMC->HSMC_CFG |= HSMC_CFG_RSPARE;}
#define hsmc_nfc_disable_spare_read()  {HSMC->HSMC_CFG &= (~HSMC_CFG_RSPARE);}
#define hsmc_nfc_enable_spare_write()  {HSMC->HSMC_CFG |= HSMC_CFG_WSPARE;}
#define hsmc_nfc_disable_spare_write() {HSMC->HSMC_CFG &= (~HSMC_CFG_WSPARE);}

#define hsmc_pmecc_reset()             {HSMC->HSMC_PMECCTRL = HSMC_PMECCTRL_RST; }
#define hsmc_pmecc_or_reset()          {HSMC->HSMC_PMECCTRL |= HSMC_PMECCTRL_RST; }
#define hsmc_pmecc_data_phase()        {HSMC->HSMC_PMECCTRL |= HSMC_PMECCTRL_DATA; }
#define hsmc_pmecc_enable_write()      {HSMC->HSMC_PMECCFG |= HSMC_PMECCFG_NANDWR;}
#define hsmc_pmecc_enable_read()       {HSMC->HSMC_PMECCFG &= (~HSMC_PMECCFG_NANDWR);}
 
#define hsmc_pmecc_error_status()      (HSMC->HSMC_PMECCISR )
#define hsmc_pmecc_enable()            {HSMC->HSMC_PMECCTRL = HSMC_PMECCTRL_ENABLE;}
#define hsmc_pmecc_disable()           {HSMC->HSMC_PMECCTRL = HSMC_PMECCTRL_DISABLE;}
#define hsmc_pmecc_auto_enable()       {HSMC->HSMC_PMECCFG |= HSMC_PMECCFG_AUTO;}
#define hsmc_pmecc_auto_disable()      {HSMC->HSMC_PMECCFG &= (~HSMC_PMECCFG_AUTO);}
#define hsmc_pmecc_auto_apare_en()     ((HSMC->HSMC_PMECCFG & HSMC_PMECCFG_SPAREEN) == HSMC_PMECCFG_SPAREEN) 
#define hsmc_pmecc(i)                  (HSMC->SMC_PMECC[i])

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

#define HSMC_SR_RB_EDGE0     (0x1u << 24)

/* -------- NFCADDR_CMD : NFC Address Command -------- */

#define NFCADDR_CMD_CMD1      (0xFFu <<  2)	/* Command Register Value for Cycle 1 */
#define NFCADDR_CMD_CMD2      (0xFFu << 10)	/* Command Register Value for Cycle 2 */
#define NFCADDR_CMD_VCMD2     (0x1u << 18)	/* Valid Cycle 2 Command */
#define NFCADDR_CMD_ACYCLE    (0x7u << 19)	/* Number of Address required for the current command */
#define   NFCADDR_CMD_ACYCLE_NONE    (0x0u << 19)	/* No address cycle */
#define   NFCADDR_CMD_ACYCLE_ONE     (0x1u << 19)	/* One address cycle */
#define   NFCADDR_CMD_ACYCLE_TWO     (0x2u << 19)	/* Two address cycles */
#define   NFCADDR_CMD_ACYCLE_THREE   (0x3u << 19)	/* Three address cycles */
#define   NFCADDR_CMD_ACYCLE_FOUR    (0x4u << 19)	/* Four address cycles */
#define   NFCADDR_CMD_ACYCLE_FIVE    (0x5u << 19)	/* Five address cycles */
#define NFCADDR_CMD_CSID      (0x7u << 22)	/* Chip Select Identifier */
#define   NFCADDR_CMD_CSID_0                    (0x0u << 22)	/* CS0 */
#define   NFCADDR_CMD_CSID_1                    (0x1u << 22)	/* CS1 */
#define   NFCADDR_CMD_CSID_2                    (0x2u << 22)	/* CS2 */
#define   NFCADDR_CMD_CSID_3                    (0x3u << 22)	/* CS3 */
#define   NFCADDR_CMD_CSID_4                    (0x4u << 22)	/* CS4 */
#define   NFCADDR_CMD_CSID_5                    (0x5u << 22)	/* CS5 */
#define   NFCADDR_CMD_CSID_6                    (0x6u << 22)	/* CS6 */
#define   NFCADDR_CMD_CSID_7                    (0x7u << 22)	/* CS7 */
#define NFCADDR_CMD_DATAEN   (0x1u << 25)	/* NFC Data Enable */
#define NFCADDR_CMD_DATADIS  (0x0u << 25)	/* NFC Data disable */
#define NFCADDR_CMD_NFCRD    (0x0u << 26)	/* NFC Read Enable */
#define NFCADDR_CMD_NFCWR    (0x1u << 26)	/* NFC Write Enable */
#define NFCADDR_CMD_NFCCMD   (0x1u << 27)	/* NFC Command Enable */

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern void hsmc_nand_configure(uint8_t cs, uint8_t bus_width);

extern void hsmc_nor_configure(uint8_t cs, uint8_t bus_width);

extern void hsmc_nfc_reset(void);

extern bool hsmc_nfc_is_spare_read_enabled(void);

extern bool hsmc_nfc_is_spare_write_enabled(void);

extern bool hsmc_nfc_is_nfc_busy(void);

extern void hsmc_wait_rb(void);

extern void hsmc_nfc_send_cmd(uint32_t cmd, uint32_t address_cycle, uint32_t cycle0);

extern void hsmc_nfc_wait_cmd_done(void);

extern void hsmc_nfc_wait_xfr_done(void);

extern void hsmc_nfc_wait_rb_busy(void);

extern void hsmc_nfc_wait_hamming_ready(void);

extern void hsmc_pmecc_wait_ready(void);

#endif /* _HSMC_ */
