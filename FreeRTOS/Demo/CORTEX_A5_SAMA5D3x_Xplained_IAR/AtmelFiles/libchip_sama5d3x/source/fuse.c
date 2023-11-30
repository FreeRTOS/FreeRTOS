/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

 
/** \addtogroup fuse_module Working with FUSE
 * The Fuse driver provides the Interface for configuration the FUSE 
 * peripheral.
 *
 * For more accurate information, please look at the FUSE section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref fuse.c\n
 * \ref fuse.h.\n
*/
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of FUSE controller.
 *
 */
/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/
#include "chip.h"

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

 /**
 * \brief Read fuse vlaue by given word position. 
 *
 * \param wordPosition  select the 32-bit word 0 to 9.
 */

uint32_t FUSE_Read (uint8_t wordPosition )
{
    uint32_t fuse;
    /* Enable peripheral clock. */
    PMC->PMC_PCER1 = (1 << (ID_FUSE - 32 ));
    /* Request read fuse */
    FUSE->FUSE_CR = FUSE_CR_RRQ | FUSE_CR_KEY_VALID;
    /* RS and WS bits of the Fuse Index register (FUSE_IR) must be at level one
    before issuing the read request */
    while (!((FUSE->FUSE_IR & (FUSE_IR_WS | FUSE_IR_RS)) == (FUSE_IR_WS | FUSE_IR_RS)));
    /* Read fuse values, The fuse states are automatically read on CORE startup and are available for reading in the
    SR_REG_NB Fuse Status (FUSE_SRx) registers. */
    fuse = FUSE->FUSE_SR[wordPosition];
    /* Disable peripheral clock.*/
    PMC->PMC_PCDR1 = (1 << (ID_FUSE -32 ));
    return fuse;
}

/**
 * \brief Program fuse vlaue by given word position. 
 *
 * \param data  word to be program.
 * \param wordPosition  select the 32-bit word 0 to 9.
 */

void FUSE_Write (uint32_t data, uint8_t wordPosition )
{
    /* Enable peripheral clock. */
    PMC->PMC_PCER1 = (1 << (ID_FUSE - 32 ));
    /* Select the word to write, using the SELW field of the Fuse_Index register (FUSE_IR). */
    FUSE->FUSE_IR = (FUSE_IR_WSEL(wordPosition));
    /* Write the word to program in the Fuse_Data register (FUSE_DR).*/
    FUSE->FUSE_DR = data;
    /* Check that RS and WS bits of the Fuse_Index register are at level one (no read and
    no write pending). */
    while (!((FUSE->FUSE_IR & (FUSE_IR_WS | FUSE_IR_RS)) == (FUSE_IR_WS | FUSE_IR_RS)));
    /* Write the WRQ bit of the Fuse_Control register (FUSE_CR) to begin the fuse programming. */
    FUSE->FUSE_CR = FUSE_CR_WRQ | FUSE_CR_KEY_VALID;
    /* Check the WS bit of FUSE_SRx, when WS has a value of ¡°1¡± the fuse write process
    is over. */
    while (!((FUSE->FUSE_IR & FUSE_IR_WS) == FUSE_IR_WS));
    /* Disable peripheral clock. */
    PMC->PMC_PCDR1 = (1 << (ID_FUSE - 32 ));
}
