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

#ifndef OMNIVISION_H
#define OMNIVISION_H


/*---------------------------------------------------------------------------
 *         TYPE
 *---------------------------------------------------------------------------*/
/** define a structure for ovxxxx register initialization values */
struct ov_reg
{
    /* Register to be written */
    uint16_t reg;
    /* Value to be written in the register */
    uint8_t val;
};


/*---------------------------------------------------------------------------
 *         DEFINITAION
 *---------------------------------------------------------------------------*/
#define OV_2640          0x00
#define OV_2643          0x01
#define OV_5640          0x02
#define OV_7740          0x03
#define OV_9740          0x04
#define OV_UNKNOWN       0xFF
 
/*----------------------------------------------------------------------------
 *       Exported functions
 *----------------------------------------------------------------------------*/
extern uint8_t ov_init(Twid *pTwid);
extern void ov_DumpRegisters8(Twid *pTwid);
extern void ov_DumpRegisters16(Twid *pTwid);
extern uint32_t ov_write_regs8(Twid *pTwid, const struct ov_reg* pReglist);
extern uint32_t ov_write_regs16(Twid *pTwid, const struct ov_reg* pReglist);
extern uint8_t ov_read_reg8(Twid *pTwid, uint8_t reg, uint8_t *pData);
extern uint8_t ov_read_reg16(Twid *pTwid, uint16_t reg, uint8_t *pData);
extern uint8_t ov_write_reg8(Twid *pTwid, uint8_t reg, uint8_t val);
extern uint8_t ov_write_reg16(Twid *pTwid, uint16_t reg, uint8_t val);
extern void isOV5640_AF_InitDone(Twid *pTwid);
extern uint32_t ov_5640_AF_single(Twid *pTwid);
extern uint32_t ov_5640_AF_continue(Twid *pTwid);
extern uint32_t ov_5640_AFPause(Twid *pTwid);
extern uint32_t ov_5640_AFrelease(Twid *pTwid);
#endif
