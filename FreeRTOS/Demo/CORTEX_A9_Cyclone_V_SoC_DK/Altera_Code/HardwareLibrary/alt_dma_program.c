/******************************************************************************
 *
 * Copyright 2013 Altera Corporation. All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of the author may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 ******************************************************************************/

#include "alt_dma_program.h"
#include "alt_cache.h"
#include <stdio.h>

/////

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf(fmt, ...) printf(fmt, ##__VA_ARGS__)

/////

//
// The following section describes how the bits are used in the "flag" field:
//

// [17:16] Which loop registers (LOOP0, LOOP1) are currently being used by a
//   partially assembled program. LOOP0 is always used before LOOP1. LOOP1 is
//   always ended before LOOP0.
#define ALT_DMA_PROGRAM_FLAG_LOOP0 (1UL << 16)
#define ALT_DMA_PROGRAM_FLAG_LOOP1 (1UL << 17)
#define ALT_DMA_PROGRAM_FLAG_LOOP_ALL (ALT_DMA_PROGRAM_FLAG_LOOP0 | ALT_DMA_PROGRAM_FLAG_LOOP1)

// [18] Flag that marks LOOP0 as a forever loop. Said another way, LOOP0 is
//   being used to execute the DMALPFE directive.
#define ALT_DMA_PROGRAM_FLAG_LOOP0_IS_FE (1UL << 18)
// [19] Flag that marks LOOP1 as a forever loop. Said another way, LOOP1 is
//   being used to execute the DMALPFE directive.
#define ALT_DMA_PROGRAM_FLAG_LOOP1_IS_FE (1UL << 19)

// [24] Flag that the first SAR has been programmed. The SAR field is valid and
//    is the offset from the start of the buffer where SAR is located.
#define ALT_DMA_PROGRAM_FLAG_SAR (1UL << 24)
// [25] Flag that the first DAR has been programmed. The DAR field is valid and
//    is the offset from the start of the buffer where DAR is located.
#define ALT_DMA_PROGRAM_FLAG_DAR (1UL << 25)

// [31] Flag that marks the last assembled instruction as DMAEND.
#define ALT_DMA_PROGRAM_FLAG_ENDED (1UL << 31)

/////

ALT_STATUS_CODE alt_dma_program_init(ALT_DMA_PROGRAM_t * pgm)
{
    // Clear the variables that matter.
    pgm->flag      = 0;
    pgm->code_size = 0;

    // Calculate the cache aligned start location of the buffer.
    size_t buffer = (size_t)pgm->program;
    size_t offset = ((buffer + ALT_DMA_PROGRAM_CACHE_LINE_SIZE - 1) & ~(ALT_DMA_PROGRAM_CACHE_LINE_SIZE - 1)) - buffer;

    // It is safe to cast to uint16_t because the extra offset can only be up to
    // (ALT_DMA_PROGRAM_CACHE_LINE_SIZE - 1) or 31, which is within range of the
    // uint16_t.
    pgm->buffer_start = (uint16_t)offset;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_uninit(ALT_DMA_PROGRAM_t * pgm)
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_clear(ALT_DMA_PROGRAM_t * pgm)
{
    // Clear the variables that matter
    pgm->flag      = 0;
    pgm->code_size = 0;

    return ALT_E_SUCCESS;
}

__attribute__((weak)) ALT_STATUS_CODE alt_cache_system_clean(void * address, size_t length)
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_validate(const ALT_DMA_PROGRAM_t * pgm)
{
    // Verify that at least one instruction is in the buffer
    if (pgm->code_size == 0)
    {
        return ALT_E_ERROR;
    }

    // Verify all loops are completed.
    if (pgm->flag & ALT_DMA_PROGRAM_FLAG_LOOP_ALL)
    {
        return ALT_E_ERROR;
    }

    // Verify last item is DMAEND
    if (!(pgm->flag & ALT_DMA_PROGRAM_FLAG_ENDED))
    {
        return ALT_E_ERROR;
    }

    // Sync the DMA program to RAM.
    void * vaddr  = (void *)((uintptr_t)(pgm->program + pgm->buffer_start) & ~(ALT_CACHE_LINE_SIZE - 1));
    size_t length = (pgm->code_size + ALT_CACHE_LINE_SIZE) & ~(ALT_CACHE_LINE_SIZE - 1);

    dprintf("DEBUG[DMAP]: Program (real) @ %p, length = 0x%x.\n", pgm->program + pgm->buffer_start, pgm->code_size);
    dprintf("DEBUG[DMAP]: Clean: addr = %p, length = 0x%x.\n", vaddr, length);

    return alt_cache_system_clean(vaddr, length);
}

ALT_STATUS_CODE alt_dma_program_progress_reg(ALT_DMA_PROGRAM_t * pgm,
                                             ALT_DMA_PROGRAM_REG_t reg,
                                             uint32_t current, uint32_t * progress)
{
    // Pointer to where the register is initialized in the program buffer.
    uint8_t * buffer = NULL;

    switch (reg)
    {
    case ALT_DMA_PROGRAM_REG_SAR:
        if (!(pgm->flag & ALT_DMA_PROGRAM_FLAG_SAR))
        {
            return ALT_E_BAD_ARG;
        }
        buffer = pgm->program + pgm->buffer_start + pgm->sar;
        break;

    case ALT_DMA_PROGRAM_REG_DAR:
        if (!(pgm->flag & ALT_DMA_PROGRAM_FLAG_DAR))
        {
            return ALT_E_BAD_ARG;
        }
        buffer = pgm->program + pgm->buffer_start + pgm->dar;
        break;

    default:
        return ALT_E_BAD_ARG;
    }

    uint32_t initial =
        (buffer[3] << 24) |
        (buffer[2] << 16) |
        (buffer[1] <<  8) |
        (buffer[0] <<  0);

    *progress = current - initial;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_update_reg(ALT_DMA_PROGRAM_t * pgm,
                                           ALT_DMA_PROGRAM_REG_t reg, uint32_t val)
{
    uint8_t * buffer = NULL;

    switch (reg)
    {
    case ALT_DMA_PROGRAM_REG_SAR:
        if (!(pgm->flag & ALT_DMA_PROGRAM_FLAG_SAR))
        {
            return ALT_E_BAD_ARG;
        }
        buffer = pgm->program + pgm->buffer_start + pgm->sar;
        break;

    case ALT_DMA_PROGRAM_REG_DAR:
        if (!(pgm->flag & ALT_DMA_PROGRAM_FLAG_DAR))
        {
            return ALT_E_BAD_ARG;
        }
        buffer = pgm->program + pgm->buffer_start + pgm->dar;
        break;

    default:
        return ALT_E_BAD_ARG;
    }

    buffer[0] = (uint8_t)((val >>  0) & 0xff);
    buffer[1] = (uint8_t)((val >>  8) & 0xff);
    buffer[2] = (uint8_t)((val >> 16) & 0xff);
    buffer[3] = (uint8_t)((val >> 24) & 0xff);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAADDH(ALT_DMA_PROGRAM_t * pgm,
                                        ALT_DMA_PROGRAM_REG_t addr_reg, uint16_t val)
{
    // For information on DMAADDH, see PL330, section 4.3.1.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 3) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify valid register; construct instruction modifier.
    uint8_t ra_mask = 0;
    switch (addr_reg)
    {
    case ALT_DMA_PROGRAM_REG_SAR:
        ra_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_REG_DAR:
        ra_mask = 0x2;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAADDH
    buffer[0] = 0x54 | ra_mask;
    buffer[1] = (uint8_t)(val & 0xff);
    buffer[2] = (uint8_t)(val >> 8);

    // Update the code size.
    pgm->code_size += 3;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAADNH(ALT_DMA_PROGRAM_t * pgm,
                                        ALT_DMA_PROGRAM_REG_t addr_reg, uint16_t val)
{
    // For information on DMAADNH, see PL330, section 4.3.2.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 3) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify valid register; construct instruction modifier.
    uint8_t ra_mask = 0;
    switch (addr_reg)
    {
    case ALT_DMA_PROGRAM_REG_SAR:
        ra_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_REG_DAR:
        ra_mask = 0x2;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAADNH
    buffer[0] = 0x5c | ra_mask;
    buffer[1] = (uint8_t)(val & 0xff);
    buffer[2] = (uint8_t)(val >> 8);

    // Update the code size.
    pgm->code_size += 3;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAEND(ALT_DMA_PROGRAM_t * pgm)
{
    // For information on DMAEND, see PL330, section 4.3.3.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAEND
    buffer[0] = 0x00;

    // Update the code size.
    pgm->code_size += 1;

    // Mark program as ended.
    pgm->flag |= ALT_DMA_PROGRAM_FLAG_ENDED;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAFLUSHP(ALT_DMA_PROGRAM_t * pgm,
                                          ALT_DMA_PERIPH_t periph)
{
    // For information on DMAFLUSHP, see PL330, section 4.3.4.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify valid peripheral identifier.
    if (periph > ((1 << 5) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAFLUSHP
    buffer[0] = 0x35;
    buffer[1] = (uint8_t)(periph) << 3;

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAGO(ALT_DMA_PROGRAM_t * pgm,
                                      ALT_DMA_CHANNEL_t channel, uint32_t val,
                                      ALT_DMA_SECURITY_t sec)
{
    // For information on DMAGO, see PL330, section 4.3.5.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 6) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify channel
    switch (channel)
    {
    case ALT_DMA_CHANNEL_0:
    case ALT_DMA_CHANNEL_1:
    case ALT_DMA_CHANNEL_2:
    case ALT_DMA_CHANNEL_3:
    case ALT_DMA_CHANNEL_4:
    case ALT_DMA_CHANNEL_5:
    case ALT_DMA_CHANNEL_6:
    case ALT_DMA_CHANNEL_7:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Verify security; construct ns mask value
    uint8_t ns_mask = 0;
    switch (sec)
    {
    case ALT_DMA_SECURITY_DEFAULT:
    case ALT_DMA_SECURITY_SECURE:
        ns_mask = 0x0;
        break;
    case ALT_DMA_SECURITY_NONSECURE:
        ns_mask = 0x2;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAGO
    buffer[0] = 0xa0 | ns_mask;
    buffer[1] = (uint8_t)channel;
    buffer[2] = (uint8_t)((val >>  0) & 0xff);
    buffer[3] = (uint8_t)((val >>  8) & 0xff);
    buffer[4] = (uint8_t)((val >> 16) & 0xff);
    buffer[5] = (uint8_t)((val >> 24) & 0xff);

    // Update the code size.
    pgm->code_size += 6;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAKILL(ALT_DMA_PROGRAM_t * pgm)
{
    // For information on DMAKILL, see PL330, section 4.3.6.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAKILL
    buffer[0] = 0x01;

    // Update the code size.
    pgm->code_size += 1;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMALD(ALT_DMA_PROGRAM_t * pgm,
                                      ALT_DMA_PROGRAM_INST_MOD_t mod)
{
    // For information on DMALD, see PL330, section 4.3.7.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify instruction modifier; construct bs, x mask value.
    uint8_t bsx_mask = 0;
    switch (mod)
    {
    case ALT_DMA_PROGRAM_INST_MOD_NONE:
        bsx_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_SINGLE:
        bsx_mask = 0x1;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_BURST:
        bsx_mask = 0x3;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMALD
    buffer[0] = 0x04 | bsx_mask;

    // Update the code size.
    pgm->code_size += 1;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMALDP(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PROGRAM_INST_MOD_t mod, ALT_DMA_PERIPH_t periph)
{
    // For information on DMALDP, see PL330, section 4.3.8.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify instruction modifier; construct bs mask value.
    uint8_t bs_mask = 0;
    switch (mod)
    {
    case ALT_DMA_PROGRAM_INST_MOD_SINGLE:
        bs_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_BURST:
        bs_mask = 0x2;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Verify valid peripheral identifier.
    if (periph > ((1 << 5) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMALDP
    buffer[0] = 0x25 | bs_mask;
    buffer[1] = (uint8_t)(periph) << 3;

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMALP(ALT_DMA_PROGRAM_t * pgm,
                                      uint32_t iterations)
{
    // For information on DMALP, see PL330, section 4.3.9.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify iterations in range
    if ((iterations == 0) || (iterations > 256))
    {
        return ALT_E_BAD_ARG;
    }

    // Find suitable LOOPx register to use; construct lc mask value.
    uint8_t lc_mask = 0;
    switch (pgm->flag & ALT_DMA_PROGRAM_FLAG_LOOP_ALL)
    {
    case 0:                              // No LOOPx in use. Use LOOP0.
        pgm->flag |= ALT_DMA_PROGRAM_FLAG_LOOP0;
        pgm->loop0 = pgm->code_size + 2; // This is the first instruction after the DMALP
        lc_mask = 0x0;
        break;

    case ALT_DMA_PROGRAM_FLAG_LOOP0:     // LOOP0 in use. Use LOOP1.
        pgm->flag |= ALT_DMA_PROGRAM_FLAG_LOOP1;
        pgm->loop1 = pgm->code_size + 2; // This is the first instruction after the DMALP
        lc_mask = 0x2;
        break;

    case ALT_DMA_PROGRAM_FLAG_LOOP_ALL: // All LOOPx in use. Report error.
        return ALT_E_BAD_OPERATION;

    default:                            // Catastrophic error !!!
        return ALT_E_ERROR;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMALP
    buffer[0] = 0x20 | lc_mask;
    buffer[1] = (uint8_t)(iterations - 1);

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMALPEND(ALT_DMA_PROGRAM_t * pgm,
                                         ALT_DMA_PROGRAM_INST_MOD_t mod)
{
    // For information on DMALPEND, see PL330, section 4.3.10.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify instruction modifier; construct bs, x mask value.
    uint8_t bsx_mask = 0;
    switch (mod)
    {
    case ALT_DMA_PROGRAM_INST_MOD_NONE:
        bsx_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_SINGLE:
        bsx_mask = 0x1;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_BURST:
        bsx_mask = 0x3;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Determine the loop to end, if it is a forever loop; construct lc mask, nf mask, and backwards jump value.
    uint8_t lc_mask = 0;
    uint8_t nf_mask = 0;
    uint16_t backwards_jump = 0;
    switch (pgm->flag & ALT_DMA_PROGRAM_FLAG_LOOP_ALL)
    {
    case ALT_DMA_PROGRAM_FLAG_LOOP0:    // LOOP0 in use. End LOOP0.

        backwards_jump = pgm->code_size - pgm->loop0;

        pgm->flag &= ~ALT_DMA_PROGRAM_FLAG_LOOP0;
        pgm->loop0 = 0;

        lc_mask = 0x0;

        if (pgm->flag & ALT_DMA_PROGRAM_FLAG_LOOP0_IS_FE)
        {
            pgm->flag &= ~ALT_DMA_PROGRAM_FLAG_LOOP0_IS_FE;
        }
        else
        {
            nf_mask = 0x10;
        }
        break;

    case ALT_DMA_PROGRAM_FLAG_LOOP_ALL: // All LOOPx in use. End LOOP1.

        backwards_jump = pgm->code_size - pgm->loop1;

        pgm->flag &= ~ALT_DMA_PROGRAM_FLAG_LOOP1;
        pgm->loop1 = 0;

        lc_mask = 0x4;

        if (pgm->flag & ALT_DMA_PROGRAM_FLAG_LOOP1_IS_FE)
        {
            pgm->flag &= ~ALT_DMA_PROGRAM_FLAG_LOOP1_IS_FE;
        }
        else
        {
            nf_mask = 0x10;
        }
        break;

    case 0:                             // No LOOPx in use. Report error!
        return ALT_E_BAD_OPERATION;

    default:                            // Catastrophic error !!!
        return ALT_E_ERROR;
    }

    // Verify that the jump size is suitable
    if (backwards_jump > 255)
    {
        return ALT_E_ARG_RANGE;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMALPEND
    buffer[0] = 0x28 | nf_mask | lc_mask | bsx_mask;
    buffer[1] = (uint8_t)(backwards_jump);

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMALPFE(ALT_DMA_PROGRAM_t * pgm)
{
    // For information on DMALPFE, see PL330, section 4.3.11.

    // Find suitable LOOPx register to use;
    switch (pgm->flag & ALT_DMA_PROGRAM_FLAG_LOOP_ALL)
    {
    case 0:                             // No LOOPx in use. Use LOOP0.
        pgm->flag |= ALT_DMA_PROGRAM_FLAG_LOOP0;
        pgm->flag |= ALT_DMA_PROGRAM_FLAG_LOOP0_IS_FE;
        pgm->loop0 = pgm->code_size;
        break;

    case ALT_DMA_PROGRAM_FLAG_LOOP0:    // LOOP0 in use. Use LOOP1.
        pgm->flag |= ALT_DMA_PROGRAM_FLAG_LOOP1;
        pgm->flag |= ALT_DMA_PROGRAM_FLAG_LOOP1_IS_FE;
        pgm->loop1 = pgm->code_size;
        break;

    case ALT_DMA_PROGRAM_FLAG_LOOP_ALL: // All LOOPx in use. Report error.
        return ALT_E_BAD_OPERATION;

    default:                            // Catastrophic error !!!
        return ALT_E_ERROR;
    }

    // Nothing to assemble.

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAMOV(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PROGRAM_REG_t chan_reg, uint32_t val)
{
    // For information on DMAMOV, see PL330, section 4.3.12.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 6) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify channel register; construct rd mask value
    uint8_t rd_mask = 0;
    switch (chan_reg)
    {
    case ALT_DMA_PROGRAM_REG_SAR:
        rd_mask = 0;
        // If SAR has not been set before, mark the location of where SAR is in the buffer.
        if (!(pgm->flag & ALT_DMA_PROGRAM_FLAG_SAR))
        {
            pgm->flag |= ALT_DMA_PROGRAM_FLAG_SAR;
            pgm->sar = pgm->code_size + 2;
        }
        break;

    case ALT_DMA_PROGRAM_REG_CCR:
        rd_mask = 1;
        break;

    case ALT_DMA_PROGRAM_REG_DAR:
        rd_mask = 2;
        // If DAR has not been set before, mark the location of where DAR is in the buffer.
        if (!(pgm->flag & ALT_DMA_PROGRAM_FLAG_DAR))
        {
            pgm->flag |= ALT_DMA_PROGRAM_FLAG_DAR;
            pgm->dar = pgm->code_size + 2;
        }
        break;

    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAMOV
    buffer[0] = 0xbc;;
    buffer[1] = rd_mask;
    buffer[2] = (uint8_t)((val >>  0) & 0xff);
    buffer[3] = (uint8_t)((val >>  8) & 0xff);
    buffer[4] = (uint8_t)((val >> 16) & 0xff);
    buffer[5] = (uint8_t)((val >> 24) & 0xff);

    // Update the code size.
    pgm->code_size += 6;

    return ALT_E_SUCCESS;

}

ALT_STATUS_CODE alt_dma_program_DMANOP(ALT_DMA_PROGRAM_t * pgm)
{
    // For information on DMANOP, see PL330, section 4.3.13.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMANOP
    buffer[0] = 0x18;

    // Update the code size.
    pgm->code_size += 1;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMARMB(ALT_DMA_PROGRAM_t * pgm)
{
    // For information on DMARMB, see PL330, section 4.3.14.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMARMB
    buffer[0] = 0x12;

    // Update the code size.
    pgm->code_size += 1;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMASEV(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_EVENT_t evt)
{
    // For information on DMA, see PL330, section 4.3.15.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Validate evt selection
    switch (evt)
    {
    case ALT_DMA_EVENT_0:
    case ALT_DMA_EVENT_1:
    case ALT_DMA_EVENT_2:
    case ALT_DMA_EVENT_3:
    case ALT_DMA_EVENT_4:
    case ALT_DMA_EVENT_5:
    case ALT_DMA_EVENT_6:
    case ALT_DMA_EVENT_7:
    case ALT_DMA_EVENT_ABORT:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMASEV
    buffer[0] = 0x34;
    buffer[1] = (uint8_t)(evt) << 3;

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAST(ALT_DMA_PROGRAM_t * pgm,
                                      ALT_DMA_PROGRAM_INST_MOD_t mod)
{
    // For information on DMAST, see PL330, section 4.3.16.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify instruction modifier; construct bs, x mask value.
    uint8_t bsx_mask = 0;
    switch (mod)
    {
    case ALT_DMA_PROGRAM_INST_MOD_NONE:
        bsx_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_SINGLE:
        bsx_mask = 0x1;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_BURST:
        bsx_mask = 0x3;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAST
    buffer[0] = 0x08 | bsx_mask;

    // Update the code size.
    pgm->code_size += 1;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMASTP(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PROGRAM_INST_MOD_t mod, ALT_DMA_PERIPH_t periph)
{
    // For information on DMASTP, see PL330, section 4.3.17.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify instruction modifier; construct bs mask value.
    uint8_t bs_mask = 0;
    switch (mod)
    {
    case ALT_DMA_PROGRAM_INST_MOD_SINGLE:
        bs_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_BURST:
        bs_mask = 0x2;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Verify valid peripheral identifier.
    if (periph > ((1 << 5) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMASTP
    buffer[0] = 0x29 | bs_mask;
    buffer[1] = (uint8_t)(periph) << 3;

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMASTZ(ALT_DMA_PROGRAM_t * pgm)
{
    // For information on DMASTZ, see PL330, section 4.3.18.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMASTZ
    buffer[0] = 0x0c;

    // Update the code size.
    pgm->code_size += 1;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAWFE(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_EVENT_t evt, bool invalid)
{
    // For information on DMAWFE, see PL330, section 4.3.19.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Validate evt selection
    switch (evt)
    {
    case ALT_DMA_EVENT_0:
    case ALT_DMA_EVENT_1:
    case ALT_DMA_EVENT_2:
    case ALT_DMA_EVENT_3:
    case ALT_DMA_EVENT_4:
    case ALT_DMA_EVENT_5:
    case ALT_DMA_EVENT_6:
    case ALT_DMA_EVENT_7:
    case ALT_DMA_EVENT_ABORT:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Construct i mask value
    uint8_t i_mask = 0;
    if (invalid)
    {
        i_mask = 0x2;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAWFE
    buffer[0] = 0x36;
    buffer[1] = ((uint8_t)(evt) << 3) | i_mask;

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAWFP(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PERIPH_t periph, ALT_DMA_PROGRAM_INST_MOD_t mod)
{
    // For information on DMAWFP, see PL330, section 4.3.20.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 2) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Verify valid peripheral identifier.
    if (periph > ((1 << 5) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    // Verify instruction modifier; construct bs, p mask value.
    uint8_t bsp_mask = 0;
    switch (mod)
    {
    case ALT_DMA_PROGRAM_INST_MOD_SINGLE:
        bsp_mask = 0x0;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_BURST:
        bsp_mask = 0x2;
        break;
    case ALT_DMA_PROGRAM_INST_MOD_PERIPH:
        bsp_mask = 0x1;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAWFP
    buffer[0] = 0x30 | bsp_mask;
    buffer[1] = (uint8_t)(periph) << 3;

    // Update the code size.
    pgm->code_size += 2;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_program_DMAWMB(ALT_DMA_PROGRAM_t * pgm)
{
    // For information on DMAWMB, see PL330, section 4.3.21.

    // Check for sufficient space in buffer
    if ((pgm->code_size + 1) > ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE)
    {
        return ALT_E_BUF_OVF;
    }

    // Buffer of where to assemble the instruction.
    uint8_t * buffer = pgm->program + pgm->buffer_start + pgm->code_size;

    // Assemble DMAWMB
    buffer[0] = 0x13;

    // Update the code size.
    pgm->code_size += 1;

    return ALT_E_SUCCESS;
}
