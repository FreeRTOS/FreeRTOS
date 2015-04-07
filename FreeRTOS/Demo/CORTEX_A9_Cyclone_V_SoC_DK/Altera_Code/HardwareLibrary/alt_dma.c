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

#include <stdio.h>
#include "alt_dma.h"
#include "socal/socal.h"
#include "socal/hps.h"
#include "socal/alt_rstmgr.h"
#include "socal/alt_sysmgr.h"

#if ALT_DMA_PERIPH_PROVISION_16550_SUPPORT
#include "alt_16550_uart.h"
#include "socal/alt_uart.h"
#endif

#if ALT_DMA_PERIPH_PROVISION_QSPI_SUPPORT
#include "socal/alt_qspi.h"
#endif

/////

#ifndef MIN
#define MIN(a, b) ((a) > (b) ? (b) : (a))
#endif // MIN

#ifndef ARRAY_COUNT
#define ARRAY_COUNT(array) (sizeof(array) / sizeof(array[0]))
#endif

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf(fmt, ...) printf(fmt, ##__VA_ARGS__)

/////

//
// SoCAL stand in for DMA Controller registers
//
// The base can be one of the following: 
//  - ALT_DMANONSECURE_ADDR
//  - ALT_DMASECURE_ADDR
//
// Macros which have a channel parameter does no validation.
//

// DMA Manager Status Register
#define ALT_DMA_DSR_OFST 0x0
#define ALT_DMA_DSR_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_DSR_OFST))
#define ALT_DMA_DSR_DMASTATUS_SET_MSK 0x0000000f
#define ALT_DMA_DSR_DMASTATUS_GET(value) ((value) & 0x0000000f)

// DMA Program Counter Register
#define ALT_DMA_DPC_OFST 0x4
#define ALT_DMA_DPC_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_DPC_OFST))

// Interrupt Enable Register
#define ALT_DMA_INTEN_OFST 0x20
#define ALT_DMA_INTEN_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_INTEN_OFST))

// Event-Interrupt Raw Status Register
#define ALT_DMA_INT_EVENT_RIS_OFST 0x24
#define ALT_DMA_INT_EVENT_RIS_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_INT_EVENT_RIS_OFST))

// Interrupt Status Register
#define ALT_DMA_INTMIS_OFST 0x28
#define ALT_DMA_INTMIS_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_INTMIS_OFST))

// Interrupt Clear Register
#define ALT_DMA_INTCLR_OFST 0x2c
#define ALT_DMA_INTCLR_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_INTCLR_OFST))

// Fault Status DMA Manager Register
#define ALT_DMA_FSRD_OFST 0x30
#define ALT_DMA_FSRD_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_FSRD_OFST))

// Fault Status DMA Channel Register
#define ALT_DMA_FSRC_OFST 0x34
#define ALT_DMA_FSRC_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_FSRC_OFST))

// Fault Type DMA Manager Register
#define ALT_DMA_FTRD_OFST 0x38
#define ALT_DMA_FTRD_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_FSRD_OFST))

// Fault Type DMA Channel Registers
#define ALT_DMA_FTRx_OFST(channel) (0x40 + 0x4 * (channel))
#define ALT_DMA_FTRx_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_FTRx_OFST(channel)))

// Channel Status Registers
#define ALT_DMA_CSRx_OFST(channel) (0x100 + 0x8 * (channel))
#define ALT_DMA_CSRx_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CSRx_OFST(channel)))
#define ALT_DMA_CSRx_CHANNELSTATUS_SET_MSK 0x0000000f
#define ALT_DMA_CSRx_CHANNELSTATUS_GET(value) ((value) & 0x0000000f)

// Channel Program Counter Registers
#define ALT_DMA_CPCx_OFST(channel) (0x104 + 0x8 * (channel))
#define ALT_DMA_CPCx_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CPCx_OFST(channel)))

// Source Address Registers
#define ALT_DMA_SARx_OFST(channel) (0x400 + 0x20 * (channel))
#define ALT_DMA_SARx_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_SARx_OFST(channel)))

// Destination Address Registers
#define ALT_DMA_DARx_OFST(channel) (0x404 + 0x20 * (channel))
#define ALT_DMA_DARx_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_DARx_OFST(channel)))

// Channel Control Registers
#define ALT_DMA_CCRx_OFST(channel) (0x408 + 0x20 * (channel))
#define ALT_DMA_CCRx_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CCRx_OFST(channel)))

// Loop Counter 0 Registers
#define ALT_DMA_LC0_x_OFST(channel) (0x40c + 0x20 * (channel))
#define ALT_DMA_LC0_x_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_LC0_x_OFST(channel)))

// Loop Counter 1 Registers
#define ALT_DMA_LC1_x_OFST(channel) (0x410 + 0x20 * (channel))
#define ALT_DMA_LC1_x_ADDR(base, channel) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_LC1_x_OFST(channel)))

// Debug Status Register
#define ALT_DMA_DBGSTATUS_OFST 0xd00
#define ALT_DMA_DBGSTATUS_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_DBGSTATUS_OFST))

// Debug Command Register
#define ALT_DMA_DBGCMD_OFST 0xd04
#define ALT_DMA_DBGCMD_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_DBGCMD_OFST))

// Debug Instruction-0 Register
#define ALT_DMA_DBGINST0_OFST 0xd08
#define ALT_DMA_DBGINST0_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_DBGINST0_OFST))
#define ALT_DMA_DBGINST0_CHANNELNUMBER_SET(value) (((value) & 0x7) << 8)
#define ALT_DMA_DBGINST0_DEBUGTHREAD_SET(value) ((value) & 0x1)
#define ALT_DMA_DBGINST0_DEBUGTHREAD_E_MANAGER 0
#define ALT_DMA_DBGINST0_DEBUGTHREAD_E_CHANNEL 1
#define ALT_DMA_DBGINST0_INSTRUCTIONBYTE0_SET(value) (((value) & 0xff) << 16)
#define ALT_DMA_DBGINST0_INSTRUCTIONBYTE1_SET(value) (((value) & 0xff) << 24)

// Debug Instruction-1 Register
#define ALT_DMA_DBGINST1_OFST 0xd0c
#define ALT_DMA_DBGINST1_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_DBGINST1_OFST))

// Configuration Registers 0 - 4
#define ALT_DMA_CR0_OFST 0xe00
#define ALT_DMA_CR1_OFST 0xe04
#define ALT_DMA_CR2_OFST 0xe08
#define ALT_DMA_CR3_OFST 0xe0c
#define ALT_DMA_CR4_OFST 0xe10
#define ALT_DMA_CR0_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CR0_OFST))
#define ALT_DMA_CR1_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CR1_OFST))
#define ALT_DMA_CR2_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CR2_OFST))
#define ALT_DMA_CR3_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CR3_OFST))
#define ALT_DMA_CR4_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CR4_OFST))

// DMA Configuration Register
#define ALT_DMA_CRD_OFST 0xe14
#define ALT_DMA_CRD_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_CRD_OFST))

// Watchdog Register
#define ALT_DMA_WD_OFST 0xe80
#define ALT_DMA_WD_ADDR(base) ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_DMA_WD_OFST))

/////

//
// Internal Data structures
//

// This flag marks the channel as being allocated.
#define ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED (1 << 0)

typedef struct ALT_DMA_CHANNEL_INFO_s
{
    uint8_t flag;
}
ALT_DMA_CHANNEL_INFO_t;

static ALT_DMA_CHANNEL_INFO_t channel_info_array[8];

/////

ALT_STATUS_CODE alt_dma_init(const ALT_DMA_CFG_t * dma_cfg)
{
    // Initialize the channel information array
    for (int i = 0; i < 8; ++i)
    {
        channel_info_array[i].flag = 0;
    }

    // Update the System Manager DMA configuration items
    
    uint32_t dmactrl = 0;

    // Handle FPGA / CAN muxing
    for (int i = 0; i < 4; ++i)
    {
        // The default is FPGA.
        switch (dma_cfg->periph_mux[i])
        {
        case ALT_DMA_PERIPH_MUX_DEFAULT:
        case ALT_DMA_PERIPH_MUX_FPGA:
            break;
        case ALT_DMA_PERIPH_MUX_CAN:
            dmactrl |= (ALT_SYSMGR_DMA_CTL_CHANSEL_0_SET_MSK << i);
            break;
        default:
            return ALT_E_ERROR;
        }
    }

    // Handle Manager security
    // Default is Secure state.
    switch (dma_cfg->manager_sec)
    {
    case ALT_DMA_SECURITY_DEFAULT:
    case ALT_DMA_SECURITY_SECURE:
        break;
    case ALT_DMA_SECURITY_NONSECURE:
        dmactrl |= ALT_SYSMGR_DMA_CTL_MGRNONSECURE_SET_MSK;
        break;
    default:
        return ALT_E_ERROR;
    }

    // Handle IRQ security
    for (int i = 0; i < ALT_SYSMGR_DMA_CTL_IRQNONSECURE_WIDTH; ++i)
    {
        // Default is Secure state.
        switch (dma_cfg->irq_sec[i])
        {
        case ALT_DMA_SECURITY_DEFAULT:
        case ALT_DMA_SECURITY_SECURE:
            break;
        case ALT_DMA_SECURITY_NONSECURE:
            dmactrl |= (1 << (i + ALT_SYSMGR_DMA_CTL_IRQNONSECURE_LSB));
            break;
        default:
            return ALT_E_ERROR;
        }
    }

    alt_write_word(ALT_SYSMGR_DMA_CTL_ADDR, dmactrl);

    // Update the System Manager DMA peripheral security items

    uint32_t dmapersecurity = 0;

    for (int i = 0; i < 32; ++i)
    {
        // Default is Secure state.
        switch (dma_cfg->periph_sec[i])
        {
        case ALT_DMA_SECURITY_DEFAULT:
        case ALT_DMA_SECURITY_SECURE:
            break;
        case ALT_DMA_SECURITY_NONSECURE:
            dmapersecurity |= (1 << i);
            break;
        default:
            return ALT_E_ERROR;
        }
    }

    alt_write_word(ALT_SYSMGR_DMA_PERSECURITY_ADDR, dmapersecurity);

    // Take DMA out of reset.

    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_DMA_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_uninit(void)
{
    // DMAKILL all channel and free all allocated channels.
    for (int i = 0; i < 8; ++i)
    {
        if (channel_info_array[i].flag & ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED)
        {
            alt_dma_channel_kill((ALT_DMA_CHANNEL_t)i);
            alt_dma_channel_free((ALT_DMA_CHANNEL_t)i);
        }
    }

    // Put DMA into reset.

    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_DMA_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_channel_alloc(ALT_DMA_CHANNEL_t channel)
{
    // Validate channel
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

    // Verify channel is unallocated

    if (channel_info_array[channel].flag & ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED)
    {
        return ALT_E_ERROR;
    }

    // Mark channel as allocated

    channel_info_array[channel].flag |= ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_channel_alloc_any(ALT_DMA_CHANNEL_t * allocated)
{
    // Sweep channel array for unallocated channel

    for (int i = 0; i < 8; ++i)
    {
        if (!(channel_info_array[i].flag & ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED))
        {
            // Allocate that free channel.

            ALT_STATUS_CODE status = alt_dma_channel_alloc((ALT_DMA_CHANNEL_t)i);
            if (status == ALT_E_SUCCESS)
            {
                *allocated = (ALT_DMA_CHANNEL_t)i;
            }
            return status;
        }
    }

    // No free channels found.

    return ALT_E_ERROR;
}

ALT_STATUS_CODE alt_dma_channel_free(ALT_DMA_CHANNEL_t channel)
{
    // Validate channel
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

    // Verify channel is allocated

    if (!(channel_info_array[channel].flag & ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED))
    {
        return ALT_E_ERROR;
    }

    // Verify channel is stopped

    ALT_DMA_CHANNEL_STATE_t state;
    ALT_STATUS_CODE status = alt_dma_channel_state_get(channel, &state);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    if (state != ALT_DMA_CHANNEL_STATE_STOPPED)
    {
        return ALT_E_ERROR;
    }

    // Mark channel as unallocated.

    channel_info_array[channel].flag &= ~ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_channel_exec(ALT_DMA_CHANNEL_t channel, ALT_DMA_PROGRAM_t * pgm)
{
    // Validate channel
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

    // Verify channel is allocated

    if (!(channel_info_array[channel].flag & ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED))
    {
        return ALT_E_ERROR;
    }

    // Verify channel is stopped

    ALT_DMA_CHANNEL_STATE_t state;
    ALT_STATUS_CODE status = alt_dma_channel_state_get(channel, &state);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    if (state != ALT_DMA_CHANNEL_STATE_STOPPED)
    {
        return ALT_E_ERROR;
    }

    // Validate the program

    if (alt_dma_program_validate(pgm) != ALT_E_SUCCESS)
    {
        return ALT_E_ERROR;
    }

    //
    // Execute the program
    //

    // Get the start address

    uint32_t start = (uint32_t) &pgm->program[pgm->buffer_start];

    dprintf("DMA[exec]: pgm->program = %p.\n", pgm->program);
    dprintf("DMA[exec]: start        = %p.\n", (void *)start);

    // Configure DBGINST0 and DBGINST1 to execute DMAGO targetting the requested channel.

    // For information on APB Interface, see PL330, section 2.5.1.
    // For information on DBGINSTx, see PL330, section 3.3.20 - 3.3.21.
    // For information on DMAGO, see PL330, section 4.3.5.

    alt_write_word(ALT_DMA_DBGINST0_ADDR(ALT_DMASECURE_ADDR),
                   ALT_DMA_DBGINST0_INSTRUCTIONBYTE0_SET(0xa0) | 
                   ALT_DMA_DBGINST0_INSTRUCTIONBYTE1_SET(channel));

    alt_write_word(ALT_DMA_DBGINST1_ADDR(ALT_DMASECURE_ADDR), start);

    // Execute the instruction held in DBGINST{0,1}

    // For information on DBGCMD, see PL330, section 3.3.19.

    alt_write_word(ALT_DMA_DBGCMD_ADDR(ALT_DMASECURE_ADDR), 0);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_channel_kill(ALT_DMA_CHANNEL_t channel)
{
    // Validate channel
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

    // Verify channel is allocated

    if (!(channel_info_array[channel].flag & ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED))
    {
        return ALT_E_ERROR;
    }

    // NOTE: Don't worry about the current channel state. Just issue DMAKILL
    //   instruction. The channel state cannot move from from Stopped back to
    //   Killing.

    // Configure DBGINST0 to execute DMAKILL on the requested channel thread.
    // DMAKILL is short enough not to use DBGINST1 register.

    // For information on APB Interface, see PL330, section 2.5.1.
    // For information on DBGINSTx, see PL330, section 3.3.20 - 3.3.21.
    // For information on DMAKILL, see PL330, section 4.3.6.

    alt_write_word(ALT_DMA_DBGINST0_ADDR(ALT_DMASECURE_ADDR),
                   ALT_DMA_DBGINST0_INSTRUCTIONBYTE0_SET(0x1) |
                   ALT_DMA_DBGINST0_CHANNELNUMBER_SET(channel) |
                   ALT_DMA_DBGINST0_DEBUGTHREAD_SET(ALT_DMA_DBGINST0_DEBUGTHREAD_E_CHANNEL));

    // Execute the instruction held in DBGINST0

    // For information on DBGCMD, see PL330, section 3.3.19.

    alt_write_word(ALT_DMA_DBGCMD_ADDR(ALT_DMASECURE_ADDR), 0);

    // Wait for channel to move to KILLING or STOPPED state. Do not wait for
    // the STOPPED only. If the AXI transaction hangs permanently, it can be
    // waiting indefinately.

    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    ALT_DMA_CHANNEL_STATE_t current;
    uint32_t i = 20000;

    while (--i)
    {
        status = alt_dma_channel_state_get(channel, &current);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }
        if (   (current == ALT_DMA_CHANNEL_STATE_KILLING)
            || (current == ALT_DMA_CHANNEL_STATE_STOPPED))
        {
            break;
        }
    }

    if (i == 0)
    {
        status = ALT_E_TMO;
    }

    return status;
}

ALT_STATUS_CODE alt_dma_channel_reg_get(ALT_DMA_CHANNEL_t channel,
                                        ALT_DMA_PROGRAM_REG_t reg, uint32_t * val)
{
    // Validate channel
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

    // For information on SAR, see PL330, section 3.3.13.
    // For information on DAR, see PL330, section 3.3.14.
    // For information on CCR, see PL330, section 3.3.15.

    switch (reg)
    {
    case ALT_DMA_PROGRAM_REG_SAR:
        *val = alt_read_word(ALT_DMA_SARx_ADDR(ALT_DMASECURE_ADDR, channel));
        break;
    case ALT_DMA_PROGRAM_REG_DAR:
        *val = alt_read_word(ALT_DMA_DARx_ADDR(ALT_DMASECURE_ADDR, channel));
        break;
    case ALT_DMA_PROGRAM_REG_CCR:
        *val = alt_read_word(ALT_DMA_CCRx_ADDR(ALT_DMASECURE_ADDR, channel));
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_send_event(ALT_DMA_EVENT_t evt_num)
{
    // Validate evt_num

    switch (evt_num)
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

    // Issue the DMASEV on the DMA manager thread.
    // DMASEV is short enough not to use DBGINST1 register.

    // For information on APB Interface, see PL330, section 2.5.1.
    // For information on DBGINSTx, see PL330, section 3.3.20 - 3.3.21.
    // For information on DMASEV, see PL330, section 4.3.15.

    alt_write_word(ALT_DMA_DBGINST0_ADDR(ALT_DMASECURE_ADDR),
                   ALT_DMA_DBGINST0_INSTRUCTIONBYTE0_SET(0x34) | // opcode for DMASEV
                   ALT_DMA_DBGINST0_INSTRUCTIONBYTE1_SET(evt_num << 3) |
                   ALT_DMA_DBGINST0_DEBUGTHREAD_SET(ALT_DMA_DBGINST0_DEBUGTHREAD_E_MANAGER)
        );

    // Execute the instruction held in DBGINST0

    // For information on DBGCMD, see PL330, section 3.3.19.

    alt_write_word(ALT_DMA_DBGCMD_ADDR(ALT_DMASECURE_ADDR), 0);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_manager_state_get(ALT_DMA_MANAGER_STATE_t * state)
{
    // For information on DSR, see PL330, section 3.3.1.

    uint32_t raw_state = alt_read_word(ALT_DMA_DSR_ADDR(ALT_DMASECURE_ADDR));

    *state = (ALT_DMA_MANAGER_STATE_t)ALT_DMA_DSR_DMASTATUS_GET(raw_state);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_channel_state_get(ALT_DMA_CHANNEL_t channel,
                                          ALT_DMA_CHANNEL_STATE_t * state)
{
    // Validate channel
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

    // For information on CSR, see PL330, section 3.3.11.

    uint32_t raw_state = alt_read_word(ALT_DMA_CSRx_ADDR(ALT_DMASECURE_ADDR, channel));

    *state = (ALT_DMA_CHANNEL_STATE_t)ALT_DMA_CSRx_CHANNELSTATUS_GET(raw_state);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_manager_fault_status_get(ALT_DMA_MANAGER_FAULT_t * fault)
{
    // For information on FTRD, see PL330, section 3.3.9.

    *fault = (ALT_DMA_MANAGER_FAULT_t)alt_read_word(ALT_DMA_FTRD_ADDR(ALT_DMASECURE_ADDR));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_channel_fault_status_get(ALT_DMA_CHANNEL_t channel,
                                                 ALT_DMA_CHANNEL_FAULT_t * fault)
{
    // Validate channel
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

    // For information on FTR, see PL330, section 3.3.10.

    *fault = (ALT_DMA_CHANNEL_FAULT_t)alt_read_word(ALT_DMA_FTRx_ADDR(ALT_DMASECURE_ADDR, channel));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_event_int_select(ALT_DMA_EVENT_t evt_num,
                                         ALT_DMA_EVENT_SELECT_t opt)
{
    // Validate evt_num
    switch (evt_num)
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

    // For information on INTEN, see PL330, section 3.3.3.

    switch (opt)
    {
    case ALT_DMA_EVENT_SELECT_SEND_EVT:
        alt_clrbits_word(ALT_DMA_INTEN_ADDR(ALT_DMASECURE_ADDR), 1 << evt_num);
        break;
    case ALT_DMA_EVENT_SELECT_SIG_IRQ:
        alt_setbits_word(ALT_DMA_INTEN_ADDR(ALT_DMASECURE_ADDR), 1 << evt_num);
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_dma_event_int_status_get_raw(ALT_DMA_EVENT_t evt_num)
{
    // Validate evt_num
    switch (evt_num)
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

    // For information on INT_EVENT_RIS, see PL330, section 3.3.4.

    uint32_t status_raw = alt_read_word(ALT_DMA_INT_EVENT_RIS_ADDR(ALT_DMASECURE_ADDR));

    if (status_raw & (1 << evt_num))
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

ALT_STATUS_CODE alt_dma_int_status_get(ALT_DMA_EVENT_t irq_num)
{
    // Validate evt_num
    switch (irq_num)
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

    // For information on INTMIS, see PL330, section 3.3.5.

    uint32_t int_status = alt_read_word(ALT_DMA_INTMIS_ADDR(ALT_DMASECURE_ADDR));

    if (int_status & (1 << irq_num))
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

ALT_STATUS_CODE alt_dma_int_clear(ALT_DMA_EVENT_t irq_num)
{
    // Validate evt_num
    switch (irq_num)
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

    // For information on INTCLR, see PL330, section 3.3.6.

    alt_write_word(ALT_DMA_INTCLR_ADDR(ALT_DMASECURE_ADDR), 1 << irq_num);

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_dma_memory_to_memory(ALT_DMA_CHANNEL_t channel,
                                         ALT_DMA_PROGRAM_t * program,
                                         void * dst,
                                         const void * src,
                                         size_t size,
                                         bool send_evt,
                                         ALT_DMA_EVENT_t evt)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // If the size is zero, and no event is requested, just return success.
    if ((size == 0) && (send_evt == false))
    {
        return status;
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_init(program);
    }

    if (size != 0)
    {
        uintptr_t udst = (uintptr_t)dst;
        uintptr_t usrc = (uintptr_t)src;

        dprintf("DMA[M->M]: dst  = %p.\n", dst);
        dprintf("DMA[M->M]: src  = %p.\n", src);
        dprintf("DMA[M->M]: size = 0x%x.\n", size);
        
        // Detect if memory regions overshoots the address space.

        if (udst + size - 1 < udst)
        {
            return ALT_E_BAD_ARG;
        }
        if (usrc + size - 1 < usrc)
        {
            return ALT_E_BAD_ARG;
        }

        // Detect if memory regions overlaps.

        if (udst > usrc)
        {
            if (usrc + size - 1 > udst)
            {
                return ALT_E_BAD_ARG;
            }
        }
        else
        {
            if (udst + size - 1 > usrc)
            {
                return ALT_E_BAD_ARG;
            }
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_SAR, usrc);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR, udst);
        }

        size_t sizeleft = size;

        //
        // The algorithm uses the strategy described in PL330 B.3.1.
        // It is extended for 2-byte and 1-byte unaligned cases.
        //

        // First see how many byte(s) we need to transfer to get src to be 8 byte aligned
        if (usrc & 0x7)
        {
            uint32_t aligncount = MIN(8 - (usrc & 0x7), sizeleft);
            sizeleft -= aligncount;

            dprintf("DMA[M->M]: Total pre-alignment 1-byte burst size tranfer(s): %lu.\n", aligncount);

            // Program in the following parameters:
            //  - SS8 (Source      burst size of 1-byte)
            //  - DS8 (Destination burst size of 1-byte)
            //  - SBx (Source      burst length of [aligncount] transfers)
            //  - DBx (Destination burst length of [aligncount] transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ((aligncount - 1) << 4) // SB
                                                  | ALT_DMA_CCR_OPT_SS8
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((aligncount - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DS8
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }

        // This is the number of 8-byte bursts
        uint32_t burstcount = sizeleft >> 3;

        bool correction = (burstcount != 0);

        // Update the size left to transfer
        sizeleft &= 0x7;

        dprintf("DMA[M->M]: Total Main 8-byte burst size transfer(s): %lu.\n", burstcount);
        dprintf("DMA[M->M]: Total Main 1-byte burst size transfer(s): %u.\n", sizeleft);

        // Determine how many 16 length bursts can be done

        if (burstcount >> 4)
        {
            uint32_t length16burstcount = burstcount >> 4;
            burstcount &= 0xf;

            dprintf("DMA[M->M]:   Number of 16 burst length 8-byte transfer(s): %lu.\n", length16burstcount);
            dprintf("DMA[M->M]:   Number of remaining 8-byte transfer(s):       %lu.\n", burstcount);

            // Program in the following parameters:
            //  - SS64 (Source      burst size of 8-byte)
            //  - DS64 (Destination burst size of 8-byte)
            //  - SB16 (Source      burst length of 16 transfers)
            //  - DB16 (Destination burst length of 16 transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ALT_DMA_CCR_OPT_SB16
                                                  | ALT_DMA_CCR_OPT_SS64
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DB16
                                                  | ALT_DMA_CCR_OPT_DS64
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }

            while (length16burstcount > 0)
            {
                if (status != ALT_E_SUCCESS)
                {
                    break;
                }

                uint32_t loopcount = MIN(length16burstcount, 256);
                length16burstcount -= loopcount;

                dprintf("DMA[M->M]:   Looping %lux 16 burst length 8-byte transfer(s).\n", loopcount);

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALP(program, loopcount);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
            }
        }

        // At this point, we should have [burstcount] 8-byte transfer(s)
        // remaining. [burstcount] should be less than 16.

        // Do one more burst with a SB / DB of length [burstcount].

        if (burstcount)
        {
            // Program in the following parameters:
            //  - SS64 (Source      burst size of 8-byte)
            //  - DS64 (Destination burst size of 8-byte)
            //  - SBx  (Source      burst length of [burstlength] transfers)
            //  - DBx  (Destination burst length of [burstlength] transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ((burstcount - 1) << 4) // SB
                                                  | ALT_DMA_CCR_OPT_SS64
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((burstcount - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DS64
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }

        // This is where the last DMAMOV CCR and DMAST is done if an
        // alignment correction required.

        if (   (correction == true)
            && ((usrc & 0x7) != (udst & 0x7)) // If src and dst are mod-8 congruent, no correction is needed.
           )
        {
            if (status == ALT_E_SUCCESS)
            {
                // Determine what type of correction.

                // Set the source parameters to match that of the destination
                // parameters. This way the SAR is increment in the same fashion as
                // DAR. This will allow the non 8-byte transfers to copy correctly.

                uint32_t ccr;

                if ((usrc & 0x3) == (udst & 0x3))
                {
                    dprintf("DMA[M->M]: Single correction 4-byte burst size tranfer.\n");

                    // Program in the following parameters:
                    //  - SS32 (Source      burst size of 4-byte)
                    //  - DS32 (Destination burst size of 4-byte)
                    //  - SB1  (Source      burst length of 1 transfer)
                    //  - DB1  (Destination burst length of 1 transfer)
                    //  - All other options default.

                    ccr = (   ALT_DMA_CCR_OPT_SB1
                            | ALT_DMA_CCR_OPT_SS32
                            | ALT_DMA_CCR_OPT_SA_DEFAULT
                            | ALT_DMA_CCR_OPT_SP_DEFAULT
                            | ALT_DMA_CCR_OPT_SC_DEFAULT
                            | ALT_DMA_CCR_OPT_DB1
                            | ALT_DMA_CCR_OPT_DS32
                            | ALT_DMA_CCR_OPT_DA_DEFAULT
                            | ALT_DMA_CCR_OPT_DP_DEFAULT
                            | ALT_DMA_CCR_OPT_DC_DEFAULT
                            | ALT_DMA_CCR_OPT_ES_DEFAULT
                          );
                }
                else if ((usrc & 0x1) == (udst & 0x1))
                {
                    dprintf("DMA[M->M]: Single correction 2-byte burst size tranfer.\n");

                    // Program in the following parameters:
                    //  - SS16 (Source      burst size of 2-byte)
                    //  - DS16 (Destination burst size of 2-byte)
                    //  - SB1  (Source      burst length of 1 transfer)
                    //  - DB1  (Destination burst length of 1 transfer)
                    //  - All other options default.

                    ccr = (   ALT_DMA_CCR_OPT_SB1
                            | ALT_DMA_CCR_OPT_SS16
                            | ALT_DMA_CCR_OPT_SA_DEFAULT
                            | ALT_DMA_CCR_OPT_SP_DEFAULT
                            | ALT_DMA_CCR_OPT_SC_DEFAULT
                            | ALT_DMA_CCR_OPT_DB1
                            | ALT_DMA_CCR_OPT_DS16
                            | ALT_DMA_CCR_OPT_DA_DEFAULT
                            | ALT_DMA_CCR_OPT_DP_DEFAULT
                            | ALT_DMA_CCR_OPT_DC_DEFAULT
                            | ALT_DMA_CCR_OPT_ES_DEFAULT
                          );
                }
                else
                {
                    dprintf("DMA[M->M]: Single correction 1-byte burst size tranfer.\n");

                    // Program in the following parameters:
                    //  - SS8 (Source      burst size of 1-byte)
                    //  - DS8 (Destination burst size of 1-byte)
                    //  - SB1 (Source      burst length of 1 transfer)
                    //  - DB1 (Destination burst length of 1 transfer)
                    //  - All other options default.

                    ccr = (   ALT_DMA_CCR_OPT_SB1
                            | ALT_DMA_CCR_OPT_SS8
                            | ALT_DMA_CCR_OPT_SA_DEFAULT
                            | ALT_DMA_CCR_OPT_SP_DEFAULT
                            | ALT_DMA_CCR_OPT_SC_DEFAULT
                            | ALT_DMA_CCR_OPT_DB1
                            | ALT_DMA_CCR_OPT_DS8
                            | ALT_DMA_CCR_OPT_DA_DEFAULT
                            | ALT_DMA_CCR_OPT_DP_DEFAULT
                            | ALT_DMA_CCR_OPT_DC_DEFAULT
                            | ALT_DMA_CCR_OPT_ES_DEFAULT
                          );
                }

                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                ccr);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }

        // At this point, there should be 0 - 7 1-byte transfers remaining.

        if (sizeleft)
        {
            dprintf("DMA[M->M]: Total post 1-byte burst size tranfer(s): %u.\n", sizeleft);

            // Program in the following parameters:
            //  - SS8 (Source      burst size of 1-byte)
            //  - DS8 (Destination burst size of 1-byte)
            //  - SBx (Source      burst length of [sizeleft] transfers)
            //  - DBx (Destination burst length of [sizeleft] transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ((sizeleft - 1) << 4) // SB
                                                  | ALT_DMA_CCR_OPT_SS8
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((sizeleft - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DS8
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }
    } // if (size != 0)

    // Send event if requested.
    if (send_evt)
    {
        if (status == ALT_E_SUCCESS)
        {
            dprintf("DMA[M->M]: Adding event ...\n");
            status = alt_dma_program_DMASEV(program, evt);
        }
    }

    // Now that everything is done, end the program.
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAEND(program);
    }

    // If there was a problem assembling the program, clean up the buffer and exit.
    if (status != ALT_E_SUCCESS)
    {
        // Do not report the status for the clear operation. A failure should be
        // reported regardless of if the clear is successful.
        alt_dma_program_clear(program);
        return status;
    }

    // Execute the program on the given channel.
    return alt_dma_channel_exec(channel, program);
}

ALT_STATUS_CODE alt_dma_zero_to_memory(ALT_DMA_CHANNEL_t channel,
                                       ALT_DMA_PROGRAM_t * program,
                                       void * buf,
                                       size_t size,
                                       bool send_evt,
                                       ALT_DMA_EVENT_t evt)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // If the size is zero, and no event is requested, just return success.
    if ((size == 0) && (send_evt == false))
    {
        return status;
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_init(program);
    }

    if (size != 0)
    {
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR, (uint32_t)buf);
        }

        dprintf("DMA[Z->M]: buf  = %p.\n", buf);
        dprintf("DMA[Z->M]: size = 0x%x.\n", size);

        size_t sizeleft = size;

        // First see how many byte(s) we need to transfer to get dst to be 8 byte aligned.
        if ((uint32_t)buf & 0x7)
        {
            uint32_t aligncount = MIN(8 - ((uint32_t)buf & 0x7), sizeleft);
            sizeleft -= aligncount;

            dprintf("DMA[Z->M]: Total pre-alignment 1-byte burst size tranfer(s): %lu.\n", aligncount);

            // Program in the following parameters:
            //  - DS8 (Destination burst size of 1-byte)
            //  - DBx (Destination burst length of [aligncount] transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ALT_DMA_CCR_OPT_SB_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SS_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((aligncount - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DS8
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMASTZ(program);
            }
        }

        // This is the number of 8-byte bursts left
        uint32_t burstcount = sizeleft >> 3;

        // Update the size left to transfer
        sizeleft &= 0x7;

        dprintf("DMA[Z->M]: Total Main 8-byte burst size transfer(s): %lu.\n", burstcount);
        dprintf("DMA[Z->M]: Total Main 1-byte burst size transfer(s): %u.\n", sizeleft);

        // Determine how many 16 length bursts can be done
        if (burstcount >> 4)
        {
            uint32_t length16burstcount = burstcount >> 4;
            burstcount &= 0xf;

            dprintf("DMA[Z->M]:   Number of 16 burst length 8-byte transfer(s): %lu.\n", length16burstcount);
            dprintf("DMA[Z->M]:   Number of remaining 8-byte transfer(s):       %lu.\n", burstcount);

            // Program in the following parameters:
            //  - DS64 (Destination burst size of 8-byte)
            //  - DB16 (Destination burst length of 16 transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ALT_DMA_CCR_OPT_SB_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SS_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DB16
                                                  | ALT_DMA_CCR_OPT_DS64
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }

            while (length16burstcount > 0)
            {
                if (status != ALT_E_SUCCESS)
                {
                    break;
                }

                uint32_t loopcount = MIN(length16burstcount, 256);
                length16burstcount -= loopcount;

                dprintf("DMA[Z->M]:   Looping %lux 16 burst length 8-byte transfer(s).\n", loopcount);

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALP(program, loopcount);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMASTZ(program);
                }
                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
            }
        }

        // At this point, we should have [burstcount] 8-byte transfer(s)
        // remaining. [burstcount] should be less than 16.

        // Do one more burst with a SB / DB of length [burstcount].

        if (burstcount)
        {
            // Program in the following parameters:
            //  - DS64 (Destination burst size of 8-byte)
            //  - DBx  (Destination burst length of [burstlength] transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ALT_DMA_CCR_OPT_SB_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SS_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((burstcount - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DS64
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMASTZ(program);
            }
        }

        // At this point, there should be 0 - 7 1-byte transfers remaining.

        if (sizeleft)
        {
            dprintf("DMA[Z->M]: Total post 1-byte burst size tranfer(s): %u.\n", sizeleft);

            // Program in the following parameters:
            //  - DS8 (Destination burst size of 1-byte)
            //  - DBx (Destination burst length of [sizeleft] transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ALT_DMA_CCR_OPT_SB_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SS_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((sizeleft - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DS8
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMASTZ(program);
            }
        }
    } // if (size != 0)

    // Send event if requested.
    if (send_evt)
    {
        if (status == ALT_E_SUCCESS)
        {
            dprintf("DMA[Z->M]: Adding event ...\n");
            status = alt_dma_program_DMASEV(program, evt);
        }
    }

    // Now that everything is done, end the program.
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAEND(program);
    }

    // If there was a problem assembling the program, clean up the buffer and exit.
    if (status != ALT_E_SUCCESS)
    {
        // Do not report the status for the clear operation. A failure should be
        // reported regardless of if the clear is successful.
        alt_dma_program_clear(program);
        return status;
    }

    // Execute the program on the given channel.
    return alt_dma_channel_exec(channel, program);
}

ALT_STATUS_CODE alt_dma_memory_to_register(ALT_DMA_CHANNEL_t channel,
                                           ALT_DMA_PROGRAM_t * program,
                                           void * dst_reg,
                                           const void * src_buf,
                                           size_t count,
                                           uint32_t register_width_bits,
                                           bool send_evt,
                                           ALT_DMA_EVENT_t evt)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // If the count is zero, and no event is requested, just return success.
    if ((count == 0) && (send_evt == false))
    {
        return status;
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_init(program);
    }

    if (count != 0)
    {
        // Verify valid register_width_bits and construct the CCR SS and DS parameters.
        uint32_t ccr_ss_ds_mask = 0;

        if (status == ALT_E_SUCCESS)
        {
            switch (register_width_bits)
            {
            case 8:
                // Program in the following parameters:
                //  - SS8 (Source      burst size of 8 bits)
                //  - DS8 (Destination burst size of 8 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS8 | ALT_DMA_CCR_OPT_DS8;
                break;
            case 16:
                // Program in the following parameters:
                //  - SS16 (Source      burst size of 16 bits)
                //  - DS16 (Destination burst size of 16 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS16 | ALT_DMA_CCR_OPT_DS16;
                break;
            case 32:
                // Program in the following parameters:
                //  - SS32 (Source      burst size of 32 bits)
                //  - DS32 (Destination burst size of 32 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS32 | ALT_DMA_CCR_OPT_DS32;
                break;
            case 64:
                // Program in the following parameters:
                //  - SS64 (Source      burst size of 64 bits)
                //  - DS64 (Destination burst size of 64 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS64 | ALT_DMA_CCR_OPT_DS64;
                break;
            default:
                status = ALT_E_BAD_ARG;
                break;
            }
        }

        // Verify that the dst_reg and src_buf are aligned to the register width
        if (status == ALT_E_SUCCESS)
        {
            if      (((uintptr_t)dst_reg & ((register_width_bits >> 3) - 1)) != 0)
            {
                status = ALT_E_BAD_ARG;
            }
            else if (((uintptr_t)src_buf & ((register_width_bits >> 3) - 1)) != 0)
            {
                status = ALT_E_BAD_ARG;
            }
            else
            {
                dprintf("DMA[M->R]: dst_reg = %p.\n",   dst_reg);
                dprintf("DMA[M->R]: src_buf = %p.\n",   src_buf);
                dprintf("DMA[M->R]: count   = 0x%x.\n", count);
            }
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_SAR, (uint32_t)src_buf);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR, (uint32_t)dst_reg);
        }

        // This is the remaining count left to process.
        uint32_t countleft = count;

        // See how many 16-length bursts we can use
        if (countleft >> 4)
        {
            // Program in the following parameters:
            //  - SSx  (Source      burst size of [ccr_ss_ds_mask])
            //  - DSx  (Destination burst size of [ccr_ss_ds_mask])
            //  - DAF  (Destination address fixed)
            //  - SB16 (Source      burst length of 16 transfers)
            //  - DB16 (Destination burst length of 16 transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ccr_ss_ds_mask
                                                  | ALT_DMA_CCR_OPT_SB16
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DB16
                                                  | ALT_DMA_CCR_OPT_DAF
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }

            uint32_t length16burst = countleft >> 4;
            countleft &= 0xf;

            dprintf("DMA[M->R]:   Number of 16 burst length transfer(s): %lu.\n", length16burst);
            dprintf("DMA[M->R]:   Number of remaining transfer(s):       %lu.\n", countleft);

            // See how many 256x 16-length bursts we can use
            if (length16burst >> 8)
            {
                uint32_t loop256length16burst = length16burst >> 8;
                length16burst &= ((1 << 8) - 1);

                dprintf("DMA[M->R]:     Number of 256-looped 16 burst length transfer(s): %lu.\n", loop256length16burst);
                dprintf("DMA[M->R]:     Number of remaining 16 burst length transfer(s):  %lu.\n", length16burst);

                while (loop256length16burst > 0)
                {
                    if (status != ALT_E_SUCCESS)
                    {
                        break;
                    }

                    uint32_t loopcount = MIN(loop256length16burst, 256);
                    loop256length16burst -= loopcount;

                    dprintf("DMA[M->R]:     Looping %lux super loop transfer(s).\n", loopcount);

                    if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                    {
                        status = alt_dma_program_DMALP(program, loopcount);
                    }

                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALP(program, 256);
                    }
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }

                    if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                    {
                        status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }
                }
            }

            // The super loop above ensures that the length16burst is below 256.
            if (length16burst > 0)
            {
                uint32_t loopcount = length16burst;
                length16burst = 0;

                dprintf("DMA[M->R]:   Looping %lux 16 burst length transfer(s).\n", loopcount);

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALP(program, loopcount);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
            }
        }

        // At this point, we should have [countleft] transfer(s) remaining.
        // [countleft] should be less than 16.

        if (countleft)
        {
            // Program in the following parameters:
            //  - SSx (Source      burst size of [ccr_ss_ds_mask])
            //  - DSx (Destination burst size of [ccr_ss_ds_mask])
            //  - DAF (Destination address fixed)
            //  - SBx (Source      burst length of [countleft] transfer(s))
            //  - DBx (Destination burst length of [countleft] transfer(s))
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                dprintf("DMA[M->R]:   Tail end %lux transfer(s).\n", countleft);

                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ccr_ss_ds_mask
                                                  | ((countleft - 1) << 4) // SB
                                                  | ALT_DMA_CCR_OPT_SA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((countleft - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DAF
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }

    } // if (count != 0)

    // Send event if requested.
    if (send_evt)
    {
        if (status == ALT_E_SUCCESS)
        {
            dprintf("DMA[M->R]: Adding event ...\n");
            status = alt_dma_program_DMASEV(program, evt);
        }
    }

    // Now that everything is done, end the program.
    if (status == ALT_E_SUCCESS)
    {
        dprintf("DMA[M->R]: DMAEND program.\n");
        status = alt_dma_program_DMAEND(program);
    }

    // If there was a problem assembling the program, clean up the buffer and exit.
    if (status != ALT_E_SUCCESS)
    {
        // Do not report the status for the clear operation. A failure should be
        // reported regardless of if the clear is successful.
        alt_dma_program_clear(program);
        return status;
    }

    // Execute the program on the given channel.
    return alt_dma_channel_exec(channel, program);
}

ALT_STATUS_CODE alt_dma_register_to_memory(ALT_DMA_CHANNEL_t channel,
                                           ALT_DMA_PROGRAM_t * program,
                                           void * dst_buf,
                                           const void * src_reg,
                                           size_t count,
                                           uint32_t register_width_bits,
                                           bool send_evt,
                                           ALT_DMA_EVENT_t evt)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // If the count is zero, and no event is requested, just return success.
    if ((count == 0) && (send_evt == false))
    {
        return status;
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_init(program);
    }

    if (count != 0)
    {
        // Verify valid register_width_bits and construct the CCR SS and DS parameters.
        uint32_t ccr_ss_ds_mask = 0;

        if (status == ALT_E_SUCCESS)
        {
            switch (register_width_bits)
            {
            case 8:
                // Program in the following parameters:
                //  - SS8 (Source      burst size of 8 bits)
                //  - DS8 (Destination burst size of 8 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS8 | ALT_DMA_CCR_OPT_DS8;
                break;
            case 16:
                // Program in the following parameters:
                //  - SS16 (Source      burst size of 16 bits)
                //  - DS16 (Destination burst size of 16 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS16 | ALT_DMA_CCR_OPT_DS16;
                break;
            case 32:
                // Program in the following parameters:
                //  - SS32 (Source      burst size of 32 bits)
                //  - DS32 (Destination burst size of 32 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS32 | ALT_DMA_CCR_OPT_DS32;
                break;
            case 64:
                // Program in the following parameters:
                //  - SS64 (Source      burst size of 64 bits)
                //  - DS64 (Destination burst size of 64 bits)
                ccr_ss_ds_mask = ALT_DMA_CCR_OPT_SS64 | ALT_DMA_CCR_OPT_DS64;
                break;
            default:
                dprintf("DMA[R->M]: Invalid register width.\n");
                status = ALT_E_BAD_ARG;
                break;
            }
        }

        // Verify that the dst_buf and src_reg are aligned to the register width
        if (status == ALT_E_SUCCESS)
        {
            if      (((uintptr_t)dst_buf & ((register_width_bits >> 3) - 1)) != 0)
            {
                status = ALT_E_BAD_ARG;
            }
            else if (((uintptr_t)src_reg & ((register_width_bits >> 3) - 1)) != 0)
            {
                status = ALT_E_BAD_ARG;
            }
            else
            {
                dprintf("DMA[R->M]: dst_reg = %p.\n",   dst_buf);
                dprintf("DMA[R->M]: src_buf = %p.\n",   src_reg);
                dprintf("DMA[R->M]: count   = 0x%x.\n", count);
            }
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_SAR, (uint32_t)src_reg);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR, (uint32_t)dst_buf);
        }

        // This is the remaining count left to process.
        uint32_t countleft = count;

        // See how many 16-length bursts we can use
        if (countleft >> 4)
        {
            uint32_t length16burst = countleft >> 4;
            countleft &= 0xf;

            dprintf("DMA[R->M]:   Number of 16 burst length transfer(s): %lu.\n", length16burst);
            dprintf("DMA[R->M]:   Number of remaining transfer(s):       %lu.\n", countleft);

            //
            // The algorithm uses the strategy described in PL330 B.2.3.
            // Not sure if registers will accept burst transfers so read the register in its own transfer.
            //

            // Program in the following parameters:
            //  - SAF  (Source      address fixed)
            //  - SSx  (Source      burst size of [ccr_ss_ds_mask])
            //  - DSx  (Destination burst size of [ccr_ss_ds_mask])
            //  - SB16 (Source      burst length of 16 transfers)
            //  - DB16 (Destination burst length of 16 transfers)
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ccr_ss_ds_mask
                                                  | ALT_DMA_CCR_OPT_SB16
                                                  | ALT_DMA_CCR_OPT_SAF
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DB16
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }

            // See how many 256x 16-length bursts we can do
            if (length16burst >> 8)
            {
                uint32_t loop256length16burst = length16burst >> 8;
                length16burst &= ((1 << 8) - 1);

                dprintf("DMA[R->M]:     Number of 256-looped 16 burst length transfer(s): %lu.\n", loop256length16burst);
                dprintf("DMA[R->M]:     Number of remaining 16 burst length transfer(s):  %lu.\n", length16burst);

                while (loop256length16burst > 0)
                {
                    if (status != ALT_E_SUCCESS)
                    {
                        break;
                    }

                    uint32_t loopcount = MIN(loop256length16burst, 256);
                    loop256length16burst -= loopcount;

                    dprintf("DMA[R->M]:     Looping %lux super loop transfer(s).\n", loopcount);

                    if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                    {
                        status = alt_dma_program_DMALP(program, loopcount);
                    }

                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALP(program, 256);
                    }
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }

                    if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                    {
                        status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                    }
                }
            }

            // The super loop above ensures that the length16burst is below 256.
            if (length16burst > 0)
            {
                uint32_t loopcount = length16burst;
                length16burst = 0;

                dprintf("DMA[R->M]:   Looping %lux 16 burst length transfer(s).\n", loopcount);

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALP(program, loopcount);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }
            }
        }

        // At this point, we should have [countleft] transfer(s) remaining.
        // [countleft] should be less than 16.

        if (countleft)
        {
            dprintf("DMA[R->M]:   Tail end %lux transfer(s).\n", countleft);

            // Program in the following parameters:
            //  - SAF (Source      address fixed)
            //  - SSx (Source      burst size of [ccr_ss_ds_mask])
            //  - DSx (Destination burst size of [ccr_ss_ds_mask])
            //  - SBx (Source      burst length of [countleft] transfer(s))
            //  - DBx (Destination burst length of [countleft] transfer(s))
            //  - All other options default.

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                                (   ccr_ss_ds_mask
                                                  | ((countleft - 1) << 4) // SB
                                                  | ALT_DMA_CCR_OPT_SAF
                                                  | ALT_DMA_CCR_OPT_SP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_SC_DEFAULT
                                                  | ((countleft - 1) << 18) // DB
                                                  | ALT_DMA_CCR_OPT_DA_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DP_DEFAULT
                                                  | ALT_DMA_CCR_OPT_DC_DEFAULT
                                                  | ALT_DMA_CCR_OPT_ES_DEFAULT
                                                )
                    );
            }

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }

    } // if (count != 0)

    // Send event if requested.
    if (send_evt)
    {
        if (status == ALT_E_SUCCESS)
        {
            dprintf("DMA[R->M]: Adding event ...\n");
            status = alt_dma_program_DMASEV(program, evt);
        }
    }

    // Now that everything is done, end the program.
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAEND(program);
    }

    // If there was a problem assembling the program, clean up the buffer and exit.
    if (status != ALT_E_SUCCESS)
    {
        // Do not report the status for the clear operation. A failure should be
        // reported regardless of if the clear is successful.
        alt_dma_program_clear(program);
        return status;
    }

    // Execute the program on the given channel.
    return alt_dma_channel_exec(channel, program);
}

#if ALT_DMA_PERIPH_PROVISION_QSPI_SUPPORT
static ALT_STATUS_CODE alt_dma_memory_to_qspi(ALT_DMA_PROGRAM_t * program,
                                              const char * src,
                                              size_t size)
{
    if ((uintptr_t)src & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (size & 0x3)
    {
        return ALT_E_ERROR;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR,
                                        (uint32_t)ALT_QSPIDATA_ADDR);
    }
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_SAR,
                                        (uint32_t)src);
    }

    /////

    uint32_t dmaper = alt_read_word(ALT_QSPI_DMAPER_ADDR);
    uint32_t qspi_single_size_log2 = ALT_QSPI_DMAPER_NUMSGLREQBYTES_GET(dmaper);
    uint32_t qspi_burst_size_log2  = ALT_QSPI_DMAPER_NUMBURSTREQBYTES_GET(dmaper);
    uint32_t qspi_single_size      = 1 << qspi_single_size_log2;
    uint32_t qspi_burst_size       = 1 << qspi_burst_size_log2;

    dprintf("DMA[M->P][QSPI]: QSPI Single = %lu; Burst = %lu.\n", qspi_single_size, qspi_burst_size);

    // Because single transfers are equal or smaller than burst (and in the
    // smaller case, it is always a clean multiple), only the single size
    // check is needed for transfer composability.
    if (size & (qspi_single_size - 1))
    {
        dprintf("DMA[M->P][QSPI]: QSPI DMA size configuration not suitable for transfer request.\n");
        return ALT_E_ERROR;
    }

    /////

    if ((uintptr_t)src & 0x7)
    {
        // Source address is not 8-byte aligned. Do 1x 32-bit transfer to get it 8-byte aligned.

        dprintf("DMA[M->P][QSPI]: Creating 1x 4-byte aligning transfer.\n");

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                            (   ALT_DMA_CCR_OPT_SAI
                                              | ALT_DMA_CCR_OPT_SS32
                                              | ALT_DMA_CCR_OPT_SB1
                                              | ALT_DMA_CCR_OPT_SP_DEFAULT
                                              | ALT_DMA_CCR_OPT_SC_DEFAULT
                                              | ALT_DMA_CCR_OPT_DAF
                                              | ALT_DMA_CCR_OPT_DS32
                                              | ALT_DMA_CCR_OPT_DB1
                                              | ALT_DMA_CCR_OPT_DP_DEFAULT
                                              | ALT_DMA_CCR_OPT_DC_DEFAULT
                                              | ALT_DMA_CCR_OPT_ES_DEFAULT
                                            )
                );
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_TX);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_TX, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }

        size -= sizeof(uint32_t);
    }

    uint32_t qspi_single_count = 0;
    uint32_t qspi_burst_count  = size >> qspi_burst_size_log2;

    // Use QSPI burst transfers if:
    //  - QSPI bursts are larger than QSPI singles [AND]
    //  - Size is large enough that at least 1 burst will be used.

    if (   (qspi_burst_size_log2 > qspi_single_size_log2)
        && (qspi_burst_count != 0)
       )
    {
        // qspi_burst_count = size >> qspi_burst_size_log2;
        qspi_single_count   = (size & (qspi_burst_size - 1)) >> qspi_single_size_log2;

        dprintf("DMA[M->P][QSPI][B]: Burst size = %lu bytes, count = %lu.\n", qspi_burst_size, qspi_burst_count);

        // 1 << 3 => 8 bytes => 64 bits, which is the width of the AXI bus.
        uint32_t src_size_log2 = MIN(3, qspi_burst_size_log2);

        uint32_t src_length   = 0;
        uint32_t src_multiple = 0;

        if ((qspi_burst_size >> src_size_log2) <= 16)
        {
            src_length   = qspi_burst_size >> src_size_log2;
            src_multiple = 1;
        }
        else
        {
            src_length   = 16;
            src_multiple = (qspi_burst_size >> src_size_log2) >> 4; // divide by 16

            if (src_multiple == 0)
            {
                dprintf("DEBUG[QSPI][B]: src_multiple is 0.\n");
                status = ALT_E_ERROR;
            }
        }

        // uint32_t dst_length = 1; // dst_length is always 1 because the address is fixed.
        uint32_t dst_multiple = qspi_burst_size >> 2; // divide by sizeof(uint32_t)

        dprintf("DMA[M->P][QSPI][B]: dst_size = %u bits, dst_length = %u, dst_multiple = %lu.\n",
                32,                       1,          dst_multiple);
        dprintf("DMA[M->P][QSPI][B]: src_size = %u bits, src_length = %lu, src_multiple = %lu.\n",
                (1 << src_size_log2) * 8, src_length, src_multiple);

        /////

        // Program in the following parameters:
        //  - SAI  (Source      address increment)
        //  - SSx  (Source      burst size of [1 << src_size_log2]-bytes)
        //  - SBx  (Source      burst length of [src_length] transfer(s))
        //  - DAF  (Destination address fixed)
        //  - DS32 (Destination burst size of 4-bytes)
        //  - DB1  (Destination burst length of 1 transfer)
        //  - All other parameters default

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                            (   ALT_DMA_CCR_OPT_SAI
                                              | (src_size_log2 << 1) // SS
                                              | ((src_length - 1) << 4) // SB
                                              | ALT_DMA_CCR_OPT_SP_DEFAULT
                                              | ALT_DMA_CCR_OPT_SC_DEFAULT
                                              | ALT_DMA_CCR_OPT_DAF
                                              | ALT_DMA_CCR_OPT_DS32
                                              | ALT_DMA_CCR_OPT_DB1
                                              | ALT_DMA_CCR_OPT_DP_DEFAULT
                                              | ALT_DMA_CCR_OPT_DC_DEFAULT
                                              | ALT_DMA_CCR_OPT_ES_DEFAULT
                                            )
                );
        }

        // NOTE: We do not do the 256x bursts for M->P case because we only
        //   write up to 256 B at a time.

        while (qspi_burst_count > 0)
        {
            if (status != ALT_E_SUCCESS)
            {
                break;
            }

            uint32_t loopcount = MIN(qspi_burst_count, 256);
            qspi_burst_count -= loopcount;

            dprintf("DMA[M->P][QSPI][B]: Creating %lu burst-type transfer(s).\n", loopcount);

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALP(program, loopcount);
            }

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_TX);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_TX, ALT_DMA_PROGRAM_INST_MOD_BURST);
            }
            for (uint32_t j = 0; j < src_multiple; ++j)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
                }
            }
            for (uint32_t k = 0; k < dst_multiple; ++k)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
                }
            }

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }
    }
    else
    {
        qspi_single_count = size >> qspi_single_size_log2;
    }

    // Assemble the single portion of the DMA program.
    if (qspi_single_count)
    {
        dprintf("DMA[M->P][QSPI][S]: Single size = %lu bytes, count = %lu.\n", qspi_single_size, qspi_single_count);

        // 1 << 3 => 8 bytes => 64 bits, which is the width of the AXI bus.
        uint32_t src_size_log2 = MIN(3, qspi_single_size_log2);

        uint32_t src_length   = 0;
        uint32_t src_multiple = 0;

        if ((qspi_single_size >> src_size_log2) <= 16)
        {
            src_length   = qspi_single_size >> src_size_log2;
            src_multiple = 1;
        }
        else
        {
            src_length   = 16;
            src_multiple = (qspi_single_size >> src_size_log2) >> 4; // divide by 16

            if (src_multiple == 0)
            {
                dprintf("DEBUG[QSPI][S]: src_multiple is 0.\n");
                status = ALT_E_ERROR;
            }
        }

        // uint32_t dst_length = 1; // dst_length is always 1 becaus the address is fixed.
        uint32_t dst_multiple = qspi_single_size >> 2; // divide by sizeof(uint32_t)

        dprintf("DMA[M->P][QSPI][S]: dst_size = %u bits, dst_length = %u, dst_multiple = %lu.\n",
                32,                      1,          dst_multiple);
        dprintf("DMA[M->P][QSPI][S]: src_size = %u bits, src_length = %lu, src_multiple = %lu.\n",
                (1 <<src_size_log2) * 8, src_length, src_multiple);

        /////

        // Program in the following parameters:
        //  - SAI  (Source      address increment)
        //  - SSx  (Source      burst size of [1 << src_size_log2]-bytes)
        //  - SBx  (Source      burst length of [src_length] transfer(s))
        //  - DAF  (Destination address fixed)
        //  - DS32 (Destination burst size of 4-bytes)
        //  - DB1  (Destination burst length of 1 transfer)
        //  - All other parameters default

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                            (   ALT_DMA_CCR_OPT_SAI
                                              | (src_size_log2 << 1) // SS
                                              | ((src_length - 1) << 4) // SB
                                              | ALT_DMA_CCR_OPT_SP_DEFAULT
                                              | ALT_DMA_CCR_OPT_SC_DEFAULT
                                              | ALT_DMA_CCR_OPT_DAF
                                              | ALT_DMA_CCR_OPT_DS32
                                              | ALT_DMA_CCR_OPT_DB1
                                              | ALT_DMA_CCR_OPT_DP_DEFAULT
                                              | ALT_DMA_CCR_OPT_DC_DEFAULT
                                              | ALT_DMA_CCR_OPT_ES_DEFAULT
                                            )
                );
        }

        // NOTE: We do not do the 256x bursts for M->P case because we only
        //   write up to 256 B at a time.

        while (qspi_single_count > 0)
        {
            if (status != ALT_E_SUCCESS)
            {
                break;
            }

            uint32_t loopcount = MIN(qspi_single_count, 256);
            qspi_single_count -= loopcount;

            dprintf("DMA[M->P][QSPI][S]: Creating %lu single-type transfer(s).\n", loopcount);

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALP(program, loopcount);
            }

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_TX);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_TX, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
            }
            for (uint32_t j = 0; j < src_multiple; ++j)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
                }
            }
            for (uint32_t k = 0; k < dst_multiple; ++k)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
                }
            }

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }

    } // if (qspi_single_count != 0)

    return status;
}

static ALT_STATUS_CODE alt_dma_qspi_to_memory(ALT_DMA_PROGRAM_t * program,
                                              char * dst,
                                              size_t size)
{
    if ((uintptr_t)dst & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (size & 0x3)
    {
        return ALT_E_ERROR;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR,
                                        (uint32_t)dst);
    }
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_SAR,
                                        (uint32_t)ALT_QSPIDATA_ADDR);
    }

    /////

    uint32_t dmaper = alt_read_word(ALT_QSPI_DMAPER_ADDR);
    uint32_t qspi_single_size_log2 = ALT_QSPI_DMAPER_NUMSGLREQBYTES_GET(dmaper);
    uint32_t qspi_burst_size_log2  = ALT_QSPI_DMAPER_NUMBURSTREQBYTES_GET(dmaper);
    uint32_t qspi_single_size      = 1 << qspi_single_size_log2;
    uint32_t qspi_burst_size       = 1 << qspi_burst_size_log2;

    dprintf("DMA[P->M][QSPI]: QSPI Single = %lu; Burst = %lu.\n", qspi_single_size, qspi_burst_size);

    // Because single transfers are equal or smaller than burst (and in the
    // smaller case, it is always a clean multiple), only the single size
    // check is needed for transfer composability.
    if (size & (qspi_single_size - 1))
    {
        dprintf("DMA[P->M][QSPI]: QSPI DMA size configuration not suitable for transfer request.\n");
        return ALT_E_ERROR;
    }

    /////

    if ((uintptr_t)dst & 0x7)
    {
        // Destination address is not 8-byte aligned. Do 1x 32-bit transfer to get it 8-byte aligned.

        dprintf("DMA[P->M][QSPI]: Creating 1x 4-byte aligning transfer.\n");

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                            (   ALT_DMA_CCR_OPT_SAF
                                              | ALT_DMA_CCR_OPT_SS32
                                              | ALT_DMA_CCR_OPT_SB1
                                              | ALT_DMA_CCR_OPT_SP_DEFAULT
                                              | ALT_DMA_CCR_OPT_SC_DEFAULT
                                              | ALT_DMA_CCR_OPT_DAI
                                              | ALT_DMA_CCR_OPT_DS32
                                              | ALT_DMA_CCR_OPT_DB1
                                              | ALT_DMA_CCR_OPT_DP_DEFAULT
                                              | ALT_DMA_CCR_OPT_DC_DEFAULT
                                              | ALT_DMA_CCR_OPT_ES_DEFAULT
                                            )
                );
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }

        size -= sizeof(uint32_t);
    }

    uint32_t qspi_single_count = 0;
    uint32_t qspi_burst_count  = size >> qspi_burst_size_log2;

    // Use QSPI burst transfers if:
    //  - QSPI bursts are larger than QSPI singles [AND]
    //  - Size is large enough that at least 1 burst will be used.

    if (   (qspi_burst_size_log2 > qspi_single_size_log2)
        && (qspi_burst_count != 0)
       )
    {
        // qspi_burst_count = size >> qspi_burst_size_log2;
        qspi_single_count   = (size & (qspi_burst_size - 1)) >> qspi_single_size_log2;

        dprintf("DMA[P->M][QSPI][B]: Burst size = %lu bytes, count = %lu.\n", qspi_burst_size, qspi_burst_count);

        // 1 << 3 => 8 bytes => 64 bits, which is the width of the AXI bus.
        uint32_t dst_size_log2 = MIN(3, qspi_burst_size_log2);

        uint32_t dst_length   = 0;
        uint32_t dst_multiple = 0;

        if ((qspi_burst_size >> dst_size_log2) <= 16)
        {
            dst_length   = qspi_burst_size >> dst_size_log2;
            dst_multiple = 1;
        }
        else
        {
            dst_length   = 16;
            dst_multiple = (qspi_burst_size >> dst_size_log2) >> 4; // divide by 16

            if (dst_multiple == 0)
            {
                dprintf("DEBUG[QSPI][B]: dst_multiple is 0.\n");
                status = ALT_E_ERROR;
            }
        }

        // uint32_t src_length = 1; // src_length is always 1 because the address is fixed.
        uint32_t src_multiple = qspi_burst_size >> 2; // divide by sizeof(uint32_t)

        dprintf("DMA[P->M][QSPI][B]: dst_size = %u bits, dst_length = %lu, dst_multiple = %lu.\n", 
                (1 << dst_size_log2) * 8, dst_length, dst_multiple);
        dprintf("DMA[P->M][QSPI][B]: src_size = %u bits, src_length = %u, src_multiple = %lu.\n",
                32,                       1,          src_multiple);

        /////

        // Program in the following parameters:
        //  - SAF  (Source      address fixed)
        //  - SS32 (Source      burst size of 4-bytes)
        //  - SB1  (Source      burst length of 1 transfer)
        //  - DAI  (Destination address increment)
        //  - DSx  (Destination burst size of [1 << dst_size_log2]-bytes])
        //  - DBx  (Destination burst length of [dst_length] transfer(s))
        //  - All other parameters default

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                            (   ALT_DMA_CCR_OPT_SAF
                                              | ALT_DMA_CCR_OPT_SS32
                                              | ALT_DMA_CCR_OPT_SB1
                                              | ALT_DMA_CCR_OPT_SP_DEFAULT
                                              | ALT_DMA_CCR_OPT_SC_DEFAULT
                                              | ALT_DMA_CCR_OPT_DAI
                                              | (dst_size_log2 << 15) // DS
                                              | ((dst_length - 1) << 18) // DB
                                              | ALT_DMA_CCR_OPT_DP_DEFAULT
                                              | ALT_DMA_CCR_OPT_DC_DEFAULT
                                              | ALT_DMA_CCR_OPT_ES_DEFAULT
                                            )
                );
        }

        // See how many 256x bursts we can construct. This will allow for extremely large requests.

        if (qspi_burst_count >> 8)
        {
            uint32_t qspi_burst256_count = qspi_burst_count >> 8;
            qspi_burst_count &= (1 << 8) - 1;

            while (qspi_burst256_count > 0)
            {
                if (status != ALT_E_SUCCESS)
                {
                    break;
                }

                uint32_t loopcount = MIN(qspi_burst256_count, 256);
                qspi_burst256_count -= loopcount;

                dprintf("DMA[P->M][QSPI][B]: Creating %lu 256x burst-type transfer(s).\n", loopcount);

                // Outer loop {

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALP(program, loopcount);
                }

                // Inner loop {

                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALP(program, 256);
                }

                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX, ALT_DMA_PROGRAM_INST_MOD_BURST);
                }
                for (uint32_t j = 0; j < src_multiple; ++j)
                {
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
                    }
                }
                for (uint32_t k = 0; k < dst_multiple; ++k)
                {
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
                    }
                }

                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }

                // } Inner loop

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }

                // } Outer loop
            }
        }

        while (qspi_burst_count > 0)
        {
            if (status != ALT_E_SUCCESS)
            {
                break;
            }

            uint32_t loopcount = MIN(qspi_burst_count, 256);
            qspi_burst_count -= loopcount;

            dprintf("DMA[P->M][QSPI][B]: Creating %lu burst-type transfer(s).\n", loopcount);

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALP(program, loopcount);
            }

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX, ALT_DMA_PROGRAM_INST_MOD_BURST);
            }
            for (uint32_t j = 0; j < src_multiple; ++j)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
                }
            }
            for (uint32_t k = 0; k < dst_multiple; ++k)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
                }
            }

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }
    }
    else
    {
        qspi_single_count = size >> qspi_single_size_log2;
    }

    // Assemble the single portion of the DMA program.
    if (qspi_single_count)
    {
        dprintf("DMA[P->M][QSPI][S]: Single size = %lu bytes, count = %lu.\n", qspi_single_size, qspi_single_count);

        // 1 << 3 => 8 bytes => 64 bits, which is the width of the AXI bus.
        uint32_t dst_size_log2 = MIN(3, qspi_single_size_log2);

        uint32_t dst_length   = 0;
        uint32_t dst_multiple = 0;

        if ((qspi_single_size >> dst_size_log2) <= 16)
        {
            dst_length   = qspi_single_size >> dst_size_log2;
            dst_multiple = 1;
        }
        else
        {
            dst_length   = 16;
            dst_multiple = (qspi_single_size >> dst_size_log2) >> 4; // divide by 16

            if (dst_multiple == 0)
            {
                dprintf("DEBUG[QSPI][S]: dst_multiple is 0.\n");
                status = ALT_E_ERROR;
            }
        }

        // uint32_t src_length = 1; // src_length is always 1 because the address is fixed.
        uint32_t src_multiple = qspi_single_size >> 2; // divide by sizeof(uint32_t)

        dprintf("DMA[P->M][QSPI][S]: dst_size = %u bits, dst_length = %lu, dst_multiple = %lu.\n",
                (1 << dst_size_log2) * 8, dst_length, dst_multiple);
        dprintf("DMA[P->M][QSPI][S]: src_size = %u bits, src_length = %u, src_multiple = %lu.\n",
                32,                       1,          src_multiple);

        /////

        // Program in the following parameters:
        //  - SAF  (Source      address fixed)
        //  - SS32 (Source      burst size of 4-bytes)
        //  - SB1  (Source      burst length of 1 transfer)
        //  - DAI  (Destination address increment)
        //  - DSx  (Destination burst size of [1 << dst_size_log2]-bytes])
        //  - DBx  (Destination burst length of [dst_length] transfer(s))
        //  - All other parameters default

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                            (   ALT_DMA_CCR_OPT_SAF
                                              | ALT_DMA_CCR_OPT_SS32
                                              | ALT_DMA_CCR_OPT_SB1
                                              | ALT_DMA_CCR_OPT_SP_DEFAULT
                                              | ALT_DMA_CCR_OPT_SC_DEFAULT
                                              | ALT_DMA_CCR_OPT_DAI
                                              | (dst_size_log2 << 15) // DS
                                              | ((dst_length - 1) << 18) // DB
                                              | ALT_DMA_CCR_OPT_DP_DEFAULT
                                              | ALT_DMA_CCR_OPT_DC_DEFAULT
                                              | ALT_DMA_CCR_OPT_ES_DEFAULT
                                            )
                );
        }

        // See how many 256x bursts we can construct. This will allow for extremely large requests.

        if (qspi_single_count >> 8)
        {
            uint32_t qspi_single256_count = qspi_single_count >> 8;
            qspi_single_count &= (1 << 8) - 1;

            while (qspi_single256_count > 0)
            {
                if (status != ALT_E_SUCCESS)
                {
                    break;
                }

                uint32_t loopcount = MIN(qspi_single256_count, 256);
                qspi_single256_count -= loopcount;

                dprintf("DMA[P->M][QSPI][S]: Creating %lu 256x single-type transfer(s).\n", loopcount);

                // Outer loop {

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALP(program, loopcount);
                }

                // Inner loop {

                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALP(program, 256);
                }

                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX);
                }
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
                }
                for (uint32_t j = 0; j < src_multiple; ++j)
                {
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
                    }
                }
                for (uint32_t k = 0; k < dst_multiple; ++k)
                {
                    if (status == ALT_E_SUCCESS)
                    {
                        status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
                    }
                }

                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }

                // } Inner loop

                if ((status == ALT_E_SUCCESS) && (loopcount > 1))
                {
                    status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
                }

                // } Outer loop
            }
        }

        while (qspi_single_count > 0)
        {
            if (status != ALT_E_SUCCESS)
            {
                break;
            }

            uint32_t loopcount = MIN(qspi_single_count, 256);
            qspi_single_count -= loopcount;

            dprintf("DMA[P->M][QSPI][S]: Creating %lu single-type transfer(s).\n", loopcount);

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALP(program, loopcount);
            }

            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAFLUSHP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX);
            }
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_program_DMAWFP(program, ALT_DMA_PERIPH_QSPI_FLASH_RX, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
            }
            for (uint32_t j = 0; j < src_multiple; ++j)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
                }
            }
            for (uint32_t k = 0; k < dst_multiple; ++k)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
                }
            }

            if ((status == ALT_E_SUCCESS) && (loopcount > 1))
            {
                status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_NONE);
            }
        }

    } // if (qspi_single_count != 0)

    return status;
}
#endif // ALT_DMA_PERIPH_PROVISION_QSPI_SUPPORT

#if ALT_DMA_PERIPH_PROVISION_16550_SUPPORT
static ALT_STATUS_CODE alt_dma_memory_to_16550_single(ALT_DMA_PROGRAM_t * program,
                                                      ALT_DMA_PERIPH_t periph,
                                                      size_t size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Program in the following parameters:
    //  - SS8 (Source      burst size of 1-byte)
    //  - DS8 (Destination burst size of 1-byte)
    //  - SB1 (Source      burst length of 1 transfer)
    //  - DB1 (Destination burst length of 1 transfer)
    //  - DAF (Destination address fixed)
    //  - All other options default.

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                        (   ALT_DMA_CCR_OPT_SB1
                                          | ALT_DMA_CCR_OPT_SS8
                                          | ALT_DMA_CCR_OPT_SA_DEFAULT
                                          | ALT_DMA_CCR_OPT_SP_DEFAULT
                                          | ALT_DMA_CCR_OPT_SC_DEFAULT
                                          | ALT_DMA_CCR_OPT_DB1
                                          | ALT_DMA_CCR_OPT_DS8
                                          | ALT_DMA_CCR_OPT_DAF
                                          | ALT_DMA_CCR_OPT_DP_DEFAULT
                                          | ALT_DMA_CCR_OPT_DC_DEFAULT
                                          | ALT_DMA_CCR_OPT_ES_DEFAULT
                                        )
            );
    }

    uint32_t sizeleft = size;

    while (sizeleft > 0)
    {
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        uint32_t loopcount = MIN(sizeleft, 256);
        sizeleft -= loopcount;

        dprintf("DMA[M->P][16550][S]: Creating %lu transfer(s).\n", loopcount);

        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALP(program, loopcount);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAFLUSHP(program, periph);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAWFP(program, periph, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }

        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }
    }

    return status;
}

static ALT_STATUS_CODE alt_dma_memory_to_16550_burst(ALT_DMA_PROGRAM_t * program,
                                                     ALT_DMA_PERIPH_t periph,
                                                     size_t burst_size,
                                                     size_t burst_count)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Program in the following parameters:
    //  - SS8  (Source      burst size of 1-byte)
    //  - DS8  (Destination burst size of 1-byte)
    //  - SB16 (Source      burst length of 16 transfers)
    //  - DB16 (Destination burst length of 16 transfers)
    //  - DAF  (Source      address fixed)
    //  - All other options default.

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                        (   ALT_DMA_CCR_OPT_SB16
                                          | ALT_DMA_CCR_OPT_SS8
                                          | ALT_DMA_CCR_OPT_SA_DEFAULT
                                          | ALT_DMA_CCR_OPT_SP_DEFAULT
                                          | ALT_DMA_CCR_OPT_SC_DEFAULT
                                          | ALT_DMA_CCR_OPT_DB16
                                          | ALT_DMA_CCR_OPT_DS8
                                          | ALT_DMA_CCR_OPT_DAF
                                          | ALT_DMA_CCR_OPT_DP_DEFAULT
                                          | ALT_DMA_CCR_OPT_DC_DEFAULT
                                          | ALT_DMA_CCR_OPT_ES_DEFAULT
                                        )
            );
    }

    while (burst_count > 0)
    {
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        uint32_t loopcount = MIN(burst_count, 256);
        burst_count -= loopcount;

        dprintf("DMA[M->P][16550][B]: Creating outer %lu inner loop(s).\n", loopcount);

        // Outer loop {

        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALP(program, loopcount);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAFLUSHP(program, periph);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAWFP(program, periph, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }

        // Inner loop {

        // Loop [burst_size / 16] times. The burst_size was trimmed to the
        // nearest multiple of 16 by the caller. Each burst does 16 transfers
        // hence the need for the divide.

        dprintf("DMA[M->P][16550][B]: Creating inner %u transfer(s).\n", burst_size >> 4);

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALP(program, burst_size >> 4); // divide by 16.
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }

        // } Inner loop

        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }

        // } Outer loop
    }

    return status;
}

static ALT_STATUS_CODE alt_dma_memory_to_16550(ALT_DMA_PROGRAM_t * program,
                                               ALT_DMA_PERIPH_t periph,
                                               ALT_16550_HANDLE_t * handle,
                                               const void * src,
                                               size_t size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR,
                                        (uint32_t)ALT_UART_RBR_THR_DLL_ADDR(handle->location));
    }
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_SAR,
                                        (uint32_t)src);
    }

    // Determine if FIFOs are enabled from the FCR cache

    if (ALT_UART_FCR_FIFOE_GET(handle->fcr) != 0)
    {
        dprintf("DMA[M->P][16550]: FIFOs enabled.\n");

        //
        // FIFOs are enabled.
        //

        uint32_t tx_size;
        uint32_t burst_size;
        ALT_16550_FIFO_TRIGGER_TX_t trig_tx;

        // Get the TX FIFO Size
        // Use the register interface to avoid coupling the 16550 and DMA.
        tx_size = ALT_UART_CPR_FIFO_MOD_GET(alt_read_word(ALT_UART_CPR_ADDR(handle->location))) << 4;

        // Get the TX FIFO Trigger Level from the FCR cache
        trig_tx = (ALT_16550_FIFO_TRIGGER_TX_t)ALT_UART_FCR_TET_GET(handle->fcr);

        switch (trig_tx)
        {
        case ALT_16550_FIFO_TRIGGER_TX_EMPTY:
            burst_size = tx_size;
            break;
        case ALT_16550_FIFO_TRIGGER_TX_ALMOST_EMPTY:
            burst_size = tx_size - 2;
            break;
        case ALT_16550_FIFO_TRIGGER_TX_QUARTER_FULL:
            burst_size = 3 * (tx_size >> 2);
            break;
        case ALT_16550_FIFO_TRIGGER_TX_HALF_FULL:
            burst_size = tx_size >> 1;
            break;
        default:
            // This case should never happen.
            return ALT_E_ERROR;
        }

        if (burst_size < 16)
        {
            // There's no point bursting 1 byte at a time per notify, so just do single transfers.
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_memory_to_16550_single(program,
                                                        periph,
                                                        size);
            }
        }
        else
        {
            uint32_t sizeleft = size;

            // Now trip the burst size to a multiple of 16.
            // This will optimize the bursting in the fewest possible commands.
            dprintf("DMA[M->P][16550]: Untrimmed burst size = %lu.\n", burst_size);
            burst_size &= ~0xf;
            dprintf("DMA[M->P][16550]: Trimmed burst size   = %lu.\n", burst_size);

            // Determine how many burst transfers can be done
            uint32_t burst_count = 0;

            burst_count = sizeleft / burst_size;
            sizeleft -= burst_count * burst_size;

            if (burst_count == 0)
            {
                // Do the transfer
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_memory_to_16550_single(program,
                                                            periph,
                                                            sizeleft);
                }
            }
            else
            {
                // Do the burst transfers
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_memory_to_16550_burst(program,
                                                           periph,
                                                           burst_size,
                                                           burst_count);
                }

                // Program the DMA engine to transfer the non-burstable items in single tranfers
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_memory_to_16550_single(program,
                                                            periph,
                                                            sizeleft);
                }

            } // else if (burst_count == 0)
        }
    }
    else
    {
        dprintf("DMA[M->P][16550]: FIFOs disabled.\n");

        //
        // FIFOs are disabled.
        //

        status = alt_dma_memory_to_16550_single(program,
                                                periph,
                                                size);
    }

    return status;
}

static ALT_STATUS_CODE alt_dma_16550_to_memory_single(ALT_DMA_PROGRAM_t * program,
                                                      ALT_DMA_PERIPH_t periph,
                                                      size_t size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Program in the following parameters:
    //  - SS8 (Source      burst size of 1-byte)
    //  - DS8 (Destination burst size of 1-byte)
    //  - SB1 (Source      burst length of 1 transfer)
    //  - DB1 (Destination burst length of 1 transfer)
    //  - SAF (Source      address fixed)
    //  - All other options default.

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                        (   ALT_DMA_CCR_OPT_SB1
                                          | ALT_DMA_CCR_OPT_SS8
                                          | ALT_DMA_CCR_OPT_SAF
                                          | ALT_DMA_CCR_OPT_SP_DEFAULT
                                          | ALT_DMA_CCR_OPT_SC_DEFAULT
                                          | ALT_DMA_CCR_OPT_DB1
                                          | ALT_DMA_CCR_OPT_DS8
                                          | ALT_DMA_CCR_OPT_DA_DEFAULT
                                          | ALT_DMA_CCR_OPT_DP_DEFAULT
                                          | ALT_DMA_CCR_OPT_DC_DEFAULT
                                          | ALT_DMA_CCR_OPT_ES_DEFAULT
                                        )
            );
    }

    uint32_t sizeleft = size;

    while (sizeleft > 0)
    {
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        uint32_t loopcount = MIN(sizeleft, 256);
        sizeleft -= loopcount;

        dprintf("DMA[P->M][16550][S]: Creating %lu transfer(s).\n", loopcount);

        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALP(program, loopcount);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAFLUSHP(program, periph);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAWFP(program, periph, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }
        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_SINGLE);
        }
    }

    return status;
}                                              

static ALT_STATUS_CODE alt_dma_16550_to_memory_burst(ALT_DMA_PROGRAM_t * program,
                                                     ALT_DMA_PERIPH_t periph,
                                                     size_t burst_size,
                                                     size_t burst_count)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Program in the following parameters:
    //  - SS8  (Source      burst size of 1-byte)
    //  - DS8  (Destination burst size of 1-byte)
    //  - SB16 (Source      burst length of 16 transfers)
    //  - DB16 (Destination burst length of 16 transfers)
    //  - SAF  (Source      address fixed)
    //  - All other options default.

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_CCR,
                                        (   ALT_DMA_CCR_OPT_SB16
                                          | ALT_DMA_CCR_OPT_SS8
                                          | ALT_DMA_CCR_OPT_SAF
                                          | ALT_DMA_CCR_OPT_SP_DEFAULT
                                          | ALT_DMA_CCR_OPT_SC_DEFAULT
                                          | ALT_DMA_CCR_OPT_DB16
                                          | ALT_DMA_CCR_OPT_DS8
                                          | ALT_DMA_CCR_OPT_DA_DEFAULT
                                          | ALT_DMA_CCR_OPT_DP_DEFAULT
                                          | ALT_DMA_CCR_OPT_DC_DEFAULT
                                          | ALT_DMA_CCR_OPT_ES_DEFAULT
                                        )
            );
    }

    while (burst_count > 0)
    {
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        uint32_t loopcount = MIN(burst_count, 256);
        burst_count -= loopcount;

        dprintf("DMA[P->M][16550][B]: Creating outer %lu inner loop(s).\n", loopcount);

        // Outer loop {

        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALP(program, loopcount);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAFLUSHP(program, periph);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAWFP(program, periph, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }

        // Inner loop {

        // Loop [burst_size / 16] times. The burst_size was trimmed to the
        // nearest multiple of 16 by the caller. Each burst does 16 transfers
        // hence the need for the divide.

        dprintf("DMA[P->M][16550][B]: Creating inner %u transfer(s).\n", burst_size >> 4);

        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALP(program, burst_size >> 4); // divide by 16.
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALD(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMAST(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }

        // } Inner loop

        if ((status == ALT_E_SUCCESS) && (loopcount > 1))
        {
            status = alt_dma_program_DMALPEND(program, ALT_DMA_PROGRAM_INST_MOD_BURST);
        }

        // } Outer loop
    }

    return status;
}

static ALT_STATUS_CODE alt_dma_16550_to_memory(ALT_DMA_PROGRAM_t * program,
                                               ALT_DMA_PERIPH_t periph,
                                               ALT_16550_HANDLE_t * handle,
                                               void * dst,
                                               size_t size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_DAR, (uint32_t)dst);
    }
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAMOV(program, ALT_DMA_PROGRAM_REG_SAR, (uint32_t)ALT_UART_RBR_THR_DLL_ADDR(handle->location));
    }

    // Determine if FIFOs are enabled from the FCR cache

    if (ALT_UART_FCR_FIFOE_GET(handle->fcr) != 0)
    {
        dprintf("DMA[P->M][16550]: FIFOs enabled.\n");

        //
        // FIFOs are enabled.
        //

        uint32_t rx_size;
        uint32_t burst_size;
        ALT_16550_FIFO_TRIGGER_RX_t trig_rx;

        // Get the RX FIFO Size
        // Use the register interface to avoid coupling the 16550 and DMA.
        rx_size = ALT_UART_CPR_FIFO_MOD_GET(alt_read_word(ALT_UART_CPR_ADDR(handle->location))) << 4;

        // Get the RX FIFO Trigger Level from the FCR cache
        trig_rx = (ALT_16550_FIFO_TRIGGER_RX_t)ALT_UART_FCR_RT_GET(handle->fcr);

        switch (trig_rx)
        {
        case ALT_16550_FIFO_TRIGGER_RX_ANY:
            burst_size = 1;
            break;
        case ALT_16550_FIFO_TRIGGER_RX_QUARTER_FULL:
            burst_size = rx_size >> 2; // divide by 4
            break;
        case ALT_16550_FIFO_TRIGGER_RX_HALF_FULL:
            burst_size = rx_size >> 1; // divide by 2
            break;
        case ALT_16550_FIFO_TRIGGER_RX_ALMOST_FULL:
            burst_size = rx_size - 2;
            break;
        default:
            // This case should never happen.
            return ALT_E_ERROR;
        }

        if (burst_size < 16)
        {
            // There's no point bursting 1 byte at a time per notify, so just do single transfers.
            if (status == ALT_E_SUCCESS)
            {
                status = alt_dma_16550_to_memory_single(program,
                                                        periph,
                                                        size);
            }
        }
        else
        {
            uint32_t sizeleft = size;

            // Now trim the burst size to a multiple of 16.
            // This will optimize the bursting in the fewest possible commands.
            dprintf("DMA[P->M][16550]: Untrimmed burst size = %lu.\n", burst_size);
            burst_size &= ~0xf;
            dprintf("DMA[P->M][16550]: Trimmed burst size   = %lu.\n", burst_size);

            // Determine how many burst transfers can be done
            uint32_t burst_count = 0;

            burst_count = sizeleft / burst_size;
            sizeleft -= burst_count * burst_size;

            if (burst_count == 0)
            {
                // Do the transfer.
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_16550_to_memory_single(program,
                                                            periph,
                                                            sizeleft);
                }
            }
            else
            {
                // Do the burst transfers
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_16550_to_memory_burst(program,
                                                           periph,
                                                           burst_size,
                                                           burst_count);
                }

                // Program the DMA engine to transfer the non-burstable items in single transfers.
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_dma_16550_to_memory_single(program,
                                                            periph,
                                                            sizeleft);
                }

            } // if (burst_count == 0)
        }
    }
    else
    {
        dprintf("DMA[P->M][16550]: FIFOs disabled.\n");

        //
        // FIFOs are disabled.
        //

        status = alt_dma_16550_to_memory_single(program,
                                                periph,
                                                size);
    }

    return status;
}
#endif // ALT_DMA_PERIPH_PROVISION_16550_SUPPORT

ALT_STATUS_CODE alt_dma_memory_to_periph(ALT_DMA_CHANNEL_t channel,
                                         ALT_DMA_PROGRAM_t * program,
                                         ALT_DMA_PERIPH_t dstp,
                                         const void * src,
                                         size_t size,
                                         void * periph_info,
                                         bool send_evt,
                                         ALT_DMA_EVENT_t evt)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if ((size == 0) && (send_evt == false))
    {
        return status;
    }

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DMA[M->P]: Init Program.\n");
        status = alt_dma_program_init(program);
    }

    if ((status == ALT_E_SUCCESS) && (size != 0))
    {
        switch (dstp)
        {
#if ALT_DMA_PERIPH_PROVISION_QSPI_SUPPORT
        case ALT_DMA_PERIPH_QSPI_FLASH_TX:
            status = alt_dma_memory_to_qspi(program, src, size);
            break;
#endif

#if ALT_DMA_PERIPH_PROVISION_16550_SUPPORT
        case ALT_DMA_PERIPH_UART0_TX:
        case ALT_DMA_PERIPH_UART1_TX:
            status = alt_dma_memory_to_16550(program, dstp,
                                             (ALT_16550_HANDLE_t *)periph_info, src, size);
            break;
#endif

        case ALT_DMA_PERIPH_FPGA_0:
        case ALT_DMA_PERIPH_FPGA_1:
        case ALT_DMA_PERIPH_FPGA_2:
        case ALT_DMA_PERIPH_FPGA_3:
        case ALT_DMA_PERIPH_FPGA_4:
        case ALT_DMA_PERIPH_FPGA_5:
        case ALT_DMA_PERIPH_FPGA_6:
        case ALT_DMA_PERIPH_FPGA_7:
        case ALT_DMA_PERIPH_I2C0_TX:
        case ALT_DMA_PERIPH_I2C1_TX:
        case ALT_DMA_PERIPH_I2C2_TX:
        case ALT_DMA_PERIPH_I2C3_TX:
        case ALT_DMA_PERIPH_SPI0_MASTER_TX:
        case ALT_DMA_PERIPH_SPI0_SLAVE_TX:
        case ALT_DMA_PERIPH_SPI1_MASTER_TX:
        case ALT_DMA_PERIPH_SPI1_SLAVE_TX:

        default:
            status = ALT_E_BAD_ARG;
            break;
        }
    }

    // Send event if requested.
    if (send_evt)
    {
        if (status == ALT_E_SUCCESS)
        {
            dprintf("DMA[M->P]: Adding event.\n");
            status = alt_dma_program_DMASEV(program, evt);
        }
    }

    // Now that everything is done, end the program.
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAEND(program);
    }

    // If there was a problem assembling the program, clean up the buffer and exit.
    if (status != ALT_E_SUCCESS)
    {
        // Do not report the status for the clear operation. A failure should be
        // reported regardless of if the clear is successful.
        alt_dma_program_clear(program);
        return status;
    }

    // Execute the program on the given channel.

    return alt_dma_channel_exec(channel, program);
}

ALT_STATUS_CODE alt_dma_periph_to_memory(ALT_DMA_CHANNEL_t channel,
                                         ALT_DMA_PROGRAM_t * program,
                                         void * dst,
                                         ALT_DMA_PERIPH_t srcp,
                                         size_t size,
                                         void * periph_info,
                                         bool send_evt,
                                         ALT_DMA_EVENT_t evt)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if ((size == 0) && (send_evt == false))
    {
        return ALT_E_SUCCESS;
    }

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DMA[P->M]: Init Program.\n");
        status = alt_dma_program_init(program);
    }

    if ((status == ALT_E_SUCCESS) && (size != 0))
    {
        switch (srcp)
        {
#if ALT_DMA_PERIPH_PROVISION_QSPI_SUPPORT
        case ALT_DMA_PERIPH_QSPI_FLASH_RX:
            status = alt_dma_qspi_to_memory(program, dst, size);
            break;
#endif

#if ALT_DMA_PERIPH_PROVISION_16550_SUPPORT
        case ALT_DMA_PERIPH_UART0_RX:
        case ALT_DMA_PERIPH_UART1_RX:
            status = alt_dma_16550_to_memory(program, srcp,
                                             (ALT_16550_HANDLE_t *)periph_info, dst, size);
            break;
#endif

        case ALT_DMA_PERIPH_FPGA_0:
        case ALT_DMA_PERIPH_FPGA_1:
        case ALT_DMA_PERIPH_FPGA_2:
        case ALT_DMA_PERIPH_FPGA_3:
        case ALT_DMA_PERIPH_FPGA_4:
        case ALT_DMA_PERIPH_FPGA_5:
        case ALT_DMA_PERIPH_FPGA_6:
        case ALT_DMA_PERIPH_FPGA_7:
        case ALT_DMA_PERIPH_I2C0_RX:
        case ALT_DMA_PERIPH_I2C1_RX:
        case ALT_DMA_PERIPH_I2C2_RX:
        case ALT_DMA_PERIPH_I2C3_RX:
        case ALT_DMA_PERIPH_SPI0_MASTER_RX:
        case ALT_DMA_PERIPH_SPI0_SLAVE_RX:
        case ALT_DMA_PERIPH_SPI1_MASTER_RX:
        case ALT_DMA_PERIPH_SPI1_SLAVE_RX:

        default:
            status = ALT_E_BAD_ARG;
            break;
        }
    }

    // Send event if requested.
    if (send_evt)
    {
        if (status == ALT_E_SUCCESS)
        {
            dprintf("DMA[P->M]: Adding event.\n");
            status = alt_dma_program_DMASEV(program, evt);
        }
    }

    // Now that everything is done, end the program.
    if (status == ALT_E_SUCCESS)
    {
        status = alt_dma_program_DMAEND(program);
    }

    // If there was a problem assembling the program, clean up the buffer and exit.
    if (status != ALT_E_SUCCESS)
    {
        // Do not report the status for the clear operation. A failure should be
        // reported regardless of if the clear is successful.
        alt_dma_program_clear(program);
        return status;
    }

    // Execute the program on the given channel.

    return alt_dma_channel_exec(channel, program);
}

/////

static bool alt_dma_is_init(void)
{
    uint32_t permodrst = alt_read_word(ALT_RSTMGR_PERMODRST_ADDR);

    if (permodrst & ALT_RSTMGR_PERMODRST_DMA_SET_MSK)
    {
        return false;
    }
    else
    {
        return true;
    }
}

ALT_STATUS_CODE alt_dma_ecc_start(void * block, size_t size)
{
    if (alt_dma_is_init() == false)
    {
        return ALT_E_ERROR;
    }

    if ((uintptr_t)block & (sizeof(uint64_t) - 1))
    {
        return ALT_E_ERROR;
    }

    // Verify that all channels are either unallocated or allocated and idle.

    for (int i = 0; i < ARRAY_COUNT(channel_info_array); ++i)
    {
        if (channel_info_array[i].flag & ALT_DMA_CHANNEL_INFO_FLAG_ALLOCED)
        {
            ALT_DMA_CHANNEL_STATE_t state;
            alt_dma_channel_state_get((ALT_DMA_CHANNEL_t)i, &state);

            if (state != ALT_DMA_CHANNEL_STATE_STOPPED)
            {
                dprintf("DMA[ECC]: Error: Channel %d state is non-stopped (%d).\n", i, (int)state);
                return ALT_E_ERROR;
            }
        }
    }

    /////

    // Enable ECC for DMA RAM

    dprintf("DEBUG[DMA][ECC]: Enable ECC in SysMgr.\n");
    alt_write_word(ALT_SYSMGR_ECC_DMA_ADDR, ALT_SYSMGR_ECC_DMA_EN_SET_MSK);

    // Clear any pending spurious DMA ECC interrupts.

    dprintf("DEBUG[DMA][ECC]: Clear any pending spurious ECC status in SysMgr.\n");
    alt_write_word(ALT_SYSMGR_ECC_DMA_ADDR,
                     ALT_SYSMGR_ECC_DMA_EN_SET_MSK
                   | ALT_SYSMGR_ECC_DMA_SERR_SET_MSK
                   | ALT_SYSMGR_ECC_DMA_DERR_SET_MSK);

    return ALT_E_SUCCESS;
}
