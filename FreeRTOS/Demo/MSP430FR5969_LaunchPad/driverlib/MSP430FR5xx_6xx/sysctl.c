/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// sysctl.c - Driver for the sysctl Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup sysctl_api sysctl
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_SYS__
#include "sysctl.h"

#include <assert.h>

void SysCtl_enableDedicatedJTAGPins(void)
{
    HWREG8(SYS_BASE + OFS_SYSCTL_L) |= SYSJTAGPIN;
}

uint8_t SysCtl_getBSLEntryIndication(void)
{
    if(HWREG8(SYS_BASE + OFS_SYSCTL_L) & SYSBSLIND)
    {
        return (SYSCTL_BSLENTRY_INDICATED);
    }
    else
    {
        return (SYSCTL_BSLENTRY_NOTINDICATED);
    }
}

void SysCtl_enablePMMAccessProtect(void)
{
    HWREG8(SYS_BASE + OFS_SYSCTL_L) |= SYSPMMPE;
}

void SysCtl_enableRAMBasedInterruptVectors(void)
{
    HWREG8(SYS_BASE + OFS_SYSCTL_L) |= SYSRIVECT;
}

void SysCtl_disableRAMBasedInterruptVectors(void)
{
    HWREG8(SYS_BASE + OFS_SYSCTL_L) &= ~(SYSRIVECT);
}

void SysCtl_initJTAGMailbox(uint8_t mailboxSizeSelect,
                            uint8_t autoClearInboxFlagSelect)
{
    HWREG8(SYS_BASE + OFS_SYSJMBC_L) &= ~(JMBCLR1OFF + JMBCLR0OFF + JMBMODE);
    HWREG8(SYS_BASE + OFS_SYSJMBC_L) |=
        mailboxSizeSelect + autoClearInboxFlagSelect;
}

uint8_t SysCtl_getJTAGMailboxFlagStatus(uint8_t mailboxFlagMask)
{
    return (HWREG8(SYS_BASE + OFS_SYSJMBC_L) & mailboxFlagMask);
}

void SysCtl_clearJTAGMailboxFlagStatus(uint8_t mailboxFlagMask)
{
    HWREG8(SYS_BASE + OFS_SYSJMBC_L) &= ~(mailboxFlagMask);
}

uint16_t SysCtl_getJTAGInboxMessage16Bit(uint8_t inboxSelect)
{
    return (HWREG16(SYS_BASE + OFS_SYSJMBI0 + inboxSelect));
}

uint32_t SysCtl_getJTAGInboxMessage32Bit(void)
{
    uint32_t JTAGInboxMessageLow = HWREG16(SYS_BASE + OFS_SYSJMBI0);
    uint32_t JTAGInboxMessageHigh = HWREG16(SYS_BASE + OFS_SYSJMBI1);

    return ((JTAGInboxMessageHigh << 16) + JTAGInboxMessageLow);
}

void SysCtl_setJTAGOutgoingMessage16Bit(uint8_t outboxSelect,
                                        uint16_t outgoingMessage)
{
    HWREG16(SYS_BASE + OFS_SYSJMBO0 + outboxSelect) = outgoingMessage;
}

void SysCtl_setJTAGOutgoingMessage32Bit(uint32_t outgoingMessage)
{
    HWREG16(SYS_BASE + OFS_SYSJMBO0) = (outgoingMessage);
    HWREG16(SYS_BASE + OFS_SYSJMBO1) = (outgoingMessage >> 16);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for sysctl_api
//! @}
//
//*****************************************************************************
