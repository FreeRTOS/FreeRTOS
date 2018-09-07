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
// gpio.c - Driver for the gpio Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup gpio_api gpio
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#if defined(__MSP430_HAS_PORT1_R__) || defined(__MSP430_HAS_PORT2_R__) || \
    defined(__MSP430_HAS_PORTA_R__)
#include "gpio.h"

#include <assert.h>

static const uint16_t GPIO_PORT_TO_BASE[] = {
    0x00,
#if defined(__MSP430_HAS_PORT1_R__)
    __MSP430_BASEADDRESS_PORT1_R__,
#elif defined(__MSP430_HAS_PORT1__)
    __MSP430_BASEADDRESS_PORT1__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT2_R__)
    __MSP430_BASEADDRESS_PORT2_R__,
#elif defined(__MSP430_HAS_PORT2__)
    __MSP430_BASEADDRESS_PORT2__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT3_R__)
    __MSP430_BASEADDRESS_PORT3_R__,
#elif defined(__MSP430_HAS_PORT3__)
    __MSP430_BASEADDRESS_PORT3__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT4_R__)
    __MSP430_BASEADDRESS_PORT4_R__,
#elif defined(__MSP430_HAS_PORT4__)
    __MSP430_BASEADDRESS_PORT4__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT5_R__)
    __MSP430_BASEADDRESS_PORT5_R__,
#elif defined(__MSP430_HAS_PORT5__)
    __MSP430_BASEADDRESS_PORT5__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT6_R__)
    __MSP430_BASEADDRESS_PORT6_R__,
#elif defined(__MSP430_HAS_PORT6__)
    __MSP430_BASEADDRESS_PORT6__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT7_R__)
    __MSP430_BASEADDRESS_PORT7_R__,
#elif defined(__MSP430_HAS_PORT7__)
    __MSP430_BASEADDRESS_PORT7__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT8_R__)
    __MSP430_BASEADDRESS_PORT8_R__,
#elif defined(__MSP430_HAS_PORT8__)
    __MSP430_BASEADDRESS_PORT8__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT9_R__)
    __MSP430_BASEADDRESS_PORT9_R__,
#elif defined(__MSP430_HAS_PORT9__)
    __MSP430_BASEADDRESS_PORT9__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT10_R__)
    __MSP430_BASEADDRESS_PORT10_R__,
#elif defined(__MSP430_HAS_PORT10__)
    __MSP430_BASEADDRESS_PORT10__,
#else
    0xFFFF,
#endif
#if defined(__MSP430_HAS_PORT11_R__)
    __MSP430_BASEADDRESS_PORT11_R__,
#elif defined(__MSP430_HAS_PORT11__)
    __MSP430_BASEADDRESS_PORT11__,
#else
    0xFFFF,
#endif
    0xFFFF,
#if defined(__MSP430_HAS_PORTJ_R__)
    __MSP430_BASEADDRESS_PORTJ_R__
#elif defined(__MSP430_HAS_PORTJ__)
    __MSP430_BASEADDRESS_PORTJ__
#else
    0xFFFF
#endif
};

void GPIO_setAsOutputPin(uint8_t selectedPort,
                         uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PASEL0) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PASEL1) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PADIR) |= selectedPins;

    return;
}

void GPIO_setAsInputPin(uint8_t selectedPort,
                        uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PASEL0) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PASEL1) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PADIR) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PAREN) &= ~selectedPins;
}

void GPIO_setAsPeripheralModuleFunctionOutputPin(uint8_t selectedPort,
                                                 uint16_t selectedPins
                                                 ,
                                                 uint8_t mode) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PADIR) |= selectedPins;
    switch(mode)
    {
    case GPIO_PRIMARY_MODULE_FUNCTION:
        HWREG16(baseAddress + OFS_PASEL0) |= selectedPins;
        HWREG16(baseAddress + OFS_PASEL1) &= ~selectedPins;
        break;
    case GPIO_SECONDARY_MODULE_FUNCTION:
        HWREG16(baseAddress + OFS_PASEL0) &= ~selectedPins;
        HWREG16(baseAddress + OFS_PASEL1) |= selectedPins;
        break;
    case GPIO_TERNARY_MODULE_FUNCTION:
        HWREG16(baseAddress + OFS_PASEL0) |= selectedPins;
        HWREG16(baseAddress + OFS_PASEL1) |= selectedPins;
        break;
    }
}

void GPIO_setAsPeripheralModuleFunctionInputPin(uint8_t selectedPort,
                                                uint16_t selectedPins
                                                ,
                                                uint8_t mode) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PADIR) &= ~selectedPins;
    switch(mode)
    {
    case GPIO_PRIMARY_MODULE_FUNCTION:
        HWREG16(baseAddress + OFS_PASEL0) |= selectedPins;
        HWREG16(baseAddress + OFS_PASEL1) &= ~selectedPins;
        break;
    case GPIO_SECONDARY_MODULE_FUNCTION:
        HWREG16(baseAddress + OFS_PASEL0) &= ~selectedPins;
        HWREG16(baseAddress + OFS_PASEL1) |= selectedPins;
        break;
    case GPIO_TERNARY_MODULE_FUNCTION:
        HWREG16(baseAddress + OFS_PASEL0) |= selectedPins;
        HWREG16(baseAddress + OFS_PASEL1) |= selectedPins;
        break;
    }
}

void GPIO_setOutputHighOnPin(uint8_t selectedPort,
                             uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PAOUT) |= selectedPins;
}

void GPIO_setOutputLowOnPin(uint8_t selectedPort,
                            uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PAOUT) &= ~selectedPins;
}

void GPIO_toggleOutputOnPin(uint8_t selectedPort,
                            uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PAOUT) ^= selectedPins;
}

void GPIO_setAsInputPinWithPullDownResistor(uint8_t selectedPort,
                                            uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PASEL0) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PASEL1) &= ~selectedPins;

    HWREG16(baseAddress + OFS_PADIR) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PAREN) |= selectedPins;
    HWREG16(baseAddress + OFS_PAOUT) &= ~selectedPins;
}

void GPIO_setAsInputPinWithPullUpResistor(uint8_t selectedPort,
                                          uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PASEL0) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PASEL1) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PADIR) &= ~selectedPins;
    HWREG16(baseAddress + OFS_PAREN) |= selectedPins;
    HWREG16(baseAddress + OFS_PAOUT) |= selectedPins;
}

uint8_t GPIO_getInputPinValue(uint8_t selectedPort,
                              uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    uint16_t inputPinValue = HWREG16(baseAddress + OFS_PAIN) & (selectedPins);

    if(inputPinValue > 0)
    {
        return (GPIO_INPUT_PIN_HIGH);
    }
    return (GPIO_INPUT_PIN_LOW);
}

void GPIO_enableInterrupt(uint8_t selectedPort,
                          uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PAIE) |= selectedPins;
}

void GPIO_disableInterrupt(uint8_t selectedPort,
                           uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PAIE) &= ~selectedPins;
}

uint16_t GPIO_getInterruptStatus(uint8_t selectedPort,
                                 uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    return (HWREG16(baseAddress + OFS_PAIFG) & selectedPins);
}

void GPIO_clearInterrupt(uint8_t selectedPort,
                         uint16_t selectedPins) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    HWREG16(baseAddress + OFS_PAIFG) &= ~selectedPins;
}

void GPIO_selectInterruptEdge(uint8_t selectedPort,
                              uint16_t selectedPins,
                              uint8_t edgeSelect) {
    uint16_t baseAddress = GPIO_PORT_TO_BASE[selectedPort];

    #ifndef NDEBUG
    if(baseAddress == 0xFFFF)
    {
        return;
    }
    #endif

    // Shift by 8 if port is even (upper 8-bits)
    if((selectedPort & 1) ^ 1)
    {
        selectedPins <<= 8;
    }

    if(GPIO_LOW_TO_HIGH_TRANSITION == edgeSelect)
    {
        HWREG16(baseAddress + OFS_PAIES) &= ~selectedPins;
    }
    else
    {
        HWREG16(baseAddress + OFS_PAIES) |= selectedPins;
    }
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for gpio_api
//! @}
//
//*****************************************************************************
