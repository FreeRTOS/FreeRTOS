/**
 * \file
 *
 * \brief Configuration Change Protection write functions
 *
 (c) 2018 Microchip Technology Inc. and its subsidiaries.

    Subject to your compliance with these terms,you may use this software and
    any derivatives exclusively with Microchip products.It is your responsibility
    to comply with third party license terms applicable to your use of third party
    software (including open source software) that may accompany Microchip software.

    THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS". NO WARRANTIES, WHETHER
    EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY IMPLIED
    WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS FOR A
    PARTICULAR PURPOSE.

    IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
    INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
    WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
    BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE. TO THE
    FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL CLAIMS IN
    ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF FEES, IF ANY,
    THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
 *
 */

#ifndef CPU_CCP_H
#define CPU_CCP_H

#include "protected_io.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \brief Write to a CCP-protected 8-bit I/O register
 *
 * \param addr Address of the I/O register
 * \param value Value to be written
 *
 * \note Using IAR Embedded workbench, the choice of memory model has an impact
 *       on calling convention. The memory model is not visible to the
 *       preprocessor, so it must be defined in the Assembler preprocessor directives.
 */
static inline void ccp_write_io(void *addr, uint8_t value)
{
    protected_write_io(addr, CCP_IOREG_gc, value);
}

/** @} */

/**
 * \brief Write to CCP-protected 8-bit SPM register
 *
 * \param addr Address of the SPM register
 * \param value Value to be written
 *
 * \note Using IAR Embedded workbench, the choice of memory model has an impact
 *       on calling convention. The memory model is not visible to the
 *       preprocessor, so it must be defined in the Assembler preprocessor directives.
 */
static inline void ccp_write_spm(void *addr, uint8_t value)
{
    protected_write_io(addr, CCP_SPM_gc, value);
}

    /** @} */

#ifdef __cplusplus
}
#endif

#endif /* CPU_CCP_H */
