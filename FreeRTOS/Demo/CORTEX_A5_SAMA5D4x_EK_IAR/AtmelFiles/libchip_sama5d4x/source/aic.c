/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/** \addtogroup aic_module
 *
 * The Advanced Interrupt Controller (AIC) is an 8-level priority, individually 
 * maskable, vectored interrupt controller, providing handling of up to thirty-two interrupt sources. 
 *
 * \section Usage
 * <ul>
 * <li> Each interrupt source can be enabled or disabled by using the IRQ_EnableIT() and IRQ_DisableIT()</li>
 * <li> Configure the AIC interrupt to its requirements and special needs,such as priorty 
 * level, source type and configure the addresses of the corresponding handler for each interrupt source
 * could be setting by  IRQ_ConfigureIT(). </li>
 * <li> Start conversion by setting ADC_CR_START in ADC_CR. </li>
 * </ul>
 *
 * For more accurate information, please look at the AIC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref aic.c\n
 * \ref irq.h\n
 */
/*@{*/
/*@}*/

 /**
 * \file
 *
 * Implementation of Advanced Interrupt Controller (AIC) controller.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enables interrupts coming from the given AIC and (unique) source (ID_xxx).
 *
 * \param aic  AIC instance. 
 * \param source  Interrupt source to enable.
 */
static void _aic_EnableIT(Aic *aic, uint32_t source)
{
    aic->AIC_SSR  = AIC_SSR_INTSEL(source);
    aic->AIC_IECR = AIC_IECR_INTEN;
}

/**
 * \brief Disables interrupts coming from the given AIC and (unique) source (ID_xxx).
 *
 * \param aic  AIC instance.
 * \param source  Interrupt source to disable.
 */
static void _aic_DisableIT(Aic *aic, uint32_t source)
{
    aic->AIC_SSR  =  AIC_SSR_INTSEL(source);
    aic->AIC_IDCR = AIC_IDCR_INTD ;
}

/**
 * \brief return if the giving peripheral is H64 Matrix
 *
 * \param pid  peripheral ID
 */
static uint8_t _isH64Matrix(uint32_t pid){
    if ((pid == ID_ARM) || 
        (pid == ID_XDMAC0) ||
        //(pid == ID_PKCC) ||
        (pid == ID_AESB) ||
        (pid == ID_MPDDRC) ||
        (pid == ID_VDEC) ||
        (pid == ID_XDMAC1) ||
        (pid == ID_LCDC) ||
        (pid == ID_ISI) ||
        (pid == ID_L2CC)) 
    {
        return 1;
    } else {
        return 0;
    }
}

/**
 * \brief Enables interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param source  Interrupt source to enable.
 */
void AIC_EnableIT( uint32_t source)
{
    volatile unsigned int * pAicFuse = (volatile unsigned int *) REG_SFR_AICREDIR;
    
    if(*pAicFuse)
    {
      _aic_EnableIT(AIC, source);
    }
    else
    {
      if (_isH64Matrix(source)) {
          if ( MATRIX0->MATRIX_SPSELR[source / 32] & (1 << (source % 32)))
              _aic_EnableIT(AIC, source);
          else 
              _aic_EnableIT(SAIC, source);
      } else {
          if ( MATRIX1->MATRIX_SPSELR[source / 32] & (1 << (source % 32)))
              _aic_EnableIT(AIC, source);
          else 
              _aic_EnableIT(SAIC, source);
      }
    }
}

/**
 * \brief Disables interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param source  Interrupt source to disable.
 */
void AIC_DisableIT(uint32_t source)
{
    if (_isH64Matrix(source)) {
        if ( MATRIX0->MATRIX_SPSELR[source / 32] & (1 << (source % 32)))
            _aic_DisableIT(AIC, source);
        else 
            _aic_DisableIT(SAIC, source);
    } else {
        if ( MATRIX1->MATRIX_SPSELR[source / 32] & (1 << (source % 32)))
            _aic_DisableIT(AIC, source);
        else 
            _aic_DisableIT(SAIC, source);
    }
}
