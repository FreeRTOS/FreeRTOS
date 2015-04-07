/*******************************************************************************
 *
 * HAL_PMM.h
 * Power Management Module Library for MSP430F5xx/6xx family
 *
 *
 * Copyright (C) 2010 Texas Instruments Incorporated - http://www.ti.com/
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 ******************************************************************************/

#ifndef HAL_PMM_H
#define HAL_PMM_H

#include <stdint.h>
#include "HAL_MACROS.h"

/*******************************************************************************
 * Macros
 ******************************************************************************/
#define ENABLE_SVSL()        st(PMMCTL0_H = 0xA5; SVSMLCTL |= SVSLE; PMMCTL0_H = 0x00; )
#define DISABLE_SVSL()       st(PMMCTL0_H = 0xA5; SVSMLCTL &= ~SVSLE; PMMCTL0_H = 0x00; )
#define ENABLE_SVML()        st(PMMCTL0_H = 0xA5; SVSMLCTL |= SVMLE; PMMCTL0_H = 0x00; )
#define DISABLE_SVML()       st(PMMCTL0_H = 0xA5; SVSMLCTL &= ~SVMLE; PMMCTL0_H = 0x00; )
#define ENABLE_SVSH()        st(PMMCTL0_H = 0xA5; SVSMHCTL |= SVSHE; PMMCTL0_H = 0x00; )
#define DISABLE_SVSH()       st(PMMCTL0_H = 0xA5; SVSMHCTL &= ~SVSHE; PMMCTL0_H = 0x00; )
#define ENABLE_SVMH()        st(PMMCTL0_H = 0xA5; SVSMHCTL |= SVMHE; PMMCTL0_H = 0x00; )
#define DISABLE_SVMH()       st(PMMCTL0_H = 0xA5; SVSMHCTL &= ~SVMHE; PMMCTL0_H = 0x00; )
#define ENABLE_SVSL_SVML()   st(PMMCTL0_H = 0xA5; SVSMLCTL |= (SVSLE + SVMLE); PMMCTL0_H = 0x00; )
#define DISABLE_SVSL_SVML()  st(PMMCTL0_H = 0xA5; SVSMLCTL &= ~(SVSLE + SVMLE); PMMCTL0_H = 0x00; )
#define ENABLE_SVSH_SVMH()   st(PMMCTL0_H = 0xA5; SVSMHCTL |= (SVSHE + SVMHE); PMMCTL0_H = 0x00; )
#define DISABLE_SVSH_SVMH()  st(PMMCTL0_H = 0xA5; SVSMHCTL &= ~(SVSHE + SVMHE); PMMCTL0_H = 0x00; )

#define ENABLE_SVSL_RESET()       st(PMMCTL0_H = 0xA5; PMMRIE |= SVSLPE; PMMCTL0_H = 0x00; )
#define DISABLE_SVSL_RESET()      st(PMMCTL0_H = 0xA5; PMMRIE &= ~SVSLPE; PMMCTL0_H = 0x00; )
#define ENABLE_SVML_INTERRUPT()   st(PMMCTL0_H = 0xA5; PMMRIE |= SVMLIE; PMMCTL0_H = 0x00; )
#define DISABLE_SVML_INTERRUPT()  st(PMMCTL0_H = 0xA5; PMMRIE &= ~SVMLIE; PMMCTL0_H = 0x00; )
#define ENABLE_SVSH_RESET()       st(PMMCTL0_H = 0xA5; PMMRIE |= SVSHPE; PMMCTL0_H = 0x00; )
#define DISABLE_SVSH_RESET()      st(PMMCTL0_H = 0xA5; PMMRIE &= ~SVSHPE; PMMCTL0_H = 0x00; )
#define ENABLE_SVMH_INTERRUPT()   st(PMMCTL0_H = 0xA5; PMMRIE |= SVMHIE; PMMCTL0_H = 0x00; )
#define DISABLE_SVMH_INTERRUPT()  st(PMMCTL0_H = 0xA5; PMMRIE &= ~SVMHIE; PMMCTL0_H = 0x00; )
#define CLEAR_PMM_IFGS()          st(PMMCTL0_H = 0xA5; PMMIFG = 0; PMMCTL0_H = 0x00; )

// These settings use SVSH/LACE = 0
#define SVSL_ENABLED_IN_LPM_FAST_WAKE()  st( \
        PMMCTL0_H = 0xA5; SVSMLCTL |= (SVSLFP + SVSLMD); SVSMLCTL &= ~SVSMLACE; PMMCTL0_H = 0x00; )
#define SVSL_ENABLED_IN_LPM_SLOW_WAKE()  st(PMMCTL0_H = 0xA5; SVSMLCTL |= SVSLMD; SVSMLCTL &= \
                                                ~(SVSLFP + SVSMLACE); PMMCTL0_H = 0x00; )

#define SVSL_DISABLED_IN_LPM_FAST_WAKE() st(PMMCTL0_H = 0xA5; SVSMLCTL |= SVSLFP; SVSMLCTL &= \
                                                ~(SVSLMD + SVSMLACE); PMMCTL0_H = 0x00; )
#define SVSL_DISABLED_IN_LPM_SLOW_WAKE() st(PMMCTL0_H = 0xA5; SVSMLCTL &= \
                                                ~(SVSLFP + SVSMLACE + SVSLMD); PMMCTL0_H = 0x00; )

#define SVSH_ENABLED_IN_LPM_NORM_PERF()  st(PMMCTL0_H = 0xA5; SVSMHCTL |= SVSHMD; SVSMHCTL &= \
                                                ~(SVSMHACE + SVSHFP); PMMCTL0_H = 0x00; )
#define SVSH_ENABLED_IN_LPM_FULL_PERF()  st( \
        PMMCTL0_H = 0xA5; SVSMHCTL |= (SVSHMD + SVSHFP); SVSMHCTL &= ~SVSMHACE; PMMCTL0_H = 0x00; )

#define SVSH_DISABLED_IN_LPM_NORM_PERF() st(PMMCTL0_H = 0xA5; SVSMHCTL &= \
                                                ~(SVSMHACE + SVSHFP + SVSHMD); PMMCTL0_H = 0x00; )
#define SVSH_DISABLED_IN_LPM_FULL_PERF() st(PMMCTL0_H = 0xA5; SVSMHCTL |= SVSHFP; SVSMHCTL &= \
                                                ~(SVSMHACE + SVSHMD); PMMCTL0_H = 0x00; )

// These setting use SVSH/LACE = 1
#define SVSL_OPTIMIZED_IN_LPM_FAST_WAKE() st(PMMCTL0_H = 0xA5; SVSMLCTL |= \
                                                 (SVSLFP + SVSLMD + SVSMLACE); PMMCTL0_H = 0x00; )
#define SVSH_OPTIMIZED_IN_LPM_FULL_PERF() st(PMMCTL0_H = 0xA5; SVSMHCTL |= \
                                                 (SVSHMD + SVSHFP + SVSMHACE); PMMCTL0_H = 0x00; )

/*******************************************************************************
 * Defines
 ******************************************************************************/
#define PMM_STATUS_OK     0
#define PMM_STATUS_ERROR  1

/*******************************************************************************
 * \brief   Set Vcore to expected level
 *
 * \param level     Level to which Vcore needs to be increased/decreased
 * \return status   Success/failure
 ******************************************************************************/
extern uint16_t SetVCore(uint8_t level);

#endif /* HAL_PMM_H */
