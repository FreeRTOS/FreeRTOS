/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
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

/**
 * \file
 *
 * Interface for Synchronous Serial (SSC) controller.
 *
 */

#ifndef _SSC_
#define _SSC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

#include <stdint.h>

#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
extern void SSC_Configure(Ssc *ssc, uint32_t bitRate, uint32_t masterClock);
extern void SSC_ConfigureTransmitter(Ssc *ssc, uint32_t tcmr, uint32_t tfmr);
extern void SSC_ConfigureReceiver(Ssc *ssc, uint32_t rcmr, uint32_t rfmr);
extern void SSC_EnableTransmitter(Ssc *ssc);
extern void SSC_DisableTransmitter(Ssc *ssc);
extern void SSC_EnableReceiver(Ssc *ssc);
extern void SSC_DisableReceiver(Ssc *ssc );
extern void SSC_EnableInterrupts(Ssc *ssc, uint32_t sources);
extern void SSC_DisableInterrupts(Ssc *ssc, uint32_t sources);
extern void SSC_Write(Ssc *ssc, uint32_t frame);
extern uint32_t SSC_Read(Ssc *ssc );
extern uint8_t SSC_IsRxReady(Ssc *ssc);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _SSC_ */

