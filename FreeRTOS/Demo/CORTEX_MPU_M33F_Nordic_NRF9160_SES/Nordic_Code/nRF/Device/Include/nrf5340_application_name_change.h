/*

Copyright (c) 2010 - 2021, Nordic Semiconductor ASA All rights reserved.

SPDX-License-Identifier: BSD-3-Clause

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

3. Neither the name of Nordic Semiconductor ASA nor the names of its
   contributors may be used to endorse or promote products derived from this
   software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY, AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL NORDIC SEMICONDUCTOR ASA OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

#ifndef NRF5340_APPLICATION_NAME_CHANGE_H
#define NRF5340_APPLICATION_NAME_CHANGE_H

/*lint ++flb "Enter library region */

/* This file is given to prevent your SW from not compiling with the updates made to nrf5340_application.h and
 * nrf5340_application_bitfields.h. The macros defined in this file were available previously. Do not use these
 * macros on purpose. Use the ones defined in nrf5340_application.h and nrf5340_application_bitfields.h instead.
 */
 
/* The serial box interrupt ISRs were renamed. Adding old names as macros. */
#define SPIM0_SPIS0_TWIM0_TWIS0_UARTE0_IRQHandler          SERIAL0_IRQHandler
#define SPIM0_SPIS0_TWIM0_TWIS0_UARTE0_IRQn                SERIAL0_IRQn
#define SPIM1_SPIS1_TWIM1_TWIS1_UARTE1_IRQHandler          SERIAL1_IRQHandler
#define SPIM1_SPIS1_TWIM1_TWIS1_UARTE1_IRQn                SERIAL1_IRQn
#define SPIM2_SPIS2_TWIM2_TWIS2_UARTE2_IRQHandler          SERIAL2_IRQHandler
#define SPIM2_SPIS2_TWIM2_TWIS2_UARTE2_IRQn                SERIAL2_IRQn
#define SPIM3_SPIS3_TWIM3_TWIS3_UARTE3_IRQHandler          SERIAL3_IRQHandler
#define SPIM3_SPIS3_TWIM3_TWIS3_UARTE3_IRQn                SERIAL3_IRQn
 
 /*lint --flb "Leave library region" */

#endif /* NRF5340_APPLICATION_NAME_CHANGE_H */
