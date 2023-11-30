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

#ifndef NRF9160_NAME_CHANGE_H
#define NRF9160_NAME_CHANGE_H

/*lint ++flb "Enter library region */

/* This file is given to prevent your SW from not compiling with the updates made to nrf9160.h and 
 * nrf9160_bitfields.h. The macros defined in this file were available previously. Do not use these
 * macros on purpose. Use the ones defined in nrf9160.h and nrf9160_bitfields.h instead.
 */
 
 /* SAADC enums */
 /* Changes to enum names in SAADC */
 #define SAADC_CH_PSELP_PSELP_VDD       SAADC_CH_PSELP_PSELP_VDDGPIO
 #define SAADC_CH_PSELP_PSELN_VDD       SAADC_CH_PSELP_PSELN_VDDGPIO
 
 /* CTRLAP PERI Fields */
 #define CTRLAPPERI_ERASEPROTECT_LOCK_ERASEPROTECTLOCK_Pos       CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Pos     
 #define CTRLAPPERI_ERASEPROTECT_LOCK_ERASEPROTECTLOCK_Msk       CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Msk     
 #define CTRLAPPERI_ERASEPROTECT_LOCK_ERASEPROTECTLOCK_Unlocked  CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Unlocked
 #define CTRLAPPERI_ERASEPROTECT_LOCK_ERASEPROTECTLOCK_Locked    CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Locked  
 
 /*lint --flb "Leave library region" */

#endif /* NRF9160_NAME_CHANGE_H */
