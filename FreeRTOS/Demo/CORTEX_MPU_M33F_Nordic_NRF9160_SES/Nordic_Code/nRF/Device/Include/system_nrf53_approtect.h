/*

Copyright (c) 2009-2021 ARM Limited. All rights reserved.

    SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the License); you may
not use this file except in compliance with the License.
You may obtain a copy of the License at

    www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an AS IS BASIS, WITHOUT
WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

NOTICE: This file has been modified by Nordic Semiconductor ASA.

*/

#ifndef SYSTEM_NRF53_APPROTECT_H
#define SYSTEM_NRF53_APPROTECT_H

#include "nrf.h"
#include "nrf53_erratas.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Function that handles firmware-driven enabling or disabling of APPROTECT on devices where it is supported.
        If ENABLE_APPROTECT is defined, the FW will lock the fw branch of the APPROTECT mechanism,
                            preventing it from being opened.
        If ENABLE_APPROTECT_USER_HANDLING is defined, the FW will not write to the fw branch of the APPROTECT mechanism.
                            This allows later stages of the fw to handle APPROTECT,
                            for example to implement authenticated debug.
        Otherwise, the fw branch state is loaded from UICR.

         The same mechanism is implemented for SECURE APPROTECT, with the macros
         ENABLE_SECURE_APPROTECT and ENABLE_SECURE_APPROTECT_USER_HANDLING. */

static inline void nrf53_handle_approtect(void)
{
    #if defined(NRF_APPLICATION)
        #if defined (ENABLE_APPROTECT)
            /* Prevent processor from unlocking APPROTECT soft branch after this point. */
            NRF_CTRLAP_S->APPROTECT.LOCK = CTRLAPPERI_APPROTECT_LOCK_LOCK_Locked;

        #elif  defined (ENABLE_APPROTECT_USER_HANDLING)
                /* Do nothing, allow user code to handle APPROTECT. Use this if you want to enable authenticated debug. */

        #else
            /* Load APPROTECT soft branch from UICR.
               If UICR->APPROTECT is disabled, CTRLAP->APPROTECT will be disabled. */
            NRF_CTRLAP_S->APPROTECT.DISABLE = NRF_UICR_S->APPROTECT;
        #endif

        /* Secure APPROTECT is only available for Application core. */
        #if defined (ENABLE_SECURE_APPROTECT)
            /* Prevent processor from unlocking SECURE APPROTECT soft branch after this point. */
            NRF_CTRLAP_S->SECUREAPPROTECT.LOCK = CTRLAPPERI_SECUREAPPROTECT_LOCK_LOCK_Locked;

        #elif  defined (ENABLE_SECURE_APPROTECT_USER_HANDLING)
                /* Do nothing, allow user code to handle SECURE APPROTECT. Use this if you want to enable authenticated debug. */

        #else
            /* Load SECURE APPROTECT soft branch from UICR.
               If UICR->SECUREAPPROTECT is disabled, CTRLAP->SECUREAPPROTECT will be disabled. */
            NRF_CTRLAP_S->SECUREAPPROTECT.DISABLE = NRF_UICR_S->SECUREAPPROTECT;
        #endif
    #endif
    #if defined(NRF_NETWORK)
        #if defined (ENABLE_APPROTECT)
            /* Prevent processor from unlocking APPROTECT soft branch after this point. */
            NRF_CTRLAP_NS->APPROTECT.LOCK = CTRLAPPERI_APPROTECT_LOCK_LOCK_Locked;

        #elif  defined (ENABLE_APPROTECT_USER_HANDLING)
                /* Do nothing, allow user code to handle APPROTECT. Use this if you want to enable authenticated debug. */

        #else
            /* Load APPROTECT soft branch from UICR.
               If UICR->APPROTECT is disabled, CTRLAP->APPROTECT will be disabled. */
            NRF_CTRLAP_NS->APPROTECT.DISABLE = NRF_UICR_NS->APPROTECT;
        #endif
    #endif
}

#ifdef __cplusplus
}
#endif

#endif /* SYSTEM_NRF5_APPROTECT_H */
