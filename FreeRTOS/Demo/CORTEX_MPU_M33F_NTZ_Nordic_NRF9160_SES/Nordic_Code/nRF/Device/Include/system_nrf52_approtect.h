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

#ifndef SYSTEM_NRF52_APPROTECT_H
#define SYSTEM_NRF52_APPROTECT_H

#include "nrf.h"
#include "nrf52_erratas.h"

#ifdef __cplusplus
extern "C" {
#endif


/* Function that handles firmware-driven enabling or disabling of APPROTECT on devices where it is supported.
        If ENABLE_APPROTECT is defined, the FW will lock the fw branch of the APPROTECT mechanism,
                            preventing it from being opened.
        Otherwise, the fw branch state is loaded from UICR, emulating the legacy APPROTECT behavior.

         The same mechanism is implemented for SECURE APPROTECT, with the macros
         ENABLE_SECURE_APPROTECT and ENABLE_SECURE_APPROTECT_USER_HANDLING. */
static inline void nrf52_handle_approtect(void)
{
    #if NRF52_CONFIGURATION_249_PRESENT
        #if defined (ENABLE_APPROTECT)
            if (nrf52_configuration_249())
            {
                /* Prevent processor from unlocking APPROTECT soft branch after this point. */
                NRF_APPROTECT->FORCEPROTECT = APPROTECT_FORCEPROTECT_FORCEPROTECT_Force;
            }
        #else
            if (nrf52_configuration_249())
            {
                /* Load APPROTECT soft branch from UICR.
                   If UICR->APPROTECT is disabled, POWER->APPROTECT will be disabled. */
                NRF_APPROTECT->DISABLE = NRF_UICR->APPROTECT;
            }
        #endif
    #endif
}

#ifdef __cplusplus
}
#endif

#endif /* SYSTEM_NRF52_APPROTECT_H */
