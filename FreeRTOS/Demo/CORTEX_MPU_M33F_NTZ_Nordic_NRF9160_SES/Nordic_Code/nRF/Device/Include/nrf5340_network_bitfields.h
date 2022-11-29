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

#ifndef __NRF5340_NETWORK_BITS_H
#define __NRF5340_NETWORK_BITS_H

/*lint ++flb "Enter library region" */

/* Peripheral: AAR */
/* Description: Accelerated Address Resolver */

/* Register: AAR_TASKS_START */
/* Description: Start resolving addresses based on IRKs specified in the IRK data structure */

/* Bit 0 : Start resolving addresses based on IRKs specified in the IRK data structure */
#define AAR_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define AAR_TASKS_START_TASKS_START_Msk (0x1UL << AAR_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define AAR_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: AAR_TASKS_STOP */
/* Description: Stop resolving addresses */

/* Bit 0 : Stop resolving addresses */
#define AAR_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define AAR_TASKS_STOP_TASKS_STOP_Msk (0x1UL << AAR_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define AAR_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: AAR_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define AAR_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define AAR_SUBSCRIBE_START_EN_Msk (0x1UL << AAR_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define AAR_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define AAR_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define AAR_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define AAR_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << AAR_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: AAR_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define AAR_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define AAR_SUBSCRIBE_STOP_EN_Msk (0x1UL << AAR_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define AAR_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define AAR_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define AAR_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define AAR_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << AAR_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: AAR_EVENTS_END */
/* Description: Address resolution procedure complete */

/* Bit 0 : Address resolution procedure complete */
#define AAR_EVENTS_END_EVENTS_END_Pos (0UL) /*!< Position of EVENTS_END field. */
#define AAR_EVENTS_END_EVENTS_END_Msk (0x1UL << AAR_EVENTS_END_EVENTS_END_Pos) /*!< Bit mask of EVENTS_END field. */
#define AAR_EVENTS_END_EVENTS_END_NotGenerated (0UL) /*!< Event not generated */
#define AAR_EVENTS_END_EVENTS_END_Generated (1UL) /*!< Event generated */

/* Register: AAR_EVENTS_RESOLVED */
/* Description: Address resolved */

/* Bit 0 : Address resolved */
#define AAR_EVENTS_RESOLVED_EVENTS_RESOLVED_Pos (0UL) /*!< Position of EVENTS_RESOLVED field. */
#define AAR_EVENTS_RESOLVED_EVENTS_RESOLVED_Msk (0x1UL << AAR_EVENTS_RESOLVED_EVENTS_RESOLVED_Pos) /*!< Bit mask of EVENTS_RESOLVED field. */
#define AAR_EVENTS_RESOLVED_EVENTS_RESOLVED_NotGenerated (0UL) /*!< Event not generated */
#define AAR_EVENTS_RESOLVED_EVENTS_RESOLVED_Generated (1UL) /*!< Event generated */

/* Register: AAR_EVENTS_NOTRESOLVED */
/* Description: Address not resolved */

/* Bit 0 : Address not resolved */
#define AAR_EVENTS_NOTRESOLVED_EVENTS_NOTRESOLVED_Pos (0UL) /*!< Position of EVENTS_NOTRESOLVED field. */
#define AAR_EVENTS_NOTRESOLVED_EVENTS_NOTRESOLVED_Msk (0x1UL << AAR_EVENTS_NOTRESOLVED_EVENTS_NOTRESOLVED_Pos) /*!< Bit mask of EVENTS_NOTRESOLVED field. */
#define AAR_EVENTS_NOTRESOLVED_EVENTS_NOTRESOLVED_NotGenerated (0UL) /*!< Event not generated */
#define AAR_EVENTS_NOTRESOLVED_EVENTS_NOTRESOLVED_Generated (1UL) /*!< Event generated */

/* Register: AAR_PUBLISH_END */
/* Description: Publish configuration for event END */

/* Bit 31 :   */
#define AAR_PUBLISH_END_EN_Pos (31UL) /*!< Position of EN field. */
#define AAR_PUBLISH_END_EN_Msk (0x1UL << AAR_PUBLISH_END_EN_Pos) /*!< Bit mask of EN field. */
#define AAR_PUBLISH_END_EN_Disabled (0UL) /*!< Disable publishing */
#define AAR_PUBLISH_END_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event END will publish to. */
#define AAR_PUBLISH_END_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define AAR_PUBLISH_END_CHIDX_Msk (0xFFUL << AAR_PUBLISH_END_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: AAR_PUBLISH_RESOLVED */
/* Description: Publish configuration for event RESOLVED */

/* Bit 31 :   */
#define AAR_PUBLISH_RESOLVED_EN_Pos (31UL) /*!< Position of EN field. */
#define AAR_PUBLISH_RESOLVED_EN_Msk (0x1UL << AAR_PUBLISH_RESOLVED_EN_Pos) /*!< Bit mask of EN field. */
#define AAR_PUBLISH_RESOLVED_EN_Disabled (0UL) /*!< Disable publishing */
#define AAR_PUBLISH_RESOLVED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RESOLVED will publish to. */
#define AAR_PUBLISH_RESOLVED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define AAR_PUBLISH_RESOLVED_CHIDX_Msk (0xFFUL << AAR_PUBLISH_RESOLVED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: AAR_PUBLISH_NOTRESOLVED */
/* Description: Publish configuration for event NOTRESOLVED */

/* Bit 31 :   */
#define AAR_PUBLISH_NOTRESOLVED_EN_Pos (31UL) /*!< Position of EN field. */
#define AAR_PUBLISH_NOTRESOLVED_EN_Msk (0x1UL << AAR_PUBLISH_NOTRESOLVED_EN_Pos) /*!< Bit mask of EN field. */
#define AAR_PUBLISH_NOTRESOLVED_EN_Disabled (0UL) /*!< Disable publishing */
#define AAR_PUBLISH_NOTRESOLVED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event NOTRESOLVED will publish to. */
#define AAR_PUBLISH_NOTRESOLVED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define AAR_PUBLISH_NOTRESOLVED_CHIDX_Msk (0xFFUL << AAR_PUBLISH_NOTRESOLVED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: AAR_INTENSET */
/* Description: Enable interrupt */

/* Bit 2 : Write '1' to enable interrupt for event NOTRESOLVED */
#define AAR_INTENSET_NOTRESOLVED_Pos (2UL) /*!< Position of NOTRESOLVED field. */
#define AAR_INTENSET_NOTRESOLVED_Msk (0x1UL << AAR_INTENSET_NOTRESOLVED_Pos) /*!< Bit mask of NOTRESOLVED field. */
#define AAR_INTENSET_NOTRESOLVED_Disabled (0UL) /*!< Read: Disabled */
#define AAR_INTENSET_NOTRESOLVED_Enabled (1UL) /*!< Read: Enabled */
#define AAR_INTENSET_NOTRESOLVED_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event RESOLVED */
#define AAR_INTENSET_RESOLVED_Pos (1UL) /*!< Position of RESOLVED field. */
#define AAR_INTENSET_RESOLVED_Msk (0x1UL << AAR_INTENSET_RESOLVED_Pos) /*!< Bit mask of RESOLVED field. */
#define AAR_INTENSET_RESOLVED_Disabled (0UL) /*!< Read: Disabled */
#define AAR_INTENSET_RESOLVED_Enabled (1UL) /*!< Read: Enabled */
#define AAR_INTENSET_RESOLVED_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event END */
#define AAR_INTENSET_END_Pos (0UL) /*!< Position of END field. */
#define AAR_INTENSET_END_Msk (0x1UL << AAR_INTENSET_END_Pos) /*!< Bit mask of END field. */
#define AAR_INTENSET_END_Disabled (0UL) /*!< Read: Disabled */
#define AAR_INTENSET_END_Enabled (1UL) /*!< Read: Enabled */
#define AAR_INTENSET_END_Set (1UL) /*!< Enable */

/* Register: AAR_INTENCLR */
/* Description: Disable interrupt */

/* Bit 2 : Write '1' to disable interrupt for event NOTRESOLVED */
#define AAR_INTENCLR_NOTRESOLVED_Pos (2UL) /*!< Position of NOTRESOLVED field. */
#define AAR_INTENCLR_NOTRESOLVED_Msk (0x1UL << AAR_INTENCLR_NOTRESOLVED_Pos) /*!< Bit mask of NOTRESOLVED field. */
#define AAR_INTENCLR_NOTRESOLVED_Disabled (0UL) /*!< Read: Disabled */
#define AAR_INTENCLR_NOTRESOLVED_Enabled (1UL) /*!< Read: Enabled */
#define AAR_INTENCLR_NOTRESOLVED_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event RESOLVED */
#define AAR_INTENCLR_RESOLVED_Pos (1UL) /*!< Position of RESOLVED field. */
#define AAR_INTENCLR_RESOLVED_Msk (0x1UL << AAR_INTENCLR_RESOLVED_Pos) /*!< Bit mask of RESOLVED field. */
#define AAR_INTENCLR_RESOLVED_Disabled (0UL) /*!< Read: Disabled */
#define AAR_INTENCLR_RESOLVED_Enabled (1UL) /*!< Read: Enabled */
#define AAR_INTENCLR_RESOLVED_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event END */
#define AAR_INTENCLR_END_Pos (0UL) /*!< Position of END field. */
#define AAR_INTENCLR_END_Msk (0x1UL << AAR_INTENCLR_END_Pos) /*!< Bit mask of END field. */
#define AAR_INTENCLR_END_Disabled (0UL) /*!< Read: Disabled */
#define AAR_INTENCLR_END_Enabled (1UL) /*!< Read: Enabled */
#define AAR_INTENCLR_END_Clear (1UL) /*!< Disable */

/* Register: AAR_STATUS */
/* Description: Resolution status */

/* Bits 3..0 : The IRK that was used last time an address was resolved */
#define AAR_STATUS_STATUS_Pos (0UL) /*!< Position of STATUS field. */
#define AAR_STATUS_STATUS_Msk (0xFUL << AAR_STATUS_STATUS_Pos) /*!< Bit mask of STATUS field. */

/* Register: AAR_ENABLE */
/* Description: Enable AAR */

/* Bits 1..0 : Enable or disable AAR */
#define AAR_ENABLE_ENABLE_Pos (0UL) /*!< Position of ENABLE field. */
#define AAR_ENABLE_ENABLE_Msk (0x3UL << AAR_ENABLE_ENABLE_Pos) /*!< Bit mask of ENABLE field. */
#define AAR_ENABLE_ENABLE_Disabled (0UL) /*!< Disable */
#define AAR_ENABLE_ENABLE_Enabled (3UL) /*!< Enable */

/* Register: AAR_NIRK */
/* Description: Number of IRKs */

/* Bits 4..0 : Number of Identity Root Keys available in the IRK data structure */
#define AAR_NIRK_NIRK_Pos (0UL) /*!< Position of NIRK field. */
#define AAR_NIRK_NIRK_Msk (0x1FUL << AAR_NIRK_NIRK_Pos) /*!< Bit mask of NIRK field. */

/* Register: AAR_IRKPTR */
/* Description: Pointer to IRK data structure */

/* Bits 31..0 : Pointer to the IRK data structure */
#define AAR_IRKPTR_IRKPTR_Pos (0UL) /*!< Position of IRKPTR field. */
#define AAR_IRKPTR_IRKPTR_Msk (0xFFFFFFFFUL << AAR_IRKPTR_IRKPTR_Pos) /*!< Bit mask of IRKPTR field. */

/* Register: AAR_ADDRPTR */
/* Description: Pointer to the resolvable address */

/* Bits 31..0 : Pointer to the resolvable address (6-bytes) */
#define AAR_ADDRPTR_ADDRPTR_Pos (0UL) /*!< Position of ADDRPTR field. */
#define AAR_ADDRPTR_ADDRPTR_Msk (0xFFFFFFFFUL << AAR_ADDRPTR_ADDRPTR_Pos) /*!< Bit mask of ADDRPTR field. */

/* Register: AAR_SCRATCHPTR */
/* Description: Pointer to data area used for temporary storage */

/* Bits 31..0 : Pointer to a scratch data area used for temporary storage during resolution. A space of minimum 3 bytes must be reserved. */
#define AAR_SCRATCHPTR_SCRATCHPTR_Pos (0UL) /*!< Position of SCRATCHPTR field. */
#define AAR_SCRATCHPTR_SCRATCHPTR_Msk (0xFFFFFFFFUL << AAR_SCRATCHPTR_SCRATCHPTR_Pos) /*!< Bit mask of SCRATCHPTR field. */


/* Peripheral: ACL */
/* Description: Access control lists */

/* Register: ACL_ACL_ADDR */
/* Description: Description cluster: Start address of region to protect. The start address must be word-aligned. */

/* Bits 31..0 : Start address of flash region n. The start address must point to a flash page boundary. */
#define ACL_ACL_ADDR_ADDR_Pos (0UL) /*!< Position of ADDR field. */
#define ACL_ACL_ADDR_ADDR_Msk (0xFFFFFFFFUL << ACL_ACL_ADDR_ADDR_Pos) /*!< Bit mask of ADDR field. */

/* Register: ACL_ACL_SIZE */
/* Description: Description cluster: Size of region to protect counting from address ACL[n].ADDR. Writing a '0' has no effect. */

/* Bits 31..0 : Size of flash region n in bytes. Must be a multiple of the flash page size. */
#define ACL_ACL_SIZE_SIZE_Pos (0UL) /*!< Position of SIZE field. */
#define ACL_ACL_SIZE_SIZE_Msk (0xFFFFFFFFUL << ACL_ACL_SIZE_SIZE_Pos) /*!< Bit mask of SIZE field. */

/* Register: ACL_ACL_PERM */
/* Description: Description cluster: Access permissions for region n as defined by start address ACL[n].ADDR and size ACL[n].SIZE */

/* Bit 2 : Configure read permissions for region n. Writing a '0' has no effect. */
#define ACL_ACL_PERM_READ_Pos (2UL) /*!< Position of READ field. */
#define ACL_ACL_PERM_READ_Msk (0x1UL << ACL_ACL_PERM_READ_Pos) /*!< Bit mask of READ field. */
#define ACL_ACL_PERM_READ_Enable (0UL) /*!< Allow read instructions to region n. */
#define ACL_ACL_PERM_READ_Disable (1UL) /*!< Block read instructions to region n. */

/* Bit 1 : Configure write and erase permissions for region n. Writing a '0' has no effect. */
#define ACL_ACL_PERM_WRITE_Pos (1UL) /*!< Position of WRITE field. */
#define ACL_ACL_PERM_WRITE_Msk (0x1UL << ACL_ACL_PERM_WRITE_Pos) /*!< Bit mask of WRITE field. */
#define ACL_ACL_PERM_WRITE_Enable (0UL) /*!< Allow write and erase instructions to region n. */
#define ACL_ACL_PERM_WRITE_Disable (1UL) /*!< Block write and erase instructions to region n. */


/* Peripheral: MUTEX */
/* Description: MUTEX 0 */

/* Register: MUTEX_MUTEX */
/* Description: Description collection: Mutex register */

/* Bit 0 : Mutex register n */
#define MUTEX_MUTEX_MUTEX_Pos (0UL) /*!< Position of MUTEX field. */
#define MUTEX_MUTEX_MUTEX_Msk (0x1UL << MUTEX_MUTEX_MUTEX_Pos) /*!< Bit mask of MUTEX field. */
#define MUTEX_MUTEX_MUTEX_Unlocked (0UL) /*!< Mutex n is in unlocked state */
#define MUTEX_MUTEX_MUTEX_Locked (1UL) /*!< Mutex n is in locked state */


/* Peripheral: CCM */
/* Description: AES CCM mode encryption */

/* Register: CCM_TASKS_KSGEN */
/* Description: Start generation of keystream. This operation will stop by itself when completed. */

/* Bit 0 : Start generation of keystream. This operation will stop by itself when completed. */
#define CCM_TASKS_KSGEN_TASKS_KSGEN_Pos (0UL) /*!< Position of TASKS_KSGEN field. */
#define CCM_TASKS_KSGEN_TASKS_KSGEN_Msk (0x1UL << CCM_TASKS_KSGEN_TASKS_KSGEN_Pos) /*!< Bit mask of TASKS_KSGEN field. */
#define CCM_TASKS_KSGEN_TASKS_KSGEN_Trigger (1UL) /*!< Trigger task */

/* Register: CCM_TASKS_CRYPT */
/* Description: Start encryption/decryption. This operation will stop by itself when completed. */

/* Bit 0 : Start encryption/decryption. This operation will stop by itself when completed. */
#define CCM_TASKS_CRYPT_TASKS_CRYPT_Pos (0UL) /*!< Position of TASKS_CRYPT field. */
#define CCM_TASKS_CRYPT_TASKS_CRYPT_Msk (0x1UL << CCM_TASKS_CRYPT_TASKS_CRYPT_Pos) /*!< Bit mask of TASKS_CRYPT field. */
#define CCM_TASKS_CRYPT_TASKS_CRYPT_Trigger (1UL) /*!< Trigger task */

/* Register: CCM_TASKS_STOP */
/* Description: Stop encryption/decryption */

/* Bit 0 : Stop encryption/decryption */
#define CCM_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define CCM_TASKS_STOP_TASKS_STOP_Msk (0x1UL << CCM_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define CCM_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: CCM_TASKS_RATEOVERRIDE */
/* Description: Override DATARATE setting in MODE register with the contents of the RATEOVERRIDE register for any ongoing encryption/decryption */

/* Bit 0 : Override DATARATE setting in MODE register with the contents of the RATEOVERRIDE register for any ongoing encryption/decryption */
#define CCM_TASKS_RATEOVERRIDE_TASKS_RATEOVERRIDE_Pos (0UL) /*!< Position of TASKS_RATEOVERRIDE field. */
#define CCM_TASKS_RATEOVERRIDE_TASKS_RATEOVERRIDE_Msk (0x1UL << CCM_TASKS_RATEOVERRIDE_TASKS_RATEOVERRIDE_Pos) /*!< Bit mask of TASKS_RATEOVERRIDE field. */
#define CCM_TASKS_RATEOVERRIDE_TASKS_RATEOVERRIDE_Trigger (1UL) /*!< Trigger task */

/* Register: CCM_SUBSCRIBE_KSGEN */
/* Description: Subscribe configuration for task KSGEN */

/* Bit 31 :   */
#define CCM_SUBSCRIBE_KSGEN_EN_Pos (31UL) /*!< Position of EN field. */
#define CCM_SUBSCRIBE_KSGEN_EN_Msk (0x1UL << CCM_SUBSCRIBE_KSGEN_EN_Pos) /*!< Bit mask of EN field. */
#define CCM_SUBSCRIBE_KSGEN_EN_Disabled (0UL) /*!< Disable subscription */
#define CCM_SUBSCRIBE_KSGEN_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task KSGEN will subscribe to */
#define CCM_SUBSCRIBE_KSGEN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CCM_SUBSCRIBE_KSGEN_CHIDX_Msk (0xFFUL << CCM_SUBSCRIBE_KSGEN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CCM_SUBSCRIBE_CRYPT */
/* Description: Subscribe configuration for task CRYPT */

/* Bit 31 :   */
#define CCM_SUBSCRIBE_CRYPT_EN_Pos (31UL) /*!< Position of EN field. */
#define CCM_SUBSCRIBE_CRYPT_EN_Msk (0x1UL << CCM_SUBSCRIBE_CRYPT_EN_Pos) /*!< Bit mask of EN field. */
#define CCM_SUBSCRIBE_CRYPT_EN_Disabled (0UL) /*!< Disable subscription */
#define CCM_SUBSCRIBE_CRYPT_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CRYPT will subscribe to */
#define CCM_SUBSCRIBE_CRYPT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CCM_SUBSCRIBE_CRYPT_CHIDX_Msk (0xFFUL << CCM_SUBSCRIBE_CRYPT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CCM_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define CCM_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define CCM_SUBSCRIBE_STOP_EN_Msk (0x1UL << CCM_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define CCM_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define CCM_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define CCM_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CCM_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << CCM_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CCM_SUBSCRIBE_RATEOVERRIDE */
/* Description: Subscribe configuration for task RATEOVERRIDE */

/* Bit 31 :   */
#define CCM_SUBSCRIBE_RATEOVERRIDE_EN_Pos (31UL) /*!< Position of EN field. */
#define CCM_SUBSCRIBE_RATEOVERRIDE_EN_Msk (0x1UL << CCM_SUBSCRIBE_RATEOVERRIDE_EN_Pos) /*!< Bit mask of EN field. */
#define CCM_SUBSCRIBE_RATEOVERRIDE_EN_Disabled (0UL) /*!< Disable subscription */
#define CCM_SUBSCRIBE_RATEOVERRIDE_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RATEOVERRIDE will subscribe to */
#define CCM_SUBSCRIBE_RATEOVERRIDE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CCM_SUBSCRIBE_RATEOVERRIDE_CHIDX_Msk (0xFFUL << CCM_SUBSCRIBE_RATEOVERRIDE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CCM_EVENTS_ENDKSGEN */
/* Description: Keystream generation complete */

/* Bit 0 : Keystream generation complete */
#define CCM_EVENTS_ENDKSGEN_EVENTS_ENDKSGEN_Pos (0UL) /*!< Position of EVENTS_ENDKSGEN field. */
#define CCM_EVENTS_ENDKSGEN_EVENTS_ENDKSGEN_Msk (0x1UL << CCM_EVENTS_ENDKSGEN_EVENTS_ENDKSGEN_Pos) /*!< Bit mask of EVENTS_ENDKSGEN field. */
#define CCM_EVENTS_ENDKSGEN_EVENTS_ENDKSGEN_NotGenerated (0UL) /*!< Event not generated */
#define CCM_EVENTS_ENDKSGEN_EVENTS_ENDKSGEN_Generated (1UL) /*!< Event generated */

/* Register: CCM_EVENTS_ENDCRYPT */
/* Description: Encrypt/decrypt complete */

/* Bit 0 : Encrypt/decrypt complete */
#define CCM_EVENTS_ENDCRYPT_EVENTS_ENDCRYPT_Pos (0UL) /*!< Position of EVENTS_ENDCRYPT field. */
#define CCM_EVENTS_ENDCRYPT_EVENTS_ENDCRYPT_Msk (0x1UL << CCM_EVENTS_ENDCRYPT_EVENTS_ENDCRYPT_Pos) /*!< Bit mask of EVENTS_ENDCRYPT field. */
#define CCM_EVENTS_ENDCRYPT_EVENTS_ENDCRYPT_NotGenerated (0UL) /*!< Event not generated */
#define CCM_EVENTS_ENDCRYPT_EVENTS_ENDCRYPT_Generated (1UL) /*!< Event generated */

/* Register: CCM_EVENTS_ERROR */
/* Description: Deprecated register - CCM error event */

/* Bit 0 : Deprecated field -  CCM error event */
#define CCM_EVENTS_ERROR_EVENTS_ERROR_Pos (0UL) /*!< Position of EVENTS_ERROR field. */
#define CCM_EVENTS_ERROR_EVENTS_ERROR_Msk (0x1UL << CCM_EVENTS_ERROR_EVENTS_ERROR_Pos) /*!< Bit mask of EVENTS_ERROR field. */
#define CCM_EVENTS_ERROR_EVENTS_ERROR_NotGenerated (0UL) /*!< Event not generated */
#define CCM_EVENTS_ERROR_EVENTS_ERROR_Generated (1UL) /*!< Event generated */

/* Register: CCM_PUBLISH_ENDKSGEN */
/* Description: Publish configuration for event ENDKSGEN */

/* Bit 31 :   */
#define CCM_PUBLISH_ENDKSGEN_EN_Pos (31UL) /*!< Position of EN field. */
#define CCM_PUBLISH_ENDKSGEN_EN_Msk (0x1UL << CCM_PUBLISH_ENDKSGEN_EN_Pos) /*!< Bit mask of EN field. */
#define CCM_PUBLISH_ENDKSGEN_EN_Disabled (0UL) /*!< Disable publishing */
#define CCM_PUBLISH_ENDKSGEN_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDKSGEN will publish to. */
#define CCM_PUBLISH_ENDKSGEN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CCM_PUBLISH_ENDKSGEN_CHIDX_Msk (0xFFUL << CCM_PUBLISH_ENDKSGEN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CCM_PUBLISH_ENDCRYPT */
/* Description: Publish configuration for event ENDCRYPT */

/* Bit 31 :   */
#define CCM_PUBLISH_ENDCRYPT_EN_Pos (31UL) /*!< Position of EN field. */
#define CCM_PUBLISH_ENDCRYPT_EN_Msk (0x1UL << CCM_PUBLISH_ENDCRYPT_EN_Pos) /*!< Bit mask of EN field. */
#define CCM_PUBLISH_ENDCRYPT_EN_Disabled (0UL) /*!< Disable publishing */
#define CCM_PUBLISH_ENDCRYPT_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDCRYPT will publish to. */
#define CCM_PUBLISH_ENDCRYPT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CCM_PUBLISH_ENDCRYPT_CHIDX_Msk (0xFFUL << CCM_PUBLISH_ENDCRYPT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CCM_PUBLISH_ERROR */
/* Description: Deprecated register - Publish configuration for event ERROR */

/* Bit 31 :   */
#define CCM_PUBLISH_ERROR_EN_Pos (31UL) /*!< Position of EN field. */
#define CCM_PUBLISH_ERROR_EN_Msk (0x1UL << CCM_PUBLISH_ERROR_EN_Pos) /*!< Bit mask of EN field. */
#define CCM_PUBLISH_ERROR_EN_Disabled (0UL) /*!< Disable publishing */
#define CCM_PUBLISH_ERROR_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ERROR will publish to. */
#define CCM_PUBLISH_ERROR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CCM_PUBLISH_ERROR_CHIDX_Msk (0xFFUL << CCM_PUBLISH_ERROR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CCM_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 0 : Shortcut between event ENDKSGEN and task CRYPT */
#define CCM_SHORTS_ENDKSGEN_CRYPT_Pos (0UL) /*!< Position of ENDKSGEN_CRYPT field. */
#define CCM_SHORTS_ENDKSGEN_CRYPT_Msk (0x1UL << CCM_SHORTS_ENDKSGEN_CRYPT_Pos) /*!< Bit mask of ENDKSGEN_CRYPT field. */
#define CCM_SHORTS_ENDKSGEN_CRYPT_Disabled (0UL) /*!< Disable shortcut */
#define CCM_SHORTS_ENDKSGEN_CRYPT_Enabled (1UL) /*!< Enable shortcut */

/* Register: CCM_INTENSET */
/* Description: Enable interrupt */

/* Bit 2 : Deprecated intsetfield -  Write '1' to enable interrupt for event ERROR */
#define CCM_INTENSET_ERROR_Pos (2UL) /*!< Position of ERROR field. */
#define CCM_INTENSET_ERROR_Msk (0x1UL << CCM_INTENSET_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define CCM_INTENSET_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define CCM_INTENSET_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define CCM_INTENSET_ERROR_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event ENDCRYPT */
#define CCM_INTENSET_ENDCRYPT_Pos (1UL) /*!< Position of ENDCRYPT field. */
#define CCM_INTENSET_ENDCRYPT_Msk (0x1UL << CCM_INTENSET_ENDCRYPT_Pos) /*!< Bit mask of ENDCRYPT field. */
#define CCM_INTENSET_ENDCRYPT_Disabled (0UL) /*!< Read: Disabled */
#define CCM_INTENSET_ENDCRYPT_Enabled (1UL) /*!< Read: Enabled */
#define CCM_INTENSET_ENDCRYPT_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event ENDKSGEN */
#define CCM_INTENSET_ENDKSGEN_Pos (0UL) /*!< Position of ENDKSGEN field. */
#define CCM_INTENSET_ENDKSGEN_Msk (0x1UL << CCM_INTENSET_ENDKSGEN_Pos) /*!< Bit mask of ENDKSGEN field. */
#define CCM_INTENSET_ENDKSGEN_Disabled (0UL) /*!< Read: Disabled */
#define CCM_INTENSET_ENDKSGEN_Enabled (1UL) /*!< Read: Enabled */
#define CCM_INTENSET_ENDKSGEN_Set (1UL) /*!< Enable */

/* Register: CCM_INTENCLR */
/* Description: Disable interrupt */

/* Bit 2 : Deprecated intclrfield -  Write '1' to disable interrupt for event ERROR */
#define CCM_INTENCLR_ERROR_Pos (2UL) /*!< Position of ERROR field. */
#define CCM_INTENCLR_ERROR_Msk (0x1UL << CCM_INTENCLR_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define CCM_INTENCLR_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define CCM_INTENCLR_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define CCM_INTENCLR_ERROR_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event ENDCRYPT */
#define CCM_INTENCLR_ENDCRYPT_Pos (1UL) /*!< Position of ENDCRYPT field. */
#define CCM_INTENCLR_ENDCRYPT_Msk (0x1UL << CCM_INTENCLR_ENDCRYPT_Pos) /*!< Bit mask of ENDCRYPT field. */
#define CCM_INTENCLR_ENDCRYPT_Disabled (0UL) /*!< Read: Disabled */
#define CCM_INTENCLR_ENDCRYPT_Enabled (1UL) /*!< Read: Enabled */
#define CCM_INTENCLR_ENDCRYPT_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event ENDKSGEN */
#define CCM_INTENCLR_ENDKSGEN_Pos (0UL) /*!< Position of ENDKSGEN field. */
#define CCM_INTENCLR_ENDKSGEN_Msk (0x1UL << CCM_INTENCLR_ENDKSGEN_Pos) /*!< Bit mask of ENDKSGEN field. */
#define CCM_INTENCLR_ENDKSGEN_Disabled (0UL) /*!< Read: Disabled */
#define CCM_INTENCLR_ENDKSGEN_Enabled (1UL) /*!< Read: Enabled */
#define CCM_INTENCLR_ENDKSGEN_Clear (1UL) /*!< Disable */

/* Register: CCM_MICSTATUS */
/* Description: MIC check result */

/* Bit 0 : The result of the MIC check performed during the previous decryption operation */
#define CCM_MICSTATUS_MICSTATUS_Pos (0UL) /*!< Position of MICSTATUS field. */
#define CCM_MICSTATUS_MICSTATUS_Msk (0x1UL << CCM_MICSTATUS_MICSTATUS_Pos) /*!< Bit mask of MICSTATUS field. */
#define CCM_MICSTATUS_MICSTATUS_CheckFailed (0UL) /*!< MIC check failed */
#define CCM_MICSTATUS_MICSTATUS_CheckPassed (1UL) /*!< MIC check passed */

/* Register: CCM_ENABLE */
/* Description: Enable */

/* Bits 1..0 : Enable or disable CCM */
#define CCM_ENABLE_ENABLE_Pos (0UL) /*!< Position of ENABLE field. */
#define CCM_ENABLE_ENABLE_Msk (0x3UL << CCM_ENABLE_ENABLE_Pos) /*!< Bit mask of ENABLE field. */
#define CCM_ENABLE_ENABLE_Disabled (0UL) /*!< Disable */
#define CCM_ENABLE_ENABLE_Enabled (2UL) /*!< Enable */

/* Register: CCM_MODE */
/* Description: Operation mode */

/* Bit 24 : Packet length configuration */
#define CCM_MODE_LENGTH_Pos (24UL) /*!< Position of LENGTH field. */
#define CCM_MODE_LENGTH_Msk (0x1UL << CCM_MODE_LENGTH_Pos) /*!< Bit mask of LENGTH field. */
#define CCM_MODE_LENGTH_Default (0UL) /*!< Default length. Effective length of LENGTH field in encrypted/decrypted packet is 5 bits. A keystream for packet payloads up to 27 bytes will be generated. */
#define CCM_MODE_LENGTH_Extended (1UL) /*!< Extended length. Effective length of LENGTH field in encrypted/decrypted packet is 8 bits. A keystream for packet payloads up to MAXPACKETSIZE bytes will be generated. */

/* Bits 17..16 : Radio data rate that the CCM shall run synchronous with */
#define CCM_MODE_DATARATE_Pos (16UL) /*!< Position of DATARATE field. */
#define CCM_MODE_DATARATE_Msk (0x3UL << CCM_MODE_DATARATE_Pos) /*!< Bit mask of DATARATE field. */
#define CCM_MODE_DATARATE_1Mbit (0UL) /*!< 1 Mbps */
#define CCM_MODE_DATARATE_2Mbit (1UL) /*!< 2 Mbps */
#define CCM_MODE_DATARATE_125Kbps (2UL) /*!< 125 kbps */
#define CCM_MODE_DATARATE_500Kbps (3UL) /*!< 500 kbps */

/* Bit 0 : The mode of operation to be used. Settings in this register apply whenever either the KSGEN task or the CRYPT task is triggered. */
#define CCM_MODE_MODE_Pos (0UL) /*!< Position of MODE field. */
#define CCM_MODE_MODE_Msk (0x1UL << CCM_MODE_MODE_Pos) /*!< Bit mask of MODE field. */
#define CCM_MODE_MODE_Encryption (0UL) /*!< AES CCM packet encryption mode */
#define CCM_MODE_MODE_Decryption (1UL) /*!< AES CCM packet decryption mode */

/* Register: CCM_CNFPTR */
/* Description: Pointer to data structure holding the AES key and the NONCE vector */

/* Bits 31..0 : Pointer to the data structure holding the AES key and the CCM NONCE vector (see table CCM data structure overview) */
#define CCM_CNFPTR_CNFPTR_Pos (0UL) /*!< Position of CNFPTR field. */
#define CCM_CNFPTR_CNFPTR_Msk (0xFFFFFFFFUL << CCM_CNFPTR_CNFPTR_Pos) /*!< Bit mask of CNFPTR field. */

/* Register: CCM_INPTR */
/* Description: Input pointer */

/* Bits 31..0 : Input pointer */
#define CCM_INPTR_INPTR_Pos (0UL) /*!< Position of INPTR field. */
#define CCM_INPTR_INPTR_Msk (0xFFFFFFFFUL << CCM_INPTR_INPTR_Pos) /*!< Bit mask of INPTR field. */

/* Register: CCM_OUTPTR */
/* Description: Output pointer */

/* Bits 31..0 : Output pointer */
#define CCM_OUTPTR_OUTPTR_Pos (0UL) /*!< Position of OUTPTR field. */
#define CCM_OUTPTR_OUTPTR_Msk (0xFFFFFFFFUL << CCM_OUTPTR_OUTPTR_Pos) /*!< Bit mask of OUTPTR field. */

/* Register: CCM_SCRATCHPTR */
/* Description: Pointer to data area used for temporary storage */

/* Bits 31..0 : Pointer to a scratch data area used for temporary storage during keystream generation,
        MIC generation and encryption/decryption. */
#define CCM_SCRATCHPTR_SCRATCHPTR_Pos (0UL) /*!< Position of SCRATCHPTR field. */
#define CCM_SCRATCHPTR_SCRATCHPTR_Msk (0xFFFFFFFFUL << CCM_SCRATCHPTR_SCRATCHPTR_Pos) /*!< Bit mask of SCRATCHPTR field. */

/* Register: CCM_MAXPACKETSIZE */
/* Description: Length of keystream generated when MODE.LENGTH = Extended */

/* Bits 7..0 : Length of keystream generated when MODE.LENGTH = Extended. This value must be greater than or equal to the subsequent packet payload to be encrypted/decrypted. */
#define CCM_MAXPACKETSIZE_MAXPACKETSIZE_Pos (0UL) /*!< Position of MAXPACKETSIZE field. */
#define CCM_MAXPACKETSIZE_MAXPACKETSIZE_Msk (0xFFUL << CCM_MAXPACKETSIZE_MAXPACKETSIZE_Pos) /*!< Bit mask of MAXPACKETSIZE field. */

/* Register: CCM_RATEOVERRIDE */
/* Description: Data rate override setting. */

/* Bits 1..0 : Data rate override setting */
#define CCM_RATEOVERRIDE_RATEOVERRIDE_Pos (0UL) /*!< Position of RATEOVERRIDE field. */
#define CCM_RATEOVERRIDE_RATEOVERRIDE_Msk (0x3UL << CCM_RATEOVERRIDE_RATEOVERRIDE_Pos) /*!< Bit mask of RATEOVERRIDE field. */
#define CCM_RATEOVERRIDE_RATEOVERRIDE_1Mbit (0UL) /*!< 1 Mbps */
#define CCM_RATEOVERRIDE_RATEOVERRIDE_2Mbit (1UL) /*!< 2 Mbps */
#define CCM_RATEOVERRIDE_RATEOVERRIDE_125Kbps (2UL) /*!< 125 kbps */
#define CCM_RATEOVERRIDE_RATEOVERRIDE_500Kbps (3UL) /*!< 500 kbps */

/* Register: CCM_HEADERMASK */
/* Description: Header (S0) mask. */

/* Bits 7..0 : Header (S0) mask */
#define CCM_HEADERMASK_HEADERMASK_Pos (0UL) /*!< Position of HEADERMASK field. */
#define CCM_HEADERMASK_HEADERMASK_Msk (0xFFUL << CCM_HEADERMASK_HEADERMASK_Pos) /*!< Bit mask of HEADERMASK field. */


/* Peripheral: CLOCK */
/* Description: Clock management */

/* Register: CLOCK_TASKS_HFCLKSTART */
/* Description: Start HFCLK128M/HFCLK64M source as selected in HFCLKSRC */

/* Bit 0 : Start HFCLK128M/HFCLK64M source as selected in HFCLKSRC */
#define CLOCK_TASKS_HFCLKSTART_TASKS_HFCLKSTART_Pos (0UL) /*!< Position of TASKS_HFCLKSTART field. */
#define CLOCK_TASKS_HFCLKSTART_TASKS_HFCLKSTART_Msk (0x1UL << CLOCK_TASKS_HFCLKSTART_TASKS_HFCLKSTART_Pos) /*!< Bit mask of TASKS_HFCLKSTART field. */
#define CLOCK_TASKS_HFCLKSTART_TASKS_HFCLKSTART_Trigger (1UL) /*!< Trigger task */

/* Register: CLOCK_TASKS_HFCLKSTOP */
/* Description: Stop HFCLK128M/HFCLK64M source */

/* Bit 0 : Stop HFCLK128M/HFCLK64M source */
#define CLOCK_TASKS_HFCLKSTOP_TASKS_HFCLKSTOP_Pos (0UL) /*!< Position of TASKS_HFCLKSTOP field. */
#define CLOCK_TASKS_HFCLKSTOP_TASKS_HFCLKSTOP_Msk (0x1UL << CLOCK_TASKS_HFCLKSTOP_TASKS_HFCLKSTOP_Pos) /*!< Bit mask of TASKS_HFCLKSTOP field. */
#define CLOCK_TASKS_HFCLKSTOP_TASKS_HFCLKSTOP_Trigger (1UL) /*!< Trigger task */

/* Register: CLOCK_TASKS_LFCLKSTART */
/* Description: Start LFCLK source as selected in LFCLKSRC */

/* Bit 0 : Start LFCLK source as selected in LFCLKSRC */
#define CLOCK_TASKS_LFCLKSTART_TASKS_LFCLKSTART_Pos (0UL) /*!< Position of TASKS_LFCLKSTART field. */
#define CLOCK_TASKS_LFCLKSTART_TASKS_LFCLKSTART_Msk (0x1UL << CLOCK_TASKS_LFCLKSTART_TASKS_LFCLKSTART_Pos) /*!< Bit mask of TASKS_LFCLKSTART field. */
#define CLOCK_TASKS_LFCLKSTART_TASKS_LFCLKSTART_Trigger (1UL) /*!< Trigger task */

/* Register: CLOCK_TASKS_LFCLKSTOP */
/* Description: Stop LFCLK source */

/* Bit 0 : Stop LFCLK source */
#define CLOCK_TASKS_LFCLKSTOP_TASKS_LFCLKSTOP_Pos (0UL) /*!< Position of TASKS_LFCLKSTOP field. */
#define CLOCK_TASKS_LFCLKSTOP_TASKS_LFCLKSTOP_Msk (0x1UL << CLOCK_TASKS_LFCLKSTOP_TASKS_LFCLKSTOP_Pos) /*!< Bit mask of TASKS_LFCLKSTOP field. */
#define CLOCK_TASKS_LFCLKSTOP_TASKS_LFCLKSTOP_Trigger (1UL) /*!< Trigger task */

/* Register: CLOCK_TASKS_CAL */
/* Description: Start calibration of LFRC oscillator */

/* Bit 0 : Start calibration of LFRC oscillator */
#define CLOCK_TASKS_CAL_TASKS_CAL_Pos (0UL) /*!< Position of TASKS_CAL field. */
#define CLOCK_TASKS_CAL_TASKS_CAL_Msk (0x1UL << CLOCK_TASKS_CAL_TASKS_CAL_Pos) /*!< Bit mask of TASKS_CAL field. */
#define CLOCK_TASKS_CAL_TASKS_CAL_Trigger (1UL) /*!< Trigger task */

/* Register: CLOCK_SUBSCRIBE_HFCLKSTART */
/* Description: Subscribe configuration for task HFCLKSTART */

/* Bit 31 :   */
#define CLOCK_SUBSCRIBE_HFCLKSTART_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_SUBSCRIBE_HFCLKSTART_EN_Msk (0x1UL << CLOCK_SUBSCRIBE_HFCLKSTART_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_SUBSCRIBE_HFCLKSTART_EN_Disabled (0UL) /*!< Disable subscription */
#define CLOCK_SUBSCRIBE_HFCLKSTART_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task HFCLKSTART will subscribe to */
#define CLOCK_SUBSCRIBE_HFCLKSTART_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_SUBSCRIBE_HFCLKSTART_CHIDX_Msk (0xFFUL << CLOCK_SUBSCRIBE_HFCLKSTART_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_SUBSCRIBE_HFCLKSTOP */
/* Description: Subscribe configuration for task HFCLKSTOP */

/* Bit 31 :   */
#define CLOCK_SUBSCRIBE_HFCLKSTOP_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_SUBSCRIBE_HFCLKSTOP_EN_Msk (0x1UL << CLOCK_SUBSCRIBE_HFCLKSTOP_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_SUBSCRIBE_HFCLKSTOP_EN_Disabled (0UL) /*!< Disable subscription */
#define CLOCK_SUBSCRIBE_HFCLKSTOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task HFCLKSTOP will subscribe to */
#define CLOCK_SUBSCRIBE_HFCLKSTOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_SUBSCRIBE_HFCLKSTOP_CHIDX_Msk (0xFFUL << CLOCK_SUBSCRIBE_HFCLKSTOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_SUBSCRIBE_LFCLKSTART */
/* Description: Subscribe configuration for task LFCLKSTART */

/* Bit 31 :   */
#define CLOCK_SUBSCRIBE_LFCLKSTART_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_SUBSCRIBE_LFCLKSTART_EN_Msk (0x1UL << CLOCK_SUBSCRIBE_LFCLKSTART_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_SUBSCRIBE_LFCLKSTART_EN_Disabled (0UL) /*!< Disable subscription */
#define CLOCK_SUBSCRIBE_LFCLKSTART_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task LFCLKSTART will subscribe to */
#define CLOCK_SUBSCRIBE_LFCLKSTART_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_SUBSCRIBE_LFCLKSTART_CHIDX_Msk (0xFFUL << CLOCK_SUBSCRIBE_LFCLKSTART_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_SUBSCRIBE_LFCLKSTOP */
/* Description: Subscribe configuration for task LFCLKSTOP */

/* Bit 31 :   */
#define CLOCK_SUBSCRIBE_LFCLKSTOP_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_SUBSCRIBE_LFCLKSTOP_EN_Msk (0x1UL << CLOCK_SUBSCRIBE_LFCLKSTOP_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_SUBSCRIBE_LFCLKSTOP_EN_Disabled (0UL) /*!< Disable subscription */
#define CLOCK_SUBSCRIBE_LFCLKSTOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task LFCLKSTOP will subscribe to */
#define CLOCK_SUBSCRIBE_LFCLKSTOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_SUBSCRIBE_LFCLKSTOP_CHIDX_Msk (0xFFUL << CLOCK_SUBSCRIBE_LFCLKSTOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_SUBSCRIBE_CAL */
/* Description: Subscribe configuration for task CAL */

/* Bit 31 :   */
#define CLOCK_SUBSCRIBE_CAL_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_SUBSCRIBE_CAL_EN_Msk (0x1UL << CLOCK_SUBSCRIBE_CAL_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_SUBSCRIBE_CAL_EN_Disabled (0UL) /*!< Disable subscription */
#define CLOCK_SUBSCRIBE_CAL_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CAL will subscribe to */
#define CLOCK_SUBSCRIBE_CAL_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_SUBSCRIBE_CAL_CHIDX_Msk (0xFFUL << CLOCK_SUBSCRIBE_CAL_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_EVENTS_HFCLKSTARTED */
/* Description: HFCLK128M/HFCLK64M source started */

/* Bit 0 : HFCLK128M/HFCLK64M source started */
#define CLOCK_EVENTS_HFCLKSTARTED_EVENTS_HFCLKSTARTED_Pos (0UL) /*!< Position of EVENTS_HFCLKSTARTED field. */
#define CLOCK_EVENTS_HFCLKSTARTED_EVENTS_HFCLKSTARTED_Msk (0x1UL << CLOCK_EVENTS_HFCLKSTARTED_EVENTS_HFCLKSTARTED_Pos) /*!< Bit mask of EVENTS_HFCLKSTARTED field. */
#define CLOCK_EVENTS_HFCLKSTARTED_EVENTS_HFCLKSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define CLOCK_EVENTS_HFCLKSTARTED_EVENTS_HFCLKSTARTED_Generated (1UL) /*!< Event generated */

/* Register: CLOCK_EVENTS_LFCLKSTARTED */
/* Description: LFCLK source started */

/* Bit 0 : LFCLK source started */
#define CLOCK_EVENTS_LFCLKSTARTED_EVENTS_LFCLKSTARTED_Pos (0UL) /*!< Position of EVENTS_LFCLKSTARTED field. */
#define CLOCK_EVENTS_LFCLKSTARTED_EVENTS_LFCLKSTARTED_Msk (0x1UL << CLOCK_EVENTS_LFCLKSTARTED_EVENTS_LFCLKSTARTED_Pos) /*!< Bit mask of EVENTS_LFCLKSTARTED field. */
#define CLOCK_EVENTS_LFCLKSTARTED_EVENTS_LFCLKSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define CLOCK_EVENTS_LFCLKSTARTED_EVENTS_LFCLKSTARTED_Generated (1UL) /*!< Event generated */

/* Register: CLOCK_EVENTS_DONE */
/* Description: Calibration of LFRC oscillator complete event */

/* Bit 0 : Calibration of LFRC oscillator complete event */
#define CLOCK_EVENTS_DONE_EVENTS_DONE_Pos (0UL) /*!< Position of EVENTS_DONE field. */
#define CLOCK_EVENTS_DONE_EVENTS_DONE_Msk (0x1UL << CLOCK_EVENTS_DONE_EVENTS_DONE_Pos) /*!< Bit mask of EVENTS_DONE field. */
#define CLOCK_EVENTS_DONE_EVENTS_DONE_NotGenerated (0UL) /*!< Event not generated */
#define CLOCK_EVENTS_DONE_EVENTS_DONE_Generated (1UL) /*!< Event generated */

/* Register: CLOCK_PUBLISH_HFCLKSTARTED */
/* Description: Publish configuration for event HFCLKSTARTED */

/* Bit 31 :   */
#define CLOCK_PUBLISH_HFCLKSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_PUBLISH_HFCLKSTARTED_EN_Msk (0x1UL << CLOCK_PUBLISH_HFCLKSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_PUBLISH_HFCLKSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define CLOCK_PUBLISH_HFCLKSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event HFCLKSTARTED will publish to. */
#define CLOCK_PUBLISH_HFCLKSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_PUBLISH_HFCLKSTARTED_CHIDX_Msk (0xFFUL << CLOCK_PUBLISH_HFCLKSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_PUBLISH_LFCLKSTARTED */
/* Description: Publish configuration for event LFCLKSTARTED */

/* Bit 31 :   */
#define CLOCK_PUBLISH_LFCLKSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_PUBLISH_LFCLKSTARTED_EN_Msk (0x1UL << CLOCK_PUBLISH_LFCLKSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_PUBLISH_LFCLKSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define CLOCK_PUBLISH_LFCLKSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event LFCLKSTARTED will publish to. */
#define CLOCK_PUBLISH_LFCLKSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_PUBLISH_LFCLKSTARTED_CHIDX_Msk (0xFFUL << CLOCK_PUBLISH_LFCLKSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_PUBLISH_DONE */
/* Description: Publish configuration for event DONE */

/* Bit 31 :   */
#define CLOCK_PUBLISH_DONE_EN_Pos (31UL) /*!< Position of EN field. */
#define CLOCK_PUBLISH_DONE_EN_Msk (0x1UL << CLOCK_PUBLISH_DONE_EN_Pos) /*!< Bit mask of EN field. */
#define CLOCK_PUBLISH_DONE_EN_Disabled (0UL) /*!< Disable publishing */
#define CLOCK_PUBLISH_DONE_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event DONE will publish to. */
#define CLOCK_PUBLISH_DONE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define CLOCK_PUBLISH_DONE_CHIDX_Msk (0xFFUL << CLOCK_PUBLISH_DONE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: CLOCK_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 7 : Enable or disable interrupt for event DONE */
#define CLOCK_INTEN_DONE_Pos (7UL) /*!< Position of DONE field. */
#define CLOCK_INTEN_DONE_Msk (0x1UL << CLOCK_INTEN_DONE_Pos) /*!< Bit mask of DONE field. */
#define CLOCK_INTEN_DONE_Disabled (0UL) /*!< Disable */
#define CLOCK_INTEN_DONE_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable interrupt for event LFCLKSTARTED */
#define CLOCK_INTEN_LFCLKSTARTED_Pos (1UL) /*!< Position of LFCLKSTARTED field. */
#define CLOCK_INTEN_LFCLKSTARTED_Msk (0x1UL << CLOCK_INTEN_LFCLKSTARTED_Pos) /*!< Bit mask of LFCLKSTARTED field. */
#define CLOCK_INTEN_LFCLKSTARTED_Disabled (0UL) /*!< Disable */
#define CLOCK_INTEN_LFCLKSTARTED_Enabled (1UL) /*!< Enable */

/* Bit 0 : Enable or disable interrupt for event HFCLKSTARTED */
#define CLOCK_INTEN_HFCLKSTARTED_Pos (0UL) /*!< Position of HFCLKSTARTED field. */
#define CLOCK_INTEN_HFCLKSTARTED_Msk (0x1UL << CLOCK_INTEN_HFCLKSTARTED_Pos) /*!< Bit mask of HFCLKSTARTED field. */
#define CLOCK_INTEN_HFCLKSTARTED_Disabled (0UL) /*!< Disable */
#define CLOCK_INTEN_HFCLKSTARTED_Enabled (1UL) /*!< Enable */

/* Register: CLOCK_INTENSET */
/* Description: Enable interrupt */

/* Bit 7 : Write '1' to enable interrupt for event DONE */
#define CLOCK_INTENSET_DONE_Pos (7UL) /*!< Position of DONE field. */
#define CLOCK_INTENSET_DONE_Msk (0x1UL << CLOCK_INTENSET_DONE_Pos) /*!< Bit mask of DONE field. */
#define CLOCK_INTENSET_DONE_Disabled (0UL) /*!< Read: Disabled */
#define CLOCK_INTENSET_DONE_Enabled (1UL) /*!< Read: Enabled */
#define CLOCK_INTENSET_DONE_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event LFCLKSTARTED */
#define CLOCK_INTENSET_LFCLKSTARTED_Pos (1UL) /*!< Position of LFCLKSTARTED field. */
#define CLOCK_INTENSET_LFCLKSTARTED_Msk (0x1UL << CLOCK_INTENSET_LFCLKSTARTED_Pos) /*!< Bit mask of LFCLKSTARTED field. */
#define CLOCK_INTENSET_LFCLKSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define CLOCK_INTENSET_LFCLKSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define CLOCK_INTENSET_LFCLKSTARTED_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event HFCLKSTARTED */
#define CLOCK_INTENSET_HFCLKSTARTED_Pos (0UL) /*!< Position of HFCLKSTARTED field. */
#define CLOCK_INTENSET_HFCLKSTARTED_Msk (0x1UL << CLOCK_INTENSET_HFCLKSTARTED_Pos) /*!< Bit mask of HFCLKSTARTED field. */
#define CLOCK_INTENSET_HFCLKSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define CLOCK_INTENSET_HFCLKSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define CLOCK_INTENSET_HFCLKSTARTED_Set (1UL) /*!< Enable */

/* Register: CLOCK_INTENCLR */
/* Description: Disable interrupt */

/* Bit 7 : Write '1' to disable interrupt for event DONE */
#define CLOCK_INTENCLR_DONE_Pos (7UL) /*!< Position of DONE field. */
#define CLOCK_INTENCLR_DONE_Msk (0x1UL << CLOCK_INTENCLR_DONE_Pos) /*!< Bit mask of DONE field. */
#define CLOCK_INTENCLR_DONE_Disabled (0UL) /*!< Read: Disabled */
#define CLOCK_INTENCLR_DONE_Enabled (1UL) /*!< Read: Enabled */
#define CLOCK_INTENCLR_DONE_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event LFCLKSTARTED */
#define CLOCK_INTENCLR_LFCLKSTARTED_Pos (1UL) /*!< Position of LFCLKSTARTED field. */
#define CLOCK_INTENCLR_LFCLKSTARTED_Msk (0x1UL << CLOCK_INTENCLR_LFCLKSTARTED_Pos) /*!< Bit mask of LFCLKSTARTED field. */
#define CLOCK_INTENCLR_LFCLKSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define CLOCK_INTENCLR_LFCLKSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define CLOCK_INTENCLR_LFCLKSTARTED_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event HFCLKSTARTED */
#define CLOCK_INTENCLR_HFCLKSTARTED_Pos (0UL) /*!< Position of HFCLKSTARTED field. */
#define CLOCK_INTENCLR_HFCLKSTARTED_Msk (0x1UL << CLOCK_INTENCLR_HFCLKSTARTED_Pos) /*!< Bit mask of HFCLKSTARTED field. */
#define CLOCK_INTENCLR_HFCLKSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define CLOCK_INTENCLR_HFCLKSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define CLOCK_INTENCLR_HFCLKSTARTED_Clear (1UL) /*!< Disable */

/* Register: CLOCK_INTPEND */
/* Description: Pending interrupts */

/* Bit 7 : Read pending status of interrupt for event DONE */
#define CLOCK_INTPEND_DONE_Pos (7UL) /*!< Position of DONE field. */
#define CLOCK_INTPEND_DONE_Msk (0x1UL << CLOCK_INTPEND_DONE_Pos) /*!< Bit mask of DONE field. */
#define CLOCK_INTPEND_DONE_NotPending (0UL) /*!< Read: Not pending */
#define CLOCK_INTPEND_DONE_Pending (1UL) /*!< Read: Pending */

/* Bit 1 : Read pending status of interrupt for event LFCLKSTARTED */
#define CLOCK_INTPEND_LFCLKSTARTED_Pos (1UL) /*!< Position of LFCLKSTARTED field. */
#define CLOCK_INTPEND_LFCLKSTARTED_Msk (0x1UL << CLOCK_INTPEND_LFCLKSTARTED_Pos) /*!< Bit mask of LFCLKSTARTED field. */
#define CLOCK_INTPEND_LFCLKSTARTED_NotPending (0UL) /*!< Read: Not pending */
#define CLOCK_INTPEND_LFCLKSTARTED_Pending (1UL) /*!< Read: Pending */

/* Bit 0 : Read pending status of interrupt for event HFCLKSTARTED */
#define CLOCK_INTPEND_HFCLKSTARTED_Pos (0UL) /*!< Position of HFCLKSTARTED field. */
#define CLOCK_INTPEND_HFCLKSTARTED_Msk (0x1UL << CLOCK_INTPEND_HFCLKSTARTED_Pos) /*!< Bit mask of HFCLKSTARTED field. */
#define CLOCK_INTPEND_HFCLKSTARTED_NotPending (0UL) /*!< Read: Not pending */
#define CLOCK_INTPEND_HFCLKSTARTED_Pending (1UL) /*!< Read: Pending */

/* Register: CLOCK_HFCLKRUN */
/* Description: Status indicating that HFCLKSTART task has been triggered */

/* Bit 0 : HFCLKSTART task triggered or not */
#define CLOCK_HFCLKRUN_STATUS_Pos (0UL) /*!< Position of STATUS field. */
#define CLOCK_HFCLKRUN_STATUS_Msk (0x1UL << CLOCK_HFCLKRUN_STATUS_Pos) /*!< Bit mask of STATUS field. */
#define CLOCK_HFCLKRUN_STATUS_NotTriggered (0UL) /*!< Task not triggered */
#define CLOCK_HFCLKRUN_STATUS_Triggered (1UL) /*!< Task triggered */

/* Register: CLOCK_HFCLKSTAT */
/* Description: Status indicating which HFCLK128M/HFCLK64M source is running This register value in any CLOCK instance reflects status only due to configurations/actions in that CLOCK instance. */

/* Bit 16 : HFCLK state */
#define CLOCK_HFCLKSTAT_STATE_Pos (16UL) /*!< Position of STATE field. */
#define CLOCK_HFCLKSTAT_STATE_Msk (0x1UL << CLOCK_HFCLKSTAT_STATE_Pos) /*!< Bit mask of STATE field. */
#define CLOCK_HFCLKSTAT_STATE_NotRunning (0UL) /*!< HFCLK not running */
#define CLOCK_HFCLKSTAT_STATE_Running (1UL) /*!< HFCLK running */

/* Bit 4 : ALWAYSRUN activated */
#define CLOCK_HFCLKSTAT_ALWAYSRUNNING_Pos (4UL) /*!< Position of ALWAYSRUNNING field. */
#define CLOCK_HFCLKSTAT_ALWAYSRUNNING_Msk (0x1UL << CLOCK_HFCLKSTAT_ALWAYSRUNNING_Pos) /*!< Bit mask of ALWAYSRUNNING field. */
#define CLOCK_HFCLKSTAT_ALWAYSRUNNING_NotRunning (0UL) /*!< Automatic clock control enabled */
#define CLOCK_HFCLKSTAT_ALWAYSRUNNING_Running (1UL) /*!< Oscillator is always running */

/* Bit 0 : Active clock source */
#define CLOCK_HFCLKSTAT_SRC_Pos (0UL) /*!< Position of SRC field. */
#define CLOCK_HFCLKSTAT_SRC_Msk (0x1UL << CLOCK_HFCLKSTAT_SRC_Pos) /*!< Bit mask of SRC field. */
#define CLOCK_HFCLKSTAT_SRC_HFINT (0UL) /*!< Clock source: HFINT - 128 MHz on-chip oscillator */
#define CLOCK_HFCLKSTAT_SRC_HFXO (1UL) /*!< Clock source: HFXO - 128 MHz clock derived from external 32 MHz crystal oscillator */

/* Register: CLOCK_LFCLKRUN */
/* Description: Status indicating that LFCLKSTART task has been triggered */

/* Bit 0 : LFCLKSTART task triggered or not */
#define CLOCK_LFCLKRUN_STATUS_Pos (0UL) /*!< Position of STATUS field. */
#define CLOCK_LFCLKRUN_STATUS_Msk (0x1UL << CLOCK_LFCLKRUN_STATUS_Pos) /*!< Bit mask of STATUS field. */
#define CLOCK_LFCLKRUN_STATUS_NotTriggered (0UL) /*!< Task not triggered */
#define CLOCK_LFCLKRUN_STATUS_Triggered (1UL) /*!< Task triggered */

/* Register: CLOCK_LFCLKSTAT */
/* Description: Status indicating which LFCLK source is running This register value in any CLOCK instance reflects status only due to configurations/actions in that CLOCK instance. */

/* Bit 16 : LFCLK state */
#define CLOCK_LFCLKSTAT_STATE_Pos (16UL) /*!< Position of STATE field. */
#define CLOCK_LFCLKSTAT_STATE_Msk (0x1UL << CLOCK_LFCLKSTAT_STATE_Pos) /*!< Bit mask of STATE field. */
#define CLOCK_LFCLKSTAT_STATE_NotRunning (0UL) /*!< LFCLK not running */
#define CLOCK_LFCLKSTAT_STATE_Running (1UL) /*!< LFCLK running */

/* Bit 4 : ALWAYSRUN activated */
#define CLOCK_LFCLKSTAT_ALWAYSRUNNING_Pos (4UL) /*!< Position of ALWAYSRUNNING field. */
#define CLOCK_LFCLKSTAT_ALWAYSRUNNING_Msk (0x1UL << CLOCK_LFCLKSTAT_ALWAYSRUNNING_Pos) /*!< Bit mask of ALWAYSRUNNING field. */
#define CLOCK_LFCLKSTAT_ALWAYSRUNNING_NotRunning (0UL) /*!< Automatic clock control enabled */
#define CLOCK_LFCLKSTAT_ALWAYSRUNNING_Running (1UL) /*!< Oscillator is always running */

/* Bits 1..0 : Active clock source */
#define CLOCK_LFCLKSTAT_SRC_Pos (0UL) /*!< Position of SRC field. */
#define CLOCK_LFCLKSTAT_SRC_Msk (0x3UL << CLOCK_LFCLKSTAT_SRC_Pos) /*!< Bit mask of SRC field. */
#define CLOCK_LFCLKSTAT_SRC_LFRC (1UL) /*!< 32.768 kHz RC oscillator */
#define CLOCK_LFCLKSTAT_SRC_LFXO (2UL) /*!< 32.768 kHz crystal oscillator */
#define CLOCK_LFCLKSTAT_SRC_LFSYNT (3UL) /*!< 32.768 kHz synthesized from HFCLK */

/* Register: CLOCK_LFCLKSRCCOPY */
/* Description: Copy of LFCLKSRC register, set when LFCLKSTART task was triggered */

/* Bits 1..0 : Clock source */
#define CLOCK_LFCLKSRCCOPY_SRC_Pos (0UL) /*!< Position of SRC field. */
#define CLOCK_LFCLKSRCCOPY_SRC_Msk (0x3UL << CLOCK_LFCLKSRCCOPY_SRC_Pos) /*!< Bit mask of SRC field. */
#define CLOCK_LFCLKSRCCOPY_SRC_LFRC (1UL) /*!< 32.768 kHz RC oscillator */
#define CLOCK_LFCLKSRCCOPY_SRC_LFXO (2UL) /*!< 32.768 kHz crystal oscillator */
#define CLOCK_LFCLKSRCCOPY_SRC_LFSYNT (3UL) /*!< 32.768 kHz synthesized from HFCLK */

/* Register: CLOCK_HFCLKSRC */
/* Description: Clock source for HFCLK128M/HFCLK64M */

/* Bit 0 : Select which HFCLK source is started by the HFCLKSTART task */
#define CLOCK_HFCLKSRC_SRC_Pos (0UL) /*!< Position of SRC field. */
#define CLOCK_HFCLKSRC_SRC_Msk (0x1UL << CLOCK_HFCLKSRC_SRC_Pos) /*!< Bit mask of SRC field. */
#define CLOCK_HFCLKSRC_SRC_HFINT (0UL) /*!< HFCLKSTART task starts HFINT oscillator */
#define CLOCK_HFCLKSRC_SRC_HFXO (1UL) /*!< HFCLKSTART task starts HFXO oscillator */

/* Register: CLOCK_LFCLKSRC */
/* Description: Clock source for LFCLK */

/* Bits 1..0 : Select which LFCLK source is started by the LFCLKSTART task */
#define CLOCK_LFCLKSRC_SRC_Pos (0UL) /*!< Position of SRC field. */
#define CLOCK_LFCLKSRC_SRC_Msk (0x3UL << CLOCK_LFCLKSRC_SRC_Pos) /*!< Bit mask of SRC field. */
#define CLOCK_LFCLKSRC_SRC_LFRC (1UL) /*!< 32.768 kHz RC oscillator */
#define CLOCK_LFCLKSRC_SRC_LFXO (2UL) /*!< 32.768 kHz crystal oscillator */
#define CLOCK_LFCLKSRC_SRC_LFSYNT (3UL) /*!< 32.768 kHz synthesized from HFCLK */

/* Register: CLOCK_HFCLKCTRL */
/* Description: HFCLK128M frequency configuration */

/* Bits 1..0 : High frequency clock HCLK */
#define CLOCK_HFCLKCTRL_HCLK_Pos (0UL) /*!< Position of HCLK field. */
#define CLOCK_HFCLKCTRL_HCLK_Msk (0x3UL << CLOCK_HFCLKCTRL_HCLK_Pos) /*!< Bit mask of HCLK field. */
#define CLOCK_HFCLKCTRL_HCLK_Div1 (0UL) /*!< Divide HFCLK by 1 */
#define CLOCK_HFCLKCTRL_HCLK_Div2 (1UL) /*!< Divide HFCLK by 2 */

/* Register: CLOCK_HFCLKALWAYSRUN */
/* Description: Automatic or manual control of HFCLK128M/HFCLK64M */

/* Bit 0 : Ensure clock is always running */
#define CLOCK_HFCLKALWAYSRUN_ALWAYSRUN_Pos (0UL) /*!< Position of ALWAYSRUN field. */
#define CLOCK_HFCLKALWAYSRUN_ALWAYSRUN_Msk (0x1UL << CLOCK_HFCLKALWAYSRUN_ALWAYSRUN_Pos) /*!< Bit mask of ALWAYSRUN field. */
#define CLOCK_HFCLKALWAYSRUN_ALWAYSRUN_Automatic (0UL) /*!< Use automatic clock control */
#define CLOCK_HFCLKALWAYSRUN_ALWAYSRUN_AlwaysRun (1UL) /*!< Ensure clock is always running */

/* Register: CLOCK_LFCLKALWAYSRUN */
/* Description: Automatic or manual control of LFCLK */

/* Bit 0 : Ensure clock is always running */
#define CLOCK_LFCLKALWAYSRUN_ALWAYSRUN_Pos (0UL) /*!< Position of ALWAYSRUN field. */
#define CLOCK_LFCLKALWAYSRUN_ALWAYSRUN_Msk (0x1UL << CLOCK_LFCLKALWAYSRUN_ALWAYSRUN_Pos) /*!< Bit mask of ALWAYSRUN field. */
#define CLOCK_LFCLKALWAYSRUN_ALWAYSRUN_Automatic (0UL) /*!< Use automatic clock control */
#define CLOCK_LFCLKALWAYSRUN_ALWAYSRUN_AlwaysRun (1UL) /*!< Ensure clock is always running */


/* Peripheral: CTI */
/* Description: Cross-Trigger Interface control. NOTE: this is not a separate peripheral, but describes CM33 functionality. */

/* Register: CTI_CTICONTROL */
/* Description: CTI Control register */

/* Bit 0 : Enables or disables the CTI. */
#define CTI_CTICONTROL_GLBEN_Pos (0UL) /*!< Position of GLBEN field. */
#define CTI_CTICONTROL_GLBEN_Msk (0x1UL << CTI_CTICONTROL_GLBEN_Pos) /*!< Bit mask of GLBEN field. */
#define CTI_CTICONTROL_GLBEN_Disabled (0UL) /*!< All cross-triggering mapping logic functionality is disabled. */
#define CTI_CTICONTROL_GLBEN_Enabled (1UL) /*!< Cross-triggering mapping logic functionality is enabled. */

/* Register: CTI_CTIINTACK */
/* Description: CTI Interrupt Acknowledge register */

/* Bit 7 : N/A */
#define CTI_CTIINTACK_UNUSED5_Pos (7UL) /*!< Position of UNUSED5 field. */
#define CTI_CTIINTACK_UNUSED5_Msk (0x1UL << CTI_CTIINTACK_UNUSED5_Pos) /*!< Bit mask of UNUSED5 field. */
#define CTI_CTIINTACK_UNUSED5_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Bit 6 : N/A */
#define CTI_CTIINTACK_UNUSED4_Pos (6UL) /*!< Position of UNUSED4 field. */
#define CTI_CTIINTACK_UNUSED4_Msk (0x1UL << CTI_CTIINTACK_UNUSED4_Pos) /*!< Bit mask of UNUSED4 field. */
#define CTI_CTIINTACK_UNUSED4_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Bit 5 : N/A */
#define CTI_CTIINTACK_UNUSED3_Pos (5UL) /*!< Position of UNUSED3 field. */
#define CTI_CTIINTACK_UNUSED3_Msk (0x1UL << CTI_CTIINTACK_UNUSED3_Pos) /*!< Bit mask of UNUSED3 field. */
#define CTI_CTIINTACK_UNUSED3_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Bit 4 : N/A */
#define CTI_CTIINTACK_UNUSED2_Pos (4UL) /*!< Position of UNUSED2 field. */
#define CTI_CTIINTACK_UNUSED2_Msk (0x1UL << CTI_CTIINTACK_UNUSED2_Pos) /*!< Bit mask of UNUSED2 field. */
#define CTI_CTIINTACK_UNUSED2_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Bit 3 : N/A */
#define CTI_CTIINTACK_UNUSED1_Pos (3UL) /*!< Position of UNUSED1 field. */
#define CTI_CTIINTACK_UNUSED1_Msk (0x1UL << CTI_CTIINTACK_UNUSED1_Pos) /*!< Bit mask of UNUSED1 field. */
#define CTI_CTIINTACK_UNUSED1_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Bit 2 : N/A */
#define CTI_CTIINTACK_UNUSED0_Pos (2UL) /*!< Position of UNUSED0 field. */
#define CTI_CTIINTACK_UNUSED0_Msk (0x1UL << CTI_CTIINTACK_UNUSED0_Pos) /*!< Bit mask of UNUSED0 field. */
#define CTI_CTIINTACK_UNUSED0_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Bit 1 : Processor Restart */
#define CTI_CTIINTACK_CPURESTART_Pos (1UL) /*!< Position of CPURESTART field. */
#define CTI_CTIINTACK_CPURESTART_Msk (0x1UL << CTI_CTIINTACK_CPURESTART_Pos) /*!< Bit mask of CPURESTART field. */
#define CTI_CTIINTACK_CPURESTART_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Bit 0 : Processor debug request */
#define CTI_CTIINTACK_DEBUGREQ_Pos (0UL) /*!< Position of DEBUGREQ field. */
#define CTI_CTIINTACK_DEBUGREQ_Msk (0x1UL << CTI_CTIINTACK_DEBUGREQ_Pos) /*!< Bit mask of DEBUGREQ field. */
#define CTI_CTIINTACK_DEBUGREQ_Acknowledge (1UL) /*!< Clears the ctitrigout. */

/* Register: CTI_CTIAPPSET */
/* Description: CTI Application Trigger Set register */

/* Bit 3 : Application trigger event for channel 3. */
#define CTI_CTIAPPSET_APPSET_3_Pos (3UL) /*!< Position of APPSET_3 field. */
#define CTI_CTIAPPSET_APPSET_3_Msk (0x1UL << CTI_CTIAPPSET_APPSET_3_Pos) /*!< Bit mask of APPSET_3 field. */
#define CTI_CTIAPPSET_APPSET_3_Inactive (0UL) /*!< Application trigger 3 is inactive. */
#define CTI_CTIAPPSET_APPSET_3_Active (1UL) /*!< Application trigger 3 is active. */
#define CTI_CTIAPPSET_APPSET_3_Activate (1UL) /*!< Generate channel event for channel 3. */

/* Bit 2 : Application trigger event for channel 2. */
#define CTI_CTIAPPSET_APPSET_2_Pos (2UL) /*!< Position of APPSET_2 field. */
#define CTI_CTIAPPSET_APPSET_2_Msk (0x1UL << CTI_CTIAPPSET_APPSET_2_Pos) /*!< Bit mask of APPSET_2 field. */
#define CTI_CTIAPPSET_APPSET_2_Inactive (0UL) /*!< Application trigger 2 is inactive. */
#define CTI_CTIAPPSET_APPSET_2_Active (1UL) /*!< Application trigger 2 is active. */
#define CTI_CTIAPPSET_APPSET_2_Activate (1UL) /*!< Generate channel event for channel 2. */

/* Bit 1 : Application trigger event for channel 1. */
#define CTI_CTIAPPSET_APPSET_1_Pos (1UL) /*!< Position of APPSET_1 field. */
#define CTI_CTIAPPSET_APPSET_1_Msk (0x1UL << CTI_CTIAPPSET_APPSET_1_Pos) /*!< Bit mask of APPSET_1 field. */
#define CTI_CTIAPPSET_APPSET_1_Inactive (0UL) /*!< Application trigger 1 is inactive. */
#define CTI_CTIAPPSET_APPSET_1_Active (1UL) /*!< Application trigger 1 is active. */
#define CTI_CTIAPPSET_APPSET_1_Activate (1UL) /*!< Generate channel event for channel 1. */

/* Bit 0 : Application trigger event for channel 0. */
#define CTI_CTIAPPSET_APPSET_0_Pos (0UL) /*!< Position of APPSET_0 field. */
#define CTI_CTIAPPSET_APPSET_0_Msk (0x1UL << CTI_CTIAPPSET_APPSET_0_Pos) /*!< Bit mask of APPSET_0 field. */
#define CTI_CTIAPPSET_APPSET_0_Inactive (0UL) /*!< Application trigger 0 is inactive. */
#define CTI_CTIAPPSET_APPSET_0_Active (1UL) /*!< Application trigger 0 is active. */
#define CTI_CTIAPPSET_APPSET_0_Activate (1UL) /*!< Generate channel event for channel 0. */

/* Register: CTI_CTIAPPCLEAR */
/* Description: CTI Application Trigger Clear register */

/* Bit 3 : Sets the corresponding bits in the CTIAPPSET to 0. There is one bit of the register for each channel. */
#define CTI_CTIAPPCLEAR_APPCLEAR_3_Pos (3UL) /*!< Position of APPCLEAR_3 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_3_Msk (0x1UL << CTI_CTIAPPCLEAR_APPCLEAR_3_Pos) /*!< Bit mask of APPCLEAR_3 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_3_Clear (1UL) /*!< Clears the event for channel 3. */

/* Bit 2 : Sets the corresponding bits in the CTIAPPSET to 0. There is one bit of the register for each channel. */
#define CTI_CTIAPPCLEAR_APPCLEAR_2_Pos (2UL) /*!< Position of APPCLEAR_2 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_2_Msk (0x1UL << CTI_CTIAPPCLEAR_APPCLEAR_2_Pos) /*!< Bit mask of APPCLEAR_2 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_2_Clear (1UL) /*!< Clears the event for channel 2. */

/* Bit 1 : Sets the corresponding bits in the CTIAPPSET to 0. There is one bit of the register for each channel. */
#define CTI_CTIAPPCLEAR_APPCLEAR_1_Pos (1UL) /*!< Position of APPCLEAR_1 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_1_Msk (0x1UL << CTI_CTIAPPCLEAR_APPCLEAR_1_Pos) /*!< Bit mask of APPCLEAR_1 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_1_Clear (1UL) /*!< Clears the event for channel 1. */

/* Bit 0 : Sets the corresponding bits in the CTIAPPSET to 0. There is one bit of the register for each channel. */
#define CTI_CTIAPPCLEAR_APPCLEAR_0_Pos (0UL) /*!< Position of APPCLEAR_0 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_0_Msk (0x1UL << CTI_CTIAPPCLEAR_APPCLEAR_0_Pos) /*!< Bit mask of APPCLEAR_0 field. */
#define CTI_CTIAPPCLEAR_APPCLEAR_0_Clear (1UL) /*!< Clears the event for channel 0. */

/* Register: CTI_CTIAPPPULSE */
/* Description: CTI Application Pulse register */

/* Bit 3 : Setting a bit HIGH generates a channel event pulse for the selected channel. There is one bit of the register for each channel. */
#define CTI_CTIAPPPULSE_APPULSE_3_Pos (3UL) /*!< Position of APPULSE_3 field. */
#define CTI_CTIAPPPULSE_APPULSE_3_Msk (0x1UL << CTI_CTIAPPPULSE_APPULSE_3_Pos) /*!< Bit mask of APPULSE_3 field. */
#define CTI_CTIAPPPULSE_APPULSE_3_Generate (1UL) /*!< Generates an event pulse on channel 3. */

/* Bit 2 : Setting a bit HIGH generates a channel event pulse for the selected channel. There is one bit of the register for each channel. */
#define CTI_CTIAPPPULSE_APPULSE_2_Pos (2UL) /*!< Position of APPULSE_2 field. */
#define CTI_CTIAPPPULSE_APPULSE_2_Msk (0x1UL << CTI_CTIAPPPULSE_APPULSE_2_Pos) /*!< Bit mask of APPULSE_2 field. */
#define CTI_CTIAPPPULSE_APPULSE_2_Generate (1UL) /*!< Generates an event pulse on channel 2. */

/* Bit 1 : Setting a bit HIGH generates a channel event pulse for the selected channel. There is one bit of the register for each channel. */
#define CTI_CTIAPPPULSE_APPULSE_1_Pos (1UL) /*!< Position of APPULSE_1 field. */
#define CTI_CTIAPPPULSE_APPULSE_1_Msk (0x1UL << CTI_CTIAPPPULSE_APPULSE_1_Pos) /*!< Bit mask of APPULSE_1 field. */
#define CTI_CTIAPPPULSE_APPULSE_1_Generate (1UL) /*!< Generates an event pulse on channel 1. */

/* Bit 0 : Setting a bit HIGH generates a channel event pulse for the selected channel. There is one bit of the register for each channel. */
#define CTI_CTIAPPPULSE_APPULSE_0_Pos (0UL) /*!< Position of APPULSE_0 field. */
#define CTI_CTIAPPPULSE_APPULSE_0_Msk (0x1UL << CTI_CTIAPPPULSE_APPULSE_0_Pos) /*!< Bit mask of APPULSE_0 field. */
#define CTI_CTIAPPPULSE_APPULSE_0_Generate (1UL) /*!< Generates an event pulse on channel 0. */

/* Register: CTI_CTIINEN */
/* Description: Description collection: CTI Trigger input */

/* Bit 3 : Enables a cross trigger event to channel 3 when a ctitrigin input is activated. */
#define CTI_CTIINEN_TRIGINEN_3_Pos (3UL) /*!< Position of TRIGINEN_3 field. */
#define CTI_CTIINEN_TRIGINEN_3_Msk (0x1UL << CTI_CTIINEN_TRIGINEN_3_Pos) /*!< Bit mask of TRIGINEN_3 field. */
#define CTI_CTIINEN_TRIGINEN_3_Disabled (0UL) /*!< Input trigger n events are ignored by channel 3. */
#define CTI_CTIINEN_TRIGINEN_3_Enabled (1UL) /*!< When an event is received on input trigger n (ctitrigin[n]), generate an event on channel 3. */

/* Bit 2 : Enables a cross trigger event to channel 2 when a ctitrigin input is activated. */
#define CTI_CTIINEN_TRIGINEN_2_Pos (2UL) /*!< Position of TRIGINEN_2 field. */
#define CTI_CTIINEN_TRIGINEN_2_Msk (0x1UL << CTI_CTIINEN_TRIGINEN_2_Pos) /*!< Bit mask of TRIGINEN_2 field. */
#define CTI_CTIINEN_TRIGINEN_2_Disabled (0UL) /*!< Input trigger n events are ignored by channel 2. */
#define CTI_CTIINEN_TRIGINEN_2_Enabled (1UL) /*!< When an event is received on input trigger n (ctitrigin[n]), generate an event on channel 2. */

/* Bit 1 : Enables a cross trigger event to channel 1 when a ctitrigin input is activated. */
#define CTI_CTIINEN_TRIGINEN_1_Pos (1UL) /*!< Position of TRIGINEN_1 field. */
#define CTI_CTIINEN_TRIGINEN_1_Msk (0x1UL << CTI_CTIINEN_TRIGINEN_1_Pos) /*!< Bit mask of TRIGINEN_1 field. */
#define CTI_CTIINEN_TRIGINEN_1_Disabled (0UL) /*!< Input trigger n events are ignored by channel 1. */
#define CTI_CTIINEN_TRIGINEN_1_Enabled (1UL) /*!< When an event is received on input trigger n (ctitrigin[n]), generate an event on channel 1. */

/* Bit 0 : Enables a cross trigger event to channel 0 when a ctitrigin input is activated. */
#define CTI_CTIINEN_TRIGINEN_0_Pos (0UL) /*!< Position of TRIGINEN_0 field. */
#define CTI_CTIINEN_TRIGINEN_0_Msk (0x1UL << CTI_CTIINEN_TRIGINEN_0_Pos) /*!< Bit mask of TRIGINEN_0 field. */
#define CTI_CTIINEN_TRIGINEN_0_Disabled (0UL) /*!< Input trigger n events are ignored by channel 0. */
#define CTI_CTIINEN_TRIGINEN_0_Enabled (1UL) /*!< When an event is received on input trigger n (ctitrigin[n]), generate an event on channel 0. */

/* Register: CTI_CTIOUTEN */
/* Description: Description collection: CTI Trigger output */

/* Bit 3 : Enables a cross trigger event to ctitrigout when channel 3 is activated. */
#define CTI_CTIOUTEN_TRIGOUTEN_3_Pos (3UL) /*!< Position of TRIGOUTEN_3 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_3_Msk (0x1UL << CTI_CTIOUTEN_TRIGOUTEN_3_Pos) /*!< Bit mask of TRIGOUTEN_3 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_3_Disabled (0UL) /*!< Channel 3 is ignored by output trigger n. */
#define CTI_CTIOUTEN_TRIGOUTEN_3_Enabled (1UL) /*!< When an event occurs on channel 3, generate an event on output event n (ctitrigout[n]). */

/* Bit 2 : Enables a cross trigger event to ctitrigout when channel 2 is activated. */
#define CTI_CTIOUTEN_TRIGOUTEN_2_Pos (2UL) /*!< Position of TRIGOUTEN_2 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_2_Msk (0x1UL << CTI_CTIOUTEN_TRIGOUTEN_2_Pos) /*!< Bit mask of TRIGOUTEN_2 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_2_Disabled (0UL) /*!< Channel 2 is ignored by output trigger n. */
#define CTI_CTIOUTEN_TRIGOUTEN_2_Enabled (1UL) /*!< When an event occurs on channel 2, generate an event on output event n (ctitrigout[n]). */

/* Bit 1 : Enables a cross trigger event to ctitrigout when channel 1 is activated. */
#define CTI_CTIOUTEN_TRIGOUTEN_1_Pos (1UL) /*!< Position of TRIGOUTEN_1 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_1_Msk (0x1UL << CTI_CTIOUTEN_TRIGOUTEN_1_Pos) /*!< Bit mask of TRIGOUTEN_1 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_1_Disabled (0UL) /*!< Channel 1 is ignored by output trigger n. */
#define CTI_CTIOUTEN_TRIGOUTEN_1_Enabled (1UL) /*!< When an event occurs on channel 1, generate an event on output event n (ctitrigout[n]). */

/* Bit 0 : Enables a cross trigger event to ctitrigout when channel 0 is activated. */
#define CTI_CTIOUTEN_TRIGOUTEN_0_Pos (0UL) /*!< Position of TRIGOUTEN_0 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_0_Msk (0x1UL << CTI_CTIOUTEN_TRIGOUTEN_0_Pos) /*!< Bit mask of TRIGOUTEN_0 field. */
#define CTI_CTIOUTEN_TRIGOUTEN_0_Disabled (0UL) /*!< Channel 0 is ignored by output trigger n. */
#define CTI_CTIOUTEN_TRIGOUTEN_0_Enabled (1UL) /*!< When an event occurs on channel 0, generate an event on output event n (ctitrigout[n]). */

/* Register: CTI_CTITRIGINSTATUS */
/* Description: CTI Trigger In Status register */

/* Bit 7 : N/A */
#define CTI_CTITRIGINSTATUS_UNUSED3_Pos (7UL) /*!< Position of UNUSED3 field. */
#define CTI_CTITRIGINSTATUS_UNUSED3_Msk (0x1UL << CTI_CTITRIGINSTATUS_UNUSED3_Pos) /*!< Bit mask of UNUSED3 field. */
#define CTI_CTITRIGINSTATUS_UNUSED3_Inactive (0UL) /*!< Ctitrigin 7 is inactive. */
#define CTI_CTITRIGINSTATUS_UNUSED3_Active (1UL) /*!< Ctitrigin 7 is active. */

/* Bit 6 : N/A */
#define CTI_CTITRIGINSTATUS_UNUSED2_Pos (6UL) /*!< Position of UNUSED2 field. */
#define CTI_CTITRIGINSTATUS_UNUSED2_Msk (0x1UL << CTI_CTITRIGINSTATUS_UNUSED2_Pos) /*!< Bit mask of UNUSED2 field. */
#define CTI_CTITRIGINSTATUS_UNUSED2_Inactive (0UL) /*!< Ctitrigin 6 is inactive. */
#define CTI_CTITRIGINSTATUS_UNUSED2_Active (1UL) /*!< Ctitrigin 6 is active. */

/* Bit 5 : N/A */
#define CTI_CTITRIGINSTATUS_UNUSED1_Pos (5UL) /*!< Position of UNUSED1 field. */
#define CTI_CTITRIGINSTATUS_UNUSED1_Msk (0x1UL << CTI_CTITRIGINSTATUS_UNUSED1_Pos) /*!< Bit mask of UNUSED1 field. */
#define CTI_CTITRIGINSTATUS_UNUSED1_Inactive (0UL) /*!< Ctitrigin 5 is inactive. */
#define CTI_CTITRIGINSTATUS_UNUSED1_Active (1UL) /*!< Ctitrigin 5 is active. */

/* Bit 4 : N/A */
#define CTI_CTITRIGINSTATUS_UNUSED0_Pos (4UL) /*!< Position of UNUSED0 field. */
#define CTI_CTITRIGINSTATUS_UNUSED0_Msk (0x1UL << CTI_CTITRIGINSTATUS_UNUSED0_Pos) /*!< Bit mask of UNUSED0 field. */
#define CTI_CTITRIGINSTATUS_UNUSED0_Inactive (0UL) /*!< Ctitrigin 4 is inactive. */
#define CTI_CTITRIGINSTATUS_UNUSED0_Active (1UL) /*!< Ctitrigin 4 is active. */

/* Bit 3 : DWT Comparator Output 2 */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT2_Pos (3UL) /*!< Position of DWTCOMPOUT2 field. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT2_Msk (0x1UL << CTI_CTITRIGINSTATUS_DWTCOMPOUT2_Pos) /*!< Bit mask of DWTCOMPOUT2 field. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT2_Inactive (0UL) /*!< Ctitrigin 3 is inactive. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT2_Active (1UL) /*!< Ctitrigin 3 is active. */

/* Bit 2 : DWT Comparator Output 1 */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT1_Pos (2UL) /*!< Position of DWTCOMPOUT1 field. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT1_Msk (0x1UL << CTI_CTITRIGINSTATUS_DWTCOMPOUT1_Pos) /*!< Bit mask of DWTCOMPOUT1 field. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT1_Inactive (0UL) /*!< Ctitrigin 2 is inactive. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT1_Active (1UL) /*!< Ctitrigin 2 is active. */

/* Bit 1 : DWT Comparator Output 0 */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT0_Pos (1UL) /*!< Position of DWTCOMPOUT0 field. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT0_Msk (0x1UL << CTI_CTITRIGINSTATUS_DWTCOMPOUT0_Pos) /*!< Bit mask of DWTCOMPOUT0 field. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT0_Inactive (0UL) /*!< Ctitrigin 1 is inactive. */
#define CTI_CTITRIGINSTATUS_DWTCOMPOUT0_Active (1UL) /*!< Ctitrigin 1 is active. */

/* Bit 0 : Processor Halted */
#define CTI_CTITRIGINSTATUS_CPUHALTED_Pos (0UL) /*!< Position of CPUHALTED field. */
#define CTI_CTITRIGINSTATUS_CPUHALTED_Msk (0x1UL << CTI_CTITRIGINSTATUS_CPUHALTED_Pos) /*!< Bit mask of CPUHALTED field. */
#define CTI_CTITRIGINSTATUS_CPUHALTED_Inactive (0UL) /*!< Ctitrigin 0 is inactive. */
#define CTI_CTITRIGINSTATUS_CPUHALTED_Active (1UL) /*!< Ctitrigin 0 is active. */

/* Register: CTI_CTITRIGOUTSTATUS */
/* Description: CTI Trigger Out Status register */

/* Bit 7 : N/A */
#define CTI_CTITRIGOUTSTATUS_UNUSED5_Pos (7UL) /*!< Position of UNUSED5 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED5_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_UNUSED5_Pos) /*!< Bit mask of UNUSED5 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED5_Inactive (0UL) /*!< Ctitrigout 7 is inactive. */
#define CTI_CTITRIGOUTSTATUS_UNUSED5_Active (1UL) /*!< Ctitrigout 7 is active. */

/* Bit 6 : N/A */
#define CTI_CTITRIGOUTSTATUS_UNUSED4_Pos (6UL) /*!< Position of UNUSED4 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED4_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_UNUSED4_Pos) /*!< Bit mask of UNUSED4 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED4_Inactive (0UL) /*!< Ctitrigout 6 is inactive. */
#define CTI_CTITRIGOUTSTATUS_UNUSED4_Active (1UL) /*!< Ctitrigout 6 is active. */

/* Bit 5 : N/A */
#define CTI_CTITRIGOUTSTATUS_UNUSED3_Pos (5UL) /*!< Position of UNUSED3 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED3_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_UNUSED3_Pos) /*!< Bit mask of UNUSED3 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED3_Inactive (0UL) /*!< Ctitrigout 5 is inactive. */
#define CTI_CTITRIGOUTSTATUS_UNUSED3_Active (1UL) /*!< Ctitrigout 5 is active. */

/* Bit 4 : N/A */
#define CTI_CTITRIGOUTSTATUS_UNUSED2_Pos (4UL) /*!< Position of UNUSED2 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED2_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_UNUSED2_Pos) /*!< Bit mask of UNUSED2 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED2_Inactive (0UL) /*!< Ctitrigout 4 is inactive. */
#define CTI_CTITRIGOUTSTATUS_UNUSED2_Active (1UL) /*!< Ctitrigout 4 is active. */

/* Bit 3 : N/A */
#define CTI_CTITRIGOUTSTATUS_UNUSED1_Pos (3UL) /*!< Position of UNUSED1 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED1_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_UNUSED1_Pos) /*!< Bit mask of UNUSED1 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED1_Inactive (0UL) /*!< Ctitrigout 3 is inactive. */
#define CTI_CTITRIGOUTSTATUS_UNUSED1_Active (1UL) /*!< Ctitrigout 3 is active. */

/* Bit 2 : N/A */
#define CTI_CTITRIGOUTSTATUS_UNUSED0_Pos (2UL) /*!< Position of UNUSED0 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED0_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_UNUSED0_Pos) /*!< Bit mask of UNUSED0 field. */
#define CTI_CTITRIGOUTSTATUS_UNUSED0_Inactive (0UL) /*!< Ctitrigout 2 is inactive. */
#define CTI_CTITRIGOUTSTATUS_UNUSED0_Active (1UL) /*!< Ctitrigout 2 is active. */

/* Bit 1 : Processor Restart */
#define CTI_CTITRIGOUTSTATUS_CPURESTART_Pos (1UL) /*!< Position of CPURESTART field. */
#define CTI_CTITRIGOUTSTATUS_CPURESTART_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_CPURESTART_Pos) /*!< Bit mask of CPURESTART field. */
#define CTI_CTITRIGOUTSTATUS_CPURESTART_Inactive (0UL) /*!< Ctitrigout 1 is inactive. */
#define CTI_CTITRIGOUTSTATUS_CPURESTART_Active (1UL) /*!< Ctitrigout 1 is active. */

/* Bit 0 : Processor debug request */
#define CTI_CTITRIGOUTSTATUS_DEBUGREQ_Pos (0UL) /*!< Position of DEBUGREQ field. */
#define CTI_CTITRIGOUTSTATUS_DEBUGREQ_Msk (0x1UL << CTI_CTITRIGOUTSTATUS_DEBUGREQ_Pos) /*!< Bit mask of DEBUGREQ field. */
#define CTI_CTITRIGOUTSTATUS_DEBUGREQ_Inactive (0UL) /*!< Ctitrigout 0 is inactive. */
#define CTI_CTITRIGOUTSTATUS_DEBUGREQ_Active (1UL) /*!< Ctitrigout 0 is active. */

/* Register: CTI_CTICHINSTATUS */
/* Description: CTI Channel In Status register */

/* Bit 3 : Shows the status of the ctitrigin 3 input. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_3_Pos (3UL) /*!< Position of CTICHINSTATUS_3 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_3_Msk (0x1UL << CTI_CTICHINSTATUS_CTICHINSTATUS_3_Pos) /*!< Bit mask of CTICHINSTATUS_3 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_3_Inactive (0UL) /*!< Ctichin 3 is inactive. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_3_Active (1UL) /*!< Ctichin 3 is active. */

/* Bit 2 : Shows the status of the ctitrigin 2 input. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_2_Pos (2UL) /*!< Position of CTICHINSTATUS_2 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_2_Msk (0x1UL << CTI_CTICHINSTATUS_CTICHINSTATUS_2_Pos) /*!< Bit mask of CTICHINSTATUS_2 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_2_Inactive (0UL) /*!< Ctichin 2 is inactive. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_2_Active (1UL) /*!< Ctichin 2 is active. */

/* Bit 1 : Shows the status of the ctitrigin 1 input. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_1_Pos (1UL) /*!< Position of CTICHINSTATUS_1 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_1_Msk (0x1UL << CTI_CTICHINSTATUS_CTICHINSTATUS_1_Pos) /*!< Bit mask of CTICHINSTATUS_1 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_1_Inactive (0UL) /*!< Ctichin 1 is inactive. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_1_Active (1UL) /*!< Ctichin 1 is active. */

/* Bit 0 : Shows the status of the ctitrigin 0 input. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_0_Pos (0UL) /*!< Position of CTICHINSTATUS_0 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_0_Msk (0x1UL << CTI_CTICHINSTATUS_CTICHINSTATUS_0_Pos) /*!< Bit mask of CTICHINSTATUS_0 field. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_0_Inactive (0UL) /*!< Ctichin 0 is inactive. */
#define CTI_CTICHINSTATUS_CTICHINSTATUS_0_Active (1UL) /*!< Ctichin 0 is active. */

/* Register: CTI_CTIGATE */
/* Description: Enable CTI Channel Gate register */

/* Bit 3 : Enable ctichout3. */
#define CTI_CTIGATE_CTIGATEEN_3_Pos (3UL) /*!< Position of CTIGATEEN_3 field. */
#define CTI_CTIGATE_CTIGATEEN_3_Msk (0x1UL << CTI_CTIGATE_CTIGATEEN_3_Pos) /*!< Bit mask of CTIGATEEN_3 field. */
#define CTI_CTIGATE_CTIGATEEN_3_Disabled (0UL) /*!< Disable ctichout channel 3 propagation. */
#define CTI_CTIGATE_CTIGATEEN_3_Enabled (1UL) /*!< Enable ctichout channel 3 propagation. */

/* Bit 2 : Enable ctichout2. */
#define CTI_CTIGATE_CTIGATEEN_2_Pos (2UL) /*!< Position of CTIGATEEN_2 field. */
#define CTI_CTIGATE_CTIGATEEN_2_Msk (0x1UL << CTI_CTIGATE_CTIGATEEN_2_Pos) /*!< Bit mask of CTIGATEEN_2 field. */
#define CTI_CTIGATE_CTIGATEEN_2_Disabled (0UL) /*!< Disable ctichout channel 2 propagation. */
#define CTI_CTIGATE_CTIGATEEN_2_Enabled (1UL) /*!< Enable ctichout channel 2 propagation. */

/* Bit 1 : Enable ctichout1. */
#define CTI_CTIGATE_CTIGATEEN_1_Pos (1UL) /*!< Position of CTIGATEEN_1 field. */
#define CTI_CTIGATE_CTIGATEEN_1_Msk (0x1UL << CTI_CTIGATE_CTIGATEEN_1_Pos) /*!< Bit mask of CTIGATEEN_1 field. */
#define CTI_CTIGATE_CTIGATEEN_1_Disabled (0UL) /*!< Disable ctichout channel 1 propagation. */
#define CTI_CTIGATE_CTIGATEEN_1_Enabled (1UL) /*!< Enable ctichout channel 1 propagation. */

/* Bit 0 : Enable ctichout0. */
#define CTI_CTIGATE_CTIGATEEN_0_Pos (0UL) /*!< Position of CTIGATEEN_0 field. */
#define CTI_CTIGATE_CTIGATEEN_0_Msk (0x1UL << CTI_CTIGATE_CTIGATEEN_0_Pos) /*!< Bit mask of CTIGATEEN_0 field. */
#define CTI_CTIGATE_CTIGATEEN_0_Disabled (0UL) /*!< Disable ctichout channel 0 propagation. */
#define CTI_CTIGATE_CTIGATEEN_0_Enabled (1UL) /*!< Enable ctichout channel 0 propagation. */

/* Register: CTI_DEVARCH */
/* Description: Device Architecture register */

/* Bit 0 : Contains the CTI device architecture. */
#define CTI_DEVARCH_Architecture_Pos (0UL) /*!< Position of Architecture field. */
#define CTI_DEVARCH_Architecture_Msk (0x1UL << CTI_DEVARCH_Architecture_Pos) /*!< Bit mask of Architecture field. */

/* Register: CTI_DEVID */
/* Description: Device Configuration register */

/* Bits 19..16 : Number of ECT channels available. */
#define CTI_DEVID_NUMCH_Pos (16UL) /*!< Position of NUMCH field. */
#define CTI_DEVID_NUMCH_Msk (0xFUL << CTI_DEVID_NUMCH_Pos) /*!< Bit mask of NUMCH field. */

/* Bits 15..8 : Number of ECT triggers available. */
#define CTI_DEVID_NUMTRIG_Pos (8UL) /*!< Position of NUMTRIG field. */
#define CTI_DEVID_NUMTRIG_Msk (0xFFUL << CTI_DEVID_NUMTRIG_Pos) /*!< Bit mask of NUMTRIG field. */

/* Bits 4..0 : Indicates the number of multiplexers available on Trigger Inputs and Trigger Outputs that are using asicctl.
                    The default value of 0b00000 indicates that no multiplexing is present. */
#define CTI_DEVID_EXTMUXNUM_Pos (0UL) /*!< Position of EXTMUXNUM field. */
#define CTI_DEVID_EXTMUXNUM_Msk (0x1FUL << CTI_DEVID_EXTMUXNUM_Pos) /*!< Bit mask of EXTMUXNUM field. */

/* Register: CTI_DEVTYPE */
/* Description: Device Type Identifier register */

/* Bits 7..4 : Sub-classification of the type of the debug component as specified in the Arm Architecture Specification within
                    the major classification as specified in the MAJOR field. */
#define CTI_DEVTYPE_SUB_Pos (4UL) /*!< Position of SUB field. */
#define CTI_DEVTYPE_SUB_Msk (0xFUL << CTI_DEVTYPE_SUB_Pos) /*!< Bit mask of SUB field. */
#define CTI_DEVTYPE_SUB_Crosstrigger (1UL) /*!< Indicates that this component is a sub-triggering component. */

/* Bits 3..0 : Major classification of the type of the debug component as specified in the Arm Architecture Specification for this
                    debug and trace component. */
#define CTI_DEVTYPE_MAJOR_Pos (0UL) /*!< Position of MAJOR field. */
#define CTI_DEVTYPE_MAJOR_Msk (0xFUL << CTI_DEVTYPE_MAJOR_Pos) /*!< Bit mask of MAJOR field. */
#define CTI_DEVTYPE_MAJOR_Controller (4UL) /*!< Indicates that this component allows a debugger to control other components in an Arm CoreSight SoC-400 system. */

/* Register: CTI_PIDR4 */
/* Description: Peripheral ID4 Register */

/* Bits 7..4 : Always 0b0000. Indicates that the device only occupies 4KB of memory. */
#define CTI_PIDR4_SIZE_Pos (4UL) /*!< Position of SIZE field. */
#define CTI_PIDR4_SIZE_Msk (0xFUL << CTI_PIDR4_SIZE_Pos) /*!< Bit mask of SIZE field. */

/* Bits 3..0 : Together, PIDR1.DES_0, PIDR2.DES_1, and PIDR4.DES_2 identify the designer of the component. */
#define CTI_PIDR4_DES_2_Pos (0UL) /*!< Position of DES_2 field. */
#define CTI_PIDR4_DES_2_Msk (0xFUL << CTI_PIDR4_DES_2_Pos) /*!< Bit mask of DES_2 field. */
#define CTI_PIDR4_DES_2_Code (4UL) /*!< JEDEC continuation code. */

/* Register: CTI_PIDR0 */
/* Description: Peripheral ID0 Register */

/* Bits 7..0 : Bits[7:0] of the 12-bit part number of the component. The designer of the component assigns this part number. */
#define CTI_PIDR0_PART_0_Pos (0UL) /*!< Position of PART_0 field. */
#define CTI_PIDR0_PART_0_Msk (0xFFUL << CTI_PIDR0_PART_0_Pos) /*!< Bit mask of PART_0 field. */
#define CTI_PIDR0_PART_0_PartnumberL (0x21UL) /*!< Indicates bits[7:0] of the part number of the component. */

/* Register: CTI_PIDR1 */
/* Description: Peripheral ID1 Register */

/* Bits 7..4 : Together, PIDR1.DES_0, PIDR2.DES_1, and PIDR4.DES_2 identify the designer of the component. */
#define CTI_PIDR1_DES_0_Pos (4UL) /*!< Position of DES_0 field. */
#define CTI_PIDR1_DES_0_Msk (0xFUL << CTI_PIDR1_DES_0_Pos) /*!< Bit mask of DES_0 field. */
#define CTI_PIDR1_DES_0_Arm (11UL) /*!< Arm. Bits[3:0] of the JEDEC JEP106 Identity Code */

/* Bits 3..0 : Bits[11:8] of the 12-bit part number of the component. The designer of the component assigns this part number. */
#define CTI_PIDR1_PART_1_Pos (0UL) /*!< Position of PART_1 field. */
#define CTI_PIDR1_PART_1_Msk (0xFUL << CTI_PIDR1_PART_1_Pos) /*!< Bit mask of PART_1 field. */
#define CTI_PIDR1_PART_1_PartnumberH (13UL) /*!< Indicates bits[11:8] of the part number of the component. */

/* Register: CTI_PIDR2 */
/* Description: Peripheral ID2 Register */

/* Bits 7..4 : Peripheral revision */
#define CTI_PIDR2_REVISION_Pos (4UL) /*!< Position of REVISION field. */
#define CTI_PIDR2_REVISION_Msk (0xFUL << CTI_PIDR2_REVISION_Pos) /*!< Bit mask of REVISION field. */
#define CTI_PIDR2_REVISION_Rev0p0 (0UL) /*!< This device is at r0p0 */

/* Bit 3 : Always 1. Indicates that the JEDEC-assigned designer ID is used. */
#define CTI_PIDR2_JEDEC_Pos (3UL) /*!< Position of JEDEC field. */
#define CTI_PIDR2_JEDEC_Msk (0x1UL << CTI_PIDR2_JEDEC_Pos) /*!< Bit mask of JEDEC field. */

/* Bits 2..0 : Together, PIDR1.DES_0, PIDR2.DES_1, and PIDR4.DES_2 identify the designer of the component. */
#define CTI_PIDR2_DES_1_Pos (0UL) /*!< Position of DES_1 field. */
#define CTI_PIDR2_DES_1_Msk (0x7UL << CTI_PIDR2_DES_1_Pos) /*!< Bit mask of DES_1 field. */
#define CTI_PIDR2_DES_1_Arm (3UL) /*!< Arm. Bits[6:4] of the JEDEC JEP106 Identity Code */

/* Register: CTI_PIDR3 */
/* Description: Peripheral ID3 Register */

/* Bits 7..4 : Indicates minor errata fixes specific to the revision of the component being used, for example metal fixes after
                    implementation. In most cases, this field is 0b0000. Arm recommends that the component designers ensure that a
                    metal fix can change this field if required, for example, by driving it from registers that reset to 0b0000. */
#define CTI_PIDR3_REVAND_Pos (4UL) /*!< Position of REVAND field. */
#define CTI_PIDR3_REVAND_Msk (0xFUL << CTI_PIDR3_REVAND_Pos) /*!< Bit mask of REVAND field. */
#define CTI_PIDR3_REVAND_NoErrata (0UL) /*!< Indicates that there are no errata fixes to this component. */

/* Bits 3..0 : Customer Modified. Indicates whether the customer has modified the behavior of the component. In most cases,
                    this field is 0b0000. Customers change this value when they make authorized modifications to this component. */
#define CTI_PIDR3_CMOD_Pos (0UL) /*!< Position of CMOD field. */
#define CTI_PIDR3_CMOD_Msk (0xFUL << CTI_PIDR3_CMOD_Pos) /*!< Bit mask of CMOD field. */
#define CTI_PIDR3_CMOD_Unmodified (0UL) /*!< Indicates that the customer has not modified this component. */

/* Register: CTI_CIDR0 */
/* Description: Component ID0 Register */

/* Bits 7..0 : Preamble[0]. Contains bits[7:0] of the component identification code. */
#define CTI_CIDR0_PRMBL_0_Pos (0UL) /*!< Position of PRMBL_0 field. */
#define CTI_CIDR0_PRMBL_0_Msk (0xFFUL << CTI_CIDR0_PRMBL_0_Pos) /*!< Bit mask of PRMBL_0 field. */
#define CTI_CIDR0_PRMBL_0_Value (0x0DUL) /*!< Bits[7:0] of the identification code. */

/* Register: CTI_CIDR1 */
/* Description: Component ID1 Register */

/* Bits 7..4 : Class of the component, for example, whether the component is a ROM table or a generic CoreSight component.
                    Contains bits[15:12] of the component identification code */
#define CTI_CIDR1_CLASS_Pos (4UL) /*!< Position of CLASS field. */
#define CTI_CIDR1_CLASS_Msk (0xFUL << CTI_CIDR1_CLASS_Pos) /*!< Bit mask of CLASS field. */
#define CTI_CIDR1_CLASS_Coresight (9UL) /*!< Indicates that the component is a CoreSight component. */

/* Bits 3..0 : Preamble[1]. Contains bits[11:8] of the component identification code. */
#define CTI_CIDR1_PRMBL_1_Pos (0UL) /*!< Position of PRMBL_1 field. */
#define CTI_CIDR1_PRMBL_1_Msk (0xFUL << CTI_CIDR1_PRMBL_1_Pos) /*!< Bit mask of PRMBL_1 field. */
#define CTI_CIDR1_PRMBL_1_Value (0UL) /*!< Bits[11:8] of the identification code. */

/* Register: CTI_CIDR2 */
/* Description: Component ID2 Register */

/* Bits 7..0 : Preamble[2]. Contains bits[23:16] of the component identification code. */
#define CTI_CIDR2_PRMBL_2_Pos (0UL) /*!< Position of PRMBL_2 field. */
#define CTI_CIDR2_PRMBL_2_Msk (0xFFUL << CTI_CIDR2_PRMBL_2_Pos) /*!< Bit mask of PRMBL_2 field. */
#define CTI_CIDR2_PRMBL_2_Value (0x05UL) /*!< Bits[23:16] of the identification code. */

/* Register: CTI_CIDR3 */
/* Description: Component ID3 Register */

/* Bits 7..0 : Preamble[3]. Contains bits[31:24] of the component identification code. */
#define CTI_CIDR3_PRMBL_3_Pos (0UL) /*!< Position of PRMBL_3 field. */
#define CTI_CIDR3_PRMBL_3_Msk (0xFFUL << CTI_CIDR3_PRMBL_3_Pos) /*!< Bit mask of PRMBL_3 field. */
#define CTI_CIDR3_PRMBL_3_Value (0xB1UL) /*!< Bits[31:24] of the identification code. */


/* Peripheral: CTRLAPPERI */
/* Description: Control access port */

/* Register: CTRLAPPERI_MAILBOX_RXDATA */
/* Description: Data sent from the debugger to the CPU. */

/* Bits 31..0 : Data received from debugger */
#define CTRLAPPERI_MAILBOX_RXDATA_RXDATA_Pos (0UL) /*!< Position of RXDATA field. */
#define CTRLAPPERI_MAILBOX_RXDATA_RXDATA_Msk (0xFFFFFFFFUL << CTRLAPPERI_MAILBOX_RXDATA_RXDATA_Pos) /*!< Bit mask of RXDATA field. */

/* Register: CTRLAPPERI_MAILBOX_RXSTATUS */
/* Description: This register shows a status that indicates if data sent from the debugger to the CPU has been read. */

/* Bit 0 : Status of data in register RXDATA */
#define CTRLAPPERI_MAILBOX_RXSTATUS_RXSTATUS_Pos (0UL) /*!< Position of RXSTATUS field. */
#define CTRLAPPERI_MAILBOX_RXSTATUS_RXSTATUS_Msk (0x1UL << CTRLAPPERI_MAILBOX_RXSTATUS_RXSTATUS_Pos) /*!< Bit mask of RXSTATUS field. */
#define CTRLAPPERI_MAILBOX_RXSTATUS_RXSTATUS_NoDataPending (0UL) /*!< No data pending in register RXDATA */
#define CTRLAPPERI_MAILBOX_RXSTATUS_RXSTATUS_DataPending (1UL) /*!< Data pending in register RXDATA */

/* Register: CTRLAPPERI_MAILBOX_TXDATA */
/* Description: Data sent from the CPU to the debugger. */

/* Bits 31..0 : Data sent to debugger */
#define CTRLAPPERI_MAILBOX_TXDATA_TXDATA_Pos (0UL) /*!< Position of TXDATA field. */
#define CTRLAPPERI_MAILBOX_TXDATA_TXDATA_Msk (0xFFFFFFFFUL << CTRLAPPERI_MAILBOX_TXDATA_TXDATA_Pos) /*!< Bit mask of TXDATA field. */

/* Register: CTRLAPPERI_MAILBOX_TXSTATUS */
/* Description: This register shows a status that indicates if the data sent from the CPU to the debugger has been read. */

/* Bit 0 : Status of data in register TXDATA */
#define CTRLAPPERI_MAILBOX_TXSTATUS_TXSTATUS_Pos (0UL) /*!< Position of TXSTATUS field. */
#define CTRLAPPERI_MAILBOX_TXSTATUS_TXSTATUS_Msk (0x1UL << CTRLAPPERI_MAILBOX_TXSTATUS_TXSTATUS_Pos) /*!< Bit mask of TXSTATUS field. */
#define CTRLAPPERI_MAILBOX_TXSTATUS_TXSTATUS_NoDataPending (0UL) /*!< No data pending in register TXDATA */
#define CTRLAPPERI_MAILBOX_TXSTATUS_TXSTATUS_DataPending (1UL) /*!< Data pending in register TXDATA */

/* Register: CTRLAPPERI_ERASEPROTECT_LOCK */
/* Description: This register locks the ERASEPROTECT.DISABLE register from being written until next reset. */

/* Bit 0 : Lock ERASEPROTECT.DISABLE register from being written until next reset */
#define CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Pos (0UL) /*!< Position of LOCK field. */
#define CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Msk (0x1UL << CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Pos) /*!< Bit mask of LOCK field. */
#define CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Unlocked (0UL) /*!< Register ERASEPROTECT.DISABLE is writeable */
#define CTRLAPPERI_ERASEPROTECT_LOCK_LOCK_Locked (1UL) /*!< Register ERASEPROTECT.DISABLE is read-only */

/* Register: CTRLAPPERI_ERASEPROTECT_DISABLE */
/* Description: This register disables the ERASEPROTECT register and performs an  ERASEALL operation. */

/* Bits 31..0 : The ERASEALL sequence is initiated if the value of the KEY fields are non-zero and the KEY fields match on both the CPU and debugger sides. */
#define CTRLAPPERI_ERASEPROTECT_DISABLE_KEY_Pos (0UL) /*!< Position of KEY field. */
#define CTRLAPPERI_ERASEPROTECT_DISABLE_KEY_Msk (0xFFFFFFFFUL << CTRLAPPERI_ERASEPROTECT_DISABLE_KEY_Pos) /*!< Bit mask of KEY field. */

/* Register: CTRLAPPERI_APPROTECT_LOCK */
/* Description: This register locks the APPROTECT.DISABLE register from being written to until next reset. */

/* Bit 0 : Lock the APPROTECT.DISABLE register from being written to until next reset */
#define CTRLAPPERI_APPROTECT_LOCK_LOCK_Pos (0UL) /*!< Position of LOCK field. */
#define CTRLAPPERI_APPROTECT_LOCK_LOCK_Msk (0x1UL << CTRLAPPERI_APPROTECT_LOCK_LOCK_Pos) /*!< Bit mask of LOCK field. */
#define CTRLAPPERI_APPROTECT_LOCK_LOCK_Unlocked (0UL) /*!< Register APPROTECT.DISABLE is writeable */
#define CTRLAPPERI_APPROTECT_LOCK_LOCK_Locked (1UL) /*!< Register APPROTECT.DISABLE is read-only */

/* Register: CTRLAPPERI_APPROTECT_DISABLE */
/* Description: This register disables the APPROTECT register and enables debug access to non-secure mode. */

/* Bits 31..0 : If the value of the KEY field is non-zero, and the KEY fields match on both the
        CPU and debugger sides, disable APPROTECT and enable debug access to non-secure mode until
        the next pin reset, brown-out reset, power-on reset, or watchog timer reset. After reset the debugger side register has a fixed KEY value. To enable debug access, both CTRL-AP and UICR.APPROTECT protection needs to be disabled. */
#define CTRLAPPERI_APPROTECT_DISABLE_KEY_Pos (0UL) /*!< Position of KEY field. */
#define CTRLAPPERI_APPROTECT_DISABLE_KEY_Msk (0xFFFFFFFFUL << CTRLAPPERI_APPROTECT_DISABLE_KEY_Pos) /*!< Bit mask of KEY field. */

/* Register: CTRLAPPERI_STATUS */
/* Description: Status bits for CTRL-AP peripheral. */

/* Bit 2 : Status bit for device debug interface mode */
#define CTRLAPPERI_STATUS_DBGIFACEMODE_Pos (2UL) /*!< Position of DBGIFACEMODE field. */
#define CTRLAPPERI_STATUS_DBGIFACEMODE_Msk (0x1UL << CTRLAPPERI_STATUS_DBGIFACEMODE_Pos) /*!< Bit mask of DBGIFACEMODE field. */
#define CTRLAPPERI_STATUS_DBGIFACEMODE_Disabled (0UL) /*!< No debugger attached */
#define CTRLAPPERI_STATUS_DBGIFACEMODE_Enabled (1UL) /*!< Debugger is attached and device is in debug interface mode */

/* Bit 0 : Status bit for UICR part of access port protection at last reset. */
#define CTRLAPPERI_STATUS_UICRAPPROTECT_Pos (0UL) /*!< Position of UICRAPPROTECT field. */
#define CTRLAPPERI_STATUS_UICRAPPROTECT_Msk (0x1UL << CTRLAPPERI_STATUS_UICRAPPROTECT_Pos) /*!< Bit mask of UICRAPPROTECT field. */
#define CTRLAPPERI_STATUS_UICRAPPROTECT_Enabled (0UL) /*!< APPROTECT was enabled in UICR */
#define CTRLAPPERI_STATUS_UICRAPPROTECT_Disabled (1UL) /*!< APPROTECT wasdisabled in UICR */


/* Peripheral: DCNF */
/* Description: Domain configuration management */

/* Register: DCNF_CPUID */
/* Description: CPU ID of this subsystem */

/* Bits 7..0 : CPU ID */
#define DCNF_CPUID_CPUID_Pos (0UL) /*!< Position of CPUID field. */
#define DCNF_CPUID_CPUID_Msk (0xFFUL << DCNF_CPUID_CPUID_Pos) /*!< Bit mask of CPUID field. */


/* Peripheral: DPPIC */
/* Description: Distributed programmable peripheral interconnect controller */

/* Register: DPPIC_TASKS_CHG_EN */
/* Description: Description cluster: Enable channel group n */

/* Bit 0 : Enable channel group n */
#define DPPIC_TASKS_CHG_EN_EN_Pos (0UL) /*!< Position of EN field. */
#define DPPIC_TASKS_CHG_EN_EN_Msk (0x1UL << DPPIC_TASKS_CHG_EN_EN_Pos) /*!< Bit mask of EN field. */
#define DPPIC_TASKS_CHG_EN_EN_Trigger (1UL) /*!< Trigger task */

/* Register: DPPIC_TASKS_CHG_DIS */
/* Description: Description cluster: Disable channel group n */

/* Bit 0 : Disable channel group n */
#define DPPIC_TASKS_CHG_DIS_DIS_Pos (0UL) /*!< Position of DIS field. */
#define DPPIC_TASKS_CHG_DIS_DIS_Msk (0x1UL << DPPIC_TASKS_CHG_DIS_DIS_Pos) /*!< Bit mask of DIS field. */
#define DPPIC_TASKS_CHG_DIS_DIS_Trigger (1UL) /*!< Trigger task */

/* Register: DPPIC_SUBSCRIBE_CHG_EN */
/* Description: Description cluster: Subscribe configuration for task CHG[n].EN */

/* Bit 31 :   */
#define DPPIC_SUBSCRIBE_CHG_EN_EN_Pos (31UL) /*!< Position of EN field. */
#define DPPIC_SUBSCRIBE_CHG_EN_EN_Msk (0x1UL << DPPIC_SUBSCRIBE_CHG_EN_EN_Pos) /*!< Bit mask of EN field. */
#define DPPIC_SUBSCRIBE_CHG_EN_EN_Disabled (0UL) /*!< Disable subscription */
#define DPPIC_SUBSCRIBE_CHG_EN_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CHG[n].EN will subscribe to */
#define DPPIC_SUBSCRIBE_CHG_EN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define DPPIC_SUBSCRIBE_CHG_EN_CHIDX_Msk (0xFFUL << DPPIC_SUBSCRIBE_CHG_EN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: DPPIC_SUBSCRIBE_CHG_DIS */
/* Description: Description cluster: Subscribe configuration for task CHG[n].DIS */

/* Bit 31 :   */
#define DPPIC_SUBSCRIBE_CHG_DIS_EN_Pos (31UL) /*!< Position of EN field. */
#define DPPIC_SUBSCRIBE_CHG_DIS_EN_Msk (0x1UL << DPPIC_SUBSCRIBE_CHG_DIS_EN_Pos) /*!< Bit mask of EN field. */
#define DPPIC_SUBSCRIBE_CHG_DIS_EN_Disabled (0UL) /*!< Disable subscription */
#define DPPIC_SUBSCRIBE_CHG_DIS_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CHG[n].DIS will subscribe to */
#define DPPIC_SUBSCRIBE_CHG_DIS_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define DPPIC_SUBSCRIBE_CHG_DIS_CHIDX_Msk (0xFFUL << DPPIC_SUBSCRIBE_CHG_DIS_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: DPPIC_CHEN */
/* Description: Channel enable register */

/* Bit 31 : Enable or disable channel 31 */
#define DPPIC_CHEN_CH31_Pos (31UL) /*!< Position of CH31 field. */
#define DPPIC_CHEN_CH31_Msk (0x1UL << DPPIC_CHEN_CH31_Pos) /*!< Bit mask of CH31 field. */
#define DPPIC_CHEN_CH31_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH31_Enabled (1UL) /*!< Enable channel */

/* Bit 30 : Enable or disable channel 30 */
#define DPPIC_CHEN_CH30_Pos (30UL) /*!< Position of CH30 field. */
#define DPPIC_CHEN_CH30_Msk (0x1UL << DPPIC_CHEN_CH30_Pos) /*!< Bit mask of CH30 field. */
#define DPPIC_CHEN_CH30_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH30_Enabled (1UL) /*!< Enable channel */

/* Bit 29 : Enable or disable channel 29 */
#define DPPIC_CHEN_CH29_Pos (29UL) /*!< Position of CH29 field. */
#define DPPIC_CHEN_CH29_Msk (0x1UL << DPPIC_CHEN_CH29_Pos) /*!< Bit mask of CH29 field. */
#define DPPIC_CHEN_CH29_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH29_Enabled (1UL) /*!< Enable channel */

/* Bit 28 : Enable or disable channel 28 */
#define DPPIC_CHEN_CH28_Pos (28UL) /*!< Position of CH28 field. */
#define DPPIC_CHEN_CH28_Msk (0x1UL << DPPIC_CHEN_CH28_Pos) /*!< Bit mask of CH28 field. */
#define DPPIC_CHEN_CH28_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH28_Enabled (1UL) /*!< Enable channel */

/* Bit 27 : Enable or disable channel 27 */
#define DPPIC_CHEN_CH27_Pos (27UL) /*!< Position of CH27 field. */
#define DPPIC_CHEN_CH27_Msk (0x1UL << DPPIC_CHEN_CH27_Pos) /*!< Bit mask of CH27 field. */
#define DPPIC_CHEN_CH27_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH27_Enabled (1UL) /*!< Enable channel */

/* Bit 26 : Enable or disable channel 26 */
#define DPPIC_CHEN_CH26_Pos (26UL) /*!< Position of CH26 field. */
#define DPPIC_CHEN_CH26_Msk (0x1UL << DPPIC_CHEN_CH26_Pos) /*!< Bit mask of CH26 field. */
#define DPPIC_CHEN_CH26_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH26_Enabled (1UL) /*!< Enable channel */

/* Bit 25 : Enable or disable channel 25 */
#define DPPIC_CHEN_CH25_Pos (25UL) /*!< Position of CH25 field. */
#define DPPIC_CHEN_CH25_Msk (0x1UL << DPPIC_CHEN_CH25_Pos) /*!< Bit mask of CH25 field. */
#define DPPIC_CHEN_CH25_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH25_Enabled (1UL) /*!< Enable channel */

/* Bit 24 : Enable or disable channel 24 */
#define DPPIC_CHEN_CH24_Pos (24UL) /*!< Position of CH24 field. */
#define DPPIC_CHEN_CH24_Msk (0x1UL << DPPIC_CHEN_CH24_Pos) /*!< Bit mask of CH24 field. */
#define DPPIC_CHEN_CH24_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH24_Enabled (1UL) /*!< Enable channel */

/* Bit 23 : Enable or disable channel 23 */
#define DPPIC_CHEN_CH23_Pos (23UL) /*!< Position of CH23 field. */
#define DPPIC_CHEN_CH23_Msk (0x1UL << DPPIC_CHEN_CH23_Pos) /*!< Bit mask of CH23 field. */
#define DPPIC_CHEN_CH23_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH23_Enabled (1UL) /*!< Enable channel */

/* Bit 22 : Enable or disable channel 22 */
#define DPPIC_CHEN_CH22_Pos (22UL) /*!< Position of CH22 field. */
#define DPPIC_CHEN_CH22_Msk (0x1UL << DPPIC_CHEN_CH22_Pos) /*!< Bit mask of CH22 field. */
#define DPPIC_CHEN_CH22_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH22_Enabled (1UL) /*!< Enable channel */

/* Bit 21 : Enable or disable channel 21 */
#define DPPIC_CHEN_CH21_Pos (21UL) /*!< Position of CH21 field. */
#define DPPIC_CHEN_CH21_Msk (0x1UL << DPPIC_CHEN_CH21_Pos) /*!< Bit mask of CH21 field. */
#define DPPIC_CHEN_CH21_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH21_Enabled (1UL) /*!< Enable channel */

/* Bit 20 : Enable or disable channel 20 */
#define DPPIC_CHEN_CH20_Pos (20UL) /*!< Position of CH20 field. */
#define DPPIC_CHEN_CH20_Msk (0x1UL << DPPIC_CHEN_CH20_Pos) /*!< Bit mask of CH20 field. */
#define DPPIC_CHEN_CH20_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH20_Enabled (1UL) /*!< Enable channel */

/* Bit 19 : Enable or disable channel 19 */
#define DPPIC_CHEN_CH19_Pos (19UL) /*!< Position of CH19 field. */
#define DPPIC_CHEN_CH19_Msk (0x1UL << DPPIC_CHEN_CH19_Pos) /*!< Bit mask of CH19 field. */
#define DPPIC_CHEN_CH19_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH19_Enabled (1UL) /*!< Enable channel */

/* Bit 18 : Enable or disable channel 18 */
#define DPPIC_CHEN_CH18_Pos (18UL) /*!< Position of CH18 field. */
#define DPPIC_CHEN_CH18_Msk (0x1UL << DPPIC_CHEN_CH18_Pos) /*!< Bit mask of CH18 field. */
#define DPPIC_CHEN_CH18_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH18_Enabled (1UL) /*!< Enable channel */

/* Bit 17 : Enable or disable channel 17 */
#define DPPIC_CHEN_CH17_Pos (17UL) /*!< Position of CH17 field. */
#define DPPIC_CHEN_CH17_Msk (0x1UL << DPPIC_CHEN_CH17_Pos) /*!< Bit mask of CH17 field. */
#define DPPIC_CHEN_CH17_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH17_Enabled (1UL) /*!< Enable channel */

/* Bit 16 : Enable or disable channel 16 */
#define DPPIC_CHEN_CH16_Pos (16UL) /*!< Position of CH16 field. */
#define DPPIC_CHEN_CH16_Msk (0x1UL << DPPIC_CHEN_CH16_Pos) /*!< Bit mask of CH16 field. */
#define DPPIC_CHEN_CH16_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH16_Enabled (1UL) /*!< Enable channel */

/* Bit 15 : Enable or disable channel 15 */
#define DPPIC_CHEN_CH15_Pos (15UL) /*!< Position of CH15 field. */
#define DPPIC_CHEN_CH15_Msk (0x1UL << DPPIC_CHEN_CH15_Pos) /*!< Bit mask of CH15 field. */
#define DPPIC_CHEN_CH15_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH15_Enabled (1UL) /*!< Enable channel */

/* Bit 14 : Enable or disable channel 14 */
#define DPPIC_CHEN_CH14_Pos (14UL) /*!< Position of CH14 field. */
#define DPPIC_CHEN_CH14_Msk (0x1UL << DPPIC_CHEN_CH14_Pos) /*!< Bit mask of CH14 field. */
#define DPPIC_CHEN_CH14_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH14_Enabled (1UL) /*!< Enable channel */

/* Bit 13 : Enable or disable channel 13 */
#define DPPIC_CHEN_CH13_Pos (13UL) /*!< Position of CH13 field. */
#define DPPIC_CHEN_CH13_Msk (0x1UL << DPPIC_CHEN_CH13_Pos) /*!< Bit mask of CH13 field. */
#define DPPIC_CHEN_CH13_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH13_Enabled (1UL) /*!< Enable channel */

/* Bit 12 : Enable or disable channel 12 */
#define DPPIC_CHEN_CH12_Pos (12UL) /*!< Position of CH12 field. */
#define DPPIC_CHEN_CH12_Msk (0x1UL << DPPIC_CHEN_CH12_Pos) /*!< Bit mask of CH12 field. */
#define DPPIC_CHEN_CH12_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH12_Enabled (1UL) /*!< Enable channel */

/* Bit 11 : Enable or disable channel 11 */
#define DPPIC_CHEN_CH11_Pos (11UL) /*!< Position of CH11 field. */
#define DPPIC_CHEN_CH11_Msk (0x1UL << DPPIC_CHEN_CH11_Pos) /*!< Bit mask of CH11 field. */
#define DPPIC_CHEN_CH11_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH11_Enabled (1UL) /*!< Enable channel */

/* Bit 10 : Enable or disable channel 10 */
#define DPPIC_CHEN_CH10_Pos (10UL) /*!< Position of CH10 field. */
#define DPPIC_CHEN_CH10_Msk (0x1UL << DPPIC_CHEN_CH10_Pos) /*!< Bit mask of CH10 field. */
#define DPPIC_CHEN_CH10_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH10_Enabled (1UL) /*!< Enable channel */

/* Bit 9 : Enable or disable channel 9 */
#define DPPIC_CHEN_CH9_Pos (9UL) /*!< Position of CH9 field. */
#define DPPIC_CHEN_CH9_Msk (0x1UL << DPPIC_CHEN_CH9_Pos) /*!< Bit mask of CH9 field. */
#define DPPIC_CHEN_CH9_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH9_Enabled (1UL) /*!< Enable channel */

/* Bit 8 : Enable or disable channel 8 */
#define DPPIC_CHEN_CH8_Pos (8UL) /*!< Position of CH8 field. */
#define DPPIC_CHEN_CH8_Msk (0x1UL << DPPIC_CHEN_CH8_Pos) /*!< Bit mask of CH8 field. */
#define DPPIC_CHEN_CH8_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH8_Enabled (1UL) /*!< Enable channel */

/* Bit 7 : Enable or disable channel 7 */
#define DPPIC_CHEN_CH7_Pos (7UL) /*!< Position of CH7 field. */
#define DPPIC_CHEN_CH7_Msk (0x1UL << DPPIC_CHEN_CH7_Pos) /*!< Bit mask of CH7 field. */
#define DPPIC_CHEN_CH7_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH7_Enabled (1UL) /*!< Enable channel */

/* Bit 6 : Enable or disable channel 6 */
#define DPPIC_CHEN_CH6_Pos (6UL) /*!< Position of CH6 field. */
#define DPPIC_CHEN_CH6_Msk (0x1UL << DPPIC_CHEN_CH6_Pos) /*!< Bit mask of CH6 field. */
#define DPPIC_CHEN_CH6_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH6_Enabled (1UL) /*!< Enable channel */

/* Bit 5 : Enable or disable channel 5 */
#define DPPIC_CHEN_CH5_Pos (5UL) /*!< Position of CH5 field. */
#define DPPIC_CHEN_CH5_Msk (0x1UL << DPPIC_CHEN_CH5_Pos) /*!< Bit mask of CH5 field. */
#define DPPIC_CHEN_CH5_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH5_Enabled (1UL) /*!< Enable channel */

/* Bit 4 : Enable or disable channel 4 */
#define DPPIC_CHEN_CH4_Pos (4UL) /*!< Position of CH4 field. */
#define DPPIC_CHEN_CH4_Msk (0x1UL << DPPIC_CHEN_CH4_Pos) /*!< Bit mask of CH4 field. */
#define DPPIC_CHEN_CH4_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH4_Enabled (1UL) /*!< Enable channel */

/* Bit 3 : Enable or disable channel 3 */
#define DPPIC_CHEN_CH3_Pos (3UL) /*!< Position of CH3 field. */
#define DPPIC_CHEN_CH3_Msk (0x1UL << DPPIC_CHEN_CH3_Pos) /*!< Bit mask of CH3 field. */
#define DPPIC_CHEN_CH3_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH3_Enabled (1UL) /*!< Enable channel */

/* Bit 2 : Enable or disable channel 2 */
#define DPPIC_CHEN_CH2_Pos (2UL) /*!< Position of CH2 field. */
#define DPPIC_CHEN_CH2_Msk (0x1UL << DPPIC_CHEN_CH2_Pos) /*!< Bit mask of CH2 field. */
#define DPPIC_CHEN_CH2_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH2_Enabled (1UL) /*!< Enable channel */

/* Bit 1 : Enable or disable channel 1 */
#define DPPIC_CHEN_CH1_Pos (1UL) /*!< Position of CH1 field. */
#define DPPIC_CHEN_CH1_Msk (0x1UL << DPPIC_CHEN_CH1_Pos) /*!< Bit mask of CH1 field. */
#define DPPIC_CHEN_CH1_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH1_Enabled (1UL) /*!< Enable channel */

/* Bit 0 : Enable or disable channel 0 */
#define DPPIC_CHEN_CH0_Pos (0UL) /*!< Position of CH0 field. */
#define DPPIC_CHEN_CH0_Msk (0x1UL << DPPIC_CHEN_CH0_Pos) /*!< Bit mask of CH0 field. */
#define DPPIC_CHEN_CH0_Disabled (0UL) /*!< Disable channel */
#define DPPIC_CHEN_CH0_Enabled (1UL) /*!< Enable channel */

/* Register: DPPIC_CHENSET */
/* Description: Channel enable set register */

/* Bit 31 : Channel 31 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH31_Pos (31UL) /*!< Position of CH31 field. */
#define DPPIC_CHENSET_CH31_Msk (0x1UL << DPPIC_CHENSET_CH31_Pos) /*!< Bit mask of CH31 field. */
#define DPPIC_CHENSET_CH31_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH31_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH31_Set (1UL) /*!< Write: Enable channel */

/* Bit 30 : Channel 30 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH30_Pos (30UL) /*!< Position of CH30 field. */
#define DPPIC_CHENSET_CH30_Msk (0x1UL << DPPIC_CHENSET_CH30_Pos) /*!< Bit mask of CH30 field. */
#define DPPIC_CHENSET_CH30_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH30_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH30_Set (1UL) /*!< Write: Enable channel */

/* Bit 29 : Channel 29 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH29_Pos (29UL) /*!< Position of CH29 field. */
#define DPPIC_CHENSET_CH29_Msk (0x1UL << DPPIC_CHENSET_CH29_Pos) /*!< Bit mask of CH29 field. */
#define DPPIC_CHENSET_CH29_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH29_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH29_Set (1UL) /*!< Write: Enable channel */

/* Bit 28 : Channel 28 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH28_Pos (28UL) /*!< Position of CH28 field. */
#define DPPIC_CHENSET_CH28_Msk (0x1UL << DPPIC_CHENSET_CH28_Pos) /*!< Bit mask of CH28 field. */
#define DPPIC_CHENSET_CH28_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH28_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH28_Set (1UL) /*!< Write: Enable channel */

/* Bit 27 : Channel 27 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH27_Pos (27UL) /*!< Position of CH27 field. */
#define DPPIC_CHENSET_CH27_Msk (0x1UL << DPPIC_CHENSET_CH27_Pos) /*!< Bit mask of CH27 field. */
#define DPPIC_CHENSET_CH27_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH27_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH27_Set (1UL) /*!< Write: Enable channel */

/* Bit 26 : Channel 26 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH26_Pos (26UL) /*!< Position of CH26 field. */
#define DPPIC_CHENSET_CH26_Msk (0x1UL << DPPIC_CHENSET_CH26_Pos) /*!< Bit mask of CH26 field. */
#define DPPIC_CHENSET_CH26_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH26_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH26_Set (1UL) /*!< Write: Enable channel */

/* Bit 25 : Channel 25 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH25_Pos (25UL) /*!< Position of CH25 field. */
#define DPPIC_CHENSET_CH25_Msk (0x1UL << DPPIC_CHENSET_CH25_Pos) /*!< Bit mask of CH25 field. */
#define DPPIC_CHENSET_CH25_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH25_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH25_Set (1UL) /*!< Write: Enable channel */

/* Bit 24 : Channel 24 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH24_Pos (24UL) /*!< Position of CH24 field. */
#define DPPIC_CHENSET_CH24_Msk (0x1UL << DPPIC_CHENSET_CH24_Pos) /*!< Bit mask of CH24 field. */
#define DPPIC_CHENSET_CH24_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH24_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH24_Set (1UL) /*!< Write: Enable channel */

/* Bit 23 : Channel 23 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH23_Pos (23UL) /*!< Position of CH23 field. */
#define DPPIC_CHENSET_CH23_Msk (0x1UL << DPPIC_CHENSET_CH23_Pos) /*!< Bit mask of CH23 field. */
#define DPPIC_CHENSET_CH23_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH23_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH23_Set (1UL) /*!< Write: Enable channel */

/* Bit 22 : Channel 22 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH22_Pos (22UL) /*!< Position of CH22 field. */
#define DPPIC_CHENSET_CH22_Msk (0x1UL << DPPIC_CHENSET_CH22_Pos) /*!< Bit mask of CH22 field. */
#define DPPIC_CHENSET_CH22_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH22_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH22_Set (1UL) /*!< Write: Enable channel */

/* Bit 21 : Channel 21 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH21_Pos (21UL) /*!< Position of CH21 field. */
#define DPPIC_CHENSET_CH21_Msk (0x1UL << DPPIC_CHENSET_CH21_Pos) /*!< Bit mask of CH21 field. */
#define DPPIC_CHENSET_CH21_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH21_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH21_Set (1UL) /*!< Write: Enable channel */

/* Bit 20 : Channel 20 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH20_Pos (20UL) /*!< Position of CH20 field. */
#define DPPIC_CHENSET_CH20_Msk (0x1UL << DPPIC_CHENSET_CH20_Pos) /*!< Bit mask of CH20 field. */
#define DPPIC_CHENSET_CH20_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH20_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH20_Set (1UL) /*!< Write: Enable channel */

/* Bit 19 : Channel 19 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH19_Pos (19UL) /*!< Position of CH19 field. */
#define DPPIC_CHENSET_CH19_Msk (0x1UL << DPPIC_CHENSET_CH19_Pos) /*!< Bit mask of CH19 field. */
#define DPPIC_CHENSET_CH19_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH19_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH19_Set (1UL) /*!< Write: Enable channel */

/* Bit 18 : Channel 18 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH18_Pos (18UL) /*!< Position of CH18 field. */
#define DPPIC_CHENSET_CH18_Msk (0x1UL << DPPIC_CHENSET_CH18_Pos) /*!< Bit mask of CH18 field. */
#define DPPIC_CHENSET_CH18_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH18_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH18_Set (1UL) /*!< Write: Enable channel */

/* Bit 17 : Channel 17 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH17_Pos (17UL) /*!< Position of CH17 field. */
#define DPPIC_CHENSET_CH17_Msk (0x1UL << DPPIC_CHENSET_CH17_Pos) /*!< Bit mask of CH17 field. */
#define DPPIC_CHENSET_CH17_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH17_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH17_Set (1UL) /*!< Write: Enable channel */

/* Bit 16 : Channel 16 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH16_Pos (16UL) /*!< Position of CH16 field. */
#define DPPIC_CHENSET_CH16_Msk (0x1UL << DPPIC_CHENSET_CH16_Pos) /*!< Bit mask of CH16 field. */
#define DPPIC_CHENSET_CH16_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH16_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH16_Set (1UL) /*!< Write: Enable channel */

/* Bit 15 : Channel 15 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH15_Pos (15UL) /*!< Position of CH15 field. */
#define DPPIC_CHENSET_CH15_Msk (0x1UL << DPPIC_CHENSET_CH15_Pos) /*!< Bit mask of CH15 field. */
#define DPPIC_CHENSET_CH15_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH15_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH15_Set (1UL) /*!< Write: Enable channel */

/* Bit 14 : Channel 14 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH14_Pos (14UL) /*!< Position of CH14 field. */
#define DPPIC_CHENSET_CH14_Msk (0x1UL << DPPIC_CHENSET_CH14_Pos) /*!< Bit mask of CH14 field. */
#define DPPIC_CHENSET_CH14_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH14_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH14_Set (1UL) /*!< Write: Enable channel */

/* Bit 13 : Channel 13 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH13_Pos (13UL) /*!< Position of CH13 field. */
#define DPPIC_CHENSET_CH13_Msk (0x1UL << DPPIC_CHENSET_CH13_Pos) /*!< Bit mask of CH13 field. */
#define DPPIC_CHENSET_CH13_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH13_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH13_Set (1UL) /*!< Write: Enable channel */

/* Bit 12 : Channel 12 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH12_Pos (12UL) /*!< Position of CH12 field. */
#define DPPIC_CHENSET_CH12_Msk (0x1UL << DPPIC_CHENSET_CH12_Pos) /*!< Bit mask of CH12 field. */
#define DPPIC_CHENSET_CH12_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH12_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH12_Set (1UL) /*!< Write: Enable channel */

/* Bit 11 : Channel 11 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH11_Pos (11UL) /*!< Position of CH11 field. */
#define DPPIC_CHENSET_CH11_Msk (0x1UL << DPPIC_CHENSET_CH11_Pos) /*!< Bit mask of CH11 field. */
#define DPPIC_CHENSET_CH11_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH11_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH11_Set (1UL) /*!< Write: Enable channel */

/* Bit 10 : Channel 10 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH10_Pos (10UL) /*!< Position of CH10 field. */
#define DPPIC_CHENSET_CH10_Msk (0x1UL << DPPIC_CHENSET_CH10_Pos) /*!< Bit mask of CH10 field. */
#define DPPIC_CHENSET_CH10_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH10_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH10_Set (1UL) /*!< Write: Enable channel */

/* Bit 9 : Channel 9 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH9_Pos (9UL) /*!< Position of CH9 field. */
#define DPPIC_CHENSET_CH9_Msk (0x1UL << DPPIC_CHENSET_CH9_Pos) /*!< Bit mask of CH9 field. */
#define DPPIC_CHENSET_CH9_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH9_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH9_Set (1UL) /*!< Write: Enable channel */

/* Bit 8 : Channel 8 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH8_Pos (8UL) /*!< Position of CH8 field. */
#define DPPIC_CHENSET_CH8_Msk (0x1UL << DPPIC_CHENSET_CH8_Pos) /*!< Bit mask of CH8 field. */
#define DPPIC_CHENSET_CH8_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH8_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH8_Set (1UL) /*!< Write: Enable channel */

/* Bit 7 : Channel 7 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH7_Pos (7UL) /*!< Position of CH7 field. */
#define DPPIC_CHENSET_CH7_Msk (0x1UL << DPPIC_CHENSET_CH7_Pos) /*!< Bit mask of CH7 field. */
#define DPPIC_CHENSET_CH7_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH7_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH7_Set (1UL) /*!< Write: Enable channel */

/* Bit 6 : Channel 6 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH6_Pos (6UL) /*!< Position of CH6 field. */
#define DPPIC_CHENSET_CH6_Msk (0x1UL << DPPIC_CHENSET_CH6_Pos) /*!< Bit mask of CH6 field. */
#define DPPIC_CHENSET_CH6_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH6_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH6_Set (1UL) /*!< Write: Enable channel */

/* Bit 5 : Channel 5 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH5_Pos (5UL) /*!< Position of CH5 field. */
#define DPPIC_CHENSET_CH5_Msk (0x1UL << DPPIC_CHENSET_CH5_Pos) /*!< Bit mask of CH5 field. */
#define DPPIC_CHENSET_CH5_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH5_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH5_Set (1UL) /*!< Write: Enable channel */

/* Bit 4 : Channel 4 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH4_Pos (4UL) /*!< Position of CH4 field. */
#define DPPIC_CHENSET_CH4_Msk (0x1UL << DPPIC_CHENSET_CH4_Pos) /*!< Bit mask of CH4 field. */
#define DPPIC_CHENSET_CH4_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH4_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH4_Set (1UL) /*!< Write: Enable channel */

/* Bit 3 : Channel 3 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH3_Pos (3UL) /*!< Position of CH3 field. */
#define DPPIC_CHENSET_CH3_Msk (0x1UL << DPPIC_CHENSET_CH3_Pos) /*!< Bit mask of CH3 field. */
#define DPPIC_CHENSET_CH3_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH3_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH3_Set (1UL) /*!< Write: Enable channel */

/* Bit 2 : Channel 2 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH2_Pos (2UL) /*!< Position of CH2 field. */
#define DPPIC_CHENSET_CH2_Msk (0x1UL << DPPIC_CHENSET_CH2_Pos) /*!< Bit mask of CH2 field. */
#define DPPIC_CHENSET_CH2_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH2_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH2_Set (1UL) /*!< Write: Enable channel */

/* Bit 1 : Channel 1 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH1_Pos (1UL) /*!< Position of CH1 field. */
#define DPPIC_CHENSET_CH1_Msk (0x1UL << DPPIC_CHENSET_CH1_Pos) /*!< Bit mask of CH1 field. */
#define DPPIC_CHENSET_CH1_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH1_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH1_Set (1UL) /*!< Write: Enable channel */

/* Bit 0 : Channel 0 enable set register. Writing 0 has no effect. */
#define DPPIC_CHENSET_CH0_Pos (0UL) /*!< Position of CH0 field. */
#define DPPIC_CHENSET_CH0_Msk (0x1UL << DPPIC_CHENSET_CH0_Pos) /*!< Bit mask of CH0 field. */
#define DPPIC_CHENSET_CH0_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENSET_CH0_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENSET_CH0_Set (1UL) /*!< Write: Enable channel */

/* Register: DPPIC_CHENCLR */
/* Description: Channel enable clear register */

/* Bit 31 : Channel 31 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH31_Pos (31UL) /*!< Position of CH31 field. */
#define DPPIC_CHENCLR_CH31_Msk (0x1UL << DPPIC_CHENCLR_CH31_Pos) /*!< Bit mask of CH31 field. */
#define DPPIC_CHENCLR_CH31_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH31_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH31_Clear (1UL) /*!< Write: Disable channel */

/* Bit 30 : Channel 30 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH30_Pos (30UL) /*!< Position of CH30 field. */
#define DPPIC_CHENCLR_CH30_Msk (0x1UL << DPPIC_CHENCLR_CH30_Pos) /*!< Bit mask of CH30 field. */
#define DPPIC_CHENCLR_CH30_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH30_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH30_Clear (1UL) /*!< Write: Disable channel */

/* Bit 29 : Channel 29 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH29_Pos (29UL) /*!< Position of CH29 field. */
#define DPPIC_CHENCLR_CH29_Msk (0x1UL << DPPIC_CHENCLR_CH29_Pos) /*!< Bit mask of CH29 field. */
#define DPPIC_CHENCLR_CH29_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH29_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH29_Clear (1UL) /*!< Write: Disable channel */

/* Bit 28 : Channel 28 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH28_Pos (28UL) /*!< Position of CH28 field. */
#define DPPIC_CHENCLR_CH28_Msk (0x1UL << DPPIC_CHENCLR_CH28_Pos) /*!< Bit mask of CH28 field. */
#define DPPIC_CHENCLR_CH28_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH28_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH28_Clear (1UL) /*!< Write: Disable channel */

/* Bit 27 : Channel 27 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH27_Pos (27UL) /*!< Position of CH27 field. */
#define DPPIC_CHENCLR_CH27_Msk (0x1UL << DPPIC_CHENCLR_CH27_Pos) /*!< Bit mask of CH27 field. */
#define DPPIC_CHENCLR_CH27_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH27_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH27_Clear (1UL) /*!< Write: Disable channel */

/* Bit 26 : Channel 26 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH26_Pos (26UL) /*!< Position of CH26 field. */
#define DPPIC_CHENCLR_CH26_Msk (0x1UL << DPPIC_CHENCLR_CH26_Pos) /*!< Bit mask of CH26 field. */
#define DPPIC_CHENCLR_CH26_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH26_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH26_Clear (1UL) /*!< Write: Disable channel */

/* Bit 25 : Channel 25 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH25_Pos (25UL) /*!< Position of CH25 field. */
#define DPPIC_CHENCLR_CH25_Msk (0x1UL << DPPIC_CHENCLR_CH25_Pos) /*!< Bit mask of CH25 field. */
#define DPPIC_CHENCLR_CH25_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH25_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH25_Clear (1UL) /*!< Write: Disable channel */

/* Bit 24 : Channel 24 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH24_Pos (24UL) /*!< Position of CH24 field. */
#define DPPIC_CHENCLR_CH24_Msk (0x1UL << DPPIC_CHENCLR_CH24_Pos) /*!< Bit mask of CH24 field. */
#define DPPIC_CHENCLR_CH24_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH24_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH24_Clear (1UL) /*!< Write: Disable channel */

/* Bit 23 : Channel 23 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH23_Pos (23UL) /*!< Position of CH23 field. */
#define DPPIC_CHENCLR_CH23_Msk (0x1UL << DPPIC_CHENCLR_CH23_Pos) /*!< Bit mask of CH23 field. */
#define DPPIC_CHENCLR_CH23_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH23_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH23_Clear (1UL) /*!< Write: Disable channel */

/* Bit 22 : Channel 22 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH22_Pos (22UL) /*!< Position of CH22 field. */
#define DPPIC_CHENCLR_CH22_Msk (0x1UL << DPPIC_CHENCLR_CH22_Pos) /*!< Bit mask of CH22 field. */
#define DPPIC_CHENCLR_CH22_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH22_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH22_Clear (1UL) /*!< Write: Disable channel */

/* Bit 21 : Channel 21 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH21_Pos (21UL) /*!< Position of CH21 field. */
#define DPPIC_CHENCLR_CH21_Msk (0x1UL << DPPIC_CHENCLR_CH21_Pos) /*!< Bit mask of CH21 field. */
#define DPPIC_CHENCLR_CH21_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH21_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH21_Clear (1UL) /*!< Write: Disable channel */

/* Bit 20 : Channel 20 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH20_Pos (20UL) /*!< Position of CH20 field. */
#define DPPIC_CHENCLR_CH20_Msk (0x1UL << DPPIC_CHENCLR_CH20_Pos) /*!< Bit mask of CH20 field. */
#define DPPIC_CHENCLR_CH20_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH20_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH20_Clear (1UL) /*!< Write: Disable channel */

/* Bit 19 : Channel 19 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH19_Pos (19UL) /*!< Position of CH19 field. */
#define DPPIC_CHENCLR_CH19_Msk (0x1UL << DPPIC_CHENCLR_CH19_Pos) /*!< Bit mask of CH19 field. */
#define DPPIC_CHENCLR_CH19_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH19_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH19_Clear (1UL) /*!< Write: Disable channel */

/* Bit 18 : Channel 18 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH18_Pos (18UL) /*!< Position of CH18 field. */
#define DPPIC_CHENCLR_CH18_Msk (0x1UL << DPPIC_CHENCLR_CH18_Pos) /*!< Bit mask of CH18 field. */
#define DPPIC_CHENCLR_CH18_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH18_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH18_Clear (1UL) /*!< Write: Disable channel */

/* Bit 17 : Channel 17 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH17_Pos (17UL) /*!< Position of CH17 field. */
#define DPPIC_CHENCLR_CH17_Msk (0x1UL << DPPIC_CHENCLR_CH17_Pos) /*!< Bit mask of CH17 field. */
#define DPPIC_CHENCLR_CH17_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH17_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH17_Clear (1UL) /*!< Write: Disable channel */

/* Bit 16 : Channel 16 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH16_Pos (16UL) /*!< Position of CH16 field. */
#define DPPIC_CHENCLR_CH16_Msk (0x1UL << DPPIC_CHENCLR_CH16_Pos) /*!< Bit mask of CH16 field. */
#define DPPIC_CHENCLR_CH16_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH16_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH16_Clear (1UL) /*!< Write: Disable channel */

/* Bit 15 : Channel 15 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH15_Pos (15UL) /*!< Position of CH15 field. */
#define DPPIC_CHENCLR_CH15_Msk (0x1UL << DPPIC_CHENCLR_CH15_Pos) /*!< Bit mask of CH15 field. */
#define DPPIC_CHENCLR_CH15_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH15_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH15_Clear (1UL) /*!< Write: Disable channel */

/* Bit 14 : Channel 14 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH14_Pos (14UL) /*!< Position of CH14 field. */
#define DPPIC_CHENCLR_CH14_Msk (0x1UL << DPPIC_CHENCLR_CH14_Pos) /*!< Bit mask of CH14 field. */
#define DPPIC_CHENCLR_CH14_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH14_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH14_Clear (1UL) /*!< Write: Disable channel */

/* Bit 13 : Channel 13 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH13_Pos (13UL) /*!< Position of CH13 field. */
#define DPPIC_CHENCLR_CH13_Msk (0x1UL << DPPIC_CHENCLR_CH13_Pos) /*!< Bit mask of CH13 field. */
#define DPPIC_CHENCLR_CH13_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH13_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH13_Clear (1UL) /*!< Write: Disable channel */

/* Bit 12 : Channel 12 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH12_Pos (12UL) /*!< Position of CH12 field. */
#define DPPIC_CHENCLR_CH12_Msk (0x1UL << DPPIC_CHENCLR_CH12_Pos) /*!< Bit mask of CH12 field. */
#define DPPIC_CHENCLR_CH12_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH12_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH12_Clear (1UL) /*!< Write: Disable channel */

/* Bit 11 : Channel 11 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH11_Pos (11UL) /*!< Position of CH11 field. */
#define DPPIC_CHENCLR_CH11_Msk (0x1UL << DPPIC_CHENCLR_CH11_Pos) /*!< Bit mask of CH11 field. */
#define DPPIC_CHENCLR_CH11_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH11_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH11_Clear (1UL) /*!< Write: Disable channel */

/* Bit 10 : Channel 10 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH10_Pos (10UL) /*!< Position of CH10 field. */
#define DPPIC_CHENCLR_CH10_Msk (0x1UL << DPPIC_CHENCLR_CH10_Pos) /*!< Bit mask of CH10 field. */
#define DPPIC_CHENCLR_CH10_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH10_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH10_Clear (1UL) /*!< Write: Disable channel */

/* Bit 9 : Channel 9 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH9_Pos (9UL) /*!< Position of CH9 field. */
#define DPPIC_CHENCLR_CH9_Msk (0x1UL << DPPIC_CHENCLR_CH9_Pos) /*!< Bit mask of CH9 field. */
#define DPPIC_CHENCLR_CH9_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH9_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH9_Clear (1UL) /*!< Write: Disable channel */

/* Bit 8 : Channel 8 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH8_Pos (8UL) /*!< Position of CH8 field. */
#define DPPIC_CHENCLR_CH8_Msk (0x1UL << DPPIC_CHENCLR_CH8_Pos) /*!< Bit mask of CH8 field. */
#define DPPIC_CHENCLR_CH8_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH8_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH8_Clear (1UL) /*!< Write: Disable channel */

/* Bit 7 : Channel 7 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH7_Pos (7UL) /*!< Position of CH7 field. */
#define DPPIC_CHENCLR_CH7_Msk (0x1UL << DPPIC_CHENCLR_CH7_Pos) /*!< Bit mask of CH7 field. */
#define DPPIC_CHENCLR_CH7_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH7_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH7_Clear (1UL) /*!< Write: Disable channel */

/* Bit 6 : Channel 6 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH6_Pos (6UL) /*!< Position of CH6 field. */
#define DPPIC_CHENCLR_CH6_Msk (0x1UL << DPPIC_CHENCLR_CH6_Pos) /*!< Bit mask of CH6 field. */
#define DPPIC_CHENCLR_CH6_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH6_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH6_Clear (1UL) /*!< Write: Disable channel */

/* Bit 5 : Channel 5 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH5_Pos (5UL) /*!< Position of CH5 field. */
#define DPPIC_CHENCLR_CH5_Msk (0x1UL << DPPIC_CHENCLR_CH5_Pos) /*!< Bit mask of CH5 field. */
#define DPPIC_CHENCLR_CH5_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH5_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH5_Clear (1UL) /*!< Write: Disable channel */

/* Bit 4 : Channel 4 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH4_Pos (4UL) /*!< Position of CH4 field. */
#define DPPIC_CHENCLR_CH4_Msk (0x1UL << DPPIC_CHENCLR_CH4_Pos) /*!< Bit mask of CH4 field. */
#define DPPIC_CHENCLR_CH4_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH4_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH4_Clear (1UL) /*!< Write: Disable channel */

/* Bit 3 : Channel 3 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH3_Pos (3UL) /*!< Position of CH3 field. */
#define DPPIC_CHENCLR_CH3_Msk (0x1UL << DPPIC_CHENCLR_CH3_Pos) /*!< Bit mask of CH3 field. */
#define DPPIC_CHENCLR_CH3_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH3_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH3_Clear (1UL) /*!< Write: Disable channel */

/* Bit 2 : Channel 2 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH2_Pos (2UL) /*!< Position of CH2 field. */
#define DPPIC_CHENCLR_CH2_Msk (0x1UL << DPPIC_CHENCLR_CH2_Pos) /*!< Bit mask of CH2 field. */
#define DPPIC_CHENCLR_CH2_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH2_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH2_Clear (1UL) /*!< Write: Disable channel */

/* Bit 1 : Channel 1 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH1_Pos (1UL) /*!< Position of CH1 field. */
#define DPPIC_CHENCLR_CH1_Msk (0x1UL << DPPIC_CHENCLR_CH1_Pos) /*!< Bit mask of CH1 field. */
#define DPPIC_CHENCLR_CH1_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH1_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH1_Clear (1UL) /*!< Write: Disable channel */

/* Bit 0 : Channel 0 enable clear register.  Writing 0 has no effect. */
#define DPPIC_CHENCLR_CH0_Pos (0UL) /*!< Position of CH0 field. */
#define DPPIC_CHENCLR_CH0_Msk (0x1UL << DPPIC_CHENCLR_CH0_Pos) /*!< Bit mask of CH0 field. */
#define DPPIC_CHENCLR_CH0_Disabled (0UL) /*!< Read: Channel disabled */
#define DPPIC_CHENCLR_CH0_Enabled (1UL) /*!< Read: Channel enabled */
#define DPPIC_CHENCLR_CH0_Clear (1UL) /*!< Write: Disable channel */

/* Register: DPPIC_CHG */
/* Description: Description collection: Channel group n Note: Writes to this register are ignored if either SUBSCRIBE_CHG[n].EN or SUBSCRIBE_CHG[n].DIS is enabled */

/* Bit 31 : Include or exclude channel 31 */
#define DPPIC_CHG_CH31_Pos (31UL) /*!< Position of CH31 field. */
#define DPPIC_CHG_CH31_Msk (0x1UL << DPPIC_CHG_CH31_Pos) /*!< Bit mask of CH31 field. */
#define DPPIC_CHG_CH31_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH31_Included (1UL) /*!< Include */

/* Bit 30 : Include or exclude channel 30 */
#define DPPIC_CHG_CH30_Pos (30UL) /*!< Position of CH30 field. */
#define DPPIC_CHG_CH30_Msk (0x1UL << DPPIC_CHG_CH30_Pos) /*!< Bit mask of CH30 field. */
#define DPPIC_CHG_CH30_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH30_Included (1UL) /*!< Include */

/* Bit 29 : Include or exclude channel 29 */
#define DPPIC_CHG_CH29_Pos (29UL) /*!< Position of CH29 field. */
#define DPPIC_CHG_CH29_Msk (0x1UL << DPPIC_CHG_CH29_Pos) /*!< Bit mask of CH29 field. */
#define DPPIC_CHG_CH29_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH29_Included (1UL) /*!< Include */

/* Bit 28 : Include or exclude channel 28 */
#define DPPIC_CHG_CH28_Pos (28UL) /*!< Position of CH28 field. */
#define DPPIC_CHG_CH28_Msk (0x1UL << DPPIC_CHG_CH28_Pos) /*!< Bit mask of CH28 field. */
#define DPPIC_CHG_CH28_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH28_Included (1UL) /*!< Include */

/* Bit 27 : Include or exclude channel 27 */
#define DPPIC_CHG_CH27_Pos (27UL) /*!< Position of CH27 field. */
#define DPPIC_CHG_CH27_Msk (0x1UL << DPPIC_CHG_CH27_Pos) /*!< Bit mask of CH27 field. */
#define DPPIC_CHG_CH27_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH27_Included (1UL) /*!< Include */

/* Bit 26 : Include or exclude channel 26 */
#define DPPIC_CHG_CH26_Pos (26UL) /*!< Position of CH26 field. */
#define DPPIC_CHG_CH26_Msk (0x1UL << DPPIC_CHG_CH26_Pos) /*!< Bit mask of CH26 field. */
#define DPPIC_CHG_CH26_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH26_Included (1UL) /*!< Include */

/* Bit 25 : Include or exclude channel 25 */
#define DPPIC_CHG_CH25_Pos (25UL) /*!< Position of CH25 field. */
#define DPPIC_CHG_CH25_Msk (0x1UL << DPPIC_CHG_CH25_Pos) /*!< Bit mask of CH25 field. */
#define DPPIC_CHG_CH25_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH25_Included (1UL) /*!< Include */

/* Bit 24 : Include or exclude channel 24 */
#define DPPIC_CHG_CH24_Pos (24UL) /*!< Position of CH24 field. */
#define DPPIC_CHG_CH24_Msk (0x1UL << DPPIC_CHG_CH24_Pos) /*!< Bit mask of CH24 field. */
#define DPPIC_CHG_CH24_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH24_Included (1UL) /*!< Include */

/* Bit 23 : Include or exclude channel 23 */
#define DPPIC_CHG_CH23_Pos (23UL) /*!< Position of CH23 field. */
#define DPPIC_CHG_CH23_Msk (0x1UL << DPPIC_CHG_CH23_Pos) /*!< Bit mask of CH23 field. */
#define DPPIC_CHG_CH23_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH23_Included (1UL) /*!< Include */

/* Bit 22 : Include or exclude channel 22 */
#define DPPIC_CHG_CH22_Pos (22UL) /*!< Position of CH22 field. */
#define DPPIC_CHG_CH22_Msk (0x1UL << DPPIC_CHG_CH22_Pos) /*!< Bit mask of CH22 field. */
#define DPPIC_CHG_CH22_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH22_Included (1UL) /*!< Include */

/* Bit 21 : Include or exclude channel 21 */
#define DPPIC_CHG_CH21_Pos (21UL) /*!< Position of CH21 field. */
#define DPPIC_CHG_CH21_Msk (0x1UL << DPPIC_CHG_CH21_Pos) /*!< Bit mask of CH21 field. */
#define DPPIC_CHG_CH21_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH21_Included (1UL) /*!< Include */

/* Bit 20 : Include or exclude channel 20 */
#define DPPIC_CHG_CH20_Pos (20UL) /*!< Position of CH20 field. */
#define DPPIC_CHG_CH20_Msk (0x1UL << DPPIC_CHG_CH20_Pos) /*!< Bit mask of CH20 field. */
#define DPPIC_CHG_CH20_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH20_Included (1UL) /*!< Include */

/* Bit 19 : Include or exclude channel 19 */
#define DPPIC_CHG_CH19_Pos (19UL) /*!< Position of CH19 field. */
#define DPPIC_CHG_CH19_Msk (0x1UL << DPPIC_CHG_CH19_Pos) /*!< Bit mask of CH19 field. */
#define DPPIC_CHG_CH19_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH19_Included (1UL) /*!< Include */

/* Bit 18 : Include or exclude channel 18 */
#define DPPIC_CHG_CH18_Pos (18UL) /*!< Position of CH18 field. */
#define DPPIC_CHG_CH18_Msk (0x1UL << DPPIC_CHG_CH18_Pos) /*!< Bit mask of CH18 field. */
#define DPPIC_CHG_CH18_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH18_Included (1UL) /*!< Include */

/* Bit 17 : Include or exclude channel 17 */
#define DPPIC_CHG_CH17_Pos (17UL) /*!< Position of CH17 field. */
#define DPPIC_CHG_CH17_Msk (0x1UL << DPPIC_CHG_CH17_Pos) /*!< Bit mask of CH17 field. */
#define DPPIC_CHG_CH17_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH17_Included (1UL) /*!< Include */

/* Bit 16 : Include or exclude channel 16 */
#define DPPIC_CHG_CH16_Pos (16UL) /*!< Position of CH16 field. */
#define DPPIC_CHG_CH16_Msk (0x1UL << DPPIC_CHG_CH16_Pos) /*!< Bit mask of CH16 field. */
#define DPPIC_CHG_CH16_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH16_Included (1UL) /*!< Include */

/* Bit 15 : Include or exclude channel 15 */
#define DPPIC_CHG_CH15_Pos (15UL) /*!< Position of CH15 field. */
#define DPPIC_CHG_CH15_Msk (0x1UL << DPPIC_CHG_CH15_Pos) /*!< Bit mask of CH15 field. */
#define DPPIC_CHG_CH15_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH15_Included (1UL) /*!< Include */

/* Bit 14 : Include or exclude channel 14 */
#define DPPIC_CHG_CH14_Pos (14UL) /*!< Position of CH14 field. */
#define DPPIC_CHG_CH14_Msk (0x1UL << DPPIC_CHG_CH14_Pos) /*!< Bit mask of CH14 field. */
#define DPPIC_CHG_CH14_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH14_Included (1UL) /*!< Include */

/* Bit 13 : Include or exclude channel 13 */
#define DPPIC_CHG_CH13_Pos (13UL) /*!< Position of CH13 field. */
#define DPPIC_CHG_CH13_Msk (0x1UL << DPPIC_CHG_CH13_Pos) /*!< Bit mask of CH13 field. */
#define DPPIC_CHG_CH13_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH13_Included (1UL) /*!< Include */

/* Bit 12 : Include or exclude channel 12 */
#define DPPIC_CHG_CH12_Pos (12UL) /*!< Position of CH12 field. */
#define DPPIC_CHG_CH12_Msk (0x1UL << DPPIC_CHG_CH12_Pos) /*!< Bit mask of CH12 field. */
#define DPPIC_CHG_CH12_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH12_Included (1UL) /*!< Include */

/* Bit 11 : Include or exclude channel 11 */
#define DPPIC_CHG_CH11_Pos (11UL) /*!< Position of CH11 field. */
#define DPPIC_CHG_CH11_Msk (0x1UL << DPPIC_CHG_CH11_Pos) /*!< Bit mask of CH11 field. */
#define DPPIC_CHG_CH11_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH11_Included (1UL) /*!< Include */

/* Bit 10 : Include or exclude channel 10 */
#define DPPIC_CHG_CH10_Pos (10UL) /*!< Position of CH10 field. */
#define DPPIC_CHG_CH10_Msk (0x1UL << DPPIC_CHG_CH10_Pos) /*!< Bit mask of CH10 field. */
#define DPPIC_CHG_CH10_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH10_Included (1UL) /*!< Include */

/* Bit 9 : Include or exclude channel 9 */
#define DPPIC_CHG_CH9_Pos (9UL) /*!< Position of CH9 field. */
#define DPPIC_CHG_CH9_Msk (0x1UL << DPPIC_CHG_CH9_Pos) /*!< Bit mask of CH9 field. */
#define DPPIC_CHG_CH9_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH9_Included (1UL) /*!< Include */

/* Bit 8 : Include or exclude channel 8 */
#define DPPIC_CHG_CH8_Pos (8UL) /*!< Position of CH8 field. */
#define DPPIC_CHG_CH8_Msk (0x1UL << DPPIC_CHG_CH8_Pos) /*!< Bit mask of CH8 field. */
#define DPPIC_CHG_CH8_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH8_Included (1UL) /*!< Include */

/* Bit 7 : Include or exclude channel 7 */
#define DPPIC_CHG_CH7_Pos (7UL) /*!< Position of CH7 field. */
#define DPPIC_CHG_CH7_Msk (0x1UL << DPPIC_CHG_CH7_Pos) /*!< Bit mask of CH7 field. */
#define DPPIC_CHG_CH7_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH7_Included (1UL) /*!< Include */

/* Bit 6 : Include or exclude channel 6 */
#define DPPIC_CHG_CH6_Pos (6UL) /*!< Position of CH6 field. */
#define DPPIC_CHG_CH6_Msk (0x1UL << DPPIC_CHG_CH6_Pos) /*!< Bit mask of CH6 field. */
#define DPPIC_CHG_CH6_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH6_Included (1UL) /*!< Include */

/* Bit 5 : Include or exclude channel 5 */
#define DPPIC_CHG_CH5_Pos (5UL) /*!< Position of CH5 field. */
#define DPPIC_CHG_CH5_Msk (0x1UL << DPPIC_CHG_CH5_Pos) /*!< Bit mask of CH5 field. */
#define DPPIC_CHG_CH5_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH5_Included (1UL) /*!< Include */

/* Bit 4 : Include or exclude channel 4 */
#define DPPIC_CHG_CH4_Pos (4UL) /*!< Position of CH4 field. */
#define DPPIC_CHG_CH4_Msk (0x1UL << DPPIC_CHG_CH4_Pos) /*!< Bit mask of CH4 field. */
#define DPPIC_CHG_CH4_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH4_Included (1UL) /*!< Include */

/* Bit 3 : Include or exclude channel 3 */
#define DPPIC_CHG_CH3_Pos (3UL) /*!< Position of CH3 field. */
#define DPPIC_CHG_CH3_Msk (0x1UL << DPPIC_CHG_CH3_Pos) /*!< Bit mask of CH3 field. */
#define DPPIC_CHG_CH3_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH3_Included (1UL) /*!< Include */

/* Bit 2 : Include or exclude channel 2 */
#define DPPIC_CHG_CH2_Pos (2UL) /*!< Position of CH2 field. */
#define DPPIC_CHG_CH2_Msk (0x1UL << DPPIC_CHG_CH2_Pos) /*!< Bit mask of CH2 field. */
#define DPPIC_CHG_CH2_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH2_Included (1UL) /*!< Include */

/* Bit 1 : Include or exclude channel 1 */
#define DPPIC_CHG_CH1_Pos (1UL) /*!< Position of CH1 field. */
#define DPPIC_CHG_CH1_Msk (0x1UL << DPPIC_CHG_CH1_Pos) /*!< Bit mask of CH1 field. */
#define DPPIC_CHG_CH1_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH1_Included (1UL) /*!< Include */

/* Bit 0 : Include or exclude channel 0 */
#define DPPIC_CHG_CH0_Pos (0UL) /*!< Position of CH0 field. */
#define DPPIC_CHG_CH0_Msk (0x1UL << DPPIC_CHG_CH0_Pos) /*!< Bit mask of CH0 field. */
#define DPPIC_CHG_CH0_Excluded (0UL) /*!< Exclude */
#define DPPIC_CHG_CH0_Included (1UL) /*!< Include */


/* Peripheral: ECB */
/* Description: AES ECB Mode Encryption */

/* Register: ECB_TASKS_STARTECB */
/* Description: Start ECB block encrypt */

/* Bit 0 : Start ECB block encrypt */
#define ECB_TASKS_STARTECB_TASKS_STARTECB_Pos (0UL) /*!< Position of TASKS_STARTECB field. */
#define ECB_TASKS_STARTECB_TASKS_STARTECB_Msk (0x1UL << ECB_TASKS_STARTECB_TASKS_STARTECB_Pos) /*!< Bit mask of TASKS_STARTECB field. */
#define ECB_TASKS_STARTECB_TASKS_STARTECB_Trigger (1UL) /*!< Trigger task */

/* Register: ECB_TASKS_STOPECB */
/* Description: Abort a possible executing ECB operation */

/* Bit 0 : Abort a possible executing ECB operation */
#define ECB_TASKS_STOPECB_TASKS_STOPECB_Pos (0UL) /*!< Position of TASKS_STOPECB field. */
#define ECB_TASKS_STOPECB_TASKS_STOPECB_Msk (0x1UL << ECB_TASKS_STOPECB_TASKS_STOPECB_Pos) /*!< Bit mask of TASKS_STOPECB field. */
#define ECB_TASKS_STOPECB_TASKS_STOPECB_Trigger (1UL) /*!< Trigger task */

/* Register: ECB_SUBSCRIBE_STARTECB */
/* Description: Subscribe configuration for task STARTECB */

/* Bit 31 :   */
#define ECB_SUBSCRIBE_STARTECB_EN_Pos (31UL) /*!< Position of EN field. */
#define ECB_SUBSCRIBE_STARTECB_EN_Msk (0x1UL << ECB_SUBSCRIBE_STARTECB_EN_Pos) /*!< Bit mask of EN field. */
#define ECB_SUBSCRIBE_STARTECB_EN_Disabled (0UL) /*!< Disable subscription */
#define ECB_SUBSCRIBE_STARTECB_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STARTECB will subscribe to */
#define ECB_SUBSCRIBE_STARTECB_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define ECB_SUBSCRIBE_STARTECB_CHIDX_Msk (0xFFUL << ECB_SUBSCRIBE_STARTECB_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: ECB_SUBSCRIBE_STOPECB */
/* Description: Subscribe configuration for task STOPECB */

/* Bit 31 :   */
#define ECB_SUBSCRIBE_STOPECB_EN_Pos (31UL) /*!< Position of EN field. */
#define ECB_SUBSCRIBE_STOPECB_EN_Msk (0x1UL << ECB_SUBSCRIBE_STOPECB_EN_Pos) /*!< Bit mask of EN field. */
#define ECB_SUBSCRIBE_STOPECB_EN_Disabled (0UL) /*!< Disable subscription */
#define ECB_SUBSCRIBE_STOPECB_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOPECB will subscribe to */
#define ECB_SUBSCRIBE_STOPECB_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define ECB_SUBSCRIBE_STOPECB_CHIDX_Msk (0xFFUL << ECB_SUBSCRIBE_STOPECB_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: ECB_EVENTS_ENDECB */
/* Description: ECB block encrypt complete */

/* Bit 0 : ECB block encrypt complete */
#define ECB_EVENTS_ENDECB_EVENTS_ENDECB_Pos (0UL) /*!< Position of EVENTS_ENDECB field. */
#define ECB_EVENTS_ENDECB_EVENTS_ENDECB_Msk (0x1UL << ECB_EVENTS_ENDECB_EVENTS_ENDECB_Pos) /*!< Bit mask of EVENTS_ENDECB field. */
#define ECB_EVENTS_ENDECB_EVENTS_ENDECB_NotGenerated (0UL) /*!< Event not generated */
#define ECB_EVENTS_ENDECB_EVENTS_ENDECB_Generated (1UL) /*!< Event generated */

/* Register: ECB_EVENTS_ERRORECB */
/* Description: ECB block encrypt aborted because of a STOPECB task or due to an error */

/* Bit 0 : ECB block encrypt aborted because of a STOPECB task or due to an error */
#define ECB_EVENTS_ERRORECB_EVENTS_ERRORECB_Pos (0UL) /*!< Position of EVENTS_ERRORECB field. */
#define ECB_EVENTS_ERRORECB_EVENTS_ERRORECB_Msk (0x1UL << ECB_EVENTS_ERRORECB_EVENTS_ERRORECB_Pos) /*!< Bit mask of EVENTS_ERRORECB field. */
#define ECB_EVENTS_ERRORECB_EVENTS_ERRORECB_NotGenerated (0UL) /*!< Event not generated */
#define ECB_EVENTS_ERRORECB_EVENTS_ERRORECB_Generated (1UL) /*!< Event generated */

/* Register: ECB_PUBLISH_ENDECB */
/* Description: Publish configuration for event ENDECB */

/* Bit 31 :   */
#define ECB_PUBLISH_ENDECB_EN_Pos (31UL) /*!< Position of EN field. */
#define ECB_PUBLISH_ENDECB_EN_Msk (0x1UL << ECB_PUBLISH_ENDECB_EN_Pos) /*!< Bit mask of EN field. */
#define ECB_PUBLISH_ENDECB_EN_Disabled (0UL) /*!< Disable publishing */
#define ECB_PUBLISH_ENDECB_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDECB will publish to. */
#define ECB_PUBLISH_ENDECB_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define ECB_PUBLISH_ENDECB_CHIDX_Msk (0xFFUL << ECB_PUBLISH_ENDECB_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: ECB_PUBLISH_ERRORECB */
/* Description: Publish configuration for event ERRORECB */

/* Bit 31 :   */
#define ECB_PUBLISH_ERRORECB_EN_Pos (31UL) /*!< Position of EN field. */
#define ECB_PUBLISH_ERRORECB_EN_Msk (0x1UL << ECB_PUBLISH_ERRORECB_EN_Pos) /*!< Bit mask of EN field. */
#define ECB_PUBLISH_ERRORECB_EN_Disabled (0UL) /*!< Disable publishing */
#define ECB_PUBLISH_ERRORECB_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ERRORECB will publish to. */
#define ECB_PUBLISH_ERRORECB_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define ECB_PUBLISH_ERRORECB_CHIDX_Msk (0xFFUL << ECB_PUBLISH_ERRORECB_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: ECB_INTENSET */
/* Description: Enable interrupt */

/* Bit 1 : Write '1' to enable interrupt for event ERRORECB */
#define ECB_INTENSET_ERRORECB_Pos (1UL) /*!< Position of ERRORECB field. */
#define ECB_INTENSET_ERRORECB_Msk (0x1UL << ECB_INTENSET_ERRORECB_Pos) /*!< Bit mask of ERRORECB field. */
#define ECB_INTENSET_ERRORECB_Disabled (0UL) /*!< Read: Disabled */
#define ECB_INTENSET_ERRORECB_Enabled (1UL) /*!< Read: Enabled */
#define ECB_INTENSET_ERRORECB_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event ENDECB */
#define ECB_INTENSET_ENDECB_Pos (0UL) /*!< Position of ENDECB field. */
#define ECB_INTENSET_ENDECB_Msk (0x1UL << ECB_INTENSET_ENDECB_Pos) /*!< Bit mask of ENDECB field. */
#define ECB_INTENSET_ENDECB_Disabled (0UL) /*!< Read: Disabled */
#define ECB_INTENSET_ENDECB_Enabled (1UL) /*!< Read: Enabled */
#define ECB_INTENSET_ENDECB_Set (1UL) /*!< Enable */

/* Register: ECB_INTENCLR */
/* Description: Disable interrupt */

/* Bit 1 : Write '1' to disable interrupt for event ERRORECB */
#define ECB_INTENCLR_ERRORECB_Pos (1UL) /*!< Position of ERRORECB field. */
#define ECB_INTENCLR_ERRORECB_Msk (0x1UL << ECB_INTENCLR_ERRORECB_Pos) /*!< Bit mask of ERRORECB field. */
#define ECB_INTENCLR_ERRORECB_Disabled (0UL) /*!< Read: Disabled */
#define ECB_INTENCLR_ERRORECB_Enabled (1UL) /*!< Read: Enabled */
#define ECB_INTENCLR_ERRORECB_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event ENDECB */
#define ECB_INTENCLR_ENDECB_Pos (0UL) /*!< Position of ENDECB field. */
#define ECB_INTENCLR_ENDECB_Msk (0x1UL << ECB_INTENCLR_ENDECB_Pos) /*!< Bit mask of ENDECB field. */
#define ECB_INTENCLR_ENDECB_Disabled (0UL) /*!< Read: Disabled */
#define ECB_INTENCLR_ENDECB_Enabled (1UL) /*!< Read: Enabled */
#define ECB_INTENCLR_ENDECB_Clear (1UL) /*!< Disable */

/* Register: ECB_ECBDATAPTR */
/* Description: ECB block encrypt memory pointers */

/* Bits 31..0 : Pointer to the ECB data structure (see Table 1 ECB data structure overview) */
#define ECB_ECBDATAPTR_ECBDATAPTR_Pos (0UL) /*!< Position of ECBDATAPTR field. */
#define ECB_ECBDATAPTR_ECBDATAPTR_Msk (0xFFFFFFFFUL << ECB_ECBDATAPTR_ECBDATAPTR_Pos) /*!< Bit mask of ECBDATAPTR field. */


/* Peripheral: EGU */
/* Description: Event generator unit */

/* Register: EGU_TASKS_TRIGGER */
/* Description: Description collection: Trigger n for triggering the corresponding TRIGGERED[n] event */

/* Bit 0 : Trigger n for triggering the corresponding TRIGGERED[n] event */
#define EGU_TASKS_TRIGGER_TASKS_TRIGGER_Pos (0UL) /*!< Position of TASKS_TRIGGER field. */
#define EGU_TASKS_TRIGGER_TASKS_TRIGGER_Msk (0x1UL << EGU_TASKS_TRIGGER_TASKS_TRIGGER_Pos) /*!< Bit mask of TASKS_TRIGGER field. */
#define EGU_TASKS_TRIGGER_TASKS_TRIGGER_Trigger (1UL) /*!< Trigger task */

/* Register: EGU_SUBSCRIBE_TRIGGER */
/* Description: Description collection: Subscribe configuration for task TRIGGER[n] */

/* Bit 31 :   */
#define EGU_SUBSCRIBE_TRIGGER_EN_Pos (31UL) /*!< Position of EN field. */
#define EGU_SUBSCRIBE_TRIGGER_EN_Msk (0x1UL << EGU_SUBSCRIBE_TRIGGER_EN_Pos) /*!< Bit mask of EN field. */
#define EGU_SUBSCRIBE_TRIGGER_EN_Disabled (0UL) /*!< Disable subscription */
#define EGU_SUBSCRIBE_TRIGGER_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task TRIGGER[n] will subscribe to */
#define EGU_SUBSCRIBE_TRIGGER_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define EGU_SUBSCRIBE_TRIGGER_CHIDX_Msk (0xFFUL << EGU_SUBSCRIBE_TRIGGER_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: EGU_EVENTS_TRIGGERED */
/* Description: Description collection: Event number n generated by triggering the corresponding TRIGGER[n] task */

/* Bit 0 : Event number n generated by triggering the corresponding TRIGGER[n] task */
#define EGU_EVENTS_TRIGGERED_EVENTS_TRIGGERED_Pos (0UL) /*!< Position of EVENTS_TRIGGERED field. */
#define EGU_EVENTS_TRIGGERED_EVENTS_TRIGGERED_Msk (0x1UL << EGU_EVENTS_TRIGGERED_EVENTS_TRIGGERED_Pos) /*!< Bit mask of EVENTS_TRIGGERED field. */
#define EGU_EVENTS_TRIGGERED_EVENTS_TRIGGERED_NotGenerated (0UL) /*!< Event not generated */
#define EGU_EVENTS_TRIGGERED_EVENTS_TRIGGERED_Generated (1UL) /*!< Event generated */

/* Register: EGU_PUBLISH_TRIGGERED */
/* Description: Description collection: Publish configuration for event TRIGGERED[n] */

/* Bit 31 :   */
#define EGU_PUBLISH_TRIGGERED_EN_Pos (31UL) /*!< Position of EN field. */
#define EGU_PUBLISH_TRIGGERED_EN_Msk (0x1UL << EGU_PUBLISH_TRIGGERED_EN_Pos) /*!< Bit mask of EN field. */
#define EGU_PUBLISH_TRIGGERED_EN_Disabled (0UL) /*!< Disable publishing */
#define EGU_PUBLISH_TRIGGERED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TRIGGERED[n] will publish to. */
#define EGU_PUBLISH_TRIGGERED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define EGU_PUBLISH_TRIGGERED_CHIDX_Msk (0xFFUL << EGU_PUBLISH_TRIGGERED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: EGU_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 15 : Enable or disable interrupt for event TRIGGERED[15] */
#define EGU_INTEN_TRIGGERED15_Pos (15UL) /*!< Position of TRIGGERED15 field. */
#define EGU_INTEN_TRIGGERED15_Msk (0x1UL << EGU_INTEN_TRIGGERED15_Pos) /*!< Bit mask of TRIGGERED15 field. */
#define EGU_INTEN_TRIGGERED15_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED15_Enabled (1UL) /*!< Enable */

/* Bit 14 : Enable or disable interrupt for event TRIGGERED[14] */
#define EGU_INTEN_TRIGGERED14_Pos (14UL) /*!< Position of TRIGGERED14 field. */
#define EGU_INTEN_TRIGGERED14_Msk (0x1UL << EGU_INTEN_TRIGGERED14_Pos) /*!< Bit mask of TRIGGERED14 field. */
#define EGU_INTEN_TRIGGERED14_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED14_Enabled (1UL) /*!< Enable */

/* Bit 13 : Enable or disable interrupt for event TRIGGERED[13] */
#define EGU_INTEN_TRIGGERED13_Pos (13UL) /*!< Position of TRIGGERED13 field. */
#define EGU_INTEN_TRIGGERED13_Msk (0x1UL << EGU_INTEN_TRIGGERED13_Pos) /*!< Bit mask of TRIGGERED13 field. */
#define EGU_INTEN_TRIGGERED13_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED13_Enabled (1UL) /*!< Enable */

/* Bit 12 : Enable or disable interrupt for event TRIGGERED[12] */
#define EGU_INTEN_TRIGGERED12_Pos (12UL) /*!< Position of TRIGGERED12 field. */
#define EGU_INTEN_TRIGGERED12_Msk (0x1UL << EGU_INTEN_TRIGGERED12_Pos) /*!< Bit mask of TRIGGERED12 field. */
#define EGU_INTEN_TRIGGERED12_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED12_Enabled (1UL) /*!< Enable */

/* Bit 11 : Enable or disable interrupt for event TRIGGERED[11] */
#define EGU_INTEN_TRIGGERED11_Pos (11UL) /*!< Position of TRIGGERED11 field. */
#define EGU_INTEN_TRIGGERED11_Msk (0x1UL << EGU_INTEN_TRIGGERED11_Pos) /*!< Bit mask of TRIGGERED11 field. */
#define EGU_INTEN_TRIGGERED11_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED11_Enabled (1UL) /*!< Enable */

/* Bit 10 : Enable or disable interrupt for event TRIGGERED[10] */
#define EGU_INTEN_TRIGGERED10_Pos (10UL) /*!< Position of TRIGGERED10 field. */
#define EGU_INTEN_TRIGGERED10_Msk (0x1UL << EGU_INTEN_TRIGGERED10_Pos) /*!< Bit mask of TRIGGERED10 field. */
#define EGU_INTEN_TRIGGERED10_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED10_Enabled (1UL) /*!< Enable */

/* Bit 9 : Enable or disable interrupt for event TRIGGERED[9] */
#define EGU_INTEN_TRIGGERED9_Pos (9UL) /*!< Position of TRIGGERED9 field. */
#define EGU_INTEN_TRIGGERED9_Msk (0x1UL << EGU_INTEN_TRIGGERED9_Pos) /*!< Bit mask of TRIGGERED9 field. */
#define EGU_INTEN_TRIGGERED9_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED9_Enabled (1UL) /*!< Enable */

/* Bit 8 : Enable or disable interrupt for event TRIGGERED[8] */
#define EGU_INTEN_TRIGGERED8_Pos (8UL) /*!< Position of TRIGGERED8 field. */
#define EGU_INTEN_TRIGGERED8_Msk (0x1UL << EGU_INTEN_TRIGGERED8_Pos) /*!< Bit mask of TRIGGERED8 field. */
#define EGU_INTEN_TRIGGERED8_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED8_Enabled (1UL) /*!< Enable */

/* Bit 7 : Enable or disable interrupt for event TRIGGERED[7] */
#define EGU_INTEN_TRIGGERED7_Pos (7UL) /*!< Position of TRIGGERED7 field. */
#define EGU_INTEN_TRIGGERED7_Msk (0x1UL << EGU_INTEN_TRIGGERED7_Pos) /*!< Bit mask of TRIGGERED7 field. */
#define EGU_INTEN_TRIGGERED7_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED7_Enabled (1UL) /*!< Enable */

/* Bit 6 : Enable or disable interrupt for event TRIGGERED[6] */
#define EGU_INTEN_TRIGGERED6_Pos (6UL) /*!< Position of TRIGGERED6 field. */
#define EGU_INTEN_TRIGGERED6_Msk (0x1UL << EGU_INTEN_TRIGGERED6_Pos) /*!< Bit mask of TRIGGERED6 field. */
#define EGU_INTEN_TRIGGERED6_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED6_Enabled (1UL) /*!< Enable */

/* Bit 5 : Enable or disable interrupt for event TRIGGERED[5] */
#define EGU_INTEN_TRIGGERED5_Pos (5UL) /*!< Position of TRIGGERED5 field. */
#define EGU_INTEN_TRIGGERED5_Msk (0x1UL << EGU_INTEN_TRIGGERED5_Pos) /*!< Bit mask of TRIGGERED5 field. */
#define EGU_INTEN_TRIGGERED5_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED5_Enabled (1UL) /*!< Enable */

/* Bit 4 : Enable or disable interrupt for event TRIGGERED[4] */
#define EGU_INTEN_TRIGGERED4_Pos (4UL) /*!< Position of TRIGGERED4 field. */
#define EGU_INTEN_TRIGGERED4_Msk (0x1UL << EGU_INTEN_TRIGGERED4_Pos) /*!< Bit mask of TRIGGERED4 field. */
#define EGU_INTEN_TRIGGERED4_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED4_Enabled (1UL) /*!< Enable */

/* Bit 3 : Enable or disable interrupt for event TRIGGERED[3] */
#define EGU_INTEN_TRIGGERED3_Pos (3UL) /*!< Position of TRIGGERED3 field. */
#define EGU_INTEN_TRIGGERED3_Msk (0x1UL << EGU_INTEN_TRIGGERED3_Pos) /*!< Bit mask of TRIGGERED3 field. */
#define EGU_INTEN_TRIGGERED3_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED3_Enabled (1UL) /*!< Enable */

/* Bit 2 : Enable or disable interrupt for event TRIGGERED[2] */
#define EGU_INTEN_TRIGGERED2_Pos (2UL) /*!< Position of TRIGGERED2 field. */
#define EGU_INTEN_TRIGGERED2_Msk (0x1UL << EGU_INTEN_TRIGGERED2_Pos) /*!< Bit mask of TRIGGERED2 field. */
#define EGU_INTEN_TRIGGERED2_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED2_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable interrupt for event TRIGGERED[1] */
#define EGU_INTEN_TRIGGERED1_Pos (1UL) /*!< Position of TRIGGERED1 field. */
#define EGU_INTEN_TRIGGERED1_Msk (0x1UL << EGU_INTEN_TRIGGERED1_Pos) /*!< Bit mask of TRIGGERED1 field. */
#define EGU_INTEN_TRIGGERED1_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED1_Enabled (1UL) /*!< Enable */

/* Bit 0 : Enable or disable interrupt for event TRIGGERED[0] */
#define EGU_INTEN_TRIGGERED0_Pos (0UL) /*!< Position of TRIGGERED0 field. */
#define EGU_INTEN_TRIGGERED0_Msk (0x1UL << EGU_INTEN_TRIGGERED0_Pos) /*!< Bit mask of TRIGGERED0 field. */
#define EGU_INTEN_TRIGGERED0_Disabled (0UL) /*!< Disable */
#define EGU_INTEN_TRIGGERED0_Enabled (1UL) /*!< Enable */

/* Register: EGU_INTENSET */
/* Description: Enable interrupt */

/* Bit 15 : Write '1' to enable interrupt for event TRIGGERED[15] */
#define EGU_INTENSET_TRIGGERED15_Pos (15UL) /*!< Position of TRIGGERED15 field. */
#define EGU_INTENSET_TRIGGERED15_Msk (0x1UL << EGU_INTENSET_TRIGGERED15_Pos) /*!< Bit mask of TRIGGERED15 field. */
#define EGU_INTENSET_TRIGGERED15_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED15_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED15_Set (1UL) /*!< Enable */

/* Bit 14 : Write '1' to enable interrupt for event TRIGGERED[14] */
#define EGU_INTENSET_TRIGGERED14_Pos (14UL) /*!< Position of TRIGGERED14 field. */
#define EGU_INTENSET_TRIGGERED14_Msk (0x1UL << EGU_INTENSET_TRIGGERED14_Pos) /*!< Bit mask of TRIGGERED14 field. */
#define EGU_INTENSET_TRIGGERED14_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED14_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED14_Set (1UL) /*!< Enable */

/* Bit 13 : Write '1' to enable interrupt for event TRIGGERED[13] */
#define EGU_INTENSET_TRIGGERED13_Pos (13UL) /*!< Position of TRIGGERED13 field. */
#define EGU_INTENSET_TRIGGERED13_Msk (0x1UL << EGU_INTENSET_TRIGGERED13_Pos) /*!< Bit mask of TRIGGERED13 field. */
#define EGU_INTENSET_TRIGGERED13_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED13_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED13_Set (1UL) /*!< Enable */

/* Bit 12 : Write '1' to enable interrupt for event TRIGGERED[12] */
#define EGU_INTENSET_TRIGGERED12_Pos (12UL) /*!< Position of TRIGGERED12 field. */
#define EGU_INTENSET_TRIGGERED12_Msk (0x1UL << EGU_INTENSET_TRIGGERED12_Pos) /*!< Bit mask of TRIGGERED12 field. */
#define EGU_INTENSET_TRIGGERED12_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED12_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED12_Set (1UL) /*!< Enable */

/* Bit 11 : Write '1' to enable interrupt for event TRIGGERED[11] */
#define EGU_INTENSET_TRIGGERED11_Pos (11UL) /*!< Position of TRIGGERED11 field. */
#define EGU_INTENSET_TRIGGERED11_Msk (0x1UL << EGU_INTENSET_TRIGGERED11_Pos) /*!< Bit mask of TRIGGERED11 field. */
#define EGU_INTENSET_TRIGGERED11_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED11_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED11_Set (1UL) /*!< Enable */

/* Bit 10 : Write '1' to enable interrupt for event TRIGGERED[10] */
#define EGU_INTENSET_TRIGGERED10_Pos (10UL) /*!< Position of TRIGGERED10 field. */
#define EGU_INTENSET_TRIGGERED10_Msk (0x1UL << EGU_INTENSET_TRIGGERED10_Pos) /*!< Bit mask of TRIGGERED10 field. */
#define EGU_INTENSET_TRIGGERED10_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED10_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED10_Set (1UL) /*!< Enable */

/* Bit 9 : Write '1' to enable interrupt for event TRIGGERED[9] */
#define EGU_INTENSET_TRIGGERED9_Pos (9UL) /*!< Position of TRIGGERED9 field. */
#define EGU_INTENSET_TRIGGERED9_Msk (0x1UL << EGU_INTENSET_TRIGGERED9_Pos) /*!< Bit mask of TRIGGERED9 field. */
#define EGU_INTENSET_TRIGGERED9_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED9_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED9_Set (1UL) /*!< Enable */

/* Bit 8 : Write '1' to enable interrupt for event TRIGGERED[8] */
#define EGU_INTENSET_TRIGGERED8_Pos (8UL) /*!< Position of TRIGGERED8 field. */
#define EGU_INTENSET_TRIGGERED8_Msk (0x1UL << EGU_INTENSET_TRIGGERED8_Pos) /*!< Bit mask of TRIGGERED8 field. */
#define EGU_INTENSET_TRIGGERED8_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED8_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED8_Set (1UL) /*!< Enable */

/* Bit 7 : Write '1' to enable interrupt for event TRIGGERED[7] */
#define EGU_INTENSET_TRIGGERED7_Pos (7UL) /*!< Position of TRIGGERED7 field. */
#define EGU_INTENSET_TRIGGERED7_Msk (0x1UL << EGU_INTENSET_TRIGGERED7_Pos) /*!< Bit mask of TRIGGERED7 field. */
#define EGU_INTENSET_TRIGGERED7_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED7_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED7_Set (1UL) /*!< Enable */

/* Bit 6 : Write '1' to enable interrupt for event TRIGGERED[6] */
#define EGU_INTENSET_TRIGGERED6_Pos (6UL) /*!< Position of TRIGGERED6 field. */
#define EGU_INTENSET_TRIGGERED6_Msk (0x1UL << EGU_INTENSET_TRIGGERED6_Pos) /*!< Bit mask of TRIGGERED6 field. */
#define EGU_INTENSET_TRIGGERED6_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED6_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED6_Set (1UL) /*!< Enable */

/* Bit 5 : Write '1' to enable interrupt for event TRIGGERED[5] */
#define EGU_INTENSET_TRIGGERED5_Pos (5UL) /*!< Position of TRIGGERED5 field. */
#define EGU_INTENSET_TRIGGERED5_Msk (0x1UL << EGU_INTENSET_TRIGGERED5_Pos) /*!< Bit mask of TRIGGERED5 field. */
#define EGU_INTENSET_TRIGGERED5_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED5_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED5_Set (1UL) /*!< Enable */

/* Bit 4 : Write '1' to enable interrupt for event TRIGGERED[4] */
#define EGU_INTENSET_TRIGGERED4_Pos (4UL) /*!< Position of TRIGGERED4 field. */
#define EGU_INTENSET_TRIGGERED4_Msk (0x1UL << EGU_INTENSET_TRIGGERED4_Pos) /*!< Bit mask of TRIGGERED4 field. */
#define EGU_INTENSET_TRIGGERED4_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED4_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED4_Set (1UL) /*!< Enable */

/* Bit 3 : Write '1' to enable interrupt for event TRIGGERED[3] */
#define EGU_INTENSET_TRIGGERED3_Pos (3UL) /*!< Position of TRIGGERED3 field. */
#define EGU_INTENSET_TRIGGERED3_Msk (0x1UL << EGU_INTENSET_TRIGGERED3_Pos) /*!< Bit mask of TRIGGERED3 field. */
#define EGU_INTENSET_TRIGGERED3_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED3_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED3_Set (1UL) /*!< Enable */

/* Bit 2 : Write '1' to enable interrupt for event TRIGGERED[2] */
#define EGU_INTENSET_TRIGGERED2_Pos (2UL) /*!< Position of TRIGGERED2 field. */
#define EGU_INTENSET_TRIGGERED2_Msk (0x1UL << EGU_INTENSET_TRIGGERED2_Pos) /*!< Bit mask of TRIGGERED2 field. */
#define EGU_INTENSET_TRIGGERED2_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED2_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED2_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event TRIGGERED[1] */
#define EGU_INTENSET_TRIGGERED1_Pos (1UL) /*!< Position of TRIGGERED1 field. */
#define EGU_INTENSET_TRIGGERED1_Msk (0x1UL << EGU_INTENSET_TRIGGERED1_Pos) /*!< Bit mask of TRIGGERED1 field. */
#define EGU_INTENSET_TRIGGERED1_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED1_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED1_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event TRIGGERED[0] */
#define EGU_INTENSET_TRIGGERED0_Pos (0UL) /*!< Position of TRIGGERED0 field. */
#define EGU_INTENSET_TRIGGERED0_Msk (0x1UL << EGU_INTENSET_TRIGGERED0_Pos) /*!< Bit mask of TRIGGERED0 field. */
#define EGU_INTENSET_TRIGGERED0_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENSET_TRIGGERED0_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENSET_TRIGGERED0_Set (1UL) /*!< Enable */

/* Register: EGU_INTENCLR */
/* Description: Disable interrupt */

/* Bit 15 : Write '1' to disable interrupt for event TRIGGERED[15] */
#define EGU_INTENCLR_TRIGGERED15_Pos (15UL) /*!< Position of TRIGGERED15 field. */
#define EGU_INTENCLR_TRIGGERED15_Msk (0x1UL << EGU_INTENCLR_TRIGGERED15_Pos) /*!< Bit mask of TRIGGERED15 field. */
#define EGU_INTENCLR_TRIGGERED15_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED15_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED15_Clear (1UL) /*!< Disable */

/* Bit 14 : Write '1' to disable interrupt for event TRIGGERED[14] */
#define EGU_INTENCLR_TRIGGERED14_Pos (14UL) /*!< Position of TRIGGERED14 field. */
#define EGU_INTENCLR_TRIGGERED14_Msk (0x1UL << EGU_INTENCLR_TRIGGERED14_Pos) /*!< Bit mask of TRIGGERED14 field. */
#define EGU_INTENCLR_TRIGGERED14_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED14_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED14_Clear (1UL) /*!< Disable */

/* Bit 13 : Write '1' to disable interrupt for event TRIGGERED[13] */
#define EGU_INTENCLR_TRIGGERED13_Pos (13UL) /*!< Position of TRIGGERED13 field. */
#define EGU_INTENCLR_TRIGGERED13_Msk (0x1UL << EGU_INTENCLR_TRIGGERED13_Pos) /*!< Bit mask of TRIGGERED13 field. */
#define EGU_INTENCLR_TRIGGERED13_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED13_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED13_Clear (1UL) /*!< Disable */

/* Bit 12 : Write '1' to disable interrupt for event TRIGGERED[12] */
#define EGU_INTENCLR_TRIGGERED12_Pos (12UL) /*!< Position of TRIGGERED12 field. */
#define EGU_INTENCLR_TRIGGERED12_Msk (0x1UL << EGU_INTENCLR_TRIGGERED12_Pos) /*!< Bit mask of TRIGGERED12 field. */
#define EGU_INTENCLR_TRIGGERED12_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED12_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED12_Clear (1UL) /*!< Disable */

/* Bit 11 : Write '1' to disable interrupt for event TRIGGERED[11] */
#define EGU_INTENCLR_TRIGGERED11_Pos (11UL) /*!< Position of TRIGGERED11 field. */
#define EGU_INTENCLR_TRIGGERED11_Msk (0x1UL << EGU_INTENCLR_TRIGGERED11_Pos) /*!< Bit mask of TRIGGERED11 field. */
#define EGU_INTENCLR_TRIGGERED11_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED11_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED11_Clear (1UL) /*!< Disable */

/* Bit 10 : Write '1' to disable interrupt for event TRIGGERED[10] */
#define EGU_INTENCLR_TRIGGERED10_Pos (10UL) /*!< Position of TRIGGERED10 field. */
#define EGU_INTENCLR_TRIGGERED10_Msk (0x1UL << EGU_INTENCLR_TRIGGERED10_Pos) /*!< Bit mask of TRIGGERED10 field. */
#define EGU_INTENCLR_TRIGGERED10_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED10_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED10_Clear (1UL) /*!< Disable */

/* Bit 9 : Write '1' to disable interrupt for event TRIGGERED[9] */
#define EGU_INTENCLR_TRIGGERED9_Pos (9UL) /*!< Position of TRIGGERED9 field. */
#define EGU_INTENCLR_TRIGGERED9_Msk (0x1UL << EGU_INTENCLR_TRIGGERED9_Pos) /*!< Bit mask of TRIGGERED9 field. */
#define EGU_INTENCLR_TRIGGERED9_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED9_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED9_Clear (1UL) /*!< Disable */

/* Bit 8 : Write '1' to disable interrupt for event TRIGGERED[8] */
#define EGU_INTENCLR_TRIGGERED8_Pos (8UL) /*!< Position of TRIGGERED8 field. */
#define EGU_INTENCLR_TRIGGERED8_Msk (0x1UL << EGU_INTENCLR_TRIGGERED8_Pos) /*!< Bit mask of TRIGGERED8 field. */
#define EGU_INTENCLR_TRIGGERED8_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED8_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED8_Clear (1UL) /*!< Disable */

/* Bit 7 : Write '1' to disable interrupt for event TRIGGERED[7] */
#define EGU_INTENCLR_TRIGGERED7_Pos (7UL) /*!< Position of TRIGGERED7 field. */
#define EGU_INTENCLR_TRIGGERED7_Msk (0x1UL << EGU_INTENCLR_TRIGGERED7_Pos) /*!< Bit mask of TRIGGERED7 field. */
#define EGU_INTENCLR_TRIGGERED7_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED7_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED7_Clear (1UL) /*!< Disable */

/* Bit 6 : Write '1' to disable interrupt for event TRIGGERED[6] */
#define EGU_INTENCLR_TRIGGERED6_Pos (6UL) /*!< Position of TRIGGERED6 field. */
#define EGU_INTENCLR_TRIGGERED6_Msk (0x1UL << EGU_INTENCLR_TRIGGERED6_Pos) /*!< Bit mask of TRIGGERED6 field. */
#define EGU_INTENCLR_TRIGGERED6_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED6_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED6_Clear (1UL) /*!< Disable */

/* Bit 5 : Write '1' to disable interrupt for event TRIGGERED[5] */
#define EGU_INTENCLR_TRIGGERED5_Pos (5UL) /*!< Position of TRIGGERED5 field. */
#define EGU_INTENCLR_TRIGGERED5_Msk (0x1UL << EGU_INTENCLR_TRIGGERED5_Pos) /*!< Bit mask of TRIGGERED5 field. */
#define EGU_INTENCLR_TRIGGERED5_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED5_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED5_Clear (1UL) /*!< Disable */

/* Bit 4 : Write '1' to disable interrupt for event TRIGGERED[4] */
#define EGU_INTENCLR_TRIGGERED4_Pos (4UL) /*!< Position of TRIGGERED4 field. */
#define EGU_INTENCLR_TRIGGERED4_Msk (0x1UL << EGU_INTENCLR_TRIGGERED4_Pos) /*!< Bit mask of TRIGGERED4 field. */
#define EGU_INTENCLR_TRIGGERED4_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED4_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED4_Clear (1UL) /*!< Disable */

/* Bit 3 : Write '1' to disable interrupt for event TRIGGERED[3] */
#define EGU_INTENCLR_TRIGGERED3_Pos (3UL) /*!< Position of TRIGGERED3 field. */
#define EGU_INTENCLR_TRIGGERED3_Msk (0x1UL << EGU_INTENCLR_TRIGGERED3_Pos) /*!< Bit mask of TRIGGERED3 field. */
#define EGU_INTENCLR_TRIGGERED3_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED3_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED3_Clear (1UL) /*!< Disable */

/* Bit 2 : Write '1' to disable interrupt for event TRIGGERED[2] */
#define EGU_INTENCLR_TRIGGERED2_Pos (2UL) /*!< Position of TRIGGERED2 field. */
#define EGU_INTENCLR_TRIGGERED2_Msk (0x1UL << EGU_INTENCLR_TRIGGERED2_Pos) /*!< Bit mask of TRIGGERED2 field. */
#define EGU_INTENCLR_TRIGGERED2_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED2_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED2_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event TRIGGERED[1] */
#define EGU_INTENCLR_TRIGGERED1_Pos (1UL) /*!< Position of TRIGGERED1 field. */
#define EGU_INTENCLR_TRIGGERED1_Msk (0x1UL << EGU_INTENCLR_TRIGGERED1_Pos) /*!< Bit mask of TRIGGERED1 field. */
#define EGU_INTENCLR_TRIGGERED1_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED1_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED1_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event TRIGGERED[0] */
#define EGU_INTENCLR_TRIGGERED0_Pos (0UL) /*!< Position of TRIGGERED0 field. */
#define EGU_INTENCLR_TRIGGERED0_Msk (0x1UL << EGU_INTENCLR_TRIGGERED0_Pos) /*!< Bit mask of TRIGGERED0 field. */
#define EGU_INTENCLR_TRIGGERED0_Disabled (0UL) /*!< Read: Disabled */
#define EGU_INTENCLR_TRIGGERED0_Enabled (1UL) /*!< Read: Enabled */
#define EGU_INTENCLR_TRIGGERED0_Clear (1UL) /*!< Disable */


/* Peripheral: FICR */
/* Description: Factory Information Configuration Registers */

/* Register: FICR_INFO_CONFIGID */
/* Description: Configuration identifier */

/* Bits 15..0 : Identification number for the HW */
#define FICR_INFO_CONFIGID_HWID_Pos (0UL) /*!< Position of HWID field. */
#define FICR_INFO_CONFIGID_HWID_Msk (0xFFFFUL << FICR_INFO_CONFIGID_HWID_Pos) /*!< Bit mask of HWID field. */

/* Register: FICR_INFO_DEVICEID */
/* Description: Description collection: Device identifier */

/* Bits 31..0 : 64 bit unique device identifier */
#define FICR_INFO_DEVICEID_DEVICEID_Pos (0UL) /*!< Position of DEVICEID field. */
#define FICR_INFO_DEVICEID_DEVICEID_Msk (0xFFFFFFFFUL << FICR_INFO_DEVICEID_DEVICEID_Pos) /*!< Bit mask of DEVICEID field. */

/* Register: FICR_INFO_PART */
/* Description: Part code */

/* Bits 31..0 : Part code */
#define FICR_INFO_PART_PART_Pos (0UL) /*!< Position of PART field. */
#define FICR_INFO_PART_PART_Msk (0xFFFFFFFFUL << FICR_INFO_PART_PART_Pos) /*!< Bit mask of PART field. */
#define FICR_INFO_PART_PART_N5340 (0x5340UL) /*!< nRF5340 */
#define FICR_INFO_PART_PART_Unspecified (0xFFFFFFFFUL) /*!< Unspecified */

/* Register: FICR_INFO_VARIANT */
/* Description: Part Variant, Hardware version and Production configuration */

/* Bits 31..0 : Part Variant, Hardware version and Production configuration, encoded as ASCII */
#define FICR_INFO_VARIANT_VARIANT_Pos (0UL) /*!< Position of VARIANT field. */
#define FICR_INFO_VARIANT_VARIANT_Msk (0xFFFFFFFFUL << FICR_INFO_VARIANT_VARIANT_Pos) /*!< Bit mask of VARIANT field. */
#define FICR_INFO_VARIANT_VARIANT_CLAA (0x434C4141UL) /*!< CLAA */
#define FICR_INFO_VARIANT_VARIANT_QKAA (0x514B4141UL) /*!< QKAA */
#define FICR_INFO_VARIANT_VARIANT_Unspecified (0xFFFFFFFFUL) /*!< Unspecified */

/* Register: FICR_INFO_PACKAGE */
/* Description: Package option */

/* Bits 31..0 : Package option */
#define FICR_INFO_PACKAGE_PACKAGE_Pos (0UL) /*!< Position of PACKAGE field. */
#define FICR_INFO_PACKAGE_PACKAGE_Msk (0xFFFFFFFFUL << FICR_INFO_PACKAGE_PACKAGE_Pos) /*!< Bit mask of PACKAGE field. */
#define FICR_INFO_PACKAGE_PACKAGE_QK (0x2000UL) /*!< QKxx - 94-pin aQFN */
#define FICR_INFO_PACKAGE_PACKAGE_CL (0x2005UL) /*!< CLxx - WLCSP */
#define FICR_INFO_PACKAGE_PACKAGE_Unspecified (0xFFFFFFFFUL) /*!< Unspecified */

/* Register: FICR_INFO_RAM */
/* Description: RAM variant */

/* Bits 31..0 : RAM variant */
#define FICR_INFO_RAM_RAM_Pos (0UL) /*!< Position of RAM field. */
#define FICR_INFO_RAM_RAM_Msk (0xFFFFFFFFUL << FICR_INFO_RAM_RAM_Pos) /*!< Bit mask of RAM field. */
#define FICR_INFO_RAM_RAM_K16 (0x10UL) /*!< 16 kByte RAM */
#define FICR_INFO_RAM_RAM_K32 (0x20UL) /*!< 32 kByte RAM */
#define FICR_INFO_RAM_RAM_K64 (0x40UL) /*!< 64 kByte RAM */
#define FICR_INFO_RAM_RAM_K128 (0x80UL) /*!< 128 kByte RAM */
#define FICR_INFO_RAM_RAM_K256 (0x100UL) /*!< 256 kByte RAM */
#define FICR_INFO_RAM_RAM_K512 (0x200UL) /*!< 512 kByte RAM */
#define FICR_INFO_RAM_RAM_Unspecified (0xFFFFFFFFUL) /*!< Unspecified */

/* Register: FICR_INFO_FLASH */
/* Description: Flash variant */

/* Bits 31..0 : Flash variant */
#define FICR_INFO_FLASH_FLASH_Pos (0UL) /*!< Position of FLASH field. */
#define FICR_INFO_FLASH_FLASH_Msk (0xFFFFFFFFUL << FICR_INFO_FLASH_FLASH_Pos) /*!< Bit mask of FLASH field. */
#define FICR_INFO_FLASH_FLASH_K128 (0x80UL) /*!< 128 kByte FLASH */
#define FICR_INFO_FLASH_FLASH_K256 (0x100UL) /*!< 256 kByte FLASH */
#define FICR_INFO_FLASH_FLASH_K512 (0x200UL) /*!< 512 kByte FLASH */
#define FICR_INFO_FLASH_FLASH_K1024 (0x400UL) /*!< 1 MByte FLASH */
#define FICR_INFO_FLASH_FLASH_K2048 (0x800UL) /*!< 2 MByte FLASH */
#define FICR_INFO_FLASH_FLASH_Unspecified (0xFFFFFFFFUL) /*!< Unspecified */

/* Register: FICR_INFO_CODEPAGESIZE */
/* Description: Code memory page size in bytes */

/* Bits 31..0 : Code memory page size in bytes */
#define FICR_INFO_CODEPAGESIZE_CODEPAGESIZE_Pos (0UL) /*!< Position of CODEPAGESIZE field. */
#define FICR_INFO_CODEPAGESIZE_CODEPAGESIZE_Msk (0xFFFFFFFFUL << FICR_INFO_CODEPAGESIZE_CODEPAGESIZE_Pos) /*!< Bit mask of CODEPAGESIZE field. */
#define FICR_INFO_CODEPAGESIZE_CODEPAGESIZE_K2048 (0x800UL) /*!< 2 kByte */

/* Register: FICR_INFO_CODESIZE */
/* Description: Code memory size */

/* Bits 31..0 : Code memory size in number of pages */
#define FICR_INFO_CODESIZE_CODESIZE_Pos (0UL) /*!< Position of CODESIZE field. */
#define FICR_INFO_CODESIZE_CODESIZE_Msk (0xFFFFFFFFUL << FICR_INFO_CODESIZE_CODESIZE_Pos) /*!< Bit mask of CODESIZE field. */
#define FICR_INFO_CODESIZE_CODESIZE_P128 (128UL) /*!< 128 pages */

/* Register: FICR_INFO_DEVICETYPE */
/* Description: Device type */

/* Bits 31..0 : Device type */
#define FICR_INFO_DEVICETYPE_DEVICETYPE_Pos (0UL) /*!< Position of DEVICETYPE field. */
#define FICR_INFO_DEVICETYPE_DEVICETYPE_Msk (0xFFFFFFFFUL << FICR_INFO_DEVICETYPE_DEVICETYPE_Pos) /*!< Bit mask of DEVICETYPE field. */
#define FICR_INFO_DEVICETYPE_DEVICETYPE_Die (0x0000000UL) /*!< Device is an physical DIE */
#define FICR_INFO_DEVICETYPE_DEVICETYPE_FPGA (0xFFFFFFFFUL) /*!< Device is an FPGA */

/* Register: FICR_ER */
/* Description: Description collection: Encryption Root, word n */

/* Bits 31..0 : Encryption Root, word n */
#define FICR_ER_ER_Pos (0UL) /*!< Position of ER field. */
#define FICR_ER_ER_Msk (0xFFFFFFFFUL << FICR_ER_ER_Pos) /*!< Bit mask of ER field. */

/* Register: FICR_IR */
/* Description: Description collection: Identity Root, word n */

/* Bits 31..0 : Identity Root, word n */
#define FICR_IR_IR_Pos (0UL) /*!< Position of IR field. */
#define FICR_IR_IR_Msk (0xFFFFFFFFUL << FICR_IR_IR_Pos) /*!< Bit mask of IR field. */

/* Register: FICR_DEVICEADDRTYPE */
/* Description: Device address type */

/* Bit 0 : Device address type */
#define FICR_DEVICEADDRTYPE_DEVICEADDRTYPE_Pos (0UL) /*!< Position of DEVICEADDRTYPE field. */
#define FICR_DEVICEADDRTYPE_DEVICEADDRTYPE_Msk (0x1UL << FICR_DEVICEADDRTYPE_DEVICEADDRTYPE_Pos) /*!< Bit mask of DEVICEADDRTYPE field. */
#define FICR_DEVICEADDRTYPE_DEVICEADDRTYPE_Public (0UL) /*!< Public address */
#define FICR_DEVICEADDRTYPE_DEVICEADDRTYPE_Random (1UL) /*!< Random address */

/* Register: FICR_DEVICEADDR */
/* Description: Description collection: Device address n */

/* Bits 31..0 : 48 bit device address */
#define FICR_DEVICEADDR_DEVICEADDR_Pos (0UL) /*!< Position of DEVICEADDR field. */
#define FICR_DEVICEADDR_DEVICEADDR_Msk (0xFFFFFFFFUL << FICR_DEVICEADDR_DEVICEADDR_Pos) /*!< Bit mask of DEVICEADDR field. */

/* Register: FICR_TRIMCNF_ADDR */
/* Description: Description cluster: Address */

/* Bits 31..0 : Address */
#define FICR_TRIMCNF_ADDR_Address_Pos (0UL) /*!< Position of Address field. */
#define FICR_TRIMCNF_ADDR_Address_Msk (0xFFFFFFFFUL << FICR_TRIMCNF_ADDR_Address_Pos) /*!< Bit mask of Address field. */

/* Register: FICR_TRIMCNF_DATA */
/* Description: Description cluster: Data */

/* Bits 31..0 : Data */
#define FICR_TRIMCNF_DATA_Data_Pos (0UL) /*!< Position of Data field. */
#define FICR_TRIMCNF_DATA_Data_Msk (0xFFFFFFFFUL << FICR_TRIMCNF_DATA_Data_Pos) /*!< Bit mask of Data field. */


/* Peripheral: GPIOTE */
/* Description: GPIO Tasks and Events */

/* Register: GPIOTE_TASKS_OUT */
/* Description: Description collection: Task for writing to pin specified in CONFIG[n].PSEL. Action on pin is configured in CONFIG[n].POLARITY. */

/* Bit 0 : Task for writing to pin specified in CONFIG[n].PSEL. Action on pin is configured in CONFIG[n].POLARITY. */
#define GPIOTE_TASKS_OUT_TASKS_OUT_Pos (0UL) /*!< Position of TASKS_OUT field. */
#define GPIOTE_TASKS_OUT_TASKS_OUT_Msk (0x1UL << GPIOTE_TASKS_OUT_TASKS_OUT_Pos) /*!< Bit mask of TASKS_OUT field. */
#define GPIOTE_TASKS_OUT_TASKS_OUT_Trigger (1UL) /*!< Trigger task */

/* Register: GPIOTE_TASKS_SET */
/* Description: Description collection: Task for writing to pin specified in CONFIG[n].PSEL. Action on pin is to set it high. */

/* Bit 0 : Task for writing to pin specified in CONFIG[n].PSEL. Action on pin is to set it high. */
#define GPIOTE_TASKS_SET_TASKS_SET_Pos (0UL) /*!< Position of TASKS_SET field. */
#define GPIOTE_TASKS_SET_TASKS_SET_Msk (0x1UL << GPIOTE_TASKS_SET_TASKS_SET_Pos) /*!< Bit mask of TASKS_SET field. */
#define GPIOTE_TASKS_SET_TASKS_SET_Trigger (1UL) /*!< Trigger task */

/* Register: GPIOTE_TASKS_CLR */
/* Description: Description collection: Task for writing to pin specified in CONFIG[n].PSEL. Action on pin is to set it low. */

/* Bit 0 : Task for writing to pin specified in CONFIG[n].PSEL. Action on pin is to set it low. */
#define GPIOTE_TASKS_CLR_TASKS_CLR_Pos (0UL) /*!< Position of TASKS_CLR field. */
#define GPIOTE_TASKS_CLR_TASKS_CLR_Msk (0x1UL << GPIOTE_TASKS_CLR_TASKS_CLR_Pos) /*!< Bit mask of TASKS_CLR field. */
#define GPIOTE_TASKS_CLR_TASKS_CLR_Trigger (1UL) /*!< Trigger task */

/* Register: GPIOTE_SUBSCRIBE_OUT */
/* Description: Description collection: Subscribe configuration for task OUT[n] */

/* Bit 31 :   */
#define GPIOTE_SUBSCRIBE_OUT_EN_Pos (31UL) /*!< Position of EN field. */
#define GPIOTE_SUBSCRIBE_OUT_EN_Msk (0x1UL << GPIOTE_SUBSCRIBE_OUT_EN_Pos) /*!< Bit mask of EN field. */
#define GPIOTE_SUBSCRIBE_OUT_EN_Disabled (0UL) /*!< Disable subscription */
#define GPIOTE_SUBSCRIBE_OUT_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task OUT[n] will subscribe to */
#define GPIOTE_SUBSCRIBE_OUT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define GPIOTE_SUBSCRIBE_OUT_CHIDX_Msk (0xFFUL << GPIOTE_SUBSCRIBE_OUT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: GPIOTE_SUBSCRIBE_SET */
/* Description: Description collection: Subscribe configuration for task SET[n] */

/* Bit 31 :   */
#define GPIOTE_SUBSCRIBE_SET_EN_Pos (31UL) /*!< Position of EN field. */
#define GPIOTE_SUBSCRIBE_SET_EN_Msk (0x1UL << GPIOTE_SUBSCRIBE_SET_EN_Pos) /*!< Bit mask of EN field. */
#define GPIOTE_SUBSCRIBE_SET_EN_Disabled (0UL) /*!< Disable subscription */
#define GPIOTE_SUBSCRIBE_SET_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task SET[n] will subscribe to */
#define GPIOTE_SUBSCRIBE_SET_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define GPIOTE_SUBSCRIBE_SET_CHIDX_Msk (0xFFUL << GPIOTE_SUBSCRIBE_SET_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: GPIOTE_SUBSCRIBE_CLR */
/* Description: Description collection: Subscribe configuration for task CLR[n] */

/* Bit 31 :   */
#define GPIOTE_SUBSCRIBE_CLR_EN_Pos (31UL) /*!< Position of EN field. */
#define GPIOTE_SUBSCRIBE_CLR_EN_Msk (0x1UL << GPIOTE_SUBSCRIBE_CLR_EN_Pos) /*!< Bit mask of EN field. */
#define GPIOTE_SUBSCRIBE_CLR_EN_Disabled (0UL) /*!< Disable subscription */
#define GPIOTE_SUBSCRIBE_CLR_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CLR[n] will subscribe to */
#define GPIOTE_SUBSCRIBE_CLR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define GPIOTE_SUBSCRIBE_CLR_CHIDX_Msk (0xFFUL << GPIOTE_SUBSCRIBE_CLR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: GPIOTE_EVENTS_IN */
/* Description: Description collection: Event generated from pin specified in CONFIG[n].PSEL */

/* Bit 0 : Event generated from pin specified in CONFIG[n].PSEL */
#define GPIOTE_EVENTS_IN_EVENTS_IN_Pos (0UL) /*!< Position of EVENTS_IN field. */
#define GPIOTE_EVENTS_IN_EVENTS_IN_Msk (0x1UL << GPIOTE_EVENTS_IN_EVENTS_IN_Pos) /*!< Bit mask of EVENTS_IN field. */
#define GPIOTE_EVENTS_IN_EVENTS_IN_NotGenerated (0UL) /*!< Event not generated */
#define GPIOTE_EVENTS_IN_EVENTS_IN_Generated (1UL) /*!< Event generated */

/* Register: GPIOTE_EVENTS_PORT */
/* Description: Event generated from multiple input GPIO pins with SENSE mechanism enabled */

/* Bit 0 : Event generated from multiple input GPIO pins with SENSE mechanism enabled */
#define GPIOTE_EVENTS_PORT_EVENTS_PORT_Pos (0UL) /*!< Position of EVENTS_PORT field. */
#define GPIOTE_EVENTS_PORT_EVENTS_PORT_Msk (0x1UL << GPIOTE_EVENTS_PORT_EVENTS_PORT_Pos) /*!< Bit mask of EVENTS_PORT field. */
#define GPIOTE_EVENTS_PORT_EVENTS_PORT_NotGenerated (0UL) /*!< Event not generated */
#define GPIOTE_EVENTS_PORT_EVENTS_PORT_Generated (1UL) /*!< Event generated */

/* Register: GPIOTE_PUBLISH_IN */
/* Description: Description collection: Publish configuration for event IN[n] */

/* Bit 31 :   */
#define GPIOTE_PUBLISH_IN_EN_Pos (31UL) /*!< Position of EN field. */
#define GPIOTE_PUBLISH_IN_EN_Msk (0x1UL << GPIOTE_PUBLISH_IN_EN_Pos) /*!< Bit mask of EN field. */
#define GPIOTE_PUBLISH_IN_EN_Disabled (0UL) /*!< Disable publishing */
#define GPIOTE_PUBLISH_IN_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event IN[n] will publish to. */
#define GPIOTE_PUBLISH_IN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define GPIOTE_PUBLISH_IN_CHIDX_Msk (0xFFUL << GPIOTE_PUBLISH_IN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: GPIOTE_PUBLISH_PORT */
/* Description: Publish configuration for event PORT */

/* Bit 31 :   */
#define GPIOTE_PUBLISH_PORT_EN_Pos (31UL) /*!< Position of EN field. */
#define GPIOTE_PUBLISH_PORT_EN_Msk (0x1UL << GPIOTE_PUBLISH_PORT_EN_Pos) /*!< Bit mask of EN field. */
#define GPIOTE_PUBLISH_PORT_EN_Disabled (0UL) /*!< Disable publishing */
#define GPIOTE_PUBLISH_PORT_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event PORT will publish to. */
#define GPIOTE_PUBLISH_PORT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define GPIOTE_PUBLISH_PORT_CHIDX_Msk (0xFFUL << GPIOTE_PUBLISH_PORT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: GPIOTE_INTENSET */
/* Description: Enable interrupt */

/* Bit 31 : Write '1' to enable interrupt for event PORT */
#define GPIOTE_INTENSET_PORT_Pos (31UL) /*!< Position of PORT field. */
#define GPIOTE_INTENSET_PORT_Msk (0x1UL << GPIOTE_INTENSET_PORT_Pos) /*!< Bit mask of PORT field. */
#define GPIOTE_INTENSET_PORT_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_PORT_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_PORT_Set (1UL) /*!< Enable */

/* Bit 7 : Write '1' to enable interrupt for event IN[7] */
#define GPIOTE_INTENSET_IN7_Pos (7UL) /*!< Position of IN7 field. */
#define GPIOTE_INTENSET_IN7_Msk (0x1UL << GPIOTE_INTENSET_IN7_Pos) /*!< Bit mask of IN7 field. */
#define GPIOTE_INTENSET_IN7_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN7_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN7_Set (1UL) /*!< Enable */

/* Bit 6 : Write '1' to enable interrupt for event IN[6] */
#define GPIOTE_INTENSET_IN6_Pos (6UL) /*!< Position of IN6 field. */
#define GPIOTE_INTENSET_IN6_Msk (0x1UL << GPIOTE_INTENSET_IN6_Pos) /*!< Bit mask of IN6 field. */
#define GPIOTE_INTENSET_IN6_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN6_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN6_Set (1UL) /*!< Enable */

/* Bit 5 : Write '1' to enable interrupt for event IN[5] */
#define GPIOTE_INTENSET_IN5_Pos (5UL) /*!< Position of IN5 field. */
#define GPIOTE_INTENSET_IN5_Msk (0x1UL << GPIOTE_INTENSET_IN5_Pos) /*!< Bit mask of IN5 field. */
#define GPIOTE_INTENSET_IN5_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN5_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN5_Set (1UL) /*!< Enable */

/* Bit 4 : Write '1' to enable interrupt for event IN[4] */
#define GPIOTE_INTENSET_IN4_Pos (4UL) /*!< Position of IN4 field. */
#define GPIOTE_INTENSET_IN4_Msk (0x1UL << GPIOTE_INTENSET_IN4_Pos) /*!< Bit mask of IN4 field. */
#define GPIOTE_INTENSET_IN4_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN4_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN4_Set (1UL) /*!< Enable */

/* Bit 3 : Write '1' to enable interrupt for event IN[3] */
#define GPIOTE_INTENSET_IN3_Pos (3UL) /*!< Position of IN3 field. */
#define GPIOTE_INTENSET_IN3_Msk (0x1UL << GPIOTE_INTENSET_IN3_Pos) /*!< Bit mask of IN3 field. */
#define GPIOTE_INTENSET_IN3_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN3_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN3_Set (1UL) /*!< Enable */

/* Bit 2 : Write '1' to enable interrupt for event IN[2] */
#define GPIOTE_INTENSET_IN2_Pos (2UL) /*!< Position of IN2 field. */
#define GPIOTE_INTENSET_IN2_Msk (0x1UL << GPIOTE_INTENSET_IN2_Pos) /*!< Bit mask of IN2 field. */
#define GPIOTE_INTENSET_IN2_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN2_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN2_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event IN[1] */
#define GPIOTE_INTENSET_IN1_Pos (1UL) /*!< Position of IN1 field. */
#define GPIOTE_INTENSET_IN1_Msk (0x1UL << GPIOTE_INTENSET_IN1_Pos) /*!< Bit mask of IN1 field. */
#define GPIOTE_INTENSET_IN1_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN1_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN1_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event IN[0] */
#define GPIOTE_INTENSET_IN0_Pos (0UL) /*!< Position of IN0 field. */
#define GPIOTE_INTENSET_IN0_Msk (0x1UL << GPIOTE_INTENSET_IN0_Pos) /*!< Bit mask of IN0 field. */
#define GPIOTE_INTENSET_IN0_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENSET_IN0_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENSET_IN0_Set (1UL) /*!< Enable */

/* Register: GPIOTE_INTENCLR */
/* Description: Disable interrupt */

/* Bit 31 : Write '1' to disable interrupt for event PORT */
#define GPIOTE_INTENCLR_PORT_Pos (31UL) /*!< Position of PORT field. */
#define GPIOTE_INTENCLR_PORT_Msk (0x1UL << GPIOTE_INTENCLR_PORT_Pos) /*!< Bit mask of PORT field. */
#define GPIOTE_INTENCLR_PORT_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_PORT_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_PORT_Clear (1UL) /*!< Disable */

/* Bit 7 : Write '1' to disable interrupt for event IN[7] */
#define GPIOTE_INTENCLR_IN7_Pos (7UL) /*!< Position of IN7 field. */
#define GPIOTE_INTENCLR_IN7_Msk (0x1UL << GPIOTE_INTENCLR_IN7_Pos) /*!< Bit mask of IN7 field. */
#define GPIOTE_INTENCLR_IN7_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN7_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN7_Clear (1UL) /*!< Disable */

/* Bit 6 : Write '1' to disable interrupt for event IN[6] */
#define GPIOTE_INTENCLR_IN6_Pos (6UL) /*!< Position of IN6 field. */
#define GPIOTE_INTENCLR_IN6_Msk (0x1UL << GPIOTE_INTENCLR_IN6_Pos) /*!< Bit mask of IN6 field. */
#define GPIOTE_INTENCLR_IN6_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN6_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN6_Clear (1UL) /*!< Disable */

/* Bit 5 : Write '1' to disable interrupt for event IN[5] */
#define GPIOTE_INTENCLR_IN5_Pos (5UL) /*!< Position of IN5 field. */
#define GPIOTE_INTENCLR_IN5_Msk (0x1UL << GPIOTE_INTENCLR_IN5_Pos) /*!< Bit mask of IN5 field. */
#define GPIOTE_INTENCLR_IN5_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN5_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN5_Clear (1UL) /*!< Disable */

/* Bit 4 : Write '1' to disable interrupt for event IN[4] */
#define GPIOTE_INTENCLR_IN4_Pos (4UL) /*!< Position of IN4 field. */
#define GPIOTE_INTENCLR_IN4_Msk (0x1UL << GPIOTE_INTENCLR_IN4_Pos) /*!< Bit mask of IN4 field. */
#define GPIOTE_INTENCLR_IN4_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN4_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN4_Clear (1UL) /*!< Disable */

/* Bit 3 : Write '1' to disable interrupt for event IN[3] */
#define GPIOTE_INTENCLR_IN3_Pos (3UL) /*!< Position of IN3 field. */
#define GPIOTE_INTENCLR_IN3_Msk (0x1UL << GPIOTE_INTENCLR_IN3_Pos) /*!< Bit mask of IN3 field. */
#define GPIOTE_INTENCLR_IN3_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN3_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN3_Clear (1UL) /*!< Disable */

/* Bit 2 : Write '1' to disable interrupt for event IN[2] */
#define GPIOTE_INTENCLR_IN2_Pos (2UL) /*!< Position of IN2 field. */
#define GPIOTE_INTENCLR_IN2_Msk (0x1UL << GPIOTE_INTENCLR_IN2_Pos) /*!< Bit mask of IN2 field. */
#define GPIOTE_INTENCLR_IN2_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN2_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN2_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event IN[1] */
#define GPIOTE_INTENCLR_IN1_Pos (1UL) /*!< Position of IN1 field. */
#define GPIOTE_INTENCLR_IN1_Msk (0x1UL << GPIOTE_INTENCLR_IN1_Pos) /*!< Bit mask of IN1 field. */
#define GPIOTE_INTENCLR_IN1_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN1_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN1_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event IN[0] */
#define GPIOTE_INTENCLR_IN0_Pos (0UL) /*!< Position of IN0 field. */
#define GPIOTE_INTENCLR_IN0_Msk (0x1UL << GPIOTE_INTENCLR_IN0_Pos) /*!< Bit mask of IN0 field. */
#define GPIOTE_INTENCLR_IN0_Disabled (0UL) /*!< Read: Disabled */
#define GPIOTE_INTENCLR_IN0_Enabled (1UL) /*!< Read: Enabled */
#define GPIOTE_INTENCLR_IN0_Clear (1UL) /*!< Disable */

/* Register: GPIOTE_LATENCY */
/* Description: Latency selection for Event mode (MODE=Event) with rising or falling edge detection on the pin. */

/* Bit 0 : Latency setting */
#define GPIOTE_LATENCY_LATENCY_Pos (0UL) /*!< Position of LATENCY field. */
#define GPIOTE_LATENCY_LATENCY_Msk (0x1UL << GPIOTE_LATENCY_LATENCY_Pos) /*!< Bit mask of LATENCY field. */
#define GPIOTE_LATENCY_LATENCY_LowPower (0UL) /*!< Low power setting, for signals with minimum hold time tGPIOTE,HOLD,LP; refer to Electrical specification section */
#define GPIOTE_LATENCY_LATENCY_LowLatency (1UL) /*!< Low latency setting, for signals with minimum hold time tGPIOTE,HOLD,LL; refer to Electrical specification section */

/* Register: GPIOTE_CONFIG */
/* Description: Description collection: Configuration for OUT[n], SET[n], and CLR[n] tasks and IN[n] event */

/* Bit 20 : When in task mode: Initial value of the output when the GPIOTE channel is configured. When in event mode: No effect. */
#define GPIOTE_CONFIG_OUTINIT_Pos (20UL) /*!< Position of OUTINIT field. */
#define GPIOTE_CONFIG_OUTINIT_Msk (0x1UL << GPIOTE_CONFIG_OUTINIT_Pos) /*!< Bit mask of OUTINIT field. */
#define GPIOTE_CONFIG_OUTINIT_Low (0UL) /*!< Task mode: Initial value of pin before task triggering is low */
#define GPIOTE_CONFIG_OUTINIT_High (1UL) /*!< Task mode: Initial value of pin before task triggering is high */

/* Bits 17..16 : When In task mode: Operation to be performed on output when OUT[n] task is triggered. When In event mode: Operation on input that shall trigger IN[n] event. */
#define GPIOTE_CONFIG_POLARITY_Pos (16UL) /*!< Position of POLARITY field. */
#define GPIOTE_CONFIG_POLARITY_Msk (0x3UL << GPIOTE_CONFIG_POLARITY_Pos) /*!< Bit mask of POLARITY field. */
#define GPIOTE_CONFIG_POLARITY_None (0UL) /*!< Task mode: No effect on pin from OUT[n] task. Event mode: no IN[n] event generated on pin activity. */
#define GPIOTE_CONFIG_POLARITY_LoToHi (1UL) /*!< Task mode: Set pin from OUT[n] task. Event mode: Generate IN[n] event when rising edge on pin. */
#define GPIOTE_CONFIG_POLARITY_HiToLo (2UL) /*!< Task mode: Clear pin from OUT[n] task. Event mode: Generate IN[n] event when falling edge on pin. */
#define GPIOTE_CONFIG_POLARITY_Toggle (3UL) /*!< Task mode: Toggle pin from OUT[n]. Event mode: Generate IN[n] when any change on pin. */

/* Bit 13 : Port number */
#define GPIOTE_CONFIG_PORT_Pos (13UL) /*!< Position of PORT field. */
#define GPIOTE_CONFIG_PORT_Msk (0x1UL << GPIOTE_CONFIG_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 12..8 : GPIO number associated with SET[n], CLR[n], and OUT[n] tasks and IN[n] event */
#define GPIOTE_CONFIG_PSEL_Pos (8UL) /*!< Position of PSEL field. */
#define GPIOTE_CONFIG_PSEL_Msk (0x1FUL << GPIOTE_CONFIG_PSEL_Pos) /*!< Bit mask of PSEL field. */

/* Bits 1..0 : Mode */
#define GPIOTE_CONFIG_MODE_Pos (0UL) /*!< Position of MODE field. */
#define GPIOTE_CONFIG_MODE_Msk (0x3UL << GPIOTE_CONFIG_MODE_Pos) /*!< Bit mask of MODE field. */
#define GPIOTE_CONFIG_MODE_Disabled (0UL) /*!< Disabled. Pin specified by PSEL will not be acquired by the GPIOTE module. */
#define GPIOTE_CONFIG_MODE_Event (1UL) /*!< Event mode */
#define GPIOTE_CONFIG_MODE_Task (3UL) /*!< Task mode */


/* Peripheral: IPC */
/* Description: Interprocessor communication */

/* Register: IPC_TASKS_SEND */
/* Description: Description collection: Trigger events on IPC channel enabled in SEND_CNF[n] */

/* Bit 0 : Trigger events on IPC channel enabled in SEND_CNF[n] */
#define IPC_TASKS_SEND_TASKS_SEND_Pos (0UL) /*!< Position of TASKS_SEND field. */
#define IPC_TASKS_SEND_TASKS_SEND_Msk (0x1UL << IPC_TASKS_SEND_TASKS_SEND_Pos) /*!< Bit mask of TASKS_SEND field. */
#define IPC_TASKS_SEND_TASKS_SEND_Trigger (1UL) /*!< Trigger task */

/* Register: IPC_SUBSCRIBE_SEND */
/* Description: Description collection: Subscribe configuration for task SEND[n] */

/* Bit 31 :   */
#define IPC_SUBSCRIBE_SEND_EN_Pos (31UL) /*!< Position of EN field. */
#define IPC_SUBSCRIBE_SEND_EN_Msk (0x1UL << IPC_SUBSCRIBE_SEND_EN_Pos) /*!< Bit mask of EN field. */
#define IPC_SUBSCRIBE_SEND_EN_Disabled (0UL) /*!< Disable subscription */
#define IPC_SUBSCRIBE_SEND_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task SEND[n] will subscribe to */
#define IPC_SUBSCRIBE_SEND_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define IPC_SUBSCRIBE_SEND_CHIDX_Msk (0xFFUL << IPC_SUBSCRIBE_SEND_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: IPC_EVENTS_RECEIVE */
/* Description: Description collection: Event received on one or more of the enabled IPC channels in RECEIVE_CNF[n] */

/* Bit 0 : Event received on one or more of the enabled IPC channels in RECEIVE_CNF[n] */
#define IPC_EVENTS_RECEIVE_EVENTS_RECEIVE_Pos (0UL) /*!< Position of EVENTS_RECEIVE field. */
#define IPC_EVENTS_RECEIVE_EVENTS_RECEIVE_Msk (0x1UL << IPC_EVENTS_RECEIVE_EVENTS_RECEIVE_Pos) /*!< Bit mask of EVENTS_RECEIVE field. */
#define IPC_EVENTS_RECEIVE_EVENTS_RECEIVE_NotGenerated (0UL) /*!< Event not generated */
#define IPC_EVENTS_RECEIVE_EVENTS_RECEIVE_Generated (1UL) /*!< Event generated */

/* Register: IPC_PUBLISH_RECEIVE */
/* Description: Description collection: Publish configuration for event RECEIVE[n] */

/* Bit 31 :   */
#define IPC_PUBLISH_RECEIVE_EN_Pos (31UL) /*!< Position of EN field. */
#define IPC_PUBLISH_RECEIVE_EN_Msk (0x1UL << IPC_PUBLISH_RECEIVE_EN_Pos) /*!< Bit mask of EN field. */
#define IPC_PUBLISH_RECEIVE_EN_Disabled (0UL) /*!< Disable publishing */
#define IPC_PUBLISH_RECEIVE_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RECEIVE[n] will publish to. */
#define IPC_PUBLISH_RECEIVE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define IPC_PUBLISH_RECEIVE_CHIDX_Msk (0xFFUL << IPC_PUBLISH_RECEIVE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: IPC_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 15 : Enable or disable interrupt for event RECEIVE[15] */
#define IPC_INTEN_RECEIVE15_Pos (15UL) /*!< Position of RECEIVE15 field. */
#define IPC_INTEN_RECEIVE15_Msk (0x1UL << IPC_INTEN_RECEIVE15_Pos) /*!< Bit mask of RECEIVE15 field. */
#define IPC_INTEN_RECEIVE15_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE15_Enabled (1UL) /*!< Enable */

/* Bit 14 : Enable or disable interrupt for event RECEIVE[14] */
#define IPC_INTEN_RECEIVE14_Pos (14UL) /*!< Position of RECEIVE14 field. */
#define IPC_INTEN_RECEIVE14_Msk (0x1UL << IPC_INTEN_RECEIVE14_Pos) /*!< Bit mask of RECEIVE14 field. */
#define IPC_INTEN_RECEIVE14_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE14_Enabled (1UL) /*!< Enable */

/* Bit 13 : Enable or disable interrupt for event RECEIVE[13] */
#define IPC_INTEN_RECEIVE13_Pos (13UL) /*!< Position of RECEIVE13 field. */
#define IPC_INTEN_RECEIVE13_Msk (0x1UL << IPC_INTEN_RECEIVE13_Pos) /*!< Bit mask of RECEIVE13 field. */
#define IPC_INTEN_RECEIVE13_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE13_Enabled (1UL) /*!< Enable */

/* Bit 12 : Enable or disable interrupt for event RECEIVE[12] */
#define IPC_INTEN_RECEIVE12_Pos (12UL) /*!< Position of RECEIVE12 field. */
#define IPC_INTEN_RECEIVE12_Msk (0x1UL << IPC_INTEN_RECEIVE12_Pos) /*!< Bit mask of RECEIVE12 field. */
#define IPC_INTEN_RECEIVE12_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE12_Enabled (1UL) /*!< Enable */

/* Bit 11 : Enable or disable interrupt for event RECEIVE[11] */
#define IPC_INTEN_RECEIVE11_Pos (11UL) /*!< Position of RECEIVE11 field. */
#define IPC_INTEN_RECEIVE11_Msk (0x1UL << IPC_INTEN_RECEIVE11_Pos) /*!< Bit mask of RECEIVE11 field. */
#define IPC_INTEN_RECEIVE11_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE11_Enabled (1UL) /*!< Enable */

/* Bit 10 : Enable or disable interrupt for event RECEIVE[10] */
#define IPC_INTEN_RECEIVE10_Pos (10UL) /*!< Position of RECEIVE10 field. */
#define IPC_INTEN_RECEIVE10_Msk (0x1UL << IPC_INTEN_RECEIVE10_Pos) /*!< Bit mask of RECEIVE10 field. */
#define IPC_INTEN_RECEIVE10_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE10_Enabled (1UL) /*!< Enable */

/* Bit 9 : Enable or disable interrupt for event RECEIVE[9] */
#define IPC_INTEN_RECEIVE9_Pos (9UL) /*!< Position of RECEIVE9 field. */
#define IPC_INTEN_RECEIVE9_Msk (0x1UL << IPC_INTEN_RECEIVE9_Pos) /*!< Bit mask of RECEIVE9 field. */
#define IPC_INTEN_RECEIVE9_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE9_Enabled (1UL) /*!< Enable */

/* Bit 8 : Enable or disable interrupt for event RECEIVE[8] */
#define IPC_INTEN_RECEIVE8_Pos (8UL) /*!< Position of RECEIVE8 field. */
#define IPC_INTEN_RECEIVE8_Msk (0x1UL << IPC_INTEN_RECEIVE8_Pos) /*!< Bit mask of RECEIVE8 field. */
#define IPC_INTEN_RECEIVE8_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE8_Enabled (1UL) /*!< Enable */

/* Bit 7 : Enable or disable interrupt for event RECEIVE[7] */
#define IPC_INTEN_RECEIVE7_Pos (7UL) /*!< Position of RECEIVE7 field. */
#define IPC_INTEN_RECEIVE7_Msk (0x1UL << IPC_INTEN_RECEIVE7_Pos) /*!< Bit mask of RECEIVE7 field. */
#define IPC_INTEN_RECEIVE7_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE7_Enabled (1UL) /*!< Enable */

/* Bit 6 : Enable or disable interrupt for event RECEIVE[6] */
#define IPC_INTEN_RECEIVE6_Pos (6UL) /*!< Position of RECEIVE6 field. */
#define IPC_INTEN_RECEIVE6_Msk (0x1UL << IPC_INTEN_RECEIVE6_Pos) /*!< Bit mask of RECEIVE6 field. */
#define IPC_INTEN_RECEIVE6_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE6_Enabled (1UL) /*!< Enable */

/* Bit 5 : Enable or disable interrupt for event RECEIVE[5] */
#define IPC_INTEN_RECEIVE5_Pos (5UL) /*!< Position of RECEIVE5 field. */
#define IPC_INTEN_RECEIVE5_Msk (0x1UL << IPC_INTEN_RECEIVE5_Pos) /*!< Bit mask of RECEIVE5 field. */
#define IPC_INTEN_RECEIVE5_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE5_Enabled (1UL) /*!< Enable */

/* Bit 4 : Enable or disable interrupt for event RECEIVE[4] */
#define IPC_INTEN_RECEIVE4_Pos (4UL) /*!< Position of RECEIVE4 field. */
#define IPC_INTEN_RECEIVE4_Msk (0x1UL << IPC_INTEN_RECEIVE4_Pos) /*!< Bit mask of RECEIVE4 field. */
#define IPC_INTEN_RECEIVE4_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE4_Enabled (1UL) /*!< Enable */

/* Bit 3 : Enable or disable interrupt for event RECEIVE[3] */
#define IPC_INTEN_RECEIVE3_Pos (3UL) /*!< Position of RECEIVE3 field. */
#define IPC_INTEN_RECEIVE3_Msk (0x1UL << IPC_INTEN_RECEIVE3_Pos) /*!< Bit mask of RECEIVE3 field. */
#define IPC_INTEN_RECEIVE3_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE3_Enabled (1UL) /*!< Enable */

/* Bit 2 : Enable or disable interrupt for event RECEIVE[2] */
#define IPC_INTEN_RECEIVE2_Pos (2UL) /*!< Position of RECEIVE2 field. */
#define IPC_INTEN_RECEIVE2_Msk (0x1UL << IPC_INTEN_RECEIVE2_Pos) /*!< Bit mask of RECEIVE2 field. */
#define IPC_INTEN_RECEIVE2_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE2_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable interrupt for event RECEIVE[1] */
#define IPC_INTEN_RECEIVE1_Pos (1UL) /*!< Position of RECEIVE1 field. */
#define IPC_INTEN_RECEIVE1_Msk (0x1UL << IPC_INTEN_RECEIVE1_Pos) /*!< Bit mask of RECEIVE1 field. */
#define IPC_INTEN_RECEIVE1_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE1_Enabled (1UL) /*!< Enable */

/* Bit 0 : Enable or disable interrupt for event RECEIVE[0] */
#define IPC_INTEN_RECEIVE0_Pos (0UL) /*!< Position of RECEIVE0 field. */
#define IPC_INTEN_RECEIVE0_Msk (0x1UL << IPC_INTEN_RECEIVE0_Pos) /*!< Bit mask of RECEIVE0 field. */
#define IPC_INTEN_RECEIVE0_Disabled (0UL) /*!< Disable */
#define IPC_INTEN_RECEIVE0_Enabled (1UL) /*!< Enable */

/* Register: IPC_INTENSET */
/* Description: Enable interrupt */

/* Bit 15 : Write '1' to enable interrupt for event RECEIVE[15] */
#define IPC_INTENSET_RECEIVE15_Pos (15UL) /*!< Position of RECEIVE15 field. */
#define IPC_INTENSET_RECEIVE15_Msk (0x1UL << IPC_INTENSET_RECEIVE15_Pos) /*!< Bit mask of RECEIVE15 field. */
#define IPC_INTENSET_RECEIVE15_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE15_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE15_Set (1UL) /*!< Enable */

/* Bit 14 : Write '1' to enable interrupt for event RECEIVE[14] */
#define IPC_INTENSET_RECEIVE14_Pos (14UL) /*!< Position of RECEIVE14 field. */
#define IPC_INTENSET_RECEIVE14_Msk (0x1UL << IPC_INTENSET_RECEIVE14_Pos) /*!< Bit mask of RECEIVE14 field. */
#define IPC_INTENSET_RECEIVE14_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE14_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE14_Set (1UL) /*!< Enable */

/* Bit 13 : Write '1' to enable interrupt for event RECEIVE[13] */
#define IPC_INTENSET_RECEIVE13_Pos (13UL) /*!< Position of RECEIVE13 field. */
#define IPC_INTENSET_RECEIVE13_Msk (0x1UL << IPC_INTENSET_RECEIVE13_Pos) /*!< Bit mask of RECEIVE13 field. */
#define IPC_INTENSET_RECEIVE13_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE13_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE13_Set (1UL) /*!< Enable */

/* Bit 12 : Write '1' to enable interrupt for event RECEIVE[12] */
#define IPC_INTENSET_RECEIVE12_Pos (12UL) /*!< Position of RECEIVE12 field. */
#define IPC_INTENSET_RECEIVE12_Msk (0x1UL << IPC_INTENSET_RECEIVE12_Pos) /*!< Bit mask of RECEIVE12 field. */
#define IPC_INTENSET_RECEIVE12_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE12_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE12_Set (1UL) /*!< Enable */

/* Bit 11 : Write '1' to enable interrupt for event RECEIVE[11] */
#define IPC_INTENSET_RECEIVE11_Pos (11UL) /*!< Position of RECEIVE11 field. */
#define IPC_INTENSET_RECEIVE11_Msk (0x1UL << IPC_INTENSET_RECEIVE11_Pos) /*!< Bit mask of RECEIVE11 field. */
#define IPC_INTENSET_RECEIVE11_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE11_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE11_Set (1UL) /*!< Enable */

/* Bit 10 : Write '1' to enable interrupt for event RECEIVE[10] */
#define IPC_INTENSET_RECEIVE10_Pos (10UL) /*!< Position of RECEIVE10 field. */
#define IPC_INTENSET_RECEIVE10_Msk (0x1UL << IPC_INTENSET_RECEIVE10_Pos) /*!< Bit mask of RECEIVE10 field. */
#define IPC_INTENSET_RECEIVE10_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE10_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE10_Set (1UL) /*!< Enable */

/* Bit 9 : Write '1' to enable interrupt for event RECEIVE[9] */
#define IPC_INTENSET_RECEIVE9_Pos (9UL) /*!< Position of RECEIVE9 field. */
#define IPC_INTENSET_RECEIVE9_Msk (0x1UL << IPC_INTENSET_RECEIVE9_Pos) /*!< Bit mask of RECEIVE9 field. */
#define IPC_INTENSET_RECEIVE9_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE9_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE9_Set (1UL) /*!< Enable */

/* Bit 8 : Write '1' to enable interrupt for event RECEIVE[8] */
#define IPC_INTENSET_RECEIVE8_Pos (8UL) /*!< Position of RECEIVE8 field. */
#define IPC_INTENSET_RECEIVE8_Msk (0x1UL << IPC_INTENSET_RECEIVE8_Pos) /*!< Bit mask of RECEIVE8 field. */
#define IPC_INTENSET_RECEIVE8_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE8_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE8_Set (1UL) /*!< Enable */

/* Bit 7 : Write '1' to enable interrupt for event RECEIVE[7] */
#define IPC_INTENSET_RECEIVE7_Pos (7UL) /*!< Position of RECEIVE7 field. */
#define IPC_INTENSET_RECEIVE7_Msk (0x1UL << IPC_INTENSET_RECEIVE7_Pos) /*!< Bit mask of RECEIVE7 field. */
#define IPC_INTENSET_RECEIVE7_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE7_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE7_Set (1UL) /*!< Enable */

/* Bit 6 : Write '1' to enable interrupt for event RECEIVE[6] */
#define IPC_INTENSET_RECEIVE6_Pos (6UL) /*!< Position of RECEIVE6 field. */
#define IPC_INTENSET_RECEIVE6_Msk (0x1UL << IPC_INTENSET_RECEIVE6_Pos) /*!< Bit mask of RECEIVE6 field. */
#define IPC_INTENSET_RECEIVE6_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE6_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE6_Set (1UL) /*!< Enable */

/* Bit 5 : Write '1' to enable interrupt for event RECEIVE[5] */
#define IPC_INTENSET_RECEIVE5_Pos (5UL) /*!< Position of RECEIVE5 field. */
#define IPC_INTENSET_RECEIVE5_Msk (0x1UL << IPC_INTENSET_RECEIVE5_Pos) /*!< Bit mask of RECEIVE5 field. */
#define IPC_INTENSET_RECEIVE5_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE5_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE5_Set (1UL) /*!< Enable */

/* Bit 4 : Write '1' to enable interrupt for event RECEIVE[4] */
#define IPC_INTENSET_RECEIVE4_Pos (4UL) /*!< Position of RECEIVE4 field. */
#define IPC_INTENSET_RECEIVE4_Msk (0x1UL << IPC_INTENSET_RECEIVE4_Pos) /*!< Bit mask of RECEIVE4 field. */
#define IPC_INTENSET_RECEIVE4_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE4_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE4_Set (1UL) /*!< Enable */

/* Bit 3 : Write '1' to enable interrupt for event RECEIVE[3] */
#define IPC_INTENSET_RECEIVE3_Pos (3UL) /*!< Position of RECEIVE3 field. */
#define IPC_INTENSET_RECEIVE3_Msk (0x1UL << IPC_INTENSET_RECEIVE3_Pos) /*!< Bit mask of RECEIVE3 field. */
#define IPC_INTENSET_RECEIVE3_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE3_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE3_Set (1UL) /*!< Enable */

/* Bit 2 : Write '1' to enable interrupt for event RECEIVE[2] */
#define IPC_INTENSET_RECEIVE2_Pos (2UL) /*!< Position of RECEIVE2 field. */
#define IPC_INTENSET_RECEIVE2_Msk (0x1UL << IPC_INTENSET_RECEIVE2_Pos) /*!< Bit mask of RECEIVE2 field. */
#define IPC_INTENSET_RECEIVE2_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE2_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE2_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event RECEIVE[1] */
#define IPC_INTENSET_RECEIVE1_Pos (1UL) /*!< Position of RECEIVE1 field. */
#define IPC_INTENSET_RECEIVE1_Msk (0x1UL << IPC_INTENSET_RECEIVE1_Pos) /*!< Bit mask of RECEIVE1 field. */
#define IPC_INTENSET_RECEIVE1_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE1_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE1_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event RECEIVE[0] */
#define IPC_INTENSET_RECEIVE0_Pos (0UL) /*!< Position of RECEIVE0 field. */
#define IPC_INTENSET_RECEIVE0_Msk (0x1UL << IPC_INTENSET_RECEIVE0_Pos) /*!< Bit mask of RECEIVE0 field. */
#define IPC_INTENSET_RECEIVE0_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENSET_RECEIVE0_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENSET_RECEIVE0_Set (1UL) /*!< Enable */

/* Register: IPC_INTENCLR */
/* Description: Disable interrupt */

/* Bit 15 : Write '1' to disable interrupt for event RECEIVE[15] */
#define IPC_INTENCLR_RECEIVE15_Pos (15UL) /*!< Position of RECEIVE15 field. */
#define IPC_INTENCLR_RECEIVE15_Msk (0x1UL << IPC_INTENCLR_RECEIVE15_Pos) /*!< Bit mask of RECEIVE15 field. */
#define IPC_INTENCLR_RECEIVE15_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE15_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE15_Clear (1UL) /*!< Disable */

/* Bit 14 : Write '1' to disable interrupt for event RECEIVE[14] */
#define IPC_INTENCLR_RECEIVE14_Pos (14UL) /*!< Position of RECEIVE14 field. */
#define IPC_INTENCLR_RECEIVE14_Msk (0x1UL << IPC_INTENCLR_RECEIVE14_Pos) /*!< Bit mask of RECEIVE14 field. */
#define IPC_INTENCLR_RECEIVE14_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE14_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE14_Clear (1UL) /*!< Disable */

/* Bit 13 : Write '1' to disable interrupt for event RECEIVE[13] */
#define IPC_INTENCLR_RECEIVE13_Pos (13UL) /*!< Position of RECEIVE13 field. */
#define IPC_INTENCLR_RECEIVE13_Msk (0x1UL << IPC_INTENCLR_RECEIVE13_Pos) /*!< Bit mask of RECEIVE13 field. */
#define IPC_INTENCLR_RECEIVE13_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE13_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE13_Clear (1UL) /*!< Disable */

/* Bit 12 : Write '1' to disable interrupt for event RECEIVE[12] */
#define IPC_INTENCLR_RECEIVE12_Pos (12UL) /*!< Position of RECEIVE12 field. */
#define IPC_INTENCLR_RECEIVE12_Msk (0x1UL << IPC_INTENCLR_RECEIVE12_Pos) /*!< Bit mask of RECEIVE12 field. */
#define IPC_INTENCLR_RECEIVE12_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE12_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE12_Clear (1UL) /*!< Disable */

/* Bit 11 : Write '1' to disable interrupt for event RECEIVE[11] */
#define IPC_INTENCLR_RECEIVE11_Pos (11UL) /*!< Position of RECEIVE11 field. */
#define IPC_INTENCLR_RECEIVE11_Msk (0x1UL << IPC_INTENCLR_RECEIVE11_Pos) /*!< Bit mask of RECEIVE11 field. */
#define IPC_INTENCLR_RECEIVE11_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE11_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE11_Clear (1UL) /*!< Disable */

/* Bit 10 : Write '1' to disable interrupt for event RECEIVE[10] */
#define IPC_INTENCLR_RECEIVE10_Pos (10UL) /*!< Position of RECEIVE10 field. */
#define IPC_INTENCLR_RECEIVE10_Msk (0x1UL << IPC_INTENCLR_RECEIVE10_Pos) /*!< Bit mask of RECEIVE10 field. */
#define IPC_INTENCLR_RECEIVE10_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE10_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE10_Clear (1UL) /*!< Disable */

/* Bit 9 : Write '1' to disable interrupt for event RECEIVE[9] */
#define IPC_INTENCLR_RECEIVE9_Pos (9UL) /*!< Position of RECEIVE9 field. */
#define IPC_INTENCLR_RECEIVE9_Msk (0x1UL << IPC_INTENCLR_RECEIVE9_Pos) /*!< Bit mask of RECEIVE9 field. */
#define IPC_INTENCLR_RECEIVE9_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE9_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE9_Clear (1UL) /*!< Disable */

/* Bit 8 : Write '1' to disable interrupt for event RECEIVE[8] */
#define IPC_INTENCLR_RECEIVE8_Pos (8UL) /*!< Position of RECEIVE8 field. */
#define IPC_INTENCLR_RECEIVE8_Msk (0x1UL << IPC_INTENCLR_RECEIVE8_Pos) /*!< Bit mask of RECEIVE8 field. */
#define IPC_INTENCLR_RECEIVE8_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE8_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE8_Clear (1UL) /*!< Disable */

/* Bit 7 : Write '1' to disable interrupt for event RECEIVE[7] */
#define IPC_INTENCLR_RECEIVE7_Pos (7UL) /*!< Position of RECEIVE7 field. */
#define IPC_INTENCLR_RECEIVE7_Msk (0x1UL << IPC_INTENCLR_RECEIVE7_Pos) /*!< Bit mask of RECEIVE7 field. */
#define IPC_INTENCLR_RECEIVE7_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE7_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE7_Clear (1UL) /*!< Disable */

/* Bit 6 : Write '1' to disable interrupt for event RECEIVE[6] */
#define IPC_INTENCLR_RECEIVE6_Pos (6UL) /*!< Position of RECEIVE6 field. */
#define IPC_INTENCLR_RECEIVE6_Msk (0x1UL << IPC_INTENCLR_RECEIVE6_Pos) /*!< Bit mask of RECEIVE6 field. */
#define IPC_INTENCLR_RECEIVE6_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE6_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE6_Clear (1UL) /*!< Disable */

/* Bit 5 : Write '1' to disable interrupt for event RECEIVE[5] */
#define IPC_INTENCLR_RECEIVE5_Pos (5UL) /*!< Position of RECEIVE5 field. */
#define IPC_INTENCLR_RECEIVE5_Msk (0x1UL << IPC_INTENCLR_RECEIVE5_Pos) /*!< Bit mask of RECEIVE5 field. */
#define IPC_INTENCLR_RECEIVE5_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE5_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE5_Clear (1UL) /*!< Disable */

/* Bit 4 : Write '1' to disable interrupt for event RECEIVE[4] */
#define IPC_INTENCLR_RECEIVE4_Pos (4UL) /*!< Position of RECEIVE4 field. */
#define IPC_INTENCLR_RECEIVE4_Msk (0x1UL << IPC_INTENCLR_RECEIVE4_Pos) /*!< Bit mask of RECEIVE4 field. */
#define IPC_INTENCLR_RECEIVE4_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE4_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE4_Clear (1UL) /*!< Disable */

/* Bit 3 : Write '1' to disable interrupt for event RECEIVE[3] */
#define IPC_INTENCLR_RECEIVE3_Pos (3UL) /*!< Position of RECEIVE3 field. */
#define IPC_INTENCLR_RECEIVE3_Msk (0x1UL << IPC_INTENCLR_RECEIVE3_Pos) /*!< Bit mask of RECEIVE3 field. */
#define IPC_INTENCLR_RECEIVE3_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE3_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE3_Clear (1UL) /*!< Disable */

/* Bit 2 : Write '1' to disable interrupt for event RECEIVE[2] */
#define IPC_INTENCLR_RECEIVE2_Pos (2UL) /*!< Position of RECEIVE2 field. */
#define IPC_INTENCLR_RECEIVE2_Msk (0x1UL << IPC_INTENCLR_RECEIVE2_Pos) /*!< Bit mask of RECEIVE2 field. */
#define IPC_INTENCLR_RECEIVE2_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE2_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE2_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event RECEIVE[1] */
#define IPC_INTENCLR_RECEIVE1_Pos (1UL) /*!< Position of RECEIVE1 field. */
#define IPC_INTENCLR_RECEIVE1_Msk (0x1UL << IPC_INTENCLR_RECEIVE1_Pos) /*!< Bit mask of RECEIVE1 field. */
#define IPC_INTENCLR_RECEIVE1_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE1_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE1_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event RECEIVE[0] */
#define IPC_INTENCLR_RECEIVE0_Pos (0UL) /*!< Position of RECEIVE0 field. */
#define IPC_INTENCLR_RECEIVE0_Msk (0x1UL << IPC_INTENCLR_RECEIVE0_Pos) /*!< Bit mask of RECEIVE0 field. */
#define IPC_INTENCLR_RECEIVE0_Disabled (0UL) /*!< Read: Disabled */
#define IPC_INTENCLR_RECEIVE0_Enabled (1UL) /*!< Read: Enabled */
#define IPC_INTENCLR_RECEIVE0_Clear (1UL) /*!< Disable */

/* Register: IPC_INTPEND */
/* Description: Pending interrupts */

/* Bit 15 : Read pending status of interrupt for event RECEIVE[15] */
#define IPC_INTPEND_RECEIVE15_Pos (15UL) /*!< Position of RECEIVE15 field. */
#define IPC_INTPEND_RECEIVE15_Msk (0x1UL << IPC_INTPEND_RECEIVE15_Pos) /*!< Bit mask of RECEIVE15 field. */
#define IPC_INTPEND_RECEIVE15_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE15_Pending (1UL) /*!< Read: Pending */

/* Bit 14 : Read pending status of interrupt for event RECEIVE[14] */
#define IPC_INTPEND_RECEIVE14_Pos (14UL) /*!< Position of RECEIVE14 field. */
#define IPC_INTPEND_RECEIVE14_Msk (0x1UL << IPC_INTPEND_RECEIVE14_Pos) /*!< Bit mask of RECEIVE14 field. */
#define IPC_INTPEND_RECEIVE14_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE14_Pending (1UL) /*!< Read: Pending */

/* Bit 13 : Read pending status of interrupt for event RECEIVE[13] */
#define IPC_INTPEND_RECEIVE13_Pos (13UL) /*!< Position of RECEIVE13 field. */
#define IPC_INTPEND_RECEIVE13_Msk (0x1UL << IPC_INTPEND_RECEIVE13_Pos) /*!< Bit mask of RECEIVE13 field. */
#define IPC_INTPEND_RECEIVE13_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE13_Pending (1UL) /*!< Read: Pending */

/* Bit 12 : Read pending status of interrupt for event RECEIVE[12] */
#define IPC_INTPEND_RECEIVE12_Pos (12UL) /*!< Position of RECEIVE12 field. */
#define IPC_INTPEND_RECEIVE12_Msk (0x1UL << IPC_INTPEND_RECEIVE12_Pos) /*!< Bit mask of RECEIVE12 field. */
#define IPC_INTPEND_RECEIVE12_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE12_Pending (1UL) /*!< Read: Pending */

/* Bit 11 : Read pending status of interrupt for event RECEIVE[11] */
#define IPC_INTPEND_RECEIVE11_Pos (11UL) /*!< Position of RECEIVE11 field. */
#define IPC_INTPEND_RECEIVE11_Msk (0x1UL << IPC_INTPEND_RECEIVE11_Pos) /*!< Bit mask of RECEIVE11 field. */
#define IPC_INTPEND_RECEIVE11_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE11_Pending (1UL) /*!< Read: Pending */

/* Bit 10 : Read pending status of interrupt for event RECEIVE[10] */
#define IPC_INTPEND_RECEIVE10_Pos (10UL) /*!< Position of RECEIVE10 field. */
#define IPC_INTPEND_RECEIVE10_Msk (0x1UL << IPC_INTPEND_RECEIVE10_Pos) /*!< Bit mask of RECEIVE10 field. */
#define IPC_INTPEND_RECEIVE10_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE10_Pending (1UL) /*!< Read: Pending */

/* Bit 9 : Read pending status of interrupt for event RECEIVE[9] */
#define IPC_INTPEND_RECEIVE9_Pos (9UL) /*!< Position of RECEIVE9 field. */
#define IPC_INTPEND_RECEIVE9_Msk (0x1UL << IPC_INTPEND_RECEIVE9_Pos) /*!< Bit mask of RECEIVE9 field. */
#define IPC_INTPEND_RECEIVE9_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE9_Pending (1UL) /*!< Read: Pending */

/* Bit 8 : Read pending status of interrupt for event RECEIVE[8] */
#define IPC_INTPEND_RECEIVE8_Pos (8UL) /*!< Position of RECEIVE8 field. */
#define IPC_INTPEND_RECEIVE8_Msk (0x1UL << IPC_INTPEND_RECEIVE8_Pos) /*!< Bit mask of RECEIVE8 field. */
#define IPC_INTPEND_RECEIVE8_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE8_Pending (1UL) /*!< Read: Pending */

/* Bit 7 : Read pending status of interrupt for event RECEIVE[7] */
#define IPC_INTPEND_RECEIVE7_Pos (7UL) /*!< Position of RECEIVE7 field. */
#define IPC_INTPEND_RECEIVE7_Msk (0x1UL << IPC_INTPEND_RECEIVE7_Pos) /*!< Bit mask of RECEIVE7 field. */
#define IPC_INTPEND_RECEIVE7_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE7_Pending (1UL) /*!< Read: Pending */

/* Bit 6 : Read pending status of interrupt for event RECEIVE[6] */
#define IPC_INTPEND_RECEIVE6_Pos (6UL) /*!< Position of RECEIVE6 field. */
#define IPC_INTPEND_RECEIVE6_Msk (0x1UL << IPC_INTPEND_RECEIVE6_Pos) /*!< Bit mask of RECEIVE6 field. */
#define IPC_INTPEND_RECEIVE6_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE6_Pending (1UL) /*!< Read: Pending */

/* Bit 5 : Read pending status of interrupt for event RECEIVE[5] */
#define IPC_INTPEND_RECEIVE5_Pos (5UL) /*!< Position of RECEIVE5 field. */
#define IPC_INTPEND_RECEIVE5_Msk (0x1UL << IPC_INTPEND_RECEIVE5_Pos) /*!< Bit mask of RECEIVE5 field. */
#define IPC_INTPEND_RECEIVE5_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE5_Pending (1UL) /*!< Read: Pending */

/* Bit 4 : Read pending status of interrupt for event RECEIVE[4] */
#define IPC_INTPEND_RECEIVE4_Pos (4UL) /*!< Position of RECEIVE4 field. */
#define IPC_INTPEND_RECEIVE4_Msk (0x1UL << IPC_INTPEND_RECEIVE4_Pos) /*!< Bit mask of RECEIVE4 field. */
#define IPC_INTPEND_RECEIVE4_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE4_Pending (1UL) /*!< Read: Pending */

/* Bit 3 : Read pending status of interrupt for event RECEIVE[3] */
#define IPC_INTPEND_RECEIVE3_Pos (3UL) /*!< Position of RECEIVE3 field. */
#define IPC_INTPEND_RECEIVE3_Msk (0x1UL << IPC_INTPEND_RECEIVE3_Pos) /*!< Bit mask of RECEIVE3 field. */
#define IPC_INTPEND_RECEIVE3_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE3_Pending (1UL) /*!< Read: Pending */

/* Bit 2 : Read pending status of interrupt for event RECEIVE[2] */
#define IPC_INTPEND_RECEIVE2_Pos (2UL) /*!< Position of RECEIVE2 field. */
#define IPC_INTPEND_RECEIVE2_Msk (0x1UL << IPC_INTPEND_RECEIVE2_Pos) /*!< Bit mask of RECEIVE2 field. */
#define IPC_INTPEND_RECEIVE2_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE2_Pending (1UL) /*!< Read: Pending */

/* Bit 1 : Read pending status of interrupt for event RECEIVE[1] */
#define IPC_INTPEND_RECEIVE1_Pos (1UL) /*!< Position of RECEIVE1 field. */
#define IPC_INTPEND_RECEIVE1_Msk (0x1UL << IPC_INTPEND_RECEIVE1_Pos) /*!< Bit mask of RECEIVE1 field. */
#define IPC_INTPEND_RECEIVE1_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE1_Pending (1UL) /*!< Read: Pending */

/* Bit 0 : Read pending status of interrupt for event RECEIVE[0] */
#define IPC_INTPEND_RECEIVE0_Pos (0UL) /*!< Position of RECEIVE0 field. */
#define IPC_INTPEND_RECEIVE0_Msk (0x1UL << IPC_INTPEND_RECEIVE0_Pos) /*!< Bit mask of RECEIVE0 field. */
#define IPC_INTPEND_RECEIVE0_NotPending (0UL) /*!< Read: Not pending */
#define IPC_INTPEND_RECEIVE0_Pending (1UL) /*!< Read: Pending */

/* Register: IPC_SEND_CNF */
/* Description: Description collection: Send event configuration for TASKS_SEND[n] */

/* Bit 15 : Enable broadcasting on IPC channel 15 */
#define IPC_SEND_CNF_CHEN15_Pos (15UL) /*!< Position of CHEN15 field. */
#define IPC_SEND_CNF_CHEN15_Msk (0x1UL << IPC_SEND_CNF_CHEN15_Pos) /*!< Bit mask of CHEN15 field. */
#define IPC_SEND_CNF_CHEN15_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN15_Enable (1UL) /*!< Enable broadcast */

/* Bit 14 : Enable broadcasting on IPC channel 14 */
#define IPC_SEND_CNF_CHEN14_Pos (14UL) /*!< Position of CHEN14 field. */
#define IPC_SEND_CNF_CHEN14_Msk (0x1UL << IPC_SEND_CNF_CHEN14_Pos) /*!< Bit mask of CHEN14 field. */
#define IPC_SEND_CNF_CHEN14_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN14_Enable (1UL) /*!< Enable broadcast */

/* Bit 13 : Enable broadcasting on IPC channel 13 */
#define IPC_SEND_CNF_CHEN13_Pos (13UL) /*!< Position of CHEN13 field. */
#define IPC_SEND_CNF_CHEN13_Msk (0x1UL << IPC_SEND_CNF_CHEN13_Pos) /*!< Bit mask of CHEN13 field. */
#define IPC_SEND_CNF_CHEN13_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN13_Enable (1UL) /*!< Enable broadcast */

/* Bit 12 : Enable broadcasting on IPC channel 12 */
#define IPC_SEND_CNF_CHEN12_Pos (12UL) /*!< Position of CHEN12 field. */
#define IPC_SEND_CNF_CHEN12_Msk (0x1UL << IPC_SEND_CNF_CHEN12_Pos) /*!< Bit mask of CHEN12 field. */
#define IPC_SEND_CNF_CHEN12_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN12_Enable (1UL) /*!< Enable broadcast */

/* Bit 11 : Enable broadcasting on IPC channel 11 */
#define IPC_SEND_CNF_CHEN11_Pos (11UL) /*!< Position of CHEN11 field. */
#define IPC_SEND_CNF_CHEN11_Msk (0x1UL << IPC_SEND_CNF_CHEN11_Pos) /*!< Bit mask of CHEN11 field. */
#define IPC_SEND_CNF_CHEN11_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN11_Enable (1UL) /*!< Enable broadcast */

/* Bit 10 : Enable broadcasting on IPC channel 10 */
#define IPC_SEND_CNF_CHEN10_Pos (10UL) /*!< Position of CHEN10 field. */
#define IPC_SEND_CNF_CHEN10_Msk (0x1UL << IPC_SEND_CNF_CHEN10_Pos) /*!< Bit mask of CHEN10 field. */
#define IPC_SEND_CNF_CHEN10_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN10_Enable (1UL) /*!< Enable broadcast */

/* Bit 9 : Enable broadcasting on IPC channel 9 */
#define IPC_SEND_CNF_CHEN9_Pos (9UL) /*!< Position of CHEN9 field. */
#define IPC_SEND_CNF_CHEN9_Msk (0x1UL << IPC_SEND_CNF_CHEN9_Pos) /*!< Bit mask of CHEN9 field. */
#define IPC_SEND_CNF_CHEN9_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN9_Enable (1UL) /*!< Enable broadcast */

/* Bit 8 : Enable broadcasting on IPC channel 8 */
#define IPC_SEND_CNF_CHEN8_Pos (8UL) /*!< Position of CHEN8 field. */
#define IPC_SEND_CNF_CHEN8_Msk (0x1UL << IPC_SEND_CNF_CHEN8_Pos) /*!< Bit mask of CHEN8 field. */
#define IPC_SEND_CNF_CHEN8_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN8_Enable (1UL) /*!< Enable broadcast */

/* Bit 7 : Enable broadcasting on IPC channel 7 */
#define IPC_SEND_CNF_CHEN7_Pos (7UL) /*!< Position of CHEN7 field. */
#define IPC_SEND_CNF_CHEN7_Msk (0x1UL << IPC_SEND_CNF_CHEN7_Pos) /*!< Bit mask of CHEN7 field. */
#define IPC_SEND_CNF_CHEN7_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN7_Enable (1UL) /*!< Enable broadcast */

/* Bit 6 : Enable broadcasting on IPC channel 6 */
#define IPC_SEND_CNF_CHEN6_Pos (6UL) /*!< Position of CHEN6 field. */
#define IPC_SEND_CNF_CHEN6_Msk (0x1UL << IPC_SEND_CNF_CHEN6_Pos) /*!< Bit mask of CHEN6 field. */
#define IPC_SEND_CNF_CHEN6_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN6_Enable (1UL) /*!< Enable broadcast */

/* Bit 5 : Enable broadcasting on IPC channel 5 */
#define IPC_SEND_CNF_CHEN5_Pos (5UL) /*!< Position of CHEN5 field. */
#define IPC_SEND_CNF_CHEN5_Msk (0x1UL << IPC_SEND_CNF_CHEN5_Pos) /*!< Bit mask of CHEN5 field. */
#define IPC_SEND_CNF_CHEN5_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN5_Enable (1UL) /*!< Enable broadcast */

/* Bit 4 : Enable broadcasting on IPC channel 4 */
#define IPC_SEND_CNF_CHEN4_Pos (4UL) /*!< Position of CHEN4 field. */
#define IPC_SEND_CNF_CHEN4_Msk (0x1UL << IPC_SEND_CNF_CHEN4_Pos) /*!< Bit mask of CHEN4 field. */
#define IPC_SEND_CNF_CHEN4_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN4_Enable (1UL) /*!< Enable broadcast */

/* Bit 3 : Enable broadcasting on IPC channel 3 */
#define IPC_SEND_CNF_CHEN3_Pos (3UL) /*!< Position of CHEN3 field. */
#define IPC_SEND_CNF_CHEN3_Msk (0x1UL << IPC_SEND_CNF_CHEN3_Pos) /*!< Bit mask of CHEN3 field. */
#define IPC_SEND_CNF_CHEN3_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN3_Enable (1UL) /*!< Enable broadcast */

/* Bit 2 : Enable broadcasting on IPC channel 2 */
#define IPC_SEND_CNF_CHEN2_Pos (2UL) /*!< Position of CHEN2 field. */
#define IPC_SEND_CNF_CHEN2_Msk (0x1UL << IPC_SEND_CNF_CHEN2_Pos) /*!< Bit mask of CHEN2 field. */
#define IPC_SEND_CNF_CHEN2_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN2_Enable (1UL) /*!< Enable broadcast */

/* Bit 1 : Enable broadcasting on IPC channel 1 */
#define IPC_SEND_CNF_CHEN1_Pos (1UL) /*!< Position of CHEN1 field. */
#define IPC_SEND_CNF_CHEN1_Msk (0x1UL << IPC_SEND_CNF_CHEN1_Pos) /*!< Bit mask of CHEN1 field. */
#define IPC_SEND_CNF_CHEN1_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN1_Enable (1UL) /*!< Enable broadcast */

/* Bit 0 : Enable broadcasting on IPC channel 0 */
#define IPC_SEND_CNF_CHEN0_Pos (0UL) /*!< Position of CHEN0 field. */
#define IPC_SEND_CNF_CHEN0_Msk (0x1UL << IPC_SEND_CNF_CHEN0_Pos) /*!< Bit mask of CHEN0 field. */
#define IPC_SEND_CNF_CHEN0_Disable (0UL) /*!< Disable broadcast */
#define IPC_SEND_CNF_CHEN0_Enable (1UL) /*!< Enable broadcast */

/* Register: IPC_RECEIVE_CNF */
/* Description: Description collection: Receive event configuration for EVENTS_RECEIVE[n] */

/* Bit 15 : Enable subscription to IPC channel 15 */
#define IPC_RECEIVE_CNF_CHEN15_Pos (15UL) /*!< Position of CHEN15 field. */
#define IPC_RECEIVE_CNF_CHEN15_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN15_Pos) /*!< Bit mask of CHEN15 field. */
#define IPC_RECEIVE_CNF_CHEN15_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN15_Enable (1UL) /*!< Enable events */

/* Bit 14 : Enable subscription to IPC channel 14 */
#define IPC_RECEIVE_CNF_CHEN14_Pos (14UL) /*!< Position of CHEN14 field. */
#define IPC_RECEIVE_CNF_CHEN14_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN14_Pos) /*!< Bit mask of CHEN14 field. */
#define IPC_RECEIVE_CNF_CHEN14_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN14_Enable (1UL) /*!< Enable events */

/* Bit 13 : Enable subscription to IPC channel 13 */
#define IPC_RECEIVE_CNF_CHEN13_Pos (13UL) /*!< Position of CHEN13 field. */
#define IPC_RECEIVE_CNF_CHEN13_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN13_Pos) /*!< Bit mask of CHEN13 field. */
#define IPC_RECEIVE_CNF_CHEN13_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN13_Enable (1UL) /*!< Enable events */

/* Bit 12 : Enable subscription to IPC channel 12 */
#define IPC_RECEIVE_CNF_CHEN12_Pos (12UL) /*!< Position of CHEN12 field. */
#define IPC_RECEIVE_CNF_CHEN12_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN12_Pos) /*!< Bit mask of CHEN12 field. */
#define IPC_RECEIVE_CNF_CHEN12_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN12_Enable (1UL) /*!< Enable events */

/* Bit 11 : Enable subscription to IPC channel 11 */
#define IPC_RECEIVE_CNF_CHEN11_Pos (11UL) /*!< Position of CHEN11 field. */
#define IPC_RECEIVE_CNF_CHEN11_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN11_Pos) /*!< Bit mask of CHEN11 field. */
#define IPC_RECEIVE_CNF_CHEN11_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN11_Enable (1UL) /*!< Enable events */

/* Bit 10 : Enable subscription to IPC channel 10 */
#define IPC_RECEIVE_CNF_CHEN10_Pos (10UL) /*!< Position of CHEN10 field. */
#define IPC_RECEIVE_CNF_CHEN10_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN10_Pos) /*!< Bit mask of CHEN10 field. */
#define IPC_RECEIVE_CNF_CHEN10_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN10_Enable (1UL) /*!< Enable events */

/* Bit 9 : Enable subscription to IPC channel 9 */
#define IPC_RECEIVE_CNF_CHEN9_Pos (9UL) /*!< Position of CHEN9 field. */
#define IPC_RECEIVE_CNF_CHEN9_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN9_Pos) /*!< Bit mask of CHEN9 field. */
#define IPC_RECEIVE_CNF_CHEN9_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN9_Enable (1UL) /*!< Enable events */

/* Bit 8 : Enable subscription to IPC channel 8 */
#define IPC_RECEIVE_CNF_CHEN8_Pos (8UL) /*!< Position of CHEN8 field. */
#define IPC_RECEIVE_CNF_CHEN8_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN8_Pos) /*!< Bit mask of CHEN8 field. */
#define IPC_RECEIVE_CNF_CHEN8_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN8_Enable (1UL) /*!< Enable events */

/* Bit 7 : Enable subscription to IPC channel 7 */
#define IPC_RECEIVE_CNF_CHEN7_Pos (7UL) /*!< Position of CHEN7 field. */
#define IPC_RECEIVE_CNF_CHEN7_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN7_Pos) /*!< Bit mask of CHEN7 field. */
#define IPC_RECEIVE_CNF_CHEN7_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN7_Enable (1UL) /*!< Enable events */

/* Bit 6 : Enable subscription to IPC channel 6 */
#define IPC_RECEIVE_CNF_CHEN6_Pos (6UL) /*!< Position of CHEN6 field. */
#define IPC_RECEIVE_CNF_CHEN6_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN6_Pos) /*!< Bit mask of CHEN6 field. */
#define IPC_RECEIVE_CNF_CHEN6_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN6_Enable (1UL) /*!< Enable events */

/* Bit 5 : Enable subscription to IPC channel 5 */
#define IPC_RECEIVE_CNF_CHEN5_Pos (5UL) /*!< Position of CHEN5 field. */
#define IPC_RECEIVE_CNF_CHEN5_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN5_Pos) /*!< Bit mask of CHEN5 field. */
#define IPC_RECEIVE_CNF_CHEN5_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN5_Enable (1UL) /*!< Enable events */

/* Bit 4 : Enable subscription to IPC channel 4 */
#define IPC_RECEIVE_CNF_CHEN4_Pos (4UL) /*!< Position of CHEN4 field. */
#define IPC_RECEIVE_CNF_CHEN4_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN4_Pos) /*!< Bit mask of CHEN4 field. */
#define IPC_RECEIVE_CNF_CHEN4_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN4_Enable (1UL) /*!< Enable events */

/* Bit 3 : Enable subscription to IPC channel 3 */
#define IPC_RECEIVE_CNF_CHEN3_Pos (3UL) /*!< Position of CHEN3 field. */
#define IPC_RECEIVE_CNF_CHEN3_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN3_Pos) /*!< Bit mask of CHEN3 field. */
#define IPC_RECEIVE_CNF_CHEN3_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN3_Enable (1UL) /*!< Enable events */

/* Bit 2 : Enable subscription to IPC channel 2 */
#define IPC_RECEIVE_CNF_CHEN2_Pos (2UL) /*!< Position of CHEN2 field. */
#define IPC_RECEIVE_CNF_CHEN2_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN2_Pos) /*!< Bit mask of CHEN2 field. */
#define IPC_RECEIVE_CNF_CHEN2_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN2_Enable (1UL) /*!< Enable events */

/* Bit 1 : Enable subscription to IPC channel 1 */
#define IPC_RECEIVE_CNF_CHEN1_Pos (1UL) /*!< Position of CHEN1 field. */
#define IPC_RECEIVE_CNF_CHEN1_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN1_Pos) /*!< Bit mask of CHEN1 field. */
#define IPC_RECEIVE_CNF_CHEN1_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN1_Enable (1UL) /*!< Enable events */

/* Bit 0 : Enable subscription to IPC channel 0 */
#define IPC_RECEIVE_CNF_CHEN0_Pos (0UL) /*!< Position of CHEN0 field. */
#define IPC_RECEIVE_CNF_CHEN0_Msk (0x1UL << IPC_RECEIVE_CNF_CHEN0_Pos) /*!< Bit mask of CHEN0 field. */
#define IPC_RECEIVE_CNF_CHEN0_Disable (0UL) /*!< Disable events */
#define IPC_RECEIVE_CNF_CHEN0_Enable (1UL) /*!< Enable events */

/* Register: IPC_GPMEM */
/* Description: Description collection: General purpose memory */

/* Bits 31..0 : General purpose memory */
#define IPC_GPMEM_GPMEM_Pos (0UL) /*!< Position of GPMEM field. */
#define IPC_GPMEM_GPMEM_Msk (0xFFFFFFFFUL << IPC_GPMEM_GPMEM_Pos) /*!< Bit mask of GPMEM field. */


/* Peripheral: NVMC */
/* Description: Non-volatile memory controller */

/* Register: NVMC_READY */
/* Description: Ready flag */

/* Bit 0 : NVMC is ready or busy */
#define NVMC_READY_READY_Pos (0UL) /*!< Position of READY field. */
#define NVMC_READY_READY_Msk (0x1UL << NVMC_READY_READY_Pos) /*!< Bit mask of READY field. */
#define NVMC_READY_READY_Busy (0UL) /*!< NVMC is busy (ongoing write or erase operation) */
#define NVMC_READY_READY_Ready (1UL) /*!< NVMC is ready */

/* Register: NVMC_READYNEXT */
/* Description: Ready flag */

/* Bit 0 : NVMC can accept a new write operation */
#define NVMC_READYNEXT_READYNEXT_Pos (0UL) /*!< Position of READYNEXT field. */
#define NVMC_READYNEXT_READYNEXT_Msk (0x1UL << NVMC_READYNEXT_READYNEXT_Pos) /*!< Bit mask of READYNEXT field. */
#define NVMC_READYNEXT_READYNEXT_Busy (0UL) /*!< NVMC cannot accept any write operation */
#define NVMC_READYNEXT_READYNEXT_Ready (1UL) /*!< NVMC is ready */

/* Register: NVMC_CONFIG */
/* Description: Configuration register */

/* Bits 2..0 : Program memory access mode. It is strongly recommended to only activate erase and write modes when they are actively used. Enabling write or erase will invalidate the cache and keep it invalidated. */
#define NVMC_CONFIG_WEN_Pos (0UL) /*!< Position of WEN field. */
#define NVMC_CONFIG_WEN_Msk (0x7UL << NVMC_CONFIG_WEN_Pos) /*!< Bit mask of WEN field. */
#define NVMC_CONFIG_WEN_Ren (0UL) /*!< Read only access */
#define NVMC_CONFIG_WEN_Wen (1UL) /*!< Write enabled */
#define NVMC_CONFIG_WEN_Een (2UL) /*!< Erase enabled */
#define NVMC_CONFIG_WEN_PEen (4UL) /*!< Partial erase enabled */

/* Register: NVMC_ERASEALL */
/* Description: Register for erasing all non-volatile user memory */

/* Bit 0 : Erase all non-volatile memory including UICR registers. Before the non-volatile memory can be erased, erasing must be enabled by setting CONFIG.WEN=Een. */
#define NVMC_ERASEALL_ERASEALL_Pos (0UL) /*!< Position of ERASEALL field. */
#define NVMC_ERASEALL_ERASEALL_Msk (0x1UL << NVMC_ERASEALL_ERASEALL_Pos) /*!< Bit mask of ERASEALL field. */
#define NVMC_ERASEALL_ERASEALL_NoOperation (0UL) /*!< No operation */
#define NVMC_ERASEALL_ERASEALL_Erase (1UL) /*!< Start chip erase */

/* Register: NVMC_ERASEPAGEPARTIALCFG */
/* Description: Register for partial erase configuration */

/* Bits 6..0 : Duration of the partial erase in milliseconds */
#define NVMC_ERASEPAGEPARTIALCFG_DURATION_Pos (0UL) /*!< Position of DURATION field. */
#define NVMC_ERASEPAGEPARTIALCFG_DURATION_Msk (0x7FUL << NVMC_ERASEPAGEPARTIALCFG_DURATION_Pos) /*!< Bit mask of DURATION field. */

/* Register: NVMC_ICACHECNF */
/* Description: I-code cache configuration register */

/* Bit 8 : Cache profiling enable */
#define NVMC_ICACHECNF_CACHEPROFEN_Pos (8UL) /*!< Position of CACHEPROFEN field. */
#define NVMC_ICACHECNF_CACHEPROFEN_Msk (0x1UL << NVMC_ICACHECNF_CACHEPROFEN_Pos) /*!< Bit mask of CACHEPROFEN field. */
#define NVMC_ICACHECNF_CACHEPROFEN_Disabled (0UL) /*!< Disable cache profiling */
#define NVMC_ICACHECNF_CACHEPROFEN_Enabled (1UL) /*!< Enable cache profiling */

/* Bit 0 : Cache enable */
#define NVMC_ICACHECNF_CACHEEN_Pos (0UL) /*!< Position of CACHEEN field. */
#define NVMC_ICACHECNF_CACHEEN_Msk (0x1UL << NVMC_ICACHECNF_CACHEEN_Pos) /*!< Bit mask of CACHEEN field. */
#define NVMC_ICACHECNF_CACHEEN_Disabled (0UL) /*!< Disable cache. Invalidates all cache entries. */
#define NVMC_ICACHECNF_CACHEEN_Enabled (1UL) /*!< Enable cache */

/* Register: NVMC_IHIT */
/* Description: I-code cache hit counter */

/* Bits 31..0 : Number of cache hits Write zero to clear */
#define NVMC_IHIT_HITS_Pos (0UL) /*!< Position of HITS field. */
#define NVMC_IHIT_HITS_Msk (0xFFFFFFFFUL << NVMC_IHIT_HITS_Pos) /*!< Bit mask of HITS field. */

/* Register: NVMC_IMISS */
/* Description: I-code cache miss counter */

/* Bits 31..0 : Number of cache misses Write zero to clear */
#define NVMC_IMISS_MISSES_Pos (0UL) /*!< Position of MISSES field. */
#define NVMC_IMISS_MISSES_Msk (0xFFFFFFFFUL << NVMC_IMISS_MISSES_Pos) /*!< Bit mask of MISSES field. */


/* Peripheral: GPIO */
/* Description: GPIO Port 0 */

/* Register: GPIO_OUT */
/* Description: Write GPIO port */

/* Bit 31 : Pin 31 */
#define GPIO_OUT_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_OUT_PIN31_Msk (0x1UL << GPIO_OUT_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_OUT_PIN31_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN31_High (1UL) /*!< Pin driver is high */

/* Bit 30 : Pin 30 */
#define GPIO_OUT_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_OUT_PIN30_Msk (0x1UL << GPIO_OUT_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_OUT_PIN30_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN30_High (1UL) /*!< Pin driver is high */

/* Bit 29 : Pin 29 */
#define GPIO_OUT_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_OUT_PIN29_Msk (0x1UL << GPIO_OUT_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_OUT_PIN29_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN29_High (1UL) /*!< Pin driver is high */

/* Bit 28 : Pin 28 */
#define GPIO_OUT_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_OUT_PIN28_Msk (0x1UL << GPIO_OUT_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_OUT_PIN28_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN28_High (1UL) /*!< Pin driver is high */

/* Bit 27 : Pin 27 */
#define GPIO_OUT_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_OUT_PIN27_Msk (0x1UL << GPIO_OUT_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_OUT_PIN27_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN27_High (1UL) /*!< Pin driver is high */

/* Bit 26 : Pin 26 */
#define GPIO_OUT_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_OUT_PIN26_Msk (0x1UL << GPIO_OUT_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_OUT_PIN26_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN26_High (1UL) /*!< Pin driver is high */

/* Bit 25 : Pin 25 */
#define GPIO_OUT_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_OUT_PIN25_Msk (0x1UL << GPIO_OUT_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_OUT_PIN25_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN25_High (1UL) /*!< Pin driver is high */

/* Bit 24 : Pin 24 */
#define GPIO_OUT_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_OUT_PIN24_Msk (0x1UL << GPIO_OUT_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_OUT_PIN24_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN24_High (1UL) /*!< Pin driver is high */

/* Bit 23 : Pin 23 */
#define GPIO_OUT_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_OUT_PIN23_Msk (0x1UL << GPIO_OUT_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_OUT_PIN23_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN23_High (1UL) /*!< Pin driver is high */

/* Bit 22 : Pin 22 */
#define GPIO_OUT_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_OUT_PIN22_Msk (0x1UL << GPIO_OUT_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_OUT_PIN22_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN22_High (1UL) /*!< Pin driver is high */

/* Bit 21 : Pin 21 */
#define GPIO_OUT_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_OUT_PIN21_Msk (0x1UL << GPIO_OUT_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_OUT_PIN21_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN21_High (1UL) /*!< Pin driver is high */

/* Bit 20 : Pin 20 */
#define GPIO_OUT_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_OUT_PIN20_Msk (0x1UL << GPIO_OUT_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_OUT_PIN20_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN20_High (1UL) /*!< Pin driver is high */

/* Bit 19 : Pin 19 */
#define GPIO_OUT_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_OUT_PIN19_Msk (0x1UL << GPIO_OUT_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_OUT_PIN19_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN19_High (1UL) /*!< Pin driver is high */

/* Bit 18 : Pin 18 */
#define GPIO_OUT_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_OUT_PIN18_Msk (0x1UL << GPIO_OUT_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_OUT_PIN18_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN18_High (1UL) /*!< Pin driver is high */

/* Bit 17 : Pin 17 */
#define GPIO_OUT_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_OUT_PIN17_Msk (0x1UL << GPIO_OUT_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_OUT_PIN17_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN17_High (1UL) /*!< Pin driver is high */

/* Bit 16 : Pin 16 */
#define GPIO_OUT_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_OUT_PIN16_Msk (0x1UL << GPIO_OUT_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_OUT_PIN16_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN16_High (1UL) /*!< Pin driver is high */

/* Bit 15 : Pin 15 */
#define GPIO_OUT_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_OUT_PIN15_Msk (0x1UL << GPIO_OUT_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_OUT_PIN15_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN15_High (1UL) /*!< Pin driver is high */

/* Bit 14 : Pin 14 */
#define GPIO_OUT_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_OUT_PIN14_Msk (0x1UL << GPIO_OUT_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_OUT_PIN14_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN14_High (1UL) /*!< Pin driver is high */

/* Bit 13 : Pin 13 */
#define GPIO_OUT_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_OUT_PIN13_Msk (0x1UL << GPIO_OUT_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_OUT_PIN13_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN13_High (1UL) /*!< Pin driver is high */

/* Bit 12 : Pin 12 */
#define GPIO_OUT_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_OUT_PIN12_Msk (0x1UL << GPIO_OUT_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_OUT_PIN12_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN12_High (1UL) /*!< Pin driver is high */

/* Bit 11 : Pin 11 */
#define GPIO_OUT_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_OUT_PIN11_Msk (0x1UL << GPIO_OUT_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_OUT_PIN11_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN11_High (1UL) /*!< Pin driver is high */

/* Bit 10 : Pin 10 */
#define GPIO_OUT_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_OUT_PIN10_Msk (0x1UL << GPIO_OUT_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_OUT_PIN10_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN10_High (1UL) /*!< Pin driver is high */

/* Bit 9 : Pin 9 */
#define GPIO_OUT_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_OUT_PIN9_Msk (0x1UL << GPIO_OUT_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_OUT_PIN9_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN9_High (1UL) /*!< Pin driver is high */

/* Bit 8 : Pin 8 */
#define GPIO_OUT_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_OUT_PIN8_Msk (0x1UL << GPIO_OUT_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_OUT_PIN8_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN8_High (1UL) /*!< Pin driver is high */

/* Bit 7 : Pin 7 */
#define GPIO_OUT_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_OUT_PIN7_Msk (0x1UL << GPIO_OUT_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_OUT_PIN7_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN7_High (1UL) /*!< Pin driver is high */

/* Bit 6 : Pin 6 */
#define GPIO_OUT_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_OUT_PIN6_Msk (0x1UL << GPIO_OUT_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_OUT_PIN6_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN6_High (1UL) /*!< Pin driver is high */

/* Bit 5 : Pin 5 */
#define GPIO_OUT_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_OUT_PIN5_Msk (0x1UL << GPIO_OUT_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_OUT_PIN5_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN5_High (1UL) /*!< Pin driver is high */

/* Bit 4 : Pin 4 */
#define GPIO_OUT_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_OUT_PIN4_Msk (0x1UL << GPIO_OUT_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_OUT_PIN4_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN4_High (1UL) /*!< Pin driver is high */

/* Bit 3 : Pin 3 */
#define GPIO_OUT_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_OUT_PIN3_Msk (0x1UL << GPIO_OUT_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_OUT_PIN3_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN3_High (1UL) /*!< Pin driver is high */

/* Bit 2 : Pin 2 */
#define GPIO_OUT_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_OUT_PIN2_Msk (0x1UL << GPIO_OUT_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_OUT_PIN2_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN2_High (1UL) /*!< Pin driver is high */

/* Bit 1 : Pin 1 */
#define GPIO_OUT_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_OUT_PIN1_Msk (0x1UL << GPIO_OUT_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_OUT_PIN1_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN1_High (1UL) /*!< Pin driver is high */

/* Bit 0 : Pin 0 */
#define GPIO_OUT_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_OUT_PIN0_Msk (0x1UL << GPIO_OUT_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_OUT_PIN0_Low (0UL) /*!< Pin driver is low */
#define GPIO_OUT_PIN0_High (1UL) /*!< Pin driver is high */

/* Register: GPIO_OUTSET */
/* Description: Set individual bits in GPIO port */

/* Bit 31 : Pin 31 */
#define GPIO_OUTSET_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_OUTSET_PIN31_Msk (0x1UL << GPIO_OUTSET_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_OUTSET_PIN31_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN31_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN31_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 30 : Pin 30 */
#define GPIO_OUTSET_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_OUTSET_PIN30_Msk (0x1UL << GPIO_OUTSET_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_OUTSET_PIN30_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN30_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN30_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 29 : Pin 29 */
#define GPIO_OUTSET_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_OUTSET_PIN29_Msk (0x1UL << GPIO_OUTSET_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_OUTSET_PIN29_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN29_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN29_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 28 : Pin 28 */
#define GPIO_OUTSET_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_OUTSET_PIN28_Msk (0x1UL << GPIO_OUTSET_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_OUTSET_PIN28_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN28_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN28_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 27 : Pin 27 */
#define GPIO_OUTSET_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_OUTSET_PIN27_Msk (0x1UL << GPIO_OUTSET_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_OUTSET_PIN27_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN27_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN27_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 26 : Pin 26 */
#define GPIO_OUTSET_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_OUTSET_PIN26_Msk (0x1UL << GPIO_OUTSET_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_OUTSET_PIN26_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN26_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN26_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 25 : Pin 25 */
#define GPIO_OUTSET_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_OUTSET_PIN25_Msk (0x1UL << GPIO_OUTSET_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_OUTSET_PIN25_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN25_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN25_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 24 : Pin 24 */
#define GPIO_OUTSET_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_OUTSET_PIN24_Msk (0x1UL << GPIO_OUTSET_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_OUTSET_PIN24_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN24_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN24_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 23 : Pin 23 */
#define GPIO_OUTSET_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_OUTSET_PIN23_Msk (0x1UL << GPIO_OUTSET_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_OUTSET_PIN23_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN23_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN23_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 22 : Pin 22 */
#define GPIO_OUTSET_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_OUTSET_PIN22_Msk (0x1UL << GPIO_OUTSET_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_OUTSET_PIN22_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN22_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN22_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 21 : Pin 21 */
#define GPIO_OUTSET_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_OUTSET_PIN21_Msk (0x1UL << GPIO_OUTSET_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_OUTSET_PIN21_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN21_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN21_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 20 : Pin 20 */
#define GPIO_OUTSET_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_OUTSET_PIN20_Msk (0x1UL << GPIO_OUTSET_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_OUTSET_PIN20_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN20_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN20_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 19 : Pin 19 */
#define GPIO_OUTSET_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_OUTSET_PIN19_Msk (0x1UL << GPIO_OUTSET_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_OUTSET_PIN19_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN19_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN19_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 18 : Pin 18 */
#define GPIO_OUTSET_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_OUTSET_PIN18_Msk (0x1UL << GPIO_OUTSET_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_OUTSET_PIN18_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN18_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN18_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 17 : Pin 17 */
#define GPIO_OUTSET_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_OUTSET_PIN17_Msk (0x1UL << GPIO_OUTSET_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_OUTSET_PIN17_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN17_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN17_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 16 : Pin 16 */
#define GPIO_OUTSET_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_OUTSET_PIN16_Msk (0x1UL << GPIO_OUTSET_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_OUTSET_PIN16_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN16_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN16_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 15 : Pin 15 */
#define GPIO_OUTSET_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_OUTSET_PIN15_Msk (0x1UL << GPIO_OUTSET_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_OUTSET_PIN15_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN15_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN15_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 14 : Pin 14 */
#define GPIO_OUTSET_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_OUTSET_PIN14_Msk (0x1UL << GPIO_OUTSET_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_OUTSET_PIN14_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN14_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN14_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 13 : Pin 13 */
#define GPIO_OUTSET_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_OUTSET_PIN13_Msk (0x1UL << GPIO_OUTSET_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_OUTSET_PIN13_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN13_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN13_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 12 : Pin 12 */
#define GPIO_OUTSET_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_OUTSET_PIN12_Msk (0x1UL << GPIO_OUTSET_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_OUTSET_PIN12_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN12_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN12_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 11 : Pin 11 */
#define GPIO_OUTSET_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_OUTSET_PIN11_Msk (0x1UL << GPIO_OUTSET_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_OUTSET_PIN11_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN11_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN11_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 10 : Pin 10 */
#define GPIO_OUTSET_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_OUTSET_PIN10_Msk (0x1UL << GPIO_OUTSET_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_OUTSET_PIN10_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN10_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN10_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 9 : Pin 9 */
#define GPIO_OUTSET_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_OUTSET_PIN9_Msk (0x1UL << GPIO_OUTSET_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_OUTSET_PIN9_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN9_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN9_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 8 : Pin 8 */
#define GPIO_OUTSET_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_OUTSET_PIN8_Msk (0x1UL << GPIO_OUTSET_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_OUTSET_PIN8_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN8_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN8_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 7 : Pin 7 */
#define GPIO_OUTSET_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_OUTSET_PIN7_Msk (0x1UL << GPIO_OUTSET_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_OUTSET_PIN7_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN7_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN7_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 6 : Pin 6 */
#define GPIO_OUTSET_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_OUTSET_PIN6_Msk (0x1UL << GPIO_OUTSET_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_OUTSET_PIN6_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN6_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN6_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 5 : Pin 5 */
#define GPIO_OUTSET_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_OUTSET_PIN5_Msk (0x1UL << GPIO_OUTSET_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_OUTSET_PIN5_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN5_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN5_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 4 : Pin 4 */
#define GPIO_OUTSET_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_OUTSET_PIN4_Msk (0x1UL << GPIO_OUTSET_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_OUTSET_PIN4_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN4_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN4_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 3 : Pin 3 */
#define GPIO_OUTSET_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_OUTSET_PIN3_Msk (0x1UL << GPIO_OUTSET_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_OUTSET_PIN3_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN3_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN3_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 2 : Pin 2 */
#define GPIO_OUTSET_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_OUTSET_PIN2_Msk (0x1UL << GPIO_OUTSET_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_OUTSET_PIN2_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN2_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN2_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 1 : Pin 1 */
#define GPIO_OUTSET_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_OUTSET_PIN1_Msk (0x1UL << GPIO_OUTSET_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_OUTSET_PIN1_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN1_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN1_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Bit 0 : Pin 0 */
#define GPIO_OUTSET_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_OUTSET_PIN0_Msk (0x1UL << GPIO_OUTSET_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_OUTSET_PIN0_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTSET_PIN0_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTSET_PIN0_Set (1UL) /*!< Write: writing a '1' sets the pin high; writing a '0' has no effect */

/* Register: GPIO_OUTCLR */
/* Description: Clear individual bits in GPIO port */

/* Bit 31 : Pin 31 */
#define GPIO_OUTCLR_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_OUTCLR_PIN31_Msk (0x1UL << GPIO_OUTCLR_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_OUTCLR_PIN31_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN31_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN31_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 30 : Pin 30 */
#define GPIO_OUTCLR_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_OUTCLR_PIN30_Msk (0x1UL << GPIO_OUTCLR_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_OUTCLR_PIN30_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN30_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN30_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 29 : Pin 29 */
#define GPIO_OUTCLR_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_OUTCLR_PIN29_Msk (0x1UL << GPIO_OUTCLR_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_OUTCLR_PIN29_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN29_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN29_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 28 : Pin 28 */
#define GPIO_OUTCLR_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_OUTCLR_PIN28_Msk (0x1UL << GPIO_OUTCLR_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_OUTCLR_PIN28_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN28_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN28_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 27 : Pin 27 */
#define GPIO_OUTCLR_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_OUTCLR_PIN27_Msk (0x1UL << GPIO_OUTCLR_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_OUTCLR_PIN27_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN27_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN27_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 26 : Pin 26 */
#define GPIO_OUTCLR_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_OUTCLR_PIN26_Msk (0x1UL << GPIO_OUTCLR_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_OUTCLR_PIN26_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN26_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN26_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 25 : Pin 25 */
#define GPIO_OUTCLR_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_OUTCLR_PIN25_Msk (0x1UL << GPIO_OUTCLR_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_OUTCLR_PIN25_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN25_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN25_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 24 : Pin 24 */
#define GPIO_OUTCLR_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_OUTCLR_PIN24_Msk (0x1UL << GPIO_OUTCLR_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_OUTCLR_PIN24_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN24_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN24_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 23 : Pin 23 */
#define GPIO_OUTCLR_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_OUTCLR_PIN23_Msk (0x1UL << GPIO_OUTCLR_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_OUTCLR_PIN23_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN23_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN23_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 22 : Pin 22 */
#define GPIO_OUTCLR_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_OUTCLR_PIN22_Msk (0x1UL << GPIO_OUTCLR_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_OUTCLR_PIN22_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN22_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN22_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 21 : Pin 21 */
#define GPIO_OUTCLR_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_OUTCLR_PIN21_Msk (0x1UL << GPIO_OUTCLR_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_OUTCLR_PIN21_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN21_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN21_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 20 : Pin 20 */
#define GPIO_OUTCLR_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_OUTCLR_PIN20_Msk (0x1UL << GPIO_OUTCLR_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_OUTCLR_PIN20_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN20_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN20_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 19 : Pin 19 */
#define GPIO_OUTCLR_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_OUTCLR_PIN19_Msk (0x1UL << GPIO_OUTCLR_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_OUTCLR_PIN19_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN19_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN19_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 18 : Pin 18 */
#define GPIO_OUTCLR_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_OUTCLR_PIN18_Msk (0x1UL << GPIO_OUTCLR_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_OUTCLR_PIN18_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN18_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN18_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 17 : Pin 17 */
#define GPIO_OUTCLR_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_OUTCLR_PIN17_Msk (0x1UL << GPIO_OUTCLR_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_OUTCLR_PIN17_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN17_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN17_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 16 : Pin 16 */
#define GPIO_OUTCLR_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_OUTCLR_PIN16_Msk (0x1UL << GPIO_OUTCLR_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_OUTCLR_PIN16_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN16_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN16_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 15 : Pin 15 */
#define GPIO_OUTCLR_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_OUTCLR_PIN15_Msk (0x1UL << GPIO_OUTCLR_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_OUTCLR_PIN15_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN15_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN15_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 14 : Pin 14 */
#define GPIO_OUTCLR_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_OUTCLR_PIN14_Msk (0x1UL << GPIO_OUTCLR_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_OUTCLR_PIN14_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN14_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN14_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 13 : Pin 13 */
#define GPIO_OUTCLR_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_OUTCLR_PIN13_Msk (0x1UL << GPIO_OUTCLR_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_OUTCLR_PIN13_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN13_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN13_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 12 : Pin 12 */
#define GPIO_OUTCLR_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_OUTCLR_PIN12_Msk (0x1UL << GPIO_OUTCLR_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_OUTCLR_PIN12_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN12_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN12_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 11 : Pin 11 */
#define GPIO_OUTCLR_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_OUTCLR_PIN11_Msk (0x1UL << GPIO_OUTCLR_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_OUTCLR_PIN11_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN11_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN11_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 10 : Pin 10 */
#define GPIO_OUTCLR_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_OUTCLR_PIN10_Msk (0x1UL << GPIO_OUTCLR_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_OUTCLR_PIN10_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN10_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN10_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 9 : Pin 9 */
#define GPIO_OUTCLR_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_OUTCLR_PIN9_Msk (0x1UL << GPIO_OUTCLR_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_OUTCLR_PIN9_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN9_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN9_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 8 : Pin 8 */
#define GPIO_OUTCLR_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_OUTCLR_PIN8_Msk (0x1UL << GPIO_OUTCLR_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_OUTCLR_PIN8_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN8_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN8_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 7 : Pin 7 */
#define GPIO_OUTCLR_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_OUTCLR_PIN7_Msk (0x1UL << GPIO_OUTCLR_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_OUTCLR_PIN7_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN7_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN7_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 6 : Pin 6 */
#define GPIO_OUTCLR_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_OUTCLR_PIN6_Msk (0x1UL << GPIO_OUTCLR_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_OUTCLR_PIN6_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN6_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN6_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 5 : Pin 5 */
#define GPIO_OUTCLR_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_OUTCLR_PIN5_Msk (0x1UL << GPIO_OUTCLR_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_OUTCLR_PIN5_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN5_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN5_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 4 : Pin 4 */
#define GPIO_OUTCLR_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_OUTCLR_PIN4_Msk (0x1UL << GPIO_OUTCLR_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_OUTCLR_PIN4_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN4_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN4_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 3 : Pin 3 */
#define GPIO_OUTCLR_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_OUTCLR_PIN3_Msk (0x1UL << GPIO_OUTCLR_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_OUTCLR_PIN3_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN3_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN3_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 2 : Pin 2 */
#define GPIO_OUTCLR_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_OUTCLR_PIN2_Msk (0x1UL << GPIO_OUTCLR_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_OUTCLR_PIN2_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN2_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN2_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 1 : Pin 1 */
#define GPIO_OUTCLR_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_OUTCLR_PIN1_Msk (0x1UL << GPIO_OUTCLR_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_OUTCLR_PIN1_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN1_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN1_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Bit 0 : Pin 0 */
#define GPIO_OUTCLR_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_OUTCLR_PIN0_Msk (0x1UL << GPIO_OUTCLR_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_OUTCLR_PIN0_Low (0UL) /*!< Read: pin driver is low */
#define GPIO_OUTCLR_PIN0_High (1UL) /*!< Read: pin driver is high */
#define GPIO_OUTCLR_PIN0_Clear (1UL) /*!< Write: writing a '1' sets the pin low; writing a '0' has no effect */

/* Register: GPIO_IN */
/* Description: Read GPIO port */

/* Bit 31 : Pin 31 */
#define GPIO_IN_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_IN_PIN31_Msk (0x1UL << GPIO_IN_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_IN_PIN31_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN31_High (1UL) /*!< Pin input is high */

/* Bit 30 : Pin 30 */
#define GPIO_IN_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_IN_PIN30_Msk (0x1UL << GPIO_IN_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_IN_PIN30_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN30_High (1UL) /*!< Pin input is high */

/* Bit 29 : Pin 29 */
#define GPIO_IN_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_IN_PIN29_Msk (0x1UL << GPIO_IN_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_IN_PIN29_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN29_High (1UL) /*!< Pin input is high */

/* Bit 28 : Pin 28 */
#define GPIO_IN_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_IN_PIN28_Msk (0x1UL << GPIO_IN_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_IN_PIN28_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN28_High (1UL) /*!< Pin input is high */

/* Bit 27 : Pin 27 */
#define GPIO_IN_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_IN_PIN27_Msk (0x1UL << GPIO_IN_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_IN_PIN27_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN27_High (1UL) /*!< Pin input is high */

/* Bit 26 : Pin 26 */
#define GPIO_IN_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_IN_PIN26_Msk (0x1UL << GPIO_IN_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_IN_PIN26_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN26_High (1UL) /*!< Pin input is high */

/* Bit 25 : Pin 25 */
#define GPIO_IN_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_IN_PIN25_Msk (0x1UL << GPIO_IN_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_IN_PIN25_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN25_High (1UL) /*!< Pin input is high */

/* Bit 24 : Pin 24 */
#define GPIO_IN_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_IN_PIN24_Msk (0x1UL << GPIO_IN_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_IN_PIN24_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN24_High (1UL) /*!< Pin input is high */

/* Bit 23 : Pin 23 */
#define GPIO_IN_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_IN_PIN23_Msk (0x1UL << GPIO_IN_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_IN_PIN23_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN23_High (1UL) /*!< Pin input is high */

/* Bit 22 : Pin 22 */
#define GPIO_IN_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_IN_PIN22_Msk (0x1UL << GPIO_IN_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_IN_PIN22_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN22_High (1UL) /*!< Pin input is high */

/* Bit 21 : Pin 21 */
#define GPIO_IN_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_IN_PIN21_Msk (0x1UL << GPIO_IN_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_IN_PIN21_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN21_High (1UL) /*!< Pin input is high */

/* Bit 20 : Pin 20 */
#define GPIO_IN_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_IN_PIN20_Msk (0x1UL << GPIO_IN_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_IN_PIN20_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN20_High (1UL) /*!< Pin input is high */

/* Bit 19 : Pin 19 */
#define GPIO_IN_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_IN_PIN19_Msk (0x1UL << GPIO_IN_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_IN_PIN19_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN19_High (1UL) /*!< Pin input is high */

/* Bit 18 : Pin 18 */
#define GPIO_IN_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_IN_PIN18_Msk (0x1UL << GPIO_IN_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_IN_PIN18_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN18_High (1UL) /*!< Pin input is high */

/* Bit 17 : Pin 17 */
#define GPIO_IN_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_IN_PIN17_Msk (0x1UL << GPIO_IN_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_IN_PIN17_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN17_High (1UL) /*!< Pin input is high */

/* Bit 16 : Pin 16 */
#define GPIO_IN_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_IN_PIN16_Msk (0x1UL << GPIO_IN_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_IN_PIN16_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN16_High (1UL) /*!< Pin input is high */

/* Bit 15 : Pin 15 */
#define GPIO_IN_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_IN_PIN15_Msk (0x1UL << GPIO_IN_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_IN_PIN15_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN15_High (1UL) /*!< Pin input is high */

/* Bit 14 : Pin 14 */
#define GPIO_IN_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_IN_PIN14_Msk (0x1UL << GPIO_IN_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_IN_PIN14_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN14_High (1UL) /*!< Pin input is high */

/* Bit 13 : Pin 13 */
#define GPIO_IN_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_IN_PIN13_Msk (0x1UL << GPIO_IN_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_IN_PIN13_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN13_High (1UL) /*!< Pin input is high */

/* Bit 12 : Pin 12 */
#define GPIO_IN_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_IN_PIN12_Msk (0x1UL << GPIO_IN_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_IN_PIN12_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN12_High (1UL) /*!< Pin input is high */

/* Bit 11 : Pin 11 */
#define GPIO_IN_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_IN_PIN11_Msk (0x1UL << GPIO_IN_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_IN_PIN11_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN11_High (1UL) /*!< Pin input is high */

/* Bit 10 : Pin 10 */
#define GPIO_IN_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_IN_PIN10_Msk (0x1UL << GPIO_IN_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_IN_PIN10_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN10_High (1UL) /*!< Pin input is high */

/* Bit 9 : Pin 9 */
#define GPIO_IN_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_IN_PIN9_Msk (0x1UL << GPIO_IN_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_IN_PIN9_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN9_High (1UL) /*!< Pin input is high */

/* Bit 8 : Pin 8 */
#define GPIO_IN_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_IN_PIN8_Msk (0x1UL << GPIO_IN_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_IN_PIN8_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN8_High (1UL) /*!< Pin input is high */

/* Bit 7 : Pin 7 */
#define GPIO_IN_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_IN_PIN7_Msk (0x1UL << GPIO_IN_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_IN_PIN7_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN7_High (1UL) /*!< Pin input is high */

/* Bit 6 : Pin 6 */
#define GPIO_IN_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_IN_PIN6_Msk (0x1UL << GPIO_IN_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_IN_PIN6_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN6_High (1UL) /*!< Pin input is high */

/* Bit 5 : Pin 5 */
#define GPIO_IN_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_IN_PIN5_Msk (0x1UL << GPIO_IN_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_IN_PIN5_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN5_High (1UL) /*!< Pin input is high */

/* Bit 4 : Pin 4 */
#define GPIO_IN_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_IN_PIN4_Msk (0x1UL << GPIO_IN_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_IN_PIN4_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN4_High (1UL) /*!< Pin input is high */

/* Bit 3 : Pin 3 */
#define GPIO_IN_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_IN_PIN3_Msk (0x1UL << GPIO_IN_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_IN_PIN3_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN3_High (1UL) /*!< Pin input is high */

/* Bit 2 : Pin 2 */
#define GPIO_IN_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_IN_PIN2_Msk (0x1UL << GPIO_IN_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_IN_PIN2_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN2_High (1UL) /*!< Pin input is high */

/* Bit 1 : Pin 1 */
#define GPIO_IN_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_IN_PIN1_Msk (0x1UL << GPIO_IN_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_IN_PIN1_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN1_High (1UL) /*!< Pin input is high */

/* Bit 0 : Pin 0 */
#define GPIO_IN_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_IN_PIN0_Msk (0x1UL << GPIO_IN_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_IN_PIN0_Low (0UL) /*!< Pin input is low */
#define GPIO_IN_PIN0_High (1UL) /*!< Pin input is high */

/* Register: GPIO_DIR */
/* Description: Direction of GPIO pins */

/* Bit 31 : Pin 31 */
#define GPIO_DIR_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_DIR_PIN31_Msk (0x1UL << GPIO_DIR_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_DIR_PIN31_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN31_Output (1UL) /*!< Pin set as output */

/* Bit 30 : Pin 30 */
#define GPIO_DIR_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_DIR_PIN30_Msk (0x1UL << GPIO_DIR_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_DIR_PIN30_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN30_Output (1UL) /*!< Pin set as output */

/* Bit 29 : Pin 29 */
#define GPIO_DIR_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_DIR_PIN29_Msk (0x1UL << GPIO_DIR_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_DIR_PIN29_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN29_Output (1UL) /*!< Pin set as output */

/* Bit 28 : Pin 28 */
#define GPIO_DIR_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_DIR_PIN28_Msk (0x1UL << GPIO_DIR_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_DIR_PIN28_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN28_Output (1UL) /*!< Pin set as output */

/* Bit 27 : Pin 27 */
#define GPIO_DIR_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_DIR_PIN27_Msk (0x1UL << GPIO_DIR_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_DIR_PIN27_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN27_Output (1UL) /*!< Pin set as output */

/* Bit 26 : Pin 26 */
#define GPIO_DIR_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_DIR_PIN26_Msk (0x1UL << GPIO_DIR_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_DIR_PIN26_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN26_Output (1UL) /*!< Pin set as output */

/* Bit 25 : Pin 25 */
#define GPIO_DIR_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_DIR_PIN25_Msk (0x1UL << GPIO_DIR_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_DIR_PIN25_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN25_Output (1UL) /*!< Pin set as output */

/* Bit 24 : Pin 24 */
#define GPIO_DIR_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_DIR_PIN24_Msk (0x1UL << GPIO_DIR_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_DIR_PIN24_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN24_Output (1UL) /*!< Pin set as output */

/* Bit 23 : Pin 23 */
#define GPIO_DIR_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_DIR_PIN23_Msk (0x1UL << GPIO_DIR_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_DIR_PIN23_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN23_Output (1UL) /*!< Pin set as output */

/* Bit 22 : Pin 22 */
#define GPIO_DIR_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_DIR_PIN22_Msk (0x1UL << GPIO_DIR_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_DIR_PIN22_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN22_Output (1UL) /*!< Pin set as output */

/* Bit 21 : Pin 21 */
#define GPIO_DIR_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_DIR_PIN21_Msk (0x1UL << GPIO_DIR_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_DIR_PIN21_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN21_Output (1UL) /*!< Pin set as output */

/* Bit 20 : Pin 20 */
#define GPIO_DIR_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_DIR_PIN20_Msk (0x1UL << GPIO_DIR_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_DIR_PIN20_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN20_Output (1UL) /*!< Pin set as output */

/* Bit 19 : Pin 19 */
#define GPIO_DIR_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_DIR_PIN19_Msk (0x1UL << GPIO_DIR_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_DIR_PIN19_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN19_Output (1UL) /*!< Pin set as output */

/* Bit 18 : Pin 18 */
#define GPIO_DIR_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_DIR_PIN18_Msk (0x1UL << GPIO_DIR_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_DIR_PIN18_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN18_Output (1UL) /*!< Pin set as output */

/* Bit 17 : Pin 17 */
#define GPIO_DIR_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_DIR_PIN17_Msk (0x1UL << GPIO_DIR_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_DIR_PIN17_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN17_Output (1UL) /*!< Pin set as output */

/* Bit 16 : Pin 16 */
#define GPIO_DIR_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_DIR_PIN16_Msk (0x1UL << GPIO_DIR_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_DIR_PIN16_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN16_Output (1UL) /*!< Pin set as output */

/* Bit 15 : Pin 15 */
#define GPIO_DIR_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_DIR_PIN15_Msk (0x1UL << GPIO_DIR_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_DIR_PIN15_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN15_Output (1UL) /*!< Pin set as output */

/* Bit 14 : Pin 14 */
#define GPIO_DIR_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_DIR_PIN14_Msk (0x1UL << GPIO_DIR_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_DIR_PIN14_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN14_Output (1UL) /*!< Pin set as output */

/* Bit 13 : Pin 13 */
#define GPIO_DIR_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_DIR_PIN13_Msk (0x1UL << GPIO_DIR_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_DIR_PIN13_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN13_Output (1UL) /*!< Pin set as output */

/* Bit 12 : Pin 12 */
#define GPIO_DIR_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_DIR_PIN12_Msk (0x1UL << GPIO_DIR_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_DIR_PIN12_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN12_Output (1UL) /*!< Pin set as output */

/* Bit 11 : Pin 11 */
#define GPIO_DIR_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_DIR_PIN11_Msk (0x1UL << GPIO_DIR_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_DIR_PIN11_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN11_Output (1UL) /*!< Pin set as output */

/* Bit 10 : Pin 10 */
#define GPIO_DIR_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_DIR_PIN10_Msk (0x1UL << GPIO_DIR_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_DIR_PIN10_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN10_Output (1UL) /*!< Pin set as output */

/* Bit 9 : Pin 9 */
#define GPIO_DIR_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_DIR_PIN9_Msk (0x1UL << GPIO_DIR_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_DIR_PIN9_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN9_Output (1UL) /*!< Pin set as output */

/* Bit 8 : Pin 8 */
#define GPIO_DIR_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_DIR_PIN8_Msk (0x1UL << GPIO_DIR_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_DIR_PIN8_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN8_Output (1UL) /*!< Pin set as output */

/* Bit 7 : Pin 7 */
#define GPIO_DIR_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_DIR_PIN7_Msk (0x1UL << GPIO_DIR_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_DIR_PIN7_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN7_Output (1UL) /*!< Pin set as output */

/* Bit 6 : Pin 6 */
#define GPIO_DIR_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_DIR_PIN6_Msk (0x1UL << GPIO_DIR_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_DIR_PIN6_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN6_Output (1UL) /*!< Pin set as output */

/* Bit 5 : Pin 5 */
#define GPIO_DIR_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_DIR_PIN5_Msk (0x1UL << GPIO_DIR_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_DIR_PIN5_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN5_Output (1UL) /*!< Pin set as output */

/* Bit 4 : Pin 4 */
#define GPIO_DIR_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_DIR_PIN4_Msk (0x1UL << GPIO_DIR_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_DIR_PIN4_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN4_Output (1UL) /*!< Pin set as output */

/* Bit 3 : Pin 3 */
#define GPIO_DIR_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_DIR_PIN3_Msk (0x1UL << GPIO_DIR_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_DIR_PIN3_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN3_Output (1UL) /*!< Pin set as output */

/* Bit 2 : Pin 2 */
#define GPIO_DIR_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_DIR_PIN2_Msk (0x1UL << GPIO_DIR_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_DIR_PIN2_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN2_Output (1UL) /*!< Pin set as output */

/* Bit 1 : Pin 1 */
#define GPIO_DIR_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_DIR_PIN1_Msk (0x1UL << GPIO_DIR_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_DIR_PIN1_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN1_Output (1UL) /*!< Pin set as output */

/* Bit 0 : Pin 0 */
#define GPIO_DIR_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_DIR_PIN0_Msk (0x1UL << GPIO_DIR_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_DIR_PIN0_Input (0UL) /*!< Pin set as input */
#define GPIO_DIR_PIN0_Output (1UL) /*!< Pin set as output */

/* Register: GPIO_DIRSET */
/* Description: DIR set register */

/* Bit 31 : Set as output pin 31 */
#define GPIO_DIRSET_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_DIRSET_PIN31_Msk (0x1UL << GPIO_DIRSET_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_DIRSET_PIN31_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN31_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN31_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 30 : Set as output pin 30 */
#define GPIO_DIRSET_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_DIRSET_PIN30_Msk (0x1UL << GPIO_DIRSET_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_DIRSET_PIN30_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN30_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN30_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 29 : Set as output pin 29 */
#define GPIO_DIRSET_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_DIRSET_PIN29_Msk (0x1UL << GPIO_DIRSET_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_DIRSET_PIN29_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN29_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN29_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 28 : Set as output pin 28 */
#define GPIO_DIRSET_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_DIRSET_PIN28_Msk (0x1UL << GPIO_DIRSET_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_DIRSET_PIN28_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN28_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN28_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 27 : Set as output pin 27 */
#define GPIO_DIRSET_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_DIRSET_PIN27_Msk (0x1UL << GPIO_DIRSET_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_DIRSET_PIN27_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN27_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN27_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 26 : Set as output pin 26 */
#define GPIO_DIRSET_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_DIRSET_PIN26_Msk (0x1UL << GPIO_DIRSET_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_DIRSET_PIN26_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN26_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN26_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 25 : Set as output pin 25 */
#define GPIO_DIRSET_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_DIRSET_PIN25_Msk (0x1UL << GPIO_DIRSET_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_DIRSET_PIN25_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN25_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN25_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 24 : Set as output pin 24 */
#define GPIO_DIRSET_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_DIRSET_PIN24_Msk (0x1UL << GPIO_DIRSET_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_DIRSET_PIN24_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN24_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN24_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 23 : Set as output pin 23 */
#define GPIO_DIRSET_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_DIRSET_PIN23_Msk (0x1UL << GPIO_DIRSET_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_DIRSET_PIN23_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN23_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN23_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 22 : Set as output pin 22 */
#define GPIO_DIRSET_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_DIRSET_PIN22_Msk (0x1UL << GPIO_DIRSET_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_DIRSET_PIN22_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN22_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN22_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 21 : Set as output pin 21 */
#define GPIO_DIRSET_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_DIRSET_PIN21_Msk (0x1UL << GPIO_DIRSET_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_DIRSET_PIN21_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN21_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN21_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 20 : Set as output pin 20 */
#define GPIO_DIRSET_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_DIRSET_PIN20_Msk (0x1UL << GPIO_DIRSET_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_DIRSET_PIN20_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN20_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN20_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 19 : Set as output pin 19 */
#define GPIO_DIRSET_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_DIRSET_PIN19_Msk (0x1UL << GPIO_DIRSET_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_DIRSET_PIN19_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN19_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN19_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 18 : Set as output pin 18 */
#define GPIO_DIRSET_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_DIRSET_PIN18_Msk (0x1UL << GPIO_DIRSET_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_DIRSET_PIN18_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN18_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN18_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 17 : Set as output pin 17 */
#define GPIO_DIRSET_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_DIRSET_PIN17_Msk (0x1UL << GPIO_DIRSET_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_DIRSET_PIN17_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN17_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN17_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 16 : Set as output pin 16 */
#define GPIO_DIRSET_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_DIRSET_PIN16_Msk (0x1UL << GPIO_DIRSET_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_DIRSET_PIN16_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN16_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN16_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 15 : Set as output pin 15 */
#define GPIO_DIRSET_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_DIRSET_PIN15_Msk (0x1UL << GPIO_DIRSET_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_DIRSET_PIN15_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN15_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN15_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 14 : Set as output pin 14 */
#define GPIO_DIRSET_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_DIRSET_PIN14_Msk (0x1UL << GPIO_DIRSET_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_DIRSET_PIN14_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN14_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN14_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 13 : Set as output pin 13 */
#define GPIO_DIRSET_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_DIRSET_PIN13_Msk (0x1UL << GPIO_DIRSET_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_DIRSET_PIN13_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN13_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN13_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 12 : Set as output pin 12 */
#define GPIO_DIRSET_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_DIRSET_PIN12_Msk (0x1UL << GPIO_DIRSET_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_DIRSET_PIN12_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN12_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN12_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 11 : Set as output pin 11 */
#define GPIO_DIRSET_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_DIRSET_PIN11_Msk (0x1UL << GPIO_DIRSET_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_DIRSET_PIN11_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN11_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN11_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 10 : Set as output pin 10 */
#define GPIO_DIRSET_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_DIRSET_PIN10_Msk (0x1UL << GPIO_DIRSET_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_DIRSET_PIN10_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN10_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN10_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 9 : Set as output pin 9 */
#define GPIO_DIRSET_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_DIRSET_PIN9_Msk (0x1UL << GPIO_DIRSET_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_DIRSET_PIN9_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN9_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN9_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 8 : Set as output pin 8 */
#define GPIO_DIRSET_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_DIRSET_PIN8_Msk (0x1UL << GPIO_DIRSET_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_DIRSET_PIN8_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN8_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN8_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 7 : Set as output pin 7 */
#define GPIO_DIRSET_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_DIRSET_PIN7_Msk (0x1UL << GPIO_DIRSET_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_DIRSET_PIN7_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN7_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN7_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 6 : Set as output pin 6 */
#define GPIO_DIRSET_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_DIRSET_PIN6_Msk (0x1UL << GPIO_DIRSET_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_DIRSET_PIN6_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN6_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN6_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 5 : Set as output pin 5 */
#define GPIO_DIRSET_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_DIRSET_PIN5_Msk (0x1UL << GPIO_DIRSET_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_DIRSET_PIN5_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN5_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN5_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 4 : Set as output pin 4 */
#define GPIO_DIRSET_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_DIRSET_PIN4_Msk (0x1UL << GPIO_DIRSET_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_DIRSET_PIN4_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN4_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN4_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 3 : Set as output pin 3 */
#define GPIO_DIRSET_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_DIRSET_PIN3_Msk (0x1UL << GPIO_DIRSET_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_DIRSET_PIN3_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN3_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN3_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 2 : Set as output pin 2 */
#define GPIO_DIRSET_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_DIRSET_PIN2_Msk (0x1UL << GPIO_DIRSET_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_DIRSET_PIN2_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN2_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN2_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 1 : Set as output pin 1 */
#define GPIO_DIRSET_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_DIRSET_PIN1_Msk (0x1UL << GPIO_DIRSET_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_DIRSET_PIN1_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN1_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN1_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Bit 0 : Set as output pin 0 */
#define GPIO_DIRSET_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_DIRSET_PIN0_Msk (0x1UL << GPIO_DIRSET_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_DIRSET_PIN0_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRSET_PIN0_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRSET_PIN0_Set (1UL) /*!< Write: writing a '1' sets pin to output; writing a '0' has no effect */

/* Register: GPIO_DIRCLR */
/* Description: DIR clear register */

/* Bit 31 : Set as input pin 31 */
#define GPIO_DIRCLR_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_DIRCLR_PIN31_Msk (0x1UL << GPIO_DIRCLR_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_DIRCLR_PIN31_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN31_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN31_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 30 : Set as input pin 30 */
#define GPIO_DIRCLR_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_DIRCLR_PIN30_Msk (0x1UL << GPIO_DIRCLR_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_DIRCLR_PIN30_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN30_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN30_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 29 : Set as input pin 29 */
#define GPIO_DIRCLR_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_DIRCLR_PIN29_Msk (0x1UL << GPIO_DIRCLR_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_DIRCLR_PIN29_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN29_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN29_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 28 : Set as input pin 28 */
#define GPIO_DIRCLR_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_DIRCLR_PIN28_Msk (0x1UL << GPIO_DIRCLR_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_DIRCLR_PIN28_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN28_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN28_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 27 : Set as input pin 27 */
#define GPIO_DIRCLR_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_DIRCLR_PIN27_Msk (0x1UL << GPIO_DIRCLR_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_DIRCLR_PIN27_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN27_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN27_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 26 : Set as input pin 26 */
#define GPIO_DIRCLR_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_DIRCLR_PIN26_Msk (0x1UL << GPIO_DIRCLR_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_DIRCLR_PIN26_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN26_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN26_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 25 : Set as input pin 25 */
#define GPIO_DIRCLR_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_DIRCLR_PIN25_Msk (0x1UL << GPIO_DIRCLR_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_DIRCLR_PIN25_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN25_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN25_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 24 : Set as input pin 24 */
#define GPIO_DIRCLR_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_DIRCLR_PIN24_Msk (0x1UL << GPIO_DIRCLR_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_DIRCLR_PIN24_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN24_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN24_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 23 : Set as input pin 23 */
#define GPIO_DIRCLR_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_DIRCLR_PIN23_Msk (0x1UL << GPIO_DIRCLR_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_DIRCLR_PIN23_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN23_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN23_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 22 : Set as input pin 22 */
#define GPIO_DIRCLR_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_DIRCLR_PIN22_Msk (0x1UL << GPIO_DIRCLR_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_DIRCLR_PIN22_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN22_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN22_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 21 : Set as input pin 21 */
#define GPIO_DIRCLR_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_DIRCLR_PIN21_Msk (0x1UL << GPIO_DIRCLR_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_DIRCLR_PIN21_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN21_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN21_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 20 : Set as input pin 20 */
#define GPIO_DIRCLR_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_DIRCLR_PIN20_Msk (0x1UL << GPIO_DIRCLR_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_DIRCLR_PIN20_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN20_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN20_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 19 : Set as input pin 19 */
#define GPIO_DIRCLR_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_DIRCLR_PIN19_Msk (0x1UL << GPIO_DIRCLR_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_DIRCLR_PIN19_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN19_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN19_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 18 : Set as input pin 18 */
#define GPIO_DIRCLR_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_DIRCLR_PIN18_Msk (0x1UL << GPIO_DIRCLR_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_DIRCLR_PIN18_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN18_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN18_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 17 : Set as input pin 17 */
#define GPIO_DIRCLR_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_DIRCLR_PIN17_Msk (0x1UL << GPIO_DIRCLR_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_DIRCLR_PIN17_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN17_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN17_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 16 : Set as input pin 16 */
#define GPIO_DIRCLR_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_DIRCLR_PIN16_Msk (0x1UL << GPIO_DIRCLR_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_DIRCLR_PIN16_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN16_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN16_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 15 : Set as input pin 15 */
#define GPIO_DIRCLR_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_DIRCLR_PIN15_Msk (0x1UL << GPIO_DIRCLR_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_DIRCLR_PIN15_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN15_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN15_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 14 : Set as input pin 14 */
#define GPIO_DIRCLR_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_DIRCLR_PIN14_Msk (0x1UL << GPIO_DIRCLR_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_DIRCLR_PIN14_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN14_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN14_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 13 : Set as input pin 13 */
#define GPIO_DIRCLR_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_DIRCLR_PIN13_Msk (0x1UL << GPIO_DIRCLR_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_DIRCLR_PIN13_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN13_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN13_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 12 : Set as input pin 12 */
#define GPIO_DIRCLR_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_DIRCLR_PIN12_Msk (0x1UL << GPIO_DIRCLR_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_DIRCLR_PIN12_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN12_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN12_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 11 : Set as input pin 11 */
#define GPIO_DIRCLR_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_DIRCLR_PIN11_Msk (0x1UL << GPIO_DIRCLR_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_DIRCLR_PIN11_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN11_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN11_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 10 : Set as input pin 10 */
#define GPIO_DIRCLR_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_DIRCLR_PIN10_Msk (0x1UL << GPIO_DIRCLR_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_DIRCLR_PIN10_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN10_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN10_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 9 : Set as input pin 9 */
#define GPIO_DIRCLR_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_DIRCLR_PIN9_Msk (0x1UL << GPIO_DIRCLR_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_DIRCLR_PIN9_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN9_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN9_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 8 : Set as input pin 8 */
#define GPIO_DIRCLR_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_DIRCLR_PIN8_Msk (0x1UL << GPIO_DIRCLR_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_DIRCLR_PIN8_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN8_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN8_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 7 : Set as input pin 7 */
#define GPIO_DIRCLR_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_DIRCLR_PIN7_Msk (0x1UL << GPIO_DIRCLR_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_DIRCLR_PIN7_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN7_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN7_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 6 : Set as input pin 6 */
#define GPIO_DIRCLR_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_DIRCLR_PIN6_Msk (0x1UL << GPIO_DIRCLR_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_DIRCLR_PIN6_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN6_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN6_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 5 : Set as input pin 5 */
#define GPIO_DIRCLR_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_DIRCLR_PIN5_Msk (0x1UL << GPIO_DIRCLR_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_DIRCLR_PIN5_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN5_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN5_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 4 : Set as input pin 4 */
#define GPIO_DIRCLR_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_DIRCLR_PIN4_Msk (0x1UL << GPIO_DIRCLR_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_DIRCLR_PIN4_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN4_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN4_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 3 : Set as input pin 3 */
#define GPIO_DIRCLR_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_DIRCLR_PIN3_Msk (0x1UL << GPIO_DIRCLR_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_DIRCLR_PIN3_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN3_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN3_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 2 : Set as input pin 2 */
#define GPIO_DIRCLR_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_DIRCLR_PIN2_Msk (0x1UL << GPIO_DIRCLR_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_DIRCLR_PIN2_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN2_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN2_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 1 : Set as input pin 1 */
#define GPIO_DIRCLR_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_DIRCLR_PIN1_Msk (0x1UL << GPIO_DIRCLR_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_DIRCLR_PIN1_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN1_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN1_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Bit 0 : Set as input pin 0 */
#define GPIO_DIRCLR_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_DIRCLR_PIN0_Msk (0x1UL << GPIO_DIRCLR_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_DIRCLR_PIN0_Input (0UL) /*!< Read: pin set as input */
#define GPIO_DIRCLR_PIN0_Output (1UL) /*!< Read: pin set as output */
#define GPIO_DIRCLR_PIN0_Clear (1UL) /*!< Write: writing a '1' sets pin to input; writing a '0' has no effect */

/* Register: GPIO_LATCH */
/* Description: Latch register indicating what GPIO pins that have met the criteria set in the PIN_CNF[n].SENSE registers */

/* Bit 31 : Status on whether PIN[31] has met criteria set in PIN_CNF[31].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN31_Pos (31UL) /*!< Position of PIN31 field. */
#define GPIO_LATCH_PIN31_Msk (0x1UL << GPIO_LATCH_PIN31_Pos) /*!< Bit mask of PIN31 field. */
#define GPIO_LATCH_PIN31_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN31_Latched (1UL) /*!< Criteria has been met */

/* Bit 30 : Status on whether PIN[30] has met criteria set in PIN_CNF[30].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN30_Pos (30UL) /*!< Position of PIN30 field. */
#define GPIO_LATCH_PIN30_Msk (0x1UL << GPIO_LATCH_PIN30_Pos) /*!< Bit mask of PIN30 field. */
#define GPIO_LATCH_PIN30_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN30_Latched (1UL) /*!< Criteria has been met */

/* Bit 29 : Status on whether PIN[29] has met criteria set in PIN_CNF[29].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN29_Pos (29UL) /*!< Position of PIN29 field. */
#define GPIO_LATCH_PIN29_Msk (0x1UL << GPIO_LATCH_PIN29_Pos) /*!< Bit mask of PIN29 field. */
#define GPIO_LATCH_PIN29_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN29_Latched (1UL) /*!< Criteria has been met */

/* Bit 28 : Status on whether PIN[28] has met criteria set in PIN_CNF[28].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN28_Pos (28UL) /*!< Position of PIN28 field. */
#define GPIO_LATCH_PIN28_Msk (0x1UL << GPIO_LATCH_PIN28_Pos) /*!< Bit mask of PIN28 field. */
#define GPIO_LATCH_PIN28_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN28_Latched (1UL) /*!< Criteria has been met */

/* Bit 27 : Status on whether PIN[27] has met criteria set in PIN_CNF[27].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN27_Pos (27UL) /*!< Position of PIN27 field. */
#define GPIO_LATCH_PIN27_Msk (0x1UL << GPIO_LATCH_PIN27_Pos) /*!< Bit mask of PIN27 field. */
#define GPIO_LATCH_PIN27_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN27_Latched (1UL) /*!< Criteria has been met */

/* Bit 26 : Status on whether PIN[26] has met criteria set in PIN_CNF[26].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN26_Pos (26UL) /*!< Position of PIN26 field. */
#define GPIO_LATCH_PIN26_Msk (0x1UL << GPIO_LATCH_PIN26_Pos) /*!< Bit mask of PIN26 field. */
#define GPIO_LATCH_PIN26_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN26_Latched (1UL) /*!< Criteria has been met */

/* Bit 25 : Status on whether PIN[25] has met criteria set in PIN_CNF[25].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN25_Pos (25UL) /*!< Position of PIN25 field. */
#define GPIO_LATCH_PIN25_Msk (0x1UL << GPIO_LATCH_PIN25_Pos) /*!< Bit mask of PIN25 field. */
#define GPIO_LATCH_PIN25_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN25_Latched (1UL) /*!< Criteria has been met */

/* Bit 24 : Status on whether PIN[24] has met criteria set in PIN_CNF[24].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN24_Pos (24UL) /*!< Position of PIN24 field. */
#define GPIO_LATCH_PIN24_Msk (0x1UL << GPIO_LATCH_PIN24_Pos) /*!< Bit mask of PIN24 field. */
#define GPIO_LATCH_PIN24_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN24_Latched (1UL) /*!< Criteria has been met */

/* Bit 23 : Status on whether PIN[23] has met criteria set in PIN_CNF[23].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN23_Pos (23UL) /*!< Position of PIN23 field. */
#define GPIO_LATCH_PIN23_Msk (0x1UL << GPIO_LATCH_PIN23_Pos) /*!< Bit mask of PIN23 field. */
#define GPIO_LATCH_PIN23_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN23_Latched (1UL) /*!< Criteria has been met */

/* Bit 22 : Status on whether PIN[22] has met criteria set in PIN_CNF[22].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN22_Pos (22UL) /*!< Position of PIN22 field. */
#define GPIO_LATCH_PIN22_Msk (0x1UL << GPIO_LATCH_PIN22_Pos) /*!< Bit mask of PIN22 field. */
#define GPIO_LATCH_PIN22_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN22_Latched (1UL) /*!< Criteria has been met */

/* Bit 21 : Status on whether PIN[21] has met criteria set in PIN_CNF[21].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN21_Pos (21UL) /*!< Position of PIN21 field. */
#define GPIO_LATCH_PIN21_Msk (0x1UL << GPIO_LATCH_PIN21_Pos) /*!< Bit mask of PIN21 field. */
#define GPIO_LATCH_PIN21_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN21_Latched (1UL) /*!< Criteria has been met */

/* Bit 20 : Status on whether PIN[20] has met criteria set in PIN_CNF[20].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN20_Pos (20UL) /*!< Position of PIN20 field. */
#define GPIO_LATCH_PIN20_Msk (0x1UL << GPIO_LATCH_PIN20_Pos) /*!< Bit mask of PIN20 field. */
#define GPIO_LATCH_PIN20_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN20_Latched (1UL) /*!< Criteria has been met */

/* Bit 19 : Status on whether PIN[19] has met criteria set in PIN_CNF[19].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN19_Pos (19UL) /*!< Position of PIN19 field. */
#define GPIO_LATCH_PIN19_Msk (0x1UL << GPIO_LATCH_PIN19_Pos) /*!< Bit mask of PIN19 field. */
#define GPIO_LATCH_PIN19_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN19_Latched (1UL) /*!< Criteria has been met */

/* Bit 18 : Status on whether PIN[18] has met criteria set in PIN_CNF[18].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN18_Pos (18UL) /*!< Position of PIN18 field. */
#define GPIO_LATCH_PIN18_Msk (0x1UL << GPIO_LATCH_PIN18_Pos) /*!< Bit mask of PIN18 field. */
#define GPIO_LATCH_PIN18_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN18_Latched (1UL) /*!< Criteria has been met */

/* Bit 17 : Status on whether PIN[17] has met criteria set in PIN_CNF[17].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN17_Pos (17UL) /*!< Position of PIN17 field. */
#define GPIO_LATCH_PIN17_Msk (0x1UL << GPIO_LATCH_PIN17_Pos) /*!< Bit mask of PIN17 field. */
#define GPIO_LATCH_PIN17_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN17_Latched (1UL) /*!< Criteria has been met */

/* Bit 16 : Status on whether PIN[16] has met criteria set in PIN_CNF[16].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN16_Pos (16UL) /*!< Position of PIN16 field. */
#define GPIO_LATCH_PIN16_Msk (0x1UL << GPIO_LATCH_PIN16_Pos) /*!< Bit mask of PIN16 field. */
#define GPIO_LATCH_PIN16_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN16_Latched (1UL) /*!< Criteria has been met */

/* Bit 15 : Status on whether PIN[15] has met criteria set in PIN_CNF[15].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN15_Pos (15UL) /*!< Position of PIN15 field. */
#define GPIO_LATCH_PIN15_Msk (0x1UL << GPIO_LATCH_PIN15_Pos) /*!< Bit mask of PIN15 field. */
#define GPIO_LATCH_PIN15_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN15_Latched (1UL) /*!< Criteria has been met */

/* Bit 14 : Status on whether PIN[14] has met criteria set in PIN_CNF[14].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN14_Pos (14UL) /*!< Position of PIN14 field. */
#define GPIO_LATCH_PIN14_Msk (0x1UL << GPIO_LATCH_PIN14_Pos) /*!< Bit mask of PIN14 field. */
#define GPIO_LATCH_PIN14_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN14_Latched (1UL) /*!< Criteria has been met */

/* Bit 13 : Status on whether PIN[13] has met criteria set in PIN_CNF[13].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN13_Pos (13UL) /*!< Position of PIN13 field. */
#define GPIO_LATCH_PIN13_Msk (0x1UL << GPIO_LATCH_PIN13_Pos) /*!< Bit mask of PIN13 field. */
#define GPIO_LATCH_PIN13_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN13_Latched (1UL) /*!< Criteria has been met */

/* Bit 12 : Status on whether PIN[12] has met criteria set in PIN_CNF[12].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN12_Pos (12UL) /*!< Position of PIN12 field. */
#define GPIO_LATCH_PIN12_Msk (0x1UL << GPIO_LATCH_PIN12_Pos) /*!< Bit mask of PIN12 field. */
#define GPIO_LATCH_PIN12_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN12_Latched (1UL) /*!< Criteria has been met */

/* Bit 11 : Status on whether PIN[11] has met criteria set in PIN_CNF[11].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN11_Pos (11UL) /*!< Position of PIN11 field. */
#define GPIO_LATCH_PIN11_Msk (0x1UL << GPIO_LATCH_PIN11_Pos) /*!< Bit mask of PIN11 field. */
#define GPIO_LATCH_PIN11_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN11_Latched (1UL) /*!< Criteria has been met */

/* Bit 10 : Status on whether PIN[10] has met criteria set in PIN_CNF[10].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN10_Pos (10UL) /*!< Position of PIN10 field. */
#define GPIO_LATCH_PIN10_Msk (0x1UL << GPIO_LATCH_PIN10_Pos) /*!< Bit mask of PIN10 field. */
#define GPIO_LATCH_PIN10_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN10_Latched (1UL) /*!< Criteria has been met */

/* Bit 9 : Status on whether PIN[9] has met criteria set in PIN_CNF[9].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN9_Pos (9UL) /*!< Position of PIN9 field. */
#define GPIO_LATCH_PIN9_Msk (0x1UL << GPIO_LATCH_PIN9_Pos) /*!< Bit mask of PIN9 field. */
#define GPIO_LATCH_PIN9_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN9_Latched (1UL) /*!< Criteria has been met */

/* Bit 8 : Status on whether PIN[8] has met criteria set in PIN_CNF[8].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN8_Pos (8UL) /*!< Position of PIN8 field. */
#define GPIO_LATCH_PIN8_Msk (0x1UL << GPIO_LATCH_PIN8_Pos) /*!< Bit mask of PIN8 field. */
#define GPIO_LATCH_PIN8_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN8_Latched (1UL) /*!< Criteria has been met */

/* Bit 7 : Status on whether PIN[7] has met criteria set in PIN_CNF[7].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN7_Pos (7UL) /*!< Position of PIN7 field. */
#define GPIO_LATCH_PIN7_Msk (0x1UL << GPIO_LATCH_PIN7_Pos) /*!< Bit mask of PIN7 field. */
#define GPIO_LATCH_PIN7_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN7_Latched (1UL) /*!< Criteria has been met */

/* Bit 6 : Status on whether PIN[6] has met criteria set in PIN_CNF[6].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN6_Pos (6UL) /*!< Position of PIN6 field. */
#define GPIO_LATCH_PIN6_Msk (0x1UL << GPIO_LATCH_PIN6_Pos) /*!< Bit mask of PIN6 field. */
#define GPIO_LATCH_PIN6_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN6_Latched (1UL) /*!< Criteria has been met */

/* Bit 5 : Status on whether PIN[5] has met criteria set in PIN_CNF[5].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN5_Pos (5UL) /*!< Position of PIN5 field. */
#define GPIO_LATCH_PIN5_Msk (0x1UL << GPIO_LATCH_PIN5_Pos) /*!< Bit mask of PIN5 field. */
#define GPIO_LATCH_PIN5_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN5_Latched (1UL) /*!< Criteria has been met */

/* Bit 4 : Status on whether PIN[4] has met criteria set in PIN_CNF[4].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN4_Pos (4UL) /*!< Position of PIN4 field. */
#define GPIO_LATCH_PIN4_Msk (0x1UL << GPIO_LATCH_PIN4_Pos) /*!< Bit mask of PIN4 field. */
#define GPIO_LATCH_PIN4_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN4_Latched (1UL) /*!< Criteria has been met */

/* Bit 3 : Status on whether PIN[3] has met criteria set in PIN_CNF[3].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN3_Pos (3UL) /*!< Position of PIN3 field. */
#define GPIO_LATCH_PIN3_Msk (0x1UL << GPIO_LATCH_PIN3_Pos) /*!< Bit mask of PIN3 field. */
#define GPIO_LATCH_PIN3_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN3_Latched (1UL) /*!< Criteria has been met */

/* Bit 2 : Status on whether PIN[2] has met criteria set in PIN_CNF[2].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN2_Pos (2UL) /*!< Position of PIN2 field. */
#define GPIO_LATCH_PIN2_Msk (0x1UL << GPIO_LATCH_PIN2_Pos) /*!< Bit mask of PIN2 field. */
#define GPIO_LATCH_PIN2_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN2_Latched (1UL) /*!< Criteria has been met */

/* Bit 1 : Status on whether PIN[1] has met criteria set in PIN_CNF[1].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN1_Pos (1UL) /*!< Position of PIN1 field. */
#define GPIO_LATCH_PIN1_Msk (0x1UL << GPIO_LATCH_PIN1_Pos) /*!< Bit mask of PIN1 field. */
#define GPIO_LATCH_PIN1_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN1_Latched (1UL) /*!< Criteria has been met */

/* Bit 0 : Status on whether PIN[0] has met criteria set in PIN_CNF[0].SENSE register. Write '1' to clear. */
#define GPIO_LATCH_PIN0_Pos (0UL) /*!< Position of PIN0 field. */
#define GPIO_LATCH_PIN0_Msk (0x1UL << GPIO_LATCH_PIN0_Pos) /*!< Bit mask of PIN0 field. */
#define GPIO_LATCH_PIN0_NotLatched (0UL) /*!< Criteria has not been met */
#define GPIO_LATCH_PIN0_Latched (1UL) /*!< Criteria has been met */

/* Register: GPIO_DETECTMODE */
/* Description: Select between default DETECT signal behavior and LDETECT mode (For non-secure pin only) */

/* Bit 0 : Select between default DETECT signal behavior and LDETECT mode */
#define GPIO_DETECTMODE_DETECTMODE_Pos (0UL) /*!< Position of DETECTMODE field. */
#define GPIO_DETECTMODE_DETECTMODE_Msk (0x1UL << GPIO_DETECTMODE_DETECTMODE_Pos) /*!< Bit mask of DETECTMODE field. */
#define GPIO_DETECTMODE_DETECTMODE_Default (0UL) /*!< DETECT directly connected to PIN DETECT signals */
#define GPIO_DETECTMODE_DETECTMODE_LDETECT (1UL) /*!< Use the latched LDETECT behavior */

/* Register: GPIO_DETECTMODE_SEC */
/* Description: Select between default DETECT signal behavior and LDETECT mode (For secure pin only) */

/* Bit 0 : Select between default DETECT signal behavior and LDETECT mode */
#define GPIO_DETECTMODE_SEC_DETECTMODE_Pos (0UL) /*!< Position of DETECTMODE field. */
#define GPIO_DETECTMODE_SEC_DETECTMODE_Msk (0x1UL << GPIO_DETECTMODE_SEC_DETECTMODE_Pos) /*!< Bit mask of DETECTMODE field. */
#define GPIO_DETECTMODE_SEC_DETECTMODE_Default (0UL) /*!< DETECT directly connected to PIN DETECT signals */
#define GPIO_DETECTMODE_SEC_DETECTMODE_LDETECT (1UL) /*!< Use the latched LDETECT behavior */

/* Register: GPIO_PIN_CNF */
/* Description: Description collection: Configuration of GPIO pins */

/* Bits 30..28 : Select which MCU/Subsystem controls this pin Note: this field is only accessible from secure code. */
#define GPIO_PIN_CNF_MCUSEL_Pos (28UL) /*!< Position of MCUSEL field. */
#define GPIO_PIN_CNF_MCUSEL_Msk (0x7UL << GPIO_PIN_CNF_MCUSEL_Pos) /*!< Bit mask of MCUSEL field. */
#define GPIO_PIN_CNF_MCUSEL_AppMCU (0x0UL) /*!< Application MCU */
#define GPIO_PIN_CNF_MCUSEL_NetworkMCU (0x1UL) /*!< Network MCU */
#define GPIO_PIN_CNF_MCUSEL_Peripheral (0x3UL) /*!< Peripheral with dedicated pins */
#define GPIO_PIN_CNF_MCUSEL_TND (0x7UL) /*!< Trace and Debug Subsystem */

/* Bits 17..16 : Pin sensing mechanism */
#define GPIO_PIN_CNF_SENSE_Pos (16UL) /*!< Position of SENSE field. */
#define GPIO_PIN_CNF_SENSE_Msk (0x3UL << GPIO_PIN_CNF_SENSE_Pos) /*!< Bit mask of SENSE field. */
#define GPIO_PIN_CNF_SENSE_Disabled (0UL) /*!< Disabled */
#define GPIO_PIN_CNF_SENSE_High (2UL) /*!< Sense for high level */
#define GPIO_PIN_CNF_SENSE_Low (3UL) /*!< Sense for low level */

/* Bits 11..8 : Drive configuration */
#define GPIO_PIN_CNF_DRIVE_Pos (8UL) /*!< Position of DRIVE field. */
#define GPIO_PIN_CNF_DRIVE_Msk (0xFUL << GPIO_PIN_CNF_DRIVE_Pos) /*!< Bit mask of DRIVE field. */
#define GPIO_PIN_CNF_DRIVE_S0S1 (0UL) /*!< Standard '0', standard '1' */
#define GPIO_PIN_CNF_DRIVE_H0S1 (1UL) /*!< High drive '0', standard '1' */
#define GPIO_PIN_CNF_DRIVE_S0H1 (2UL) /*!< Standard '0', high drive '1' */
#define GPIO_PIN_CNF_DRIVE_H0H1 (3UL) /*!< High drive '0', high 'drive '1'' */
#define GPIO_PIN_CNF_DRIVE_D0S1 (4UL) /*!< Disconnect '0', standard '1' (normally used for wired-or connections) */
#define GPIO_PIN_CNF_DRIVE_D0H1 (5UL) /*!< Disconnect '0', high drive '1' (normally used for wired-or connections) */
#define GPIO_PIN_CNF_DRIVE_S0D1 (6UL) /*!< Standard '0', disconnect '1' (normally used for wired-and connections) */
#define GPIO_PIN_CNF_DRIVE_H0D1 (7UL) /*!< High drive '0', disconnect '1' (normally used for wired-and connections) */
#define GPIO_PIN_CNF_DRIVE_E0E1 (11UL) /*!< Extra high drive '0', extra high drive '1' */

/* Bits 3..2 : Pull configuration */
#define GPIO_PIN_CNF_PULL_Pos (2UL) /*!< Position of PULL field. */
#define GPIO_PIN_CNF_PULL_Msk (0x3UL << GPIO_PIN_CNF_PULL_Pos) /*!< Bit mask of PULL field. */
#define GPIO_PIN_CNF_PULL_Disabled (0UL) /*!< No pull */
#define GPIO_PIN_CNF_PULL_Pulldown (1UL) /*!< Pull down on pin */
#define GPIO_PIN_CNF_PULL_Pullup (3UL) /*!< Pull up on pin */

/* Bit 1 : Connect or disconnect input buffer */
#define GPIO_PIN_CNF_INPUT_Pos (1UL) /*!< Position of INPUT field. */
#define GPIO_PIN_CNF_INPUT_Msk (0x1UL << GPIO_PIN_CNF_INPUT_Pos) /*!< Bit mask of INPUT field. */
#define GPIO_PIN_CNF_INPUT_Connect (0UL) /*!< Connect input buffer */
#define GPIO_PIN_CNF_INPUT_Disconnect (1UL) /*!< Disconnect input buffer */

/* Bit 0 : Pin direction. Same physical register as DIR register */
#define GPIO_PIN_CNF_DIR_Pos (0UL) /*!< Position of DIR field. */
#define GPIO_PIN_CNF_DIR_Msk (0x1UL << GPIO_PIN_CNF_DIR_Pos) /*!< Bit mask of DIR field. */
#define GPIO_PIN_CNF_DIR_Input (0UL) /*!< Configure pin as an input pin */
#define GPIO_PIN_CNF_DIR_Output (1UL) /*!< Configure pin as an output pin */


/* Peripheral: POWER */
/* Description: Power control */

/* Register: POWER_TASKS_CONSTLAT */
/* Description: Enable Constant Latency mode */

/* Bit 0 : Enable Constant Latency mode */
#define POWER_TASKS_CONSTLAT_TASKS_CONSTLAT_Pos (0UL) /*!< Position of TASKS_CONSTLAT field. */
#define POWER_TASKS_CONSTLAT_TASKS_CONSTLAT_Msk (0x1UL << POWER_TASKS_CONSTLAT_TASKS_CONSTLAT_Pos) /*!< Bit mask of TASKS_CONSTLAT field. */
#define POWER_TASKS_CONSTLAT_TASKS_CONSTLAT_Trigger (1UL) /*!< Trigger task */

/* Register: POWER_TASKS_LOWPWR */
/* Description: Enable Low-Power mode (variable latency) */

/* Bit 0 : Enable Low-Power mode (variable latency) */
#define POWER_TASKS_LOWPWR_TASKS_LOWPWR_Pos (0UL) /*!< Position of TASKS_LOWPWR field. */
#define POWER_TASKS_LOWPWR_TASKS_LOWPWR_Msk (0x1UL << POWER_TASKS_LOWPWR_TASKS_LOWPWR_Pos) /*!< Bit mask of TASKS_LOWPWR field. */
#define POWER_TASKS_LOWPWR_TASKS_LOWPWR_Trigger (1UL) /*!< Trigger task */

/* Register: POWER_SUBSCRIBE_CONSTLAT */
/* Description: Subscribe configuration for task CONSTLAT */

/* Bit 31 :   */
#define POWER_SUBSCRIBE_CONSTLAT_EN_Pos (31UL) /*!< Position of EN field. */
#define POWER_SUBSCRIBE_CONSTLAT_EN_Msk (0x1UL << POWER_SUBSCRIBE_CONSTLAT_EN_Pos) /*!< Bit mask of EN field. */
#define POWER_SUBSCRIBE_CONSTLAT_EN_Disabled (0UL) /*!< Disable subscription */
#define POWER_SUBSCRIBE_CONSTLAT_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CONSTLAT will subscribe to */
#define POWER_SUBSCRIBE_CONSTLAT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define POWER_SUBSCRIBE_CONSTLAT_CHIDX_Msk (0xFFUL << POWER_SUBSCRIBE_CONSTLAT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: POWER_SUBSCRIBE_LOWPWR */
/* Description: Subscribe configuration for task LOWPWR */

/* Bit 31 :   */
#define POWER_SUBSCRIBE_LOWPWR_EN_Pos (31UL) /*!< Position of EN field. */
#define POWER_SUBSCRIBE_LOWPWR_EN_Msk (0x1UL << POWER_SUBSCRIBE_LOWPWR_EN_Pos) /*!< Bit mask of EN field. */
#define POWER_SUBSCRIBE_LOWPWR_EN_Disabled (0UL) /*!< Disable subscription */
#define POWER_SUBSCRIBE_LOWPWR_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task LOWPWR will subscribe to */
#define POWER_SUBSCRIBE_LOWPWR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define POWER_SUBSCRIBE_LOWPWR_CHIDX_Msk (0xFFUL << POWER_SUBSCRIBE_LOWPWR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: POWER_EVENTS_POFWARN */
/* Description: Power failure warning */

/* Bit 0 : Power failure warning */
#define POWER_EVENTS_POFWARN_EVENTS_POFWARN_Pos (0UL) /*!< Position of EVENTS_POFWARN field. */
#define POWER_EVENTS_POFWARN_EVENTS_POFWARN_Msk (0x1UL << POWER_EVENTS_POFWARN_EVENTS_POFWARN_Pos) /*!< Bit mask of EVENTS_POFWARN field. */
#define POWER_EVENTS_POFWARN_EVENTS_POFWARN_NotGenerated (0UL) /*!< Event not generated */
#define POWER_EVENTS_POFWARN_EVENTS_POFWARN_Generated (1UL) /*!< Event generated */

/* Register: POWER_EVENTS_SLEEPENTER */
/* Description: CPU entered WFI/WFE sleep */

/* Bit 0 : CPU entered WFI/WFE sleep */
#define POWER_EVENTS_SLEEPENTER_EVENTS_SLEEPENTER_Pos (0UL) /*!< Position of EVENTS_SLEEPENTER field. */
#define POWER_EVENTS_SLEEPENTER_EVENTS_SLEEPENTER_Msk (0x1UL << POWER_EVENTS_SLEEPENTER_EVENTS_SLEEPENTER_Pos) /*!< Bit mask of EVENTS_SLEEPENTER field. */
#define POWER_EVENTS_SLEEPENTER_EVENTS_SLEEPENTER_NotGenerated (0UL) /*!< Event not generated */
#define POWER_EVENTS_SLEEPENTER_EVENTS_SLEEPENTER_Generated (1UL) /*!< Event generated */

/* Register: POWER_EVENTS_SLEEPEXIT */
/* Description: CPU exited WFI/WFE sleep */

/* Bit 0 : CPU exited WFI/WFE sleep */
#define POWER_EVENTS_SLEEPEXIT_EVENTS_SLEEPEXIT_Pos (0UL) /*!< Position of EVENTS_SLEEPEXIT field. */
#define POWER_EVENTS_SLEEPEXIT_EVENTS_SLEEPEXIT_Msk (0x1UL << POWER_EVENTS_SLEEPEXIT_EVENTS_SLEEPEXIT_Pos) /*!< Bit mask of EVENTS_SLEEPEXIT field. */
#define POWER_EVENTS_SLEEPEXIT_EVENTS_SLEEPEXIT_NotGenerated (0UL) /*!< Event not generated */
#define POWER_EVENTS_SLEEPEXIT_EVENTS_SLEEPEXIT_Generated (1UL) /*!< Event generated */

/* Register: POWER_PUBLISH_POFWARN */
/* Description: Publish configuration for event POFWARN */

/* Bit 31 :   */
#define POWER_PUBLISH_POFWARN_EN_Pos (31UL) /*!< Position of EN field. */
#define POWER_PUBLISH_POFWARN_EN_Msk (0x1UL << POWER_PUBLISH_POFWARN_EN_Pos) /*!< Bit mask of EN field. */
#define POWER_PUBLISH_POFWARN_EN_Disabled (0UL) /*!< Disable publishing */
#define POWER_PUBLISH_POFWARN_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event POFWARN will publish to. */
#define POWER_PUBLISH_POFWARN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define POWER_PUBLISH_POFWARN_CHIDX_Msk (0xFFUL << POWER_PUBLISH_POFWARN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: POWER_PUBLISH_SLEEPENTER */
/* Description: Publish configuration for event SLEEPENTER */

/* Bit 31 :   */
#define POWER_PUBLISH_SLEEPENTER_EN_Pos (31UL) /*!< Position of EN field. */
#define POWER_PUBLISH_SLEEPENTER_EN_Msk (0x1UL << POWER_PUBLISH_SLEEPENTER_EN_Pos) /*!< Bit mask of EN field. */
#define POWER_PUBLISH_SLEEPENTER_EN_Disabled (0UL) /*!< Disable publishing */
#define POWER_PUBLISH_SLEEPENTER_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event SLEEPENTER will publish to. */
#define POWER_PUBLISH_SLEEPENTER_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define POWER_PUBLISH_SLEEPENTER_CHIDX_Msk (0xFFUL << POWER_PUBLISH_SLEEPENTER_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: POWER_PUBLISH_SLEEPEXIT */
/* Description: Publish configuration for event SLEEPEXIT */

/* Bit 31 :   */
#define POWER_PUBLISH_SLEEPEXIT_EN_Pos (31UL) /*!< Position of EN field. */
#define POWER_PUBLISH_SLEEPEXIT_EN_Msk (0x1UL << POWER_PUBLISH_SLEEPEXIT_EN_Pos) /*!< Bit mask of EN field. */
#define POWER_PUBLISH_SLEEPEXIT_EN_Disabled (0UL) /*!< Disable publishing */
#define POWER_PUBLISH_SLEEPEXIT_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event SLEEPEXIT will publish to. */
#define POWER_PUBLISH_SLEEPEXIT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define POWER_PUBLISH_SLEEPEXIT_CHIDX_Msk (0xFFUL << POWER_PUBLISH_SLEEPEXIT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: POWER_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 6 : Enable or disable interrupt for event SLEEPEXIT */
#define POWER_INTEN_SLEEPEXIT_Pos (6UL) /*!< Position of SLEEPEXIT field. */
#define POWER_INTEN_SLEEPEXIT_Msk (0x1UL << POWER_INTEN_SLEEPEXIT_Pos) /*!< Bit mask of SLEEPEXIT field. */
#define POWER_INTEN_SLEEPEXIT_Disabled (0UL) /*!< Disable */
#define POWER_INTEN_SLEEPEXIT_Enabled (1UL) /*!< Enable */

/* Bit 5 : Enable or disable interrupt for event SLEEPENTER */
#define POWER_INTEN_SLEEPENTER_Pos (5UL) /*!< Position of SLEEPENTER field. */
#define POWER_INTEN_SLEEPENTER_Msk (0x1UL << POWER_INTEN_SLEEPENTER_Pos) /*!< Bit mask of SLEEPENTER field. */
#define POWER_INTEN_SLEEPENTER_Disabled (0UL) /*!< Disable */
#define POWER_INTEN_SLEEPENTER_Enabled (1UL) /*!< Enable */

/* Bit 2 : Enable or disable interrupt for event POFWARN */
#define POWER_INTEN_POFWARN_Pos (2UL) /*!< Position of POFWARN field. */
#define POWER_INTEN_POFWARN_Msk (0x1UL << POWER_INTEN_POFWARN_Pos) /*!< Bit mask of POFWARN field. */
#define POWER_INTEN_POFWARN_Disabled (0UL) /*!< Disable */
#define POWER_INTEN_POFWARN_Enabled (1UL) /*!< Enable */

/* Register: POWER_INTENSET */
/* Description: Enable interrupt */

/* Bit 6 : Write '1' to enable interrupt for event SLEEPEXIT */
#define POWER_INTENSET_SLEEPEXIT_Pos (6UL) /*!< Position of SLEEPEXIT field. */
#define POWER_INTENSET_SLEEPEXIT_Msk (0x1UL << POWER_INTENSET_SLEEPEXIT_Pos) /*!< Bit mask of SLEEPEXIT field. */
#define POWER_INTENSET_SLEEPEXIT_Disabled (0UL) /*!< Read: Disabled */
#define POWER_INTENSET_SLEEPEXIT_Enabled (1UL) /*!< Read: Enabled */
#define POWER_INTENSET_SLEEPEXIT_Set (1UL) /*!< Enable */

/* Bit 5 : Write '1' to enable interrupt for event SLEEPENTER */
#define POWER_INTENSET_SLEEPENTER_Pos (5UL) /*!< Position of SLEEPENTER field. */
#define POWER_INTENSET_SLEEPENTER_Msk (0x1UL << POWER_INTENSET_SLEEPENTER_Pos) /*!< Bit mask of SLEEPENTER field. */
#define POWER_INTENSET_SLEEPENTER_Disabled (0UL) /*!< Read: Disabled */
#define POWER_INTENSET_SLEEPENTER_Enabled (1UL) /*!< Read: Enabled */
#define POWER_INTENSET_SLEEPENTER_Set (1UL) /*!< Enable */

/* Bit 2 : Write '1' to enable interrupt for event POFWARN */
#define POWER_INTENSET_POFWARN_Pos (2UL) /*!< Position of POFWARN field. */
#define POWER_INTENSET_POFWARN_Msk (0x1UL << POWER_INTENSET_POFWARN_Pos) /*!< Bit mask of POFWARN field. */
#define POWER_INTENSET_POFWARN_Disabled (0UL) /*!< Read: Disabled */
#define POWER_INTENSET_POFWARN_Enabled (1UL) /*!< Read: Enabled */
#define POWER_INTENSET_POFWARN_Set (1UL) /*!< Enable */

/* Register: POWER_INTENCLR */
/* Description: Disable interrupt */

/* Bit 6 : Write '1' to disable interrupt for event SLEEPEXIT */
#define POWER_INTENCLR_SLEEPEXIT_Pos (6UL) /*!< Position of SLEEPEXIT field. */
#define POWER_INTENCLR_SLEEPEXIT_Msk (0x1UL << POWER_INTENCLR_SLEEPEXIT_Pos) /*!< Bit mask of SLEEPEXIT field. */
#define POWER_INTENCLR_SLEEPEXIT_Disabled (0UL) /*!< Read: Disabled */
#define POWER_INTENCLR_SLEEPEXIT_Enabled (1UL) /*!< Read: Enabled */
#define POWER_INTENCLR_SLEEPEXIT_Clear (1UL) /*!< Disable */

/* Bit 5 : Write '1' to disable interrupt for event SLEEPENTER */
#define POWER_INTENCLR_SLEEPENTER_Pos (5UL) /*!< Position of SLEEPENTER field. */
#define POWER_INTENCLR_SLEEPENTER_Msk (0x1UL << POWER_INTENCLR_SLEEPENTER_Pos) /*!< Bit mask of SLEEPENTER field. */
#define POWER_INTENCLR_SLEEPENTER_Disabled (0UL) /*!< Read: Disabled */
#define POWER_INTENCLR_SLEEPENTER_Enabled (1UL) /*!< Read: Enabled */
#define POWER_INTENCLR_SLEEPENTER_Clear (1UL) /*!< Disable */

/* Bit 2 : Write '1' to disable interrupt for event POFWARN */
#define POWER_INTENCLR_POFWARN_Pos (2UL) /*!< Position of POFWARN field. */
#define POWER_INTENCLR_POFWARN_Msk (0x1UL << POWER_INTENCLR_POFWARN_Pos) /*!< Bit mask of POFWARN field. */
#define POWER_INTENCLR_POFWARN_Disabled (0UL) /*!< Read: Disabled */
#define POWER_INTENCLR_POFWARN_Enabled (1UL) /*!< Read: Enabled */
#define POWER_INTENCLR_POFWARN_Clear (1UL) /*!< Disable */

/* Register: POWER_GPREGRET */
/* Description: Description collection: General purpose retention register */

/* Bits 7..0 : General purpose retention register */
#define POWER_GPREGRET_GPREGRET_Pos (0UL) /*!< Position of GPREGRET field. */
#define POWER_GPREGRET_GPREGRET_Msk (0xFFUL << POWER_GPREGRET_GPREGRET_Pos) /*!< Bit mask of GPREGRET field. */


/* Peripheral: RADIO */
/* Description: 2.4 GHz radio */

/* Register: RADIO_TASKS_TXEN */
/* Description: Enable RADIO in TX mode */

/* Bit 0 : Enable RADIO in TX mode */
#define RADIO_TASKS_TXEN_TASKS_TXEN_Pos (0UL) /*!< Position of TASKS_TXEN field. */
#define RADIO_TASKS_TXEN_TASKS_TXEN_Msk (0x1UL << RADIO_TASKS_TXEN_TASKS_TXEN_Pos) /*!< Bit mask of TASKS_TXEN field. */
#define RADIO_TASKS_TXEN_TASKS_TXEN_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_RXEN */
/* Description: Enable RADIO in RX mode */

/* Bit 0 : Enable RADIO in RX mode */
#define RADIO_TASKS_RXEN_TASKS_RXEN_Pos (0UL) /*!< Position of TASKS_RXEN field. */
#define RADIO_TASKS_RXEN_TASKS_RXEN_Msk (0x1UL << RADIO_TASKS_RXEN_TASKS_RXEN_Pos) /*!< Bit mask of TASKS_RXEN field. */
#define RADIO_TASKS_RXEN_TASKS_RXEN_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_START */
/* Description: Start RADIO */

/* Bit 0 : Start RADIO */
#define RADIO_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define RADIO_TASKS_START_TASKS_START_Msk (0x1UL << RADIO_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define RADIO_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_STOP */
/* Description: Stop RADIO */

/* Bit 0 : Stop RADIO */
#define RADIO_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define RADIO_TASKS_STOP_TASKS_STOP_Msk (0x1UL << RADIO_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define RADIO_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_DISABLE */
/* Description: Disable RADIO */

/* Bit 0 : Disable RADIO */
#define RADIO_TASKS_DISABLE_TASKS_DISABLE_Pos (0UL) /*!< Position of TASKS_DISABLE field. */
#define RADIO_TASKS_DISABLE_TASKS_DISABLE_Msk (0x1UL << RADIO_TASKS_DISABLE_TASKS_DISABLE_Pos) /*!< Bit mask of TASKS_DISABLE field. */
#define RADIO_TASKS_DISABLE_TASKS_DISABLE_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_RSSISTART */
/* Description: Start the RSSI and take one single sample of the receive signal strength */

/* Bit 0 : Start the RSSI and take one single sample of the receive signal strength */
#define RADIO_TASKS_RSSISTART_TASKS_RSSISTART_Pos (0UL) /*!< Position of TASKS_RSSISTART field. */
#define RADIO_TASKS_RSSISTART_TASKS_RSSISTART_Msk (0x1UL << RADIO_TASKS_RSSISTART_TASKS_RSSISTART_Pos) /*!< Bit mask of TASKS_RSSISTART field. */
#define RADIO_TASKS_RSSISTART_TASKS_RSSISTART_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_RSSISTOP */
/* Description: Stop the RSSI measurement */

/* Bit 0 : Stop the RSSI measurement */
#define RADIO_TASKS_RSSISTOP_TASKS_RSSISTOP_Pos (0UL) /*!< Position of TASKS_RSSISTOP field. */
#define RADIO_TASKS_RSSISTOP_TASKS_RSSISTOP_Msk (0x1UL << RADIO_TASKS_RSSISTOP_TASKS_RSSISTOP_Pos) /*!< Bit mask of TASKS_RSSISTOP field. */
#define RADIO_TASKS_RSSISTOP_TASKS_RSSISTOP_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_BCSTART */
/* Description: Start the bit counter */

/* Bit 0 : Start the bit counter */
#define RADIO_TASKS_BCSTART_TASKS_BCSTART_Pos (0UL) /*!< Position of TASKS_BCSTART field. */
#define RADIO_TASKS_BCSTART_TASKS_BCSTART_Msk (0x1UL << RADIO_TASKS_BCSTART_TASKS_BCSTART_Pos) /*!< Bit mask of TASKS_BCSTART field. */
#define RADIO_TASKS_BCSTART_TASKS_BCSTART_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_BCSTOP */
/* Description: Stop the bit counter */

/* Bit 0 : Stop the bit counter */
#define RADIO_TASKS_BCSTOP_TASKS_BCSTOP_Pos (0UL) /*!< Position of TASKS_BCSTOP field. */
#define RADIO_TASKS_BCSTOP_TASKS_BCSTOP_Msk (0x1UL << RADIO_TASKS_BCSTOP_TASKS_BCSTOP_Pos) /*!< Bit mask of TASKS_BCSTOP field. */
#define RADIO_TASKS_BCSTOP_TASKS_BCSTOP_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_EDSTART */
/* Description: Start the energy detect measurement used in IEEE 802.15.4 mode */

/* Bit 0 : Start the energy detect measurement used in IEEE 802.15.4 mode */
#define RADIO_TASKS_EDSTART_TASKS_EDSTART_Pos (0UL) /*!< Position of TASKS_EDSTART field. */
#define RADIO_TASKS_EDSTART_TASKS_EDSTART_Msk (0x1UL << RADIO_TASKS_EDSTART_TASKS_EDSTART_Pos) /*!< Bit mask of TASKS_EDSTART field. */
#define RADIO_TASKS_EDSTART_TASKS_EDSTART_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_EDSTOP */
/* Description: Stop the energy detect measurement */

/* Bit 0 : Stop the energy detect measurement */
#define RADIO_TASKS_EDSTOP_TASKS_EDSTOP_Pos (0UL) /*!< Position of TASKS_EDSTOP field. */
#define RADIO_TASKS_EDSTOP_TASKS_EDSTOP_Msk (0x1UL << RADIO_TASKS_EDSTOP_TASKS_EDSTOP_Pos) /*!< Bit mask of TASKS_EDSTOP field. */
#define RADIO_TASKS_EDSTOP_TASKS_EDSTOP_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_CCASTART */
/* Description: Start the clear channel assessment used in IEEE 802.15.4 mode */

/* Bit 0 : Start the clear channel assessment used in IEEE 802.15.4 mode */
#define RADIO_TASKS_CCASTART_TASKS_CCASTART_Pos (0UL) /*!< Position of TASKS_CCASTART field. */
#define RADIO_TASKS_CCASTART_TASKS_CCASTART_Msk (0x1UL << RADIO_TASKS_CCASTART_TASKS_CCASTART_Pos) /*!< Bit mask of TASKS_CCASTART field. */
#define RADIO_TASKS_CCASTART_TASKS_CCASTART_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_TASKS_CCASTOP */
/* Description: Stop the clear channel assessment */

/* Bit 0 : Stop the clear channel assessment */
#define RADIO_TASKS_CCASTOP_TASKS_CCASTOP_Pos (0UL) /*!< Position of TASKS_CCASTOP field. */
#define RADIO_TASKS_CCASTOP_TASKS_CCASTOP_Msk (0x1UL << RADIO_TASKS_CCASTOP_TASKS_CCASTOP_Pos) /*!< Bit mask of TASKS_CCASTOP field. */
#define RADIO_TASKS_CCASTOP_TASKS_CCASTOP_Trigger (1UL) /*!< Trigger task */

/* Register: RADIO_SUBSCRIBE_TXEN */
/* Description: Subscribe configuration for task TXEN */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_TXEN_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_TXEN_EN_Msk (0x1UL << RADIO_SUBSCRIBE_TXEN_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_TXEN_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_TXEN_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task TXEN will subscribe to */
#define RADIO_SUBSCRIBE_TXEN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_TXEN_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_TXEN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_RXEN */
/* Description: Subscribe configuration for task RXEN */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_RXEN_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_RXEN_EN_Msk (0x1UL << RADIO_SUBSCRIBE_RXEN_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_RXEN_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_RXEN_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RXEN will subscribe to */
#define RADIO_SUBSCRIBE_RXEN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_RXEN_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_RXEN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_START_EN_Msk (0x1UL << RADIO_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define RADIO_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_STOP_EN_Msk (0x1UL << RADIO_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define RADIO_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_DISABLE */
/* Description: Subscribe configuration for task DISABLE */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_DISABLE_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_DISABLE_EN_Msk (0x1UL << RADIO_SUBSCRIBE_DISABLE_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_DISABLE_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_DISABLE_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task DISABLE will subscribe to */
#define RADIO_SUBSCRIBE_DISABLE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_DISABLE_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_DISABLE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_RSSISTART */
/* Description: Subscribe configuration for task RSSISTART */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_RSSISTART_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_RSSISTART_EN_Msk (0x1UL << RADIO_SUBSCRIBE_RSSISTART_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_RSSISTART_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_RSSISTART_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RSSISTART will subscribe to */
#define RADIO_SUBSCRIBE_RSSISTART_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_RSSISTART_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_RSSISTART_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_RSSISTOP */
/* Description: Subscribe configuration for task RSSISTOP */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_RSSISTOP_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_RSSISTOP_EN_Msk (0x1UL << RADIO_SUBSCRIBE_RSSISTOP_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_RSSISTOP_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_RSSISTOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RSSISTOP will subscribe to */
#define RADIO_SUBSCRIBE_RSSISTOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_RSSISTOP_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_RSSISTOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_BCSTART */
/* Description: Subscribe configuration for task BCSTART */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_BCSTART_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_BCSTART_EN_Msk (0x1UL << RADIO_SUBSCRIBE_BCSTART_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_BCSTART_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_BCSTART_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task BCSTART will subscribe to */
#define RADIO_SUBSCRIBE_BCSTART_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_BCSTART_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_BCSTART_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_BCSTOP */
/* Description: Subscribe configuration for task BCSTOP */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_BCSTOP_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_BCSTOP_EN_Msk (0x1UL << RADIO_SUBSCRIBE_BCSTOP_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_BCSTOP_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_BCSTOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task BCSTOP will subscribe to */
#define RADIO_SUBSCRIBE_BCSTOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_BCSTOP_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_BCSTOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_EDSTART */
/* Description: Subscribe configuration for task EDSTART */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_EDSTART_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_EDSTART_EN_Msk (0x1UL << RADIO_SUBSCRIBE_EDSTART_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_EDSTART_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_EDSTART_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task EDSTART will subscribe to */
#define RADIO_SUBSCRIBE_EDSTART_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_EDSTART_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_EDSTART_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_EDSTOP */
/* Description: Subscribe configuration for task EDSTOP */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_EDSTOP_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_EDSTOP_EN_Msk (0x1UL << RADIO_SUBSCRIBE_EDSTOP_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_EDSTOP_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_EDSTOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task EDSTOP will subscribe to */
#define RADIO_SUBSCRIBE_EDSTOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_EDSTOP_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_EDSTOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_CCASTART */
/* Description: Subscribe configuration for task CCASTART */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_CCASTART_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_CCASTART_EN_Msk (0x1UL << RADIO_SUBSCRIBE_CCASTART_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_CCASTART_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_CCASTART_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CCASTART will subscribe to */
#define RADIO_SUBSCRIBE_CCASTART_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_CCASTART_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_CCASTART_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SUBSCRIBE_CCASTOP */
/* Description: Subscribe configuration for task CCASTOP */

/* Bit 31 :   */
#define RADIO_SUBSCRIBE_CCASTOP_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_SUBSCRIBE_CCASTOP_EN_Msk (0x1UL << RADIO_SUBSCRIBE_CCASTOP_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_SUBSCRIBE_CCASTOP_EN_Disabled (0UL) /*!< Disable subscription */
#define RADIO_SUBSCRIBE_CCASTOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CCASTOP will subscribe to */
#define RADIO_SUBSCRIBE_CCASTOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_SUBSCRIBE_CCASTOP_CHIDX_Msk (0xFFUL << RADIO_SUBSCRIBE_CCASTOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_EVENTS_READY */
/* Description: RADIO has ramped up and is ready to be started */

/* Bit 0 : RADIO has ramped up and is ready to be started */
#define RADIO_EVENTS_READY_EVENTS_READY_Pos (0UL) /*!< Position of EVENTS_READY field. */
#define RADIO_EVENTS_READY_EVENTS_READY_Msk (0x1UL << RADIO_EVENTS_READY_EVENTS_READY_Pos) /*!< Bit mask of EVENTS_READY field. */
#define RADIO_EVENTS_READY_EVENTS_READY_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_READY_EVENTS_READY_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_ADDRESS */
/* Description: Address sent or received */

/* Bit 0 : Address sent or received */
#define RADIO_EVENTS_ADDRESS_EVENTS_ADDRESS_Pos (0UL) /*!< Position of EVENTS_ADDRESS field. */
#define RADIO_EVENTS_ADDRESS_EVENTS_ADDRESS_Msk (0x1UL << RADIO_EVENTS_ADDRESS_EVENTS_ADDRESS_Pos) /*!< Bit mask of EVENTS_ADDRESS field. */
#define RADIO_EVENTS_ADDRESS_EVENTS_ADDRESS_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_ADDRESS_EVENTS_ADDRESS_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_PAYLOAD */
/* Description: Packet payload sent or received */

/* Bit 0 : Packet payload sent or received */
#define RADIO_EVENTS_PAYLOAD_EVENTS_PAYLOAD_Pos (0UL) /*!< Position of EVENTS_PAYLOAD field. */
#define RADIO_EVENTS_PAYLOAD_EVENTS_PAYLOAD_Msk (0x1UL << RADIO_EVENTS_PAYLOAD_EVENTS_PAYLOAD_Pos) /*!< Bit mask of EVENTS_PAYLOAD field. */
#define RADIO_EVENTS_PAYLOAD_EVENTS_PAYLOAD_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_PAYLOAD_EVENTS_PAYLOAD_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_END */
/* Description: Packet sent or received */

/* Bit 0 : Packet sent or received */
#define RADIO_EVENTS_END_EVENTS_END_Pos (0UL) /*!< Position of EVENTS_END field. */
#define RADIO_EVENTS_END_EVENTS_END_Msk (0x1UL << RADIO_EVENTS_END_EVENTS_END_Pos) /*!< Bit mask of EVENTS_END field. */
#define RADIO_EVENTS_END_EVENTS_END_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_END_EVENTS_END_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_DISABLED */
/* Description: RADIO has been disabled */

/* Bit 0 : RADIO has been disabled */
#define RADIO_EVENTS_DISABLED_EVENTS_DISABLED_Pos (0UL) /*!< Position of EVENTS_DISABLED field. */
#define RADIO_EVENTS_DISABLED_EVENTS_DISABLED_Msk (0x1UL << RADIO_EVENTS_DISABLED_EVENTS_DISABLED_Pos) /*!< Bit mask of EVENTS_DISABLED field. */
#define RADIO_EVENTS_DISABLED_EVENTS_DISABLED_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_DISABLED_EVENTS_DISABLED_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_DEVMATCH */
/* Description: A device address match occurred on the last received packet */

/* Bit 0 : A device address match occurred on the last received packet */
#define RADIO_EVENTS_DEVMATCH_EVENTS_DEVMATCH_Pos (0UL) /*!< Position of EVENTS_DEVMATCH field. */
#define RADIO_EVENTS_DEVMATCH_EVENTS_DEVMATCH_Msk (0x1UL << RADIO_EVENTS_DEVMATCH_EVENTS_DEVMATCH_Pos) /*!< Bit mask of EVENTS_DEVMATCH field. */
#define RADIO_EVENTS_DEVMATCH_EVENTS_DEVMATCH_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_DEVMATCH_EVENTS_DEVMATCH_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_DEVMISS */
/* Description: No device address match occurred on the last received packet */

/* Bit 0 : No device address match occurred on the last received packet */
#define RADIO_EVENTS_DEVMISS_EVENTS_DEVMISS_Pos (0UL) /*!< Position of EVENTS_DEVMISS field. */
#define RADIO_EVENTS_DEVMISS_EVENTS_DEVMISS_Msk (0x1UL << RADIO_EVENTS_DEVMISS_EVENTS_DEVMISS_Pos) /*!< Bit mask of EVENTS_DEVMISS field. */
#define RADIO_EVENTS_DEVMISS_EVENTS_DEVMISS_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_DEVMISS_EVENTS_DEVMISS_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_RSSIEND */
/* Description: Sampling of receive signal strength complete */

/* Bit 0 : Sampling of receive signal strength complete */
#define RADIO_EVENTS_RSSIEND_EVENTS_RSSIEND_Pos (0UL) /*!< Position of EVENTS_RSSIEND field. */
#define RADIO_EVENTS_RSSIEND_EVENTS_RSSIEND_Msk (0x1UL << RADIO_EVENTS_RSSIEND_EVENTS_RSSIEND_Pos) /*!< Bit mask of EVENTS_RSSIEND field. */
#define RADIO_EVENTS_RSSIEND_EVENTS_RSSIEND_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_RSSIEND_EVENTS_RSSIEND_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_BCMATCH */
/* Description: Bit counter reached bit count value */

/* Bit 0 : Bit counter reached bit count value */
#define RADIO_EVENTS_BCMATCH_EVENTS_BCMATCH_Pos (0UL) /*!< Position of EVENTS_BCMATCH field. */
#define RADIO_EVENTS_BCMATCH_EVENTS_BCMATCH_Msk (0x1UL << RADIO_EVENTS_BCMATCH_EVENTS_BCMATCH_Pos) /*!< Bit mask of EVENTS_BCMATCH field. */
#define RADIO_EVENTS_BCMATCH_EVENTS_BCMATCH_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_BCMATCH_EVENTS_BCMATCH_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_CRCOK */
/* Description: Packet received with CRC ok */

/* Bit 0 : Packet received with CRC ok */
#define RADIO_EVENTS_CRCOK_EVENTS_CRCOK_Pos (0UL) /*!< Position of EVENTS_CRCOK field. */
#define RADIO_EVENTS_CRCOK_EVENTS_CRCOK_Msk (0x1UL << RADIO_EVENTS_CRCOK_EVENTS_CRCOK_Pos) /*!< Bit mask of EVENTS_CRCOK field. */
#define RADIO_EVENTS_CRCOK_EVENTS_CRCOK_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_CRCOK_EVENTS_CRCOK_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_CRCERROR */
/* Description: Packet received with CRC error */

/* Bit 0 : Packet received with CRC error */
#define RADIO_EVENTS_CRCERROR_EVENTS_CRCERROR_Pos (0UL) /*!< Position of EVENTS_CRCERROR field. */
#define RADIO_EVENTS_CRCERROR_EVENTS_CRCERROR_Msk (0x1UL << RADIO_EVENTS_CRCERROR_EVENTS_CRCERROR_Pos) /*!< Bit mask of EVENTS_CRCERROR field. */
#define RADIO_EVENTS_CRCERROR_EVENTS_CRCERROR_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_CRCERROR_EVENTS_CRCERROR_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_FRAMESTART */
/* Description: IEEE 802.15.4 length field received */

/* Bit 0 : IEEE 802.15.4 length field received */
#define RADIO_EVENTS_FRAMESTART_EVENTS_FRAMESTART_Pos (0UL) /*!< Position of EVENTS_FRAMESTART field. */
#define RADIO_EVENTS_FRAMESTART_EVENTS_FRAMESTART_Msk (0x1UL << RADIO_EVENTS_FRAMESTART_EVENTS_FRAMESTART_Pos) /*!< Bit mask of EVENTS_FRAMESTART field. */
#define RADIO_EVENTS_FRAMESTART_EVENTS_FRAMESTART_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_FRAMESTART_EVENTS_FRAMESTART_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_EDEND */
/* Description: Sampling of energy detection complete. A new ED sample is ready for readout from the RADIO.EDSAMPLE register. */

/* Bit 0 : Sampling of energy detection complete. A new ED sample is ready for readout from the RADIO.EDSAMPLE register. */
#define RADIO_EVENTS_EDEND_EVENTS_EDEND_Pos (0UL) /*!< Position of EVENTS_EDEND field. */
#define RADIO_EVENTS_EDEND_EVENTS_EDEND_Msk (0x1UL << RADIO_EVENTS_EDEND_EVENTS_EDEND_Pos) /*!< Bit mask of EVENTS_EDEND field. */
#define RADIO_EVENTS_EDEND_EVENTS_EDEND_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_EDEND_EVENTS_EDEND_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_EDSTOPPED */
/* Description: The sampling of energy detection has stopped */

/* Bit 0 : The sampling of energy detection has stopped */
#define RADIO_EVENTS_EDSTOPPED_EVENTS_EDSTOPPED_Pos (0UL) /*!< Position of EVENTS_EDSTOPPED field. */
#define RADIO_EVENTS_EDSTOPPED_EVENTS_EDSTOPPED_Msk (0x1UL << RADIO_EVENTS_EDSTOPPED_EVENTS_EDSTOPPED_Pos) /*!< Bit mask of EVENTS_EDSTOPPED field. */
#define RADIO_EVENTS_EDSTOPPED_EVENTS_EDSTOPPED_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_EDSTOPPED_EVENTS_EDSTOPPED_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_CCAIDLE */
/* Description: Wireless medium in idle - clear to send */

/* Bit 0 : Wireless medium in idle - clear to send */
#define RADIO_EVENTS_CCAIDLE_EVENTS_CCAIDLE_Pos (0UL) /*!< Position of EVENTS_CCAIDLE field. */
#define RADIO_EVENTS_CCAIDLE_EVENTS_CCAIDLE_Msk (0x1UL << RADIO_EVENTS_CCAIDLE_EVENTS_CCAIDLE_Pos) /*!< Bit mask of EVENTS_CCAIDLE field. */
#define RADIO_EVENTS_CCAIDLE_EVENTS_CCAIDLE_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_CCAIDLE_EVENTS_CCAIDLE_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_CCABUSY */
/* Description: Wireless medium busy - do not send */

/* Bit 0 : Wireless medium busy - do not send */
#define RADIO_EVENTS_CCABUSY_EVENTS_CCABUSY_Pos (0UL) /*!< Position of EVENTS_CCABUSY field. */
#define RADIO_EVENTS_CCABUSY_EVENTS_CCABUSY_Msk (0x1UL << RADIO_EVENTS_CCABUSY_EVENTS_CCABUSY_Pos) /*!< Bit mask of EVENTS_CCABUSY field. */
#define RADIO_EVENTS_CCABUSY_EVENTS_CCABUSY_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_CCABUSY_EVENTS_CCABUSY_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_CCASTOPPED */
/* Description: The CCA has stopped */

/* Bit 0 : The CCA has stopped */
#define RADIO_EVENTS_CCASTOPPED_EVENTS_CCASTOPPED_Pos (0UL) /*!< Position of EVENTS_CCASTOPPED field. */
#define RADIO_EVENTS_CCASTOPPED_EVENTS_CCASTOPPED_Msk (0x1UL << RADIO_EVENTS_CCASTOPPED_EVENTS_CCASTOPPED_Pos) /*!< Bit mask of EVENTS_CCASTOPPED field. */
#define RADIO_EVENTS_CCASTOPPED_EVENTS_CCASTOPPED_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_CCASTOPPED_EVENTS_CCASTOPPED_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_RATEBOOST */
/* Description: Ble_LR CI field received, receive mode is changed from Ble_LR125Kbit to Ble_LR500Kbit. */

/* Bit 0 : Ble_LR CI field received, receive mode is changed from Ble_LR125Kbit to Ble_LR500Kbit. */
#define RADIO_EVENTS_RATEBOOST_EVENTS_RATEBOOST_Pos (0UL) /*!< Position of EVENTS_RATEBOOST field. */
#define RADIO_EVENTS_RATEBOOST_EVENTS_RATEBOOST_Msk (0x1UL << RADIO_EVENTS_RATEBOOST_EVENTS_RATEBOOST_Pos) /*!< Bit mask of EVENTS_RATEBOOST field. */
#define RADIO_EVENTS_RATEBOOST_EVENTS_RATEBOOST_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_RATEBOOST_EVENTS_RATEBOOST_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_TXREADY */
/* Description: RADIO has ramped up and is ready to be started TX path */

/* Bit 0 : RADIO has ramped up and is ready to be started TX path */
#define RADIO_EVENTS_TXREADY_EVENTS_TXREADY_Pos (0UL) /*!< Position of EVENTS_TXREADY field. */
#define RADIO_EVENTS_TXREADY_EVENTS_TXREADY_Msk (0x1UL << RADIO_EVENTS_TXREADY_EVENTS_TXREADY_Pos) /*!< Bit mask of EVENTS_TXREADY field. */
#define RADIO_EVENTS_TXREADY_EVENTS_TXREADY_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_TXREADY_EVENTS_TXREADY_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_RXREADY */
/* Description: RADIO has ramped up and is ready to be started RX path */

/* Bit 0 : RADIO has ramped up and is ready to be started RX path */
#define RADIO_EVENTS_RXREADY_EVENTS_RXREADY_Pos (0UL) /*!< Position of EVENTS_RXREADY field. */
#define RADIO_EVENTS_RXREADY_EVENTS_RXREADY_Msk (0x1UL << RADIO_EVENTS_RXREADY_EVENTS_RXREADY_Pos) /*!< Bit mask of EVENTS_RXREADY field. */
#define RADIO_EVENTS_RXREADY_EVENTS_RXREADY_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_RXREADY_EVENTS_RXREADY_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_MHRMATCH */
/* Description: MAC header match found */

/* Bit 0 : MAC header match found */
#define RADIO_EVENTS_MHRMATCH_EVENTS_MHRMATCH_Pos (0UL) /*!< Position of EVENTS_MHRMATCH field. */
#define RADIO_EVENTS_MHRMATCH_EVENTS_MHRMATCH_Msk (0x1UL << RADIO_EVENTS_MHRMATCH_EVENTS_MHRMATCH_Pos) /*!< Bit mask of EVENTS_MHRMATCH field. */
#define RADIO_EVENTS_MHRMATCH_EVENTS_MHRMATCH_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_MHRMATCH_EVENTS_MHRMATCH_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_SYNC */
/* Description: Preamble indicator */

/* Bit 0 : Preamble indicator */
#define RADIO_EVENTS_SYNC_EVENTS_SYNC_Pos (0UL) /*!< Position of EVENTS_SYNC field. */
#define RADIO_EVENTS_SYNC_EVENTS_SYNC_Msk (0x1UL << RADIO_EVENTS_SYNC_EVENTS_SYNC_Pos) /*!< Bit mask of EVENTS_SYNC field. */
#define RADIO_EVENTS_SYNC_EVENTS_SYNC_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_SYNC_EVENTS_SYNC_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_PHYEND */
/* Description: Generated when last bit is sent on air, or received from air */

/* Bit 0 : Generated when last bit is sent on air, or received from air */
#define RADIO_EVENTS_PHYEND_EVENTS_PHYEND_Pos (0UL) /*!< Position of EVENTS_PHYEND field. */
#define RADIO_EVENTS_PHYEND_EVENTS_PHYEND_Msk (0x1UL << RADIO_EVENTS_PHYEND_EVENTS_PHYEND_Pos) /*!< Bit mask of EVENTS_PHYEND field. */
#define RADIO_EVENTS_PHYEND_EVENTS_PHYEND_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_PHYEND_EVENTS_PHYEND_Generated (1UL) /*!< Event generated */

/* Register: RADIO_EVENTS_CTEPRESENT */
/* Description: CTE is present (early warning right after receiving CTEInfo byte) */

/* Bit 0 : CTE is present (early warning right after receiving CTEInfo byte) */
#define RADIO_EVENTS_CTEPRESENT_EVENTS_CTEPRESENT_Pos (0UL) /*!< Position of EVENTS_CTEPRESENT field. */
#define RADIO_EVENTS_CTEPRESENT_EVENTS_CTEPRESENT_Msk (0x1UL << RADIO_EVENTS_CTEPRESENT_EVENTS_CTEPRESENT_Pos) /*!< Bit mask of EVENTS_CTEPRESENT field. */
#define RADIO_EVENTS_CTEPRESENT_EVENTS_CTEPRESENT_NotGenerated (0UL) /*!< Event not generated */
#define RADIO_EVENTS_CTEPRESENT_EVENTS_CTEPRESENT_Generated (1UL) /*!< Event generated */

/* Register: RADIO_PUBLISH_READY */
/* Description: Publish configuration for event READY */

/* Bit 31 :   */
#define RADIO_PUBLISH_READY_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_READY_EN_Msk (0x1UL << RADIO_PUBLISH_READY_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_READY_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_READY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event READY will publish to. */
#define RADIO_PUBLISH_READY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_READY_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_READY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_ADDRESS */
/* Description: Publish configuration for event ADDRESS */

/* Bit 31 :   */
#define RADIO_PUBLISH_ADDRESS_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_ADDRESS_EN_Msk (0x1UL << RADIO_PUBLISH_ADDRESS_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_ADDRESS_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_ADDRESS_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ADDRESS will publish to. */
#define RADIO_PUBLISH_ADDRESS_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_ADDRESS_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_ADDRESS_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_PAYLOAD */
/* Description: Publish configuration for event PAYLOAD */

/* Bit 31 :   */
#define RADIO_PUBLISH_PAYLOAD_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_PAYLOAD_EN_Msk (0x1UL << RADIO_PUBLISH_PAYLOAD_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_PAYLOAD_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_PAYLOAD_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event PAYLOAD will publish to. */
#define RADIO_PUBLISH_PAYLOAD_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_PAYLOAD_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_PAYLOAD_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_END */
/* Description: Publish configuration for event END */

/* Bit 31 :   */
#define RADIO_PUBLISH_END_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_END_EN_Msk (0x1UL << RADIO_PUBLISH_END_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_END_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_END_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event END will publish to. */
#define RADIO_PUBLISH_END_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_END_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_END_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_DISABLED */
/* Description: Publish configuration for event DISABLED */

/* Bit 31 :   */
#define RADIO_PUBLISH_DISABLED_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_DISABLED_EN_Msk (0x1UL << RADIO_PUBLISH_DISABLED_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_DISABLED_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_DISABLED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event DISABLED will publish to. */
#define RADIO_PUBLISH_DISABLED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_DISABLED_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_DISABLED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_DEVMATCH */
/* Description: Publish configuration for event DEVMATCH */

/* Bit 31 :   */
#define RADIO_PUBLISH_DEVMATCH_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_DEVMATCH_EN_Msk (0x1UL << RADIO_PUBLISH_DEVMATCH_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_DEVMATCH_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_DEVMATCH_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event DEVMATCH will publish to. */
#define RADIO_PUBLISH_DEVMATCH_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_DEVMATCH_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_DEVMATCH_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_DEVMISS */
/* Description: Publish configuration for event DEVMISS */

/* Bit 31 :   */
#define RADIO_PUBLISH_DEVMISS_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_DEVMISS_EN_Msk (0x1UL << RADIO_PUBLISH_DEVMISS_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_DEVMISS_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_DEVMISS_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event DEVMISS will publish to. */
#define RADIO_PUBLISH_DEVMISS_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_DEVMISS_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_DEVMISS_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_RSSIEND */
/* Description: Publish configuration for event RSSIEND */

/* Bit 31 :   */
#define RADIO_PUBLISH_RSSIEND_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_RSSIEND_EN_Msk (0x1UL << RADIO_PUBLISH_RSSIEND_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_RSSIEND_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_RSSIEND_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RSSIEND will publish to. */
#define RADIO_PUBLISH_RSSIEND_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_RSSIEND_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_RSSIEND_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_BCMATCH */
/* Description: Publish configuration for event BCMATCH */

/* Bit 31 :   */
#define RADIO_PUBLISH_BCMATCH_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_BCMATCH_EN_Msk (0x1UL << RADIO_PUBLISH_BCMATCH_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_BCMATCH_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_BCMATCH_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event BCMATCH will publish to. */
#define RADIO_PUBLISH_BCMATCH_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_BCMATCH_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_BCMATCH_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_CRCOK */
/* Description: Publish configuration for event CRCOK */

/* Bit 31 :   */
#define RADIO_PUBLISH_CRCOK_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_CRCOK_EN_Msk (0x1UL << RADIO_PUBLISH_CRCOK_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_CRCOK_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_CRCOK_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event CRCOK will publish to. */
#define RADIO_PUBLISH_CRCOK_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_CRCOK_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_CRCOK_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_CRCERROR */
/* Description: Publish configuration for event CRCERROR */

/* Bit 31 :   */
#define RADIO_PUBLISH_CRCERROR_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_CRCERROR_EN_Msk (0x1UL << RADIO_PUBLISH_CRCERROR_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_CRCERROR_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_CRCERROR_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event CRCERROR will publish to. */
#define RADIO_PUBLISH_CRCERROR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_CRCERROR_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_CRCERROR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_FRAMESTART */
/* Description: Publish configuration for event FRAMESTART */

/* Bit 31 :   */
#define RADIO_PUBLISH_FRAMESTART_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_FRAMESTART_EN_Msk (0x1UL << RADIO_PUBLISH_FRAMESTART_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_FRAMESTART_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_FRAMESTART_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event FRAMESTART will publish to. */
#define RADIO_PUBLISH_FRAMESTART_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_FRAMESTART_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_FRAMESTART_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_EDEND */
/* Description: Publish configuration for event EDEND */

/* Bit 31 :   */
#define RADIO_PUBLISH_EDEND_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_EDEND_EN_Msk (0x1UL << RADIO_PUBLISH_EDEND_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_EDEND_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_EDEND_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event EDEND will publish to. */
#define RADIO_PUBLISH_EDEND_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_EDEND_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_EDEND_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_EDSTOPPED */
/* Description: Publish configuration for event EDSTOPPED */

/* Bit 31 :   */
#define RADIO_PUBLISH_EDSTOPPED_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_EDSTOPPED_EN_Msk (0x1UL << RADIO_PUBLISH_EDSTOPPED_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_EDSTOPPED_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_EDSTOPPED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event EDSTOPPED will publish to. */
#define RADIO_PUBLISH_EDSTOPPED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_EDSTOPPED_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_EDSTOPPED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_CCAIDLE */
/* Description: Publish configuration for event CCAIDLE */

/* Bit 31 :   */
#define RADIO_PUBLISH_CCAIDLE_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_CCAIDLE_EN_Msk (0x1UL << RADIO_PUBLISH_CCAIDLE_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_CCAIDLE_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_CCAIDLE_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event CCAIDLE will publish to. */
#define RADIO_PUBLISH_CCAIDLE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_CCAIDLE_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_CCAIDLE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_CCABUSY */
/* Description: Publish configuration for event CCABUSY */

/* Bit 31 :   */
#define RADIO_PUBLISH_CCABUSY_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_CCABUSY_EN_Msk (0x1UL << RADIO_PUBLISH_CCABUSY_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_CCABUSY_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_CCABUSY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event CCABUSY will publish to. */
#define RADIO_PUBLISH_CCABUSY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_CCABUSY_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_CCABUSY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_CCASTOPPED */
/* Description: Publish configuration for event CCASTOPPED */

/* Bit 31 :   */
#define RADIO_PUBLISH_CCASTOPPED_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_CCASTOPPED_EN_Msk (0x1UL << RADIO_PUBLISH_CCASTOPPED_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_CCASTOPPED_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_CCASTOPPED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event CCASTOPPED will publish to. */
#define RADIO_PUBLISH_CCASTOPPED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_CCASTOPPED_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_CCASTOPPED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_RATEBOOST */
/* Description: Publish configuration for event RATEBOOST */

/* Bit 31 :   */
#define RADIO_PUBLISH_RATEBOOST_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_RATEBOOST_EN_Msk (0x1UL << RADIO_PUBLISH_RATEBOOST_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_RATEBOOST_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_RATEBOOST_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RATEBOOST will publish to. */
#define RADIO_PUBLISH_RATEBOOST_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_RATEBOOST_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_RATEBOOST_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_TXREADY */
/* Description: Publish configuration for event TXREADY */

/* Bit 31 :   */
#define RADIO_PUBLISH_TXREADY_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_TXREADY_EN_Msk (0x1UL << RADIO_PUBLISH_TXREADY_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_TXREADY_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_TXREADY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TXREADY will publish to. */
#define RADIO_PUBLISH_TXREADY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_TXREADY_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_TXREADY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_RXREADY */
/* Description: Publish configuration for event RXREADY */

/* Bit 31 :   */
#define RADIO_PUBLISH_RXREADY_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_RXREADY_EN_Msk (0x1UL << RADIO_PUBLISH_RXREADY_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_RXREADY_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_RXREADY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RXREADY will publish to. */
#define RADIO_PUBLISH_RXREADY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_RXREADY_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_RXREADY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_MHRMATCH */
/* Description: Publish configuration for event MHRMATCH */

/* Bit 31 :   */
#define RADIO_PUBLISH_MHRMATCH_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_MHRMATCH_EN_Msk (0x1UL << RADIO_PUBLISH_MHRMATCH_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_MHRMATCH_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_MHRMATCH_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event MHRMATCH will publish to. */
#define RADIO_PUBLISH_MHRMATCH_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_MHRMATCH_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_MHRMATCH_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_SYNC */
/* Description: Publish configuration for event SYNC */

/* Bit 31 :   */
#define RADIO_PUBLISH_SYNC_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_SYNC_EN_Msk (0x1UL << RADIO_PUBLISH_SYNC_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_SYNC_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_SYNC_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event SYNC will publish to. */
#define RADIO_PUBLISH_SYNC_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_SYNC_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_SYNC_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_PHYEND */
/* Description: Publish configuration for event PHYEND */

/* Bit 31 :   */
#define RADIO_PUBLISH_PHYEND_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_PHYEND_EN_Msk (0x1UL << RADIO_PUBLISH_PHYEND_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_PHYEND_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_PHYEND_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event PHYEND will publish to. */
#define RADIO_PUBLISH_PHYEND_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_PHYEND_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_PHYEND_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_PUBLISH_CTEPRESENT */
/* Description: Publish configuration for event CTEPRESENT */

/* Bit 31 :   */
#define RADIO_PUBLISH_CTEPRESENT_EN_Pos (31UL) /*!< Position of EN field. */
#define RADIO_PUBLISH_CTEPRESENT_EN_Msk (0x1UL << RADIO_PUBLISH_CTEPRESENT_EN_Pos) /*!< Bit mask of EN field. */
#define RADIO_PUBLISH_CTEPRESENT_EN_Disabled (0UL) /*!< Disable publishing */
#define RADIO_PUBLISH_CTEPRESENT_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event CTEPRESENT will publish to. */
#define RADIO_PUBLISH_CTEPRESENT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RADIO_PUBLISH_CTEPRESENT_CHIDX_Msk (0xFFUL << RADIO_PUBLISH_CTEPRESENT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RADIO_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 21 : Shortcut between event PHYEND and task START */
#define RADIO_SHORTS_PHYEND_START_Pos (21UL) /*!< Position of PHYEND_START field. */
#define RADIO_SHORTS_PHYEND_START_Msk (0x1UL << RADIO_SHORTS_PHYEND_START_Pos) /*!< Bit mask of PHYEND_START field. */
#define RADIO_SHORTS_PHYEND_START_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_PHYEND_START_Enabled (1UL) /*!< Enable shortcut */

/* Bit 20 : Shortcut between event PHYEND and task DISABLE */
#define RADIO_SHORTS_PHYEND_DISABLE_Pos (20UL) /*!< Position of PHYEND_DISABLE field. */
#define RADIO_SHORTS_PHYEND_DISABLE_Msk (0x1UL << RADIO_SHORTS_PHYEND_DISABLE_Pos) /*!< Bit mask of PHYEND_DISABLE field. */
#define RADIO_SHORTS_PHYEND_DISABLE_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_PHYEND_DISABLE_Enabled (1UL) /*!< Enable shortcut */

/* Bit 19 : Shortcut between event RXREADY and task START */
#define RADIO_SHORTS_RXREADY_START_Pos (19UL) /*!< Position of RXREADY_START field. */
#define RADIO_SHORTS_RXREADY_START_Msk (0x1UL << RADIO_SHORTS_RXREADY_START_Pos) /*!< Bit mask of RXREADY_START field. */
#define RADIO_SHORTS_RXREADY_START_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_RXREADY_START_Enabled (1UL) /*!< Enable shortcut */

/* Bit 18 : Shortcut between event TXREADY and task START */
#define RADIO_SHORTS_TXREADY_START_Pos (18UL) /*!< Position of TXREADY_START field. */
#define RADIO_SHORTS_TXREADY_START_Msk (0x1UL << RADIO_SHORTS_TXREADY_START_Pos) /*!< Bit mask of TXREADY_START field. */
#define RADIO_SHORTS_TXREADY_START_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_TXREADY_START_Enabled (1UL) /*!< Enable shortcut */

/* Bit 17 : Shortcut between event CCAIDLE and task STOP */
#define RADIO_SHORTS_CCAIDLE_STOP_Pos (17UL) /*!< Position of CCAIDLE_STOP field. */
#define RADIO_SHORTS_CCAIDLE_STOP_Msk (0x1UL << RADIO_SHORTS_CCAIDLE_STOP_Pos) /*!< Bit mask of CCAIDLE_STOP field. */
#define RADIO_SHORTS_CCAIDLE_STOP_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_CCAIDLE_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 16 : Shortcut between event EDEND and task DISABLE */
#define RADIO_SHORTS_EDEND_DISABLE_Pos (16UL) /*!< Position of EDEND_DISABLE field. */
#define RADIO_SHORTS_EDEND_DISABLE_Msk (0x1UL << RADIO_SHORTS_EDEND_DISABLE_Pos) /*!< Bit mask of EDEND_DISABLE field. */
#define RADIO_SHORTS_EDEND_DISABLE_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_EDEND_DISABLE_Enabled (1UL) /*!< Enable shortcut */

/* Bit 15 : Shortcut between event READY and task EDSTART */
#define RADIO_SHORTS_READY_EDSTART_Pos (15UL) /*!< Position of READY_EDSTART field. */
#define RADIO_SHORTS_READY_EDSTART_Msk (0x1UL << RADIO_SHORTS_READY_EDSTART_Pos) /*!< Bit mask of READY_EDSTART field. */
#define RADIO_SHORTS_READY_EDSTART_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_READY_EDSTART_Enabled (1UL) /*!< Enable shortcut */

/* Bit 14 : Shortcut between event FRAMESTART and task BCSTART */
#define RADIO_SHORTS_FRAMESTART_BCSTART_Pos (14UL) /*!< Position of FRAMESTART_BCSTART field. */
#define RADIO_SHORTS_FRAMESTART_BCSTART_Msk (0x1UL << RADIO_SHORTS_FRAMESTART_BCSTART_Pos) /*!< Bit mask of FRAMESTART_BCSTART field. */
#define RADIO_SHORTS_FRAMESTART_BCSTART_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_FRAMESTART_BCSTART_Enabled (1UL) /*!< Enable shortcut */

/* Bit 13 : Shortcut between event CCABUSY and task DISABLE */
#define RADIO_SHORTS_CCABUSY_DISABLE_Pos (13UL) /*!< Position of CCABUSY_DISABLE field. */
#define RADIO_SHORTS_CCABUSY_DISABLE_Msk (0x1UL << RADIO_SHORTS_CCABUSY_DISABLE_Pos) /*!< Bit mask of CCABUSY_DISABLE field. */
#define RADIO_SHORTS_CCABUSY_DISABLE_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_CCABUSY_DISABLE_Enabled (1UL) /*!< Enable shortcut */

/* Bit 12 : Shortcut between event CCAIDLE and task TXEN */
#define RADIO_SHORTS_CCAIDLE_TXEN_Pos (12UL) /*!< Position of CCAIDLE_TXEN field. */
#define RADIO_SHORTS_CCAIDLE_TXEN_Msk (0x1UL << RADIO_SHORTS_CCAIDLE_TXEN_Pos) /*!< Bit mask of CCAIDLE_TXEN field. */
#define RADIO_SHORTS_CCAIDLE_TXEN_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_CCAIDLE_TXEN_Enabled (1UL) /*!< Enable shortcut */

/* Bit 11 : Shortcut between event RXREADY and task CCASTART */
#define RADIO_SHORTS_RXREADY_CCASTART_Pos (11UL) /*!< Position of RXREADY_CCASTART field. */
#define RADIO_SHORTS_RXREADY_CCASTART_Msk (0x1UL << RADIO_SHORTS_RXREADY_CCASTART_Pos) /*!< Bit mask of RXREADY_CCASTART field. */
#define RADIO_SHORTS_RXREADY_CCASTART_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_RXREADY_CCASTART_Enabled (1UL) /*!< Enable shortcut */

/* Bit 8 : Shortcut between event DISABLED and task RSSISTOP */
#define RADIO_SHORTS_DISABLED_RSSISTOP_Pos (8UL) /*!< Position of DISABLED_RSSISTOP field. */
#define RADIO_SHORTS_DISABLED_RSSISTOP_Msk (0x1UL << RADIO_SHORTS_DISABLED_RSSISTOP_Pos) /*!< Bit mask of DISABLED_RSSISTOP field. */
#define RADIO_SHORTS_DISABLED_RSSISTOP_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_DISABLED_RSSISTOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 6 : Shortcut between event ADDRESS and task BCSTART */
#define RADIO_SHORTS_ADDRESS_BCSTART_Pos (6UL) /*!< Position of ADDRESS_BCSTART field. */
#define RADIO_SHORTS_ADDRESS_BCSTART_Msk (0x1UL << RADIO_SHORTS_ADDRESS_BCSTART_Pos) /*!< Bit mask of ADDRESS_BCSTART field. */
#define RADIO_SHORTS_ADDRESS_BCSTART_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_ADDRESS_BCSTART_Enabled (1UL) /*!< Enable shortcut */

/* Bit 5 : Shortcut between event END and task START */
#define RADIO_SHORTS_END_START_Pos (5UL) /*!< Position of END_START field. */
#define RADIO_SHORTS_END_START_Msk (0x1UL << RADIO_SHORTS_END_START_Pos) /*!< Bit mask of END_START field. */
#define RADIO_SHORTS_END_START_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_END_START_Enabled (1UL) /*!< Enable shortcut */

/* Bit 4 : Shortcut between event ADDRESS and task RSSISTART */
#define RADIO_SHORTS_ADDRESS_RSSISTART_Pos (4UL) /*!< Position of ADDRESS_RSSISTART field. */
#define RADIO_SHORTS_ADDRESS_RSSISTART_Msk (0x1UL << RADIO_SHORTS_ADDRESS_RSSISTART_Pos) /*!< Bit mask of ADDRESS_RSSISTART field. */
#define RADIO_SHORTS_ADDRESS_RSSISTART_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_ADDRESS_RSSISTART_Enabled (1UL) /*!< Enable shortcut */

/* Bit 3 : Shortcut between event DISABLED and task RXEN */
#define RADIO_SHORTS_DISABLED_RXEN_Pos (3UL) /*!< Position of DISABLED_RXEN field. */
#define RADIO_SHORTS_DISABLED_RXEN_Msk (0x1UL << RADIO_SHORTS_DISABLED_RXEN_Pos) /*!< Bit mask of DISABLED_RXEN field. */
#define RADIO_SHORTS_DISABLED_RXEN_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_DISABLED_RXEN_Enabled (1UL) /*!< Enable shortcut */

/* Bit 2 : Shortcut between event DISABLED and task TXEN */
#define RADIO_SHORTS_DISABLED_TXEN_Pos (2UL) /*!< Position of DISABLED_TXEN field. */
#define RADIO_SHORTS_DISABLED_TXEN_Msk (0x1UL << RADIO_SHORTS_DISABLED_TXEN_Pos) /*!< Bit mask of DISABLED_TXEN field. */
#define RADIO_SHORTS_DISABLED_TXEN_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_DISABLED_TXEN_Enabled (1UL) /*!< Enable shortcut */

/* Bit 1 : Shortcut between event END and task DISABLE */
#define RADIO_SHORTS_END_DISABLE_Pos (1UL) /*!< Position of END_DISABLE field. */
#define RADIO_SHORTS_END_DISABLE_Msk (0x1UL << RADIO_SHORTS_END_DISABLE_Pos) /*!< Bit mask of END_DISABLE field. */
#define RADIO_SHORTS_END_DISABLE_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_END_DISABLE_Enabled (1UL) /*!< Enable shortcut */

/* Bit 0 : Shortcut between event READY and task START */
#define RADIO_SHORTS_READY_START_Pos (0UL) /*!< Position of READY_START field. */
#define RADIO_SHORTS_READY_START_Msk (0x1UL << RADIO_SHORTS_READY_START_Pos) /*!< Bit mask of READY_START field. */
#define RADIO_SHORTS_READY_START_Disabled (0UL) /*!< Disable shortcut */
#define RADIO_SHORTS_READY_START_Enabled (1UL) /*!< Enable shortcut */

/* Register: RADIO_INTENSET */
/* Description: Enable interrupt */

/* Bit 28 : Write '1' to enable interrupt for event CTEPRESENT */
#define RADIO_INTENSET_CTEPRESENT_Pos (28UL) /*!< Position of CTEPRESENT field. */
#define RADIO_INTENSET_CTEPRESENT_Msk (0x1UL << RADIO_INTENSET_CTEPRESENT_Pos) /*!< Bit mask of CTEPRESENT field. */
#define RADIO_INTENSET_CTEPRESENT_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_CTEPRESENT_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_CTEPRESENT_Set (1UL) /*!< Enable */

/* Bit 27 : Write '1' to enable interrupt for event PHYEND */
#define RADIO_INTENSET_PHYEND_Pos (27UL) /*!< Position of PHYEND field. */
#define RADIO_INTENSET_PHYEND_Msk (0x1UL << RADIO_INTENSET_PHYEND_Pos) /*!< Bit mask of PHYEND field. */
#define RADIO_INTENSET_PHYEND_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_PHYEND_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_PHYEND_Set (1UL) /*!< Enable */

/* Bit 26 : Write '1' to enable interrupt for event SYNC */
#define RADIO_INTENSET_SYNC_Pos (26UL) /*!< Position of SYNC field. */
#define RADIO_INTENSET_SYNC_Msk (0x1UL << RADIO_INTENSET_SYNC_Pos) /*!< Bit mask of SYNC field. */
#define RADIO_INTENSET_SYNC_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_SYNC_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_SYNC_Set (1UL) /*!< Enable */

/* Bit 23 : Write '1' to enable interrupt for event MHRMATCH */
#define RADIO_INTENSET_MHRMATCH_Pos (23UL) /*!< Position of MHRMATCH field. */
#define RADIO_INTENSET_MHRMATCH_Msk (0x1UL << RADIO_INTENSET_MHRMATCH_Pos) /*!< Bit mask of MHRMATCH field. */
#define RADIO_INTENSET_MHRMATCH_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_MHRMATCH_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_MHRMATCH_Set (1UL) /*!< Enable */

/* Bit 22 : Write '1' to enable interrupt for event RXREADY */
#define RADIO_INTENSET_RXREADY_Pos (22UL) /*!< Position of RXREADY field. */
#define RADIO_INTENSET_RXREADY_Msk (0x1UL << RADIO_INTENSET_RXREADY_Pos) /*!< Bit mask of RXREADY field. */
#define RADIO_INTENSET_RXREADY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_RXREADY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_RXREADY_Set (1UL) /*!< Enable */

/* Bit 21 : Write '1' to enable interrupt for event TXREADY */
#define RADIO_INTENSET_TXREADY_Pos (21UL) /*!< Position of TXREADY field. */
#define RADIO_INTENSET_TXREADY_Msk (0x1UL << RADIO_INTENSET_TXREADY_Pos) /*!< Bit mask of TXREADY field. */
#define RADIO_INTENSET_TXREADY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_TXREADY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_TXREADY_Set (1UL) /*!< Enable */

/* Bit 20 : Write '1' to enable interrupt for event RATEBOOST */
#define RADIO_INTENSET_RATEBOOST_Pos (20UL) /*!< Position of RATEBOOST field. */
#define RADIO_INTENSET_RATEBOOST_Msk (0x1UL << RADIO_INTENSET_RATEBOOST_Pos) /*!< Bit mask of RATEBOOST field. */
#define RADIO_INTENSET_RATEBOOST_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_RATEBOOST_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_RATEBOOST_Set (1UL) /*!< Enable */

/* Bit 19 : Write '1' to enable interrupt for event CCASTOPPED */
#define RADIO_INTENSET_CCASTOPPED_Pos (19UL) /*!< Position of CCASTOPPED field. */
#define RADIO_INTENSET_CCASTOPPED_Msk (0x1UL << RADIO_INTENSET_CCASTOPPED_Pos) /*!< Bit mask of CCASTOPPED field. */
#define RADIO_INTENSET_CCASTOPPED_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_CCASTOPPED_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_CCASTOPPED_Set (1UL) /*!< Enable */

/* Bit 18 : Write '1' to enable interrupt for event CCABUSY */
#define RADIO_INTENSET_CCABUSY_Pos (18UL) /*!< Position of CCABUSY field. */
#define RADIO_INTENSET_CCABUSY_Msk (0x1UL << RADIO_INTENSET_CCABUSY_Pos) /*!< Bit mask of CCABUSY field. */
#define RADIO_INTENSET_CCABUSY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_CCABUSY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_CCABUSY_Set (1UL) /*!< Enable */

/* Bit 17 : Write '1' to enable interrupt for event CCAIDLE */
#define RADIO_INTENSET_CCAIDLE_Pos (17UL) /*!< Position of CCAIDLE field. */
#define RADIO_INTENSET_CCAIDLE_Msk (0x1UL << RADIO_INTENSET_CCAIDLE_Pos) /*!< Bit mask of CCAIDLE field. */
#define RADIO_INTENSET_CCAIDLE_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_CCAIDLE_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_CCAIDLE_Set (1UL) /*!< Enable */

/* Bit 16 : Write '1' to enable interrupt for event EDSTOPPED */
#define RADIO_INTENSET_EDSTOPPED_Pos (16UL) /*!< Position of EDSTOPPED field. */
#define RADIO_INTENSET_EDSTOPPED_Msk (0x1UL << RADIO_INTENSET_EDSTOPPED_Pos) /*!< Bit mask of EDSTOPPED field. */
#define RADIO_INTENSET_EDSTOPPED_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_EDSTOPPED_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_EDSTOPPED_Set (1UL) /*!< Enable */

/* Bit 15 : Write '1' to enable interrupt for event EDEND */
#define RADIO_INTENSET_EDEND_Pos (15UL) /*!< Position of EDEND field. */
#define RADIO_INTENSET_EDEND_Msk (0x1UL << RADIO_INTENSET_EDEND_Pos) /*!< Bit mask of EDEND field. */
#define RADIO_INTENSET_EDEND_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_EDEND_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_EDEND_Set (1UL) /*!< Enable */

/* Bit 14 : Write '1' to enable interrupt for event FRAMESTART */
#define RADIO_INTENSET_FRAMESTART_Pos (14UL) /*!< Position of FRAMESTART field. */
#define RADIO_INTENSET_FRAMESTART_Msk (0x1UL << RADIO_INTENSET_FRAMESTART_Pos) /*!< Bit mask of FRAMESTART field. */
#define RADIO_INTENSET_FRAMESTART_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_FRAMESTART_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_FRAMESTART_Set (1UL) /*!< Enable */

/* Bit 13 : Write '1' to enable interrupt for event CRCERROR */
#define RADIO_INTENSET_CRCERROR_Pos (13UL) /*!< Position of CRCERROR field. */
#define RADIO_INTENSET_CRCERROR_Msk (0x1UL << RADIO_INTENSET_CRCERROR_Pos) /*!< Bit mask of CRCERROR field. */
#define RADIO_INTENSET_CRCERROR_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_CRCERROR_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_CRCERROR_Set (1UL) /*!< Enable */

/* Bit 12 : Write '1' to enable interrupt for event CRCOK */
#define RADIO_INTENSET_CRCOK_Pos (12UL) /*!< Position of CRCOK field. */
#define RADIO_INTENSET_CRCOK_Msk (0x1UL << RADIO_INTENSET_CRCOK_Pos) /*!< Bit mask of CRCOK field. */
#define RADIO_INTENSET_CRCOK_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_CRCOK_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_CRCOK_Set (1UL) /*!< Enable */

/* Bit 10 : Write '1' to enable interrupt for event BCMATCH */
#define RADIO_INTENSET_BCMATCH_Pos (10UL) /*!< Position of BCMATCH field. */
#define RADIO_INTENSET_BCMATCH_Msk (0x1UL << RADIO_INTENSET_BCMATCH_Pos) /*!< Bit mask of BCMATCH field. */
#define RADIO_INTENSET_BCMATCH_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_BCMATCH_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_BCMATCH_Set (1UL) /*!< Enable */

/* Bit 7 : Write '1' to enable interrupt for event RSSIEND */
#define RADIO_INTENSET_RSSIEND_Pos (7UL) /*!< Position of RSSIEND field. */
#define RADIO_INTENSET_RSSIEND_Msk (0x1UL << RADIO_INTENSET_RSSIEND_Pos) /*!< Bit mask of RSSIEND field. */
#define RADIO_INTENSET_RSSIEND_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_RSSIEND_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_RSSIEND_Set (1UL) /*!< Enable */

/* Bit 6 : Write '1' to enable interrupt for event DEVMISS */
#define RADIO_INTENSET_DEVMISS_Pos (6UL) /*!< Position of DEVMISS field. */
#define RADIO_INTENSET_DEVMISS_Msk (0x1UL << RADIO_INTENSET_DEVMISS_Pos) /*!< Bit mask of DEVMISS field. */
#define RADIO_INTENSET_DEVMISS_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_DEVMISS_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_DEVMISS_Set (1UL) /*!< Enable */

/* Bit 5 : Write '1' to enable interrupt for event DEVMATCH */
#define RADIO_INTENSET_DEVMATCH_Pos (5UL) /*!< Position of DEVMATCH field. */
#define RADIO_INTENSET_DEVMATCH_Msk (0x1UL << RADIO_INTENSET_DEVMATCH_Pos) /*!< Bit mask of DEVMATCH field. */
#define RADIO_INTENSET_DEVMATCH_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_DEVMATCH_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_DEVMATCH_Set (1UL) /*!< Enable */

/* Bit 4 : Write '1' to enable interrupt for event DISABLED */
#define RADIO_INTENSET_DISABLED_Pos (4UL) /*!< Position of DISABLED field. */
#define RADIO_INTENSET_DISABLED_Msk (0x1UL << RADIO_INTENSET_DISABLED_Pos) /*!< Bit mask of DISABLED field. */
#define RADIO_INTENSET_DISABLED_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_DISABLED_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_DISABLED_Set (1UL) /*!< Enable */

/* Bit 3 : Write '1' to enable interrupt for event END */
#define RADIO_INTENSET_END_Pos (3UL) /*!< Position of END field. */
#define RADIO_INTENSET_END_Msk (0x1UL << RADIO_INTENSET_END_Pos) /*!< Bit mask of END field. */
#define RADIO_INTENSET_END_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_END_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_END_Set (1UL) /*!< Enable */

/* Bit 2 : Write '1' to enable interrupt for event PAYLOAD */
#define RADIO_INTENSET_PAYLOAD_Pos (2UL) /*!< Position of PAYLOAD field. */
#define RADIO_INTENSET_PAYLOAD_Msk (0x1UL << RADIO_INTENSET_PAYLOAD_Pos) /*!< Bit mask of PAYLOAD field. */
#define RADIO_INTENSET_PAYLOAD_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_PAYLOAD_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_PAYLOAD_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event ADDRESS */
#define RADIO_INTENSET_ADDRESS_Pos (1UL) /*!< Position of ADDRESS field. */
#define RADIO_INTENSET_ADDRESS_Msk (0x1UL << RADIO_INTENSET_ADDRESS_Pos) /*!< Bit mask of ADDRESS field. */
#define RADIO_INTENSET_ADDRESS_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_ADDRESS_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_ADDRESS_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event READY */
#define RADIO_INTENSET_READY_Pos (0UL) /*!< Position of READY field. */
#define RADIO_INTENSET_READY_Msk (0x1UL << RADIO_INTENSET_READY_Pos) /*!< Bit mask of READY field. */
#define RADIO_INTENSET_READY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENSET_READY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENSET_READY_Set (1UL) /*!< Enable */

/* Register: RADIO_INTENCLR */
/* Description: Disable interrupt */

/* Bit 28 : Write '1' to disable interrupt for event CTEPRESENT */
#define RADIO_INTENCLR_CTEPRESENT_Pos (28UL) /*!< Position of CTEPRESENT field. */
#define RADIO_INTENCLR_CTEPRESENT_Msk (0x1UL << RADIO_INTENCLR_CTEPRESENT_Pos) /*!< Bit mask of CTEPRESENT field. */
#define RADIO_INTENCLR_CTEPRESENT_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_CTEPRESENT_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_CTEPRESENT_Clear (1UL) /*!< Disable */

/* Bit 27 : Write '1' to disable interrupt for event PHYEND */
#define RADIO_INTENCLR_PHYEND_Pos (27UL) /*!< Position of PHYEND field. */
#define RADIO_INTENCLR_PHYEND_Msk (0x1UL << RADIO_INTENCLR_PHYEND_Pos) /*!< Bit mask of PHYEND field. */
#define RADIO_INTENCLR_PHYEND_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_PHYEND_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_PHYEND_Clear (1UL) /*!< Disable */

/* Bit 26 : Write '1' to disable interrupt for event SYNC */
#define RADIO_INTENCLR_SYNC_Pos (26UL) /*!< Position of SYNC field. */
#define RADIO_INTENCLR_SYNC_Msk (0x1UL << RADIO_INTENCLR_SYNC_Pos) /*!< Bit mask of SYNC field. */
#define RADIO_INTENCLR_SYNC_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_SYNC_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_SYNC_Clear (1UL) /*!< Disable */

/* Bit 23 : Write '1' to disable interrupt for event MHRMATCH */
#define RADIO_INTENCLR_MHRMATCH_Pos (23UL) /*!< Position of MHRMATCH field. */
#define RADIO_INTENCLR_MHRMATCH_Msk (0x1UL << RADIO_INTENCLR_MHRMATCH_Pos) /*!< Bit mask of MHRMATCH field. */
#define RADIO_INTENCLR_MHRMATCH_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_MHRMATCH_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_MHRMATCH_Clear (1UL) /*!< Disable */

/* Bit 22 : Write '1' to disable interrupt for event RXREADY */
#define RADIO_INTENCLR_RXREADY_Pos (22UL) /*!< Position of RXREADY field. */
#define RADIO_INTENCLR_RXREADY_Msk (0x1UL << RADIO_INTENCLR_RXREADY_Pos) /*!< Bit mask of RXREADY field. */
#define RADIO_INTENCLR_RXREADY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_RXREADY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_RXREADY_Clear (1UL) /*!< Disable */

/* Bit 21 : Write '1' to disable interrupt for event TXREADY */
#define RADIO_INTENCLR_TXREADY_Pos (21UL) /*!< Position of TXREADY field. */
#define RADIO_INTENCLR_TXREADY_Msk (0x1UL << RADIO_INTENCLR_TXREADY_Pos) /*!< Bit mask of TXREADY field. */
#define RADIO_INTENCLR_TXREADY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_TXREADY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_TXREADY_Clear (1UL) /*!< Disable */

/* Bit 20 : Write '1' to disable interrupt for event RATEBOOST */
#define RADIO_INTENCLR_RATEBOOST_Pos (20UL) /*!< Position of RATEBOOST field. */
#define RADIO_INTENCLR_RATEBOOST_Msk (0x1UL << RADIO_INTENCLR_RATEBOOST_Pos) /*!< Bit mask of RATEBOOST field. */
#define RADIO_INTENCLR_RATEBOOST_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_RATEBOOST_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_RATEBOOST_Clear (1UL) /*!< Disable */

/* Bit 19 : Write '1' to disable interrupt for event CCASTOPPED */
#define RADIO_INTENCLR_CCASTOPPED_Pos (19UL) /*!< Position of CCASTOPPED field. */
#define RADIO_INTENCLR_CCASTOPPED_Msk (0x1UL << RADIO_INTENCLR_CCASTOPPED_Pos) /*!< Bit mask of CCASTOPPED field. */
#define RADIO_INTENCLR_CCASTOPPED_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_CCASTOPPED_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_CCASTOPPED_Clear (1UL) /*!< Disable */

/* Bit 18 : Write '1' to disable interrupt for event CCABUSY */
#define RADIO_INTENCLR_CCABUSY_Pos (18UL) /*!< Position of CCABUSY field. */
#define RADIO_INTENCLR_CCABUSY_Msk (0x1UL << RADIO_INTENCLR_CCABUSY_Pos) /*!< Bit mask of CCABUSY field. */
#define RADIO_INTENCLR_CCABUSY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_CCABUSY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_CCABUSY_Clear (1UL) /*!< Disable */

/* Bit 17 : Write '1' to disable interrupt for event CCAIDLE */
#define RADIO_INTENCLR_CCAIDLE_Pos (17UL) /*!< Position of CCAIDLE field. */
#define RADIO_INTENCLR_CCAIDLE_Msk (0x1UL << RADIO_INTENCLR_CCAIDLE_Pos) /*!< Bit mask of CCAIDLE field. */
#define RADIO_INTENCLR_CCAIDLE_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_CCAIDLE_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_CCAIDLE_Clear (1UL) /*!< Disable */

/* Bit 16 : Write '1' to disable interrupt for event EDSTOPPED */
#define RADIO_INTENCLR_EDSTOPPED_Pos (16UL) /*!< Position of EDSTOPPED field. */
#define RADIO_INTENCLR_EDSTOPPED_Msk (0x1UL << RADIO_INTENCLR_EDSTOPPED_Pos) /*!< Bit mask of EDSTOPPED field. */
#define RADIO_INTENCLR_EDSTOPPED_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_EDSTOPPED_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_EDSTOPPED_Clear (1UL) /*!< Disable */

/* Bit 15 : Write '1' to disable interrupt for event EDEND */
#define RADIO_INTENCLR_EDEND_Pos (15UL) /*!< Position of EDEND field. */
#define RADIO_INTENCLR_EDEND_Msk (0x1UL << RADIO_INTENCLR_EDEND_Pos) /*!< Bit mask of EDEND field. */
#define RADIO_INTENCLR_EDEND_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_EDEND_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_EDEND_Clear (1UL) /*!< Disable */

/* Bit 14 : Write '1' to disable interrupt for event FRAMESTART */
#define RADIO_INTENCLR_FRAMESTART_Pos (14UL) /*!< Position of FRAMESTART field. */
#define RADIO_INTENCLR_FRAMESTART_Msk (0x1UL << RADIO_INTENCLR_FRAMESTART_Pos) /*!< Bit mask of FRAMESTART field. */
#define RADIO_INTENCLR_FRAMESTART_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_FRAMESTART_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_FRAMESTART_Clear (1UL) /*!< Disable */

/* Bit 13 : Write '1' to disable interrupt for event CRCERROR */
#define RADIO_INTENCLR_CRCERROR_Pos (13UL) /*!< Position of CRCERROR field. */
#define RADIO_INTENCLR_CRCERROR_Msk (0x1UL << RADIO_INTENCLR_CRCERROR_Pos) /*!< Bit mask of CRCERROR field. */
#define RADIO_INTENCLR_CRCERROR_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_CRCERROR_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_CRCERROR_Clear (1UL) /*!< Disable */

/* Bit 12 : Write '1' to disable interrupt for event CRCOK */
#define RADIO_INTENCLR_CRCOK_Pos (12UL) /*!< Position of CRCOK field. */
#define RADIO_INTENCLR_CRCOK_Msk (0x1UL << RADIO_INTENCLR_CRCOK_Pos) /*!< Bit mask of CRCOK field. */
#define RADIO_INTENCLR_CRCOK_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_CRCOK_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_CRCOK_Clear (1UL) /*!< Disable */

/* Bit 10 : Write '1' to disable interrupt for event BCMATCH */
#define RADIO_INTENCLR_BCMATCH_Pos (10UL) /*!< Position of BCMATCH field. */
#define RADIO_INTENCLR_BCMATCH_Msk (0x1UL << RADIO_INTENCLR_BCMATCH_Pos) /*!< Bit mask of BCMATCH field. */
#define RADIO_INTENCLR_BCMATCH_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_BCMATCH_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_BCMATCH_Clear (1UL) /*!< Disable */

/* Bit 7 : Write '1' to disable interrupt for event RSSIEND */
#define RADIO_INTENCLR_RSSIEND_Pos (7UL) /*!< Position of RSSIEND field. */
#define RADIO_INTENCLR_RSSIEND_Msk (0x1UL << RADIO_INTENCLR_RSSIEND_Pos) /*!< Bit mask of RSSIEND field. */
#define RADIO_INTENCLR_RSSIEND_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_RSSIEND_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_RSSIEND_Clear (1UL) /*!< Disable */

/* Bit 6 : Write '1' to disable interrupt for event DEVMISS */
#define RADIO_INTENCLR_DEVMISS_Pos (6UL) /*!< Position of DEVMISS field. */
#define RADIO_INTENCLR_DEVMISS_Msk (0x1UL << RADIO_INTENCLR_DEVMISS_Pos) /*!< Bit mask of DEVMISS field. */
#define RADIO_INTENCLR_DEVMISS_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_DEVMISS_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_DEVMISS_Clear (1UL) /*!< Disable */

/* Bit 5 : Write '1' to disable interrupt for event DEVMATCH */
#define RADIO_INTENCLR_DEVMATCH_Pos (5UL) /*!< Position of DEVMATCH field. */
#define RADIO_INTENCLR_DEVMATCH_Msk (0x1UL << RADIO_INTENCLR_DEVMATCH_Pos) /*!< Bit mask of DEVMATCH field. */
#define RADIO_INTENCLR_DEVMATCH_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_DEVMATCH_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_DEVMATCH_Clear (1UL) /*!< Disable */

/* Bit 4 : Write '1' to disable interrupt for event DISABLED */
#define RADIO_INTENCLR_DISABLED_Pos (4UL) /*!< Position of DISABLED field. */
#define RADIO_INTENCLR_DISABLED_Msk (0x1UL << RADIO_INTENCLR_DISABLED_Pos) /*!< Bit mask of DISABLED field. */
#define RADIO_INTENCLR_DISABLED_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_DISABLED_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_DISABLED_Clear (1UL) /*!< Disable */

/* Bit 3 : Write '1' to disable interrupt for event END */
#define RADIO_INTENCLR_END_Pos (3UL) /*!< Position of END field. */
#define RADIO_INTENCLR_END_Msk (0x1UL << RADIO_INTENCLR_END_Pos) /*!< Bit mask of END field. */
#define RADIO_INTENCLR_END_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_END_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_END_Clear (1UL) /*!< Disable */

/* Bit 2 : Write '1' to disable interrupt for event PAYLOAD */
#define RADIO_INTENCLR_PAYLOAD_Pos (2UL) /*!< Position of PAYLOAD field. */
#define RADIO_INTENCLR_PAYLOAD_Msk (0x1UL << RADIO_INTENCLR_PAYLOAD_Pos) /*!< Bit mask of PAYLOAD field. */
#define RADIO_INTENCLR_PAYLOAD_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_PAYLOAD_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_PAYLOAD_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event ADDRESS */
#define RADIO_INTENCLR_ADDRESS_Pos (1UL) /*!< Position of ADDRESS field. */
#define RADIO_INTENCLR_ADDRESS_Msk (0x1UL << RADIO_INTENCLR_ADDRESS_Pos) /*!< Bit mask of ADDRESS field. */
#define RADIO_INTENCLR_ADDRESS_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_ADDRESS_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_ADDRESS_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event READY */
#define RADIO_INTENCLR_READY_Pos (0UL) /*!< Position of READY field. */
#define RADIO_INTENCLR_READY_Msk (0x1UL << RADIO_INTENCLR_READY_Pos) /*!< Bit mask of READY field. */
#define RADIO_INTENCLR_READY_Disabled (0UL) /*!< Read: Disabled */
#define RADIO_INTENCLR_READY_Enabled (1UL) /*!< Read: Enabled */
#define RADIO_INTENCLR_READY_Clear (1UL) /*!< Disable */

/* Register: RADIO_CRCSTATUS */
/* Description: CRC status */

/* Bit 0 : CRC status of packet received */
#define RADIO_CRCSTATUS_CRCSTATUS_Pos (0UL) /*!< Position of CRCSTATUS field. */
#define RADIO_CRCSTATUS_CRCSTATUS_Msk (0x1UL << RADIO_CRCSTATUS_CRCSTATUS_Pos) /*!< Bit mask of CRCSTATUS field. */
#define RADIO_CRCSTATUS_CRCSTATUS_CRCError (0UL) /*!< Packet received with CRC error */
#define RADIO_CRCSTATUS_CRCSTATUS_CRCOk (1UL) /*!< Packet received with CRC ok */

/* Register: RADIO_RXMATCH */
/* Description: Received address */

/* Bits 2..0 : Received address */
#define RADIO_RXMATCH_RXMATCH_Pos (0UL) /*!< Position of RXMATCH field. */
#define RADIO_RXMATCH_RXMATCH_Msk (0x7UL << RADIO_RXMATCH_RXMATCH_Pos) /*!< Bit mask of RXMATCH field. */

/* Register: RADIO_RXCRC */
/* Description: CRC field of previously received packet */

/* Bits 23..0 : CRC field of previously received packet */
#define RADIO_RXCRC_RXCRC_Pos (0UL) /*!< Position of RXCRC field. */
#define RADIO_RXCRC_RXCRC_Msk (0xFFFFFFUL << RADIO_RXCRC_RXCRC_Pos) /*!< Bit mask of RXCRC field. */

/* Register: RADIO_DAI */
/* Description: Device address match index */

/* Bits 2..0 : Device address match index */
#define RADIO_DAI_DAI_Pos (0UL) /*!< Position of DAI field. */
#define RADIO_DAI_DAI_Msk (0x7UL << RADIO_DAI_DAI_Pos) /*!< Bit mask of DAI field. */

/* Register: RADIO_PDUSTAT */
/* Description: Payload status */

/* Bits 2..1 : Status on what rate packet is received with in Long Range */
#define RADIO_PDUSTAT_CISTAT_Pos (1UL) /*!< Position of CISTAT field. */
#define RADIO_PDUSTAT_CISTAT_Msk (0x3UL << RADIO_PDUSTAT_CISTAT_Pos) /*!< Bit mask of CISTAT field. */
#define RADIO_PDUSTAT_CISTAT_LR125kbit (0UL) /*!< Frame is received at 125 kbps */
#define RADIO_PDUSTAT_CISTAT_LR500kbit (1UL) /*!< Frame is received at 500 kbps */

/* Bit 0 : Status on payload length vs. PCNF1.MAXLEN */
#define RADIO_PDUSTAT_PDUSTAT_Pos (0UL) /*!< Position of PDUSTAT field. */
#define RADIO_PDUSTAT_PDUSTAT_Msk (0x1UL << RADIO_PDUSTAT_PDUSTAT_Pos) /*!< Bit mask of PDUSTAT field. */
#define RADIO_PDUSTAT_PDUSTAT_LessThan (0UL) /*!< Payload less than PCNF1.MAXLEN */
#define RADIO_PDUSTAT_PDUSTAT_GreaterThan (1UL) /*!< Payload greater than PCNF1.MAXLEN */

/* Register: RADIO_CTESTATUS */
/* Description: CTEInfo parsed from received packet */

/* Bits 7..6 : CTEType parsed from packet */
#define RADIO_CTESTATUS_CTETYPE_Pos (6UL) /*!< Position of CTETYPE field. */
#define RADIO_CTESTATUS_CTETYPE_Msk (0x3UL << RADIO_CTESTATUS_CTETYPE_Pos) /*!< Bit mask of CTETYPE field. */

/* Bit 5 : RFU parsed from packet */
#define RADIO_CTESTATUS_RFU_Pos (5UL) /*!< Position of RFU field. */
#define RADIO_CTESTATUS_RFU_Msk (0x1UL << RADIO_CTESTATUS_RFU_Pos) /*!< Bit mask of RFU field. */

/* Bits 4..0 : CTETime parsed from packet */
#define RADIO_CTESTATUS_CTETIME_Pos (0UL) /*!< Position of CTETIME field. */
#define RADIO_CTESTATUS_CTETIME_Msk (0x1FUL << RADIO_CTESTATUS_CTETIME_Pos) /*!< Bit mask of CTETIME field. */

/* Register: RADIO_DFESTATUS */
/* Description: DFE status information */

/* Bit 4 : Internal state of sampling state machine */
#define RADIO_DFESTATUS_SAMPLINGSTATE_Pos (4UL) /*!< Position of SAMPLINGSTATE field. */
#define RADIO_DFESTATUS_SAMPLINGSTATE_Msk (0x1UL << RADIO_DFESTATUS_SAMPLINGSTATE_Pos) /*!< Bit mask of SAMPLINGSTATE field. */
#define RADIO_DFESTATUS_SAMPLINGSTATE_Idle (0UL) /*!< Sampling state Idle */
#define RADIO_DFESTATUS_SAMPLINGSTATE_Sampling (1UL) /*!< Sampling state Sampling */

/* Bits 2..0 : Internal state of switching state machine */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Pos (0UL) /*!< Position of SWITCHINGSTATE field. */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Msk (0x7UL << RADIO_DFESTATUS_SWITCHINGSTATE_Pos) /*!< Bit mask of SWITCHINGSTATE field. */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Idle (0UL) /*!< Switching state Idle */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Offset (1UL) /*!< Switching state Offset */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Guard (2UL) /*!< Switching state Guard */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Ref (3UL) /*!< Switching state Ref */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Switching (4UL) /*!< Switching state Switching */
#define RADIO_DFESTATUS_SWITCHINGSTATE_Ending (5UL) /*!< Switching state Ending */

/* Register: RADIO_PACKETPTR */
/* Description: Packet pointer */

/* Bits 31..0 : Packet pointer */
#define RADIO_PACKETPTR_PACKETPTR_Pos (0UL) /*!< Position of PACKETPTR field. */
#define RADIO_PACKETPTR_PACKETPTR_Msk (0xFFFFFFFFUL << RADIO_PACKETPTR_PACKETPTR_Pos) /*!< Bit mask of PACKETPTR field. */

/* Register: RADIO_FREQUENCY */
/* Description: Frequency */

/* Bit 8 : Channel map selection */
#define RADIO_FREQUENCY_MAP_Pos (8UL) /*!< Position of MAP field. */
#define RADIO_FREQUENCY_MAP_Msk (0x1UL << RADIO_FREQUENCY_MAP_Pos) /*!< Bit mask of MAP field. */
#define RADIO_FREQUENCY_MAP_Default (0UL) /*!< Channel map between 2400 MHz and 2500 MHz */
#define RADIO_FREQUENCY_MAP_Low (1UL) /*!< Channel map between 2360 MHz and 2460 MHz */

/* Bits 6..0 : Radio channel frequency */
#define RADIO_FREQUENCY_FREQUENCY_Pos (0UL) /*!< Position of FREQUENCY field. */
#define RADIO_FREQUENCY_FREQUENCY_Msk (0x7FUL << RADIO_FREQUENCY_FREQUENCY_Pos) /*!< Bit mask of FREQUENCY field. */

/* Register: RADIO_TXPOWER */
/* Description: Output power */

/* Bits 7..0 : RADIO output power */
#define RADIO_TXPOWER_TXPOWER_Pos (0UL) /*!< Position of TXPOWER field. */
#define RADIO_TXPOWER_TXPOWER_Msk (0xFFUL << RADIO_TXPOWER_TXPOWER_Pos) /*!< Bit mask of TXPOWER field. */
#define RADIO_TXPOWER_TXPOWER_0dBm (0x0UL) /*!< 0 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg40dBm (0xD8UL) /*!< -40 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg30dBm (0xE2UL) /*!< Deprecated enumerator -  -40 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg20dBm (0xECUL) /*!< -20 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg16dBm (0xF0UL) /*!< -16 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg12dBm (0xF4UL) /*!< -12 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg8dBm (0xF8UL) /*!< -8 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg7dBm (0xF9UL) /*!< -7 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg6dBm (0xFAUL) /*!< -6 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg5dBm (0xFBUL) /*!< -5 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg4dBm (0xFCUL) /*!< -4 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg3dBm (0xFDUL) /*!< -3 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg2dBm (0xFEUL) /*!< -2 dBm */
#define RADIO_TXPOWER_TXPOWER_Neg1dBm (0xFFUL) /*!< -1 dBm */

/* Register: RADIO_MODE */
/* Description: Data rate and modulation */

/* Bits 3..0 : Radio data rate and modulation setting. The radio supports frequency-shift keying (FSK) modulation. */
#define RADIO_MODE_MODE_Pos (0UL) /*!< Position of MODE field. */
#define RADIO_MODE_MODE_Msk (0xFUL << RADIO_MODE_MODE_Pos) /*!< Bit mask of MODE field. */
#define RADIO_MODE_MODE_Nrf_1Mbit (0UL) /*!< 1 Mbps Nordic proprietary radio mode */
#define RADIO_MODE_MODE_Nrf_2Mbit (1UL) /*!< 2 Mbps Nordic proprietary radio mode */
#define RADIO_MODE_MODE_Ble_1Mbit (3UL) /*!< 1 Mbps BLE */
#define RADIO_MODE_MODE_Ble_2Mbit (4UL) /*!< 2 Mbps BLE */
#define RADIO_MODE_MODE_Ble_LR125Kbit (5UL) /*!< Long Range 125 kbps TX, 125 kbps and 500 kbps RX */
#define RADIO_MODE_MODE_Ble_LR500Kbit (6UL) /*!< Long Range 500 kbps TX, 125 kbps and 500 kbps RX */
#define RADIO_MODE_MODE_Ieee802154_250Kbit (15UL) /*!< IEEE 802.15.4-2006 250 kbps */

/* Register: RADIO_PCNF0 */
/* Description: Packet configuration register 0 */

/* Bits 30..29 : Length of TERM field in Long Range operation */
#define RADIO_PCNF0_TERMLEN_Pos (29UL) /*!< Position of TERMLEN field. */
#define RADIO_PCNF0_TERMLEN_Msk (0x3UL << RADIO_PCNF0_TERMLEN_Pos) /*!< Bit mask of TERMLEN field. */

/* Bit 26 : Indicates if LENGTH field contains CRC or not */
#define RADIO_PCNF0_CRCINC_Pos (26UL) /*!< Position of CRCINC field. */
#define RADIO_PCNF0_CRCINC_Msk (0x1UL << RADIO_PCNF0_CRCINC_Pos) /*!< Bit mask of CRCINC field. */
#define RADIO_PCNF0_CRCINC_Exclude (0UL) /*!< LENGTH does not contain CRC */
#define RADIO_PCNF0_CRCINC_Include (1UL) /*!< LENGTH includes CRC */

/* Bits 25..24 : Length of preamble on air. Decision point: TASKS_START task */
#define RADIO_PCNF0_PLEN_Pos (24UL) /*!< Position of PLEN field. */
#define RADIO_PCNF0_PLEN_Msk (0x3UL << RADIO_PCNF0_PLEN_Pos) /*!< Bit mask of PLEN field. */
#define RADIO_PCNF0_PLEN_8bit (0UL) /*!< 8-bit preamble */
#define RADIO_PCNF0_PLEN_16bit (1UL) /*!< 16-bit preamble */
#define RADIO_PCNF0_PLEN_32bitZero (2UL) /*!< 32-bit zero preamble - used for IEEE 802.15.4 */
#define RADIO_PCNF0_PLEN_LongRange (3UL) /*!< Preamble - used for Bluetooth LE Long Range */

/* Bits 23..22 : Length of code indicator - Long Range */
#define RADIO_PCNF0_CILEN_Pos (22UL) /*!< Position of CILEN field. */
#define RADIO_PCNF0_CILEN_Msk (0x3UL << RADIO_PCNF0_CILEN_Pos) /*!< Bit mask of CILEN field. */

/* Bit 20 : Include or exclude S1 field in RAM */
#define RADIO_PCNF0_S1INCL_Pos (20UL) /*!< Position of S1INCL field. */
#define RADIO_PCNF0_S1INCL_Msk (0x1UL << RADIO_PCNF0_S1INCL_Pos) /*!< Bit mask of S1INCL field. */
#define RADIO_PCNF0_S1INCL_Automatic (0UL) /*!< Include S1 field in RAM only if S1LEN &gt; 0 */
#define RADIO_PCNF0_S1INCL_Include (1UL) /*!< Always include S1 field in RAM independent of S1LEN */

/* Bits 19..16 : Length on air of S1 field in number of bits */
#define RADIO_PCNF0_S1LEN_Pos (16UL) /*!< Position of S1LEN field. */
#define RADIO_PCNF0_S1LEN_Msk (0xFUL << RADIO_PCNF0_S1LEN_Pos) /*!< Bit mask of S1LEN field. */

/* Bit 8 : Length on air of S0 field in number of bytes */
#define RADIO_PCNF0_S0LEN_Pos (8UL) /*!< Position of S0LEN field. */
#define RADIO_PCNF0_S0LEN_Msk (0x1UL << RADIO_PCNF0_S0LEN_Pos) /*!< Bit mask of S0LEN field. */

/* Bits 3..0 : Length on air of LENGTH field in number of bits */
#define RADIO_PCNF0_LFLEN_Pos (0UL) /*!< Position of LFLEN field. */
#define RADIO_PCNF0_LFLEN_Msk (0xFUL << RADIO_PCNF0_LFLEN_Pos) /*!< Bit mask of LFLEN field. */

/* Register: RADIO_PCNF1 */
/* Description: Packet configuration register 1 */

/* Bit 25 : Enable or disable packet whitening */
#define RADIO_PCNF1_WHITEEN_Pos (25UL) /*!< Position of WHITEEN field. */
#define RADIO_PCNF1_WHITEEN_Msk (0x1UL << RADIO_PCNF1_WHITEEN_Pos) /*!< Bit mask of WHITEEN field. */
#define RADIO_PCNF1_WHITEEN_Disabled (0UL) /*!< Disable */
#define RADIO_PCNF1_WHITEEN_Enabled (1UL) /*!< Enable */

/* Bit 24 : On-air endianness of packet, this applies to the S0, LENGTH, S1, and the PAYLOAD fields. */
#define RADIO_PCNF1_ENDIAN_Pos (24UL) /*!< Position of ENDIAN field. */
#define RADIO_PCNF1_ENDIAN_Msk (0x1UL << RADIO_PCNF1_ENDIAN_Pos) /*!< Bit mask of ENDIAN field. */
#define RADIO_PCNF1_ENDIAN_Little (0UL) /*!< Least significant bit on air first */
#define RADIO_PCNF1_ENDIAN_Big (1UL) /*!< Most significant bit on air first */

/* Bits 18..16 : Base address length in number of bytes */
#define RADIO_PCNF1_BALEN_Pos (16UL) /*!< Position of BALEN field. */
#define RADIO_PCNF1_BALEN_Msk (0x7UL << RADIO_PCNF1_BALEN_Pos) /*!< Bit mask of BALEN field. */

/* Bits 15..8 : Static length in number of bytes */
#define RADIO_PCNF1_STATLEN_Pos (8UL) /*!< Position of STATLEN field. */
#define RADIO_PCNF1_STATLEN_Msk (0xFFUL << RADIO_PCNF1_STATLEN_Pos) /*!< Bit mask of STATLEN field. */

/* Bits 7..0 : Maximum length of packet payload. If the packet payload is larger than MAXLEN, the radio will truncate the payload to MAXLEN. */
#define RADIO_PCNF1_MAXLEN_Pos (0UL) /*!< Position of MAXLEN field. */
#define RADIO_PCNF1_MAXLEN_Msk (0xFFUL << RADIO_PCNF1_MAXLEN_Pos) /*!< Bit mask of MAXLEN field. */

/* Register: RADIO_BASE0 */
/* Description: Base address 0 */

/* Bits 31..0 : Base address 0 */
#define RADIO_BASE0_BASE0_Pos (0UL) /*!< Position of BASE0 field. */
#define RADIO_BASE0_BASE0_Msk (0xFFFFFFFFUL << RADIO_BASE0_BASE0_Pos) /*!< Bit mask of BASE0 field. */

/* Register: RADIO_BASE1 */
/* Description: Base address 1 */

/* Bits 31..0 : Base address 1 */
#define RADIO_BASE1_BASE1_Pos (0UL) /*!< Position of BASE1 field. */
#define RADIO_BASE1_BASE1_Msk (0xFFFFFFFFUL << RADIO_BASE1_BASE1_Pos) /*!< Bit mask of BASE1 field. */

/* Register: RADIO_PREFIX0 */
/* Description: Prefixes bytes for logical addresses 0-3 */

/* Bits 31..24 : Address prefix 3. */
#define RADIO_PREFIX0_AP3_Pos (24UL) /*!< Position of AP3 field. */
#define RADIO_PREFIX0_AP3_Msk (0xFFUL << RADIO_PREFIX0_AP3_Pos) /*!< Bit mask of AP3 field. */

/* Bits 23..16 : Address prefix 2. */
#define RADIO_PREFIX0_AP2_Pos (16UL) /*!< Position of AP2 field. */
#define RADIO_PREFIX0_AP2_Msk (0xFFUL << RADIO_PREFIX0_AP2_Pos) /*!< Bit mask of AP2 field. */

/* Bits 15..8 : Address prefix 1. */
#define RADIO_PREFIX0_AP1_Pos (8UL) /*!< Position of AP1 field. */
#define RADIO_PREFIX0_AP1_Msk (0xFFUL << RADIO_PREFIX0_AP1_Pos) /*!< Bit mask of AP1 field. */

/* Bits 7..0 : Address prefix 0. */
#define RADIO_PREFIX0_AP0_Pos (0UL) /*!< Position of AP0 field. */
#define RADIO_PREFIX0_AP0_Msk (0xFFUL << RADIO_PREFIX0_AP0_Pos) /*!< Bit mask of AP0 field. */

/* Register: RADIO_PREFIX1 */
/* Description: Prefixes bytes for logical addresses 4-7 */

/* Bits 31..24 : Address prefix 7. */
#define RADIO_PREFIX1_AP7_Pos (24UL) /*!< Position of AP7 field. */
#define RADIO_PREFIX1_AP7_Msk (0xFFUL << RADIO_PREFIX1_AP7_Pos) /*!< Bit mask of AP7 field. */

/* Bits 23..16 : Address prefix 6. */
#define RADIO_PREFIX1_AP6_Pos (16UL) /*!< Position of AP6 field. */
#define RADIO_PREFIX1_AP6_Msk (0xFFUL << RADIO_PREFIX1_AP6_Pos) /*!< Bit mask of AP6 field. */

/* Bits 15..8 : Address prefix 5. */
#define RADIO_PREFIX1_AP5_Pos (8UL) /*!< Position of AP5 field. */
#define RADIO_PREFIX1_AP5_Msk (0xFFUL << RADIO_PREFIX1_AP5_Pos) /*!< Bit mask of AP5 field. */

/* Bits 7..0 : Address prefix 4. */
#define RADIO_PREFIX1_AP4_Pos (0UL) /*!< Position of AP4 field. */
#define RADIO_PREFIX1_AP4_Msk (0xFFUL << RADIO_PREFIX1_AP4_Pos) /*!< Bit mask of AP4 field. */

/* Register: RADIO_TXADDRESS */
/* Description: Transmit address select */

/* Bits 2..0 : Transmit address select */
#define RADIO_TXADDRESS_TXADDRESS_Pos (0UL) /*!< Position of TXADDRESS field. */
#define RADIO_TXADDRESS_TXADDRESS_Msk (0x7UL << RADIO_TXADDRESS_TXADDRESS_Pos) /*!< Bit mask of TXADDRESS field. */

/* Register: RADIO_RXADDRESSES */
/* Description: Receive address select */

/* Bit 7 : Enable or disable reception on logical address 7. */
#define RADIO_RXADDRESSES_ADDR7_Pos (7UL) /*!< Position of ADDR7 field. */
#define RADIO_RXADDRESSES_ADDR7_Msk (0x1UL << RADIO_RXADDRESSES_ADDR7_Pos) /*!< Bit mask of ADDR7 field. */
#define RADIO_RXADDRESSES_ADDR7_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR7_Enabled (1UL) /*!< Enable */

/* Bit 6 : Enable or disable reception on logical address 6. */
#define RADIO_RXADDRESSES_ADDR6_Pos (6UL) /*!< Position of ADDR6 field. */
#define RADIO_RXADDRESSES_ADDR6_Msk (0x1UL << RADIO_RXADDRESSES_ADDR6_Pos) /*!< Bit mask of ADDR6 field. */
#define RADIO_RXADDRESSES_ADDR6_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR6_Enabled (1UL) /*!< Enable */

/* Bit 5 : Enable or disable reception on logical address 5. */
#define RADIO_RXADDRESSES_ADDR5_Pos (5UL) /*!< Position of ADDR5 field. */
#define RADIO_RXADDRESSES_ADDR5_Msk (0x1UL << RADIO_RXADDRESSES_ADDR5_Pos) /*!< Bit mask of ADDR5 field. */
#define RADIO_RXADDRESSES_ADDR5_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR5_Enabled (1UL) /*!< Enable */

/* Bit 4 : Enable or disable reception on logical address 4. */
#define RADIO_RXADDRESSES_ADDR4_Pos (4UL) /*!< Position of ADDR4 field. */
#define RADIO_RXADDRESSES_ADDR4_Msk (0x1UL << RADIO_RXADDRESSES_ADDR4_Pos) /*!< Bit mask of ADDR4 field. */
#define RADIO_RXADDRESSES_ADDR4_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR4_Enabled (1UL) /*!< Enable */

/* Bit 3 : Enable or disable reception on logical address 3. */
#define RADIO_RXADDRESSES_ADDR3_Pos (3UL) /*!< Position of ADDR3 field. */
#define RADIO_RXADDRESSES_ADDR3_Msk (0x1UL << RADIO_RXADDRESSES_ADDR3_Pos) /*!< Bit mask of ADDR3 field. */
#define RADIO_RXADDRESSES_ADDR3_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR3_Enabled (1UL) /*!< Enable */

/* Bit 2 : Enable or disable reception on logical address 2. */
#define RADIO_RXADDRESSES_ADDR2_Pos (2UL) /*!< Position of ADDR2 field. */
#define RADIO_RXADDRESSES_ADDR2_Msk (0x1UL << RADIO_RXADDRESSES_ADDR2_Pos) /*!< Bit mask of ADDR2 field. */
#define RADIO_RXADDRESSES_ADDR2_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR2_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable reception on logical address 1. */
#define RADIO_RXADDRESSES_ADDR1_Pos (1UL) /*!< Position of ADDR1 field. */
#define RADIO_RXADDRESSES_ADDR1_Msk (0x1UL << RADIO_RXADDRESSES_ADDR1_Pos) /*!< Bit mask of ADDR1 field. */
#define RADIO_RXADDRESSES_ADDR1_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR1_Enabled (1UL) /*!< Enable */

/* Bit 0 : Enable or disable reception on logical address 0. */
#define RADIO_RXADDRESSES_ADDR0_Pos (0UL) /*!< Position of ADDR0 field. */
#define RADIO_RXADDRESSES_ADDR0_Msk (0x1UL << RADIO_RXADDRESSES_ADDR0_Pos) /*!< Bit mask of ADDR0 field. */
#define RADIO_RXADDRESSES_ADDR0_Disabled (0UL) /*!< Disable */
#define RADIO_RXADDRESSES_ADDR0_Enabled (1UL) /*!< Enable */

/* Register: RADIO_CRCCNF */
/* Description: CRC configuration */

/* Bits 9..8 : Include or exclude packet address field out of CRC calculation. */
#define RADIO_CRCCNF_SKIPADDR_Pos (8UL) /*!< Position of SKIPADDR field. */
#define RADIO_CRCCNF_SKIPADDR_Msk (0x3UL << RADIO_CRCCNF_SKIPADDR_Pos) /*!< Bit mask of SKIPADDR field. */
#define RADIO_CRCCNF_SKIPADDR_Include (0UL) /*!< CRC calculation includes address field */
#define RADIO_CRCCNF_SKIPADDR_Skip (1UL) /*!< CRC calculation does not include address field. The CRC calculation will start at the first byte after the address. */
#define RADIO_CRCCNF_SKIPADDR_Ieee802154 (2UL) /*!< CRC calculation as per 802.15.4 standard. Starting at first byte after length field. */

/* Bits 1..0 : CRC length in number of bytes For MODE Ble_LR125Kbit and Ble_LR500Kbit, only LEN set to 3 is supported */
#define RADIO_CRCCNF_LEN_Pos (0UL) /*!< Position of LEN field. */
#define RADIO_CRCCNF_LEN_Msk (0x3UL << RADIO_CRCCNF_LEN_Pos) /*!< Bit mask of LEN field. */
#define RADIO_CRCCNF_LEN_Disabled (0UL) /*!< CRC length is zero and CRC calculation is disabled */
#define RADIO_CRCCNF_LEN_One (1UL) /*!< CRC length is one byte and CRC calculation is enabled */
#define RADIO_CRCCNF_LEN_Two (2UL) /*!< CRC length is two bytes and CRC calculation is enabled */
#define RADIO_CRCCNF_LEN_Three (3UL) /*!< CRC length is three bytes and CRC calculation is enabled */

/* Register: RADIO_CRCPOLY */
/* Description: CRC polynomial */

/* Bits 23..0 : CRC polynomial */
#define RADIO_CRCPOLY_CRCPOLY_Pos (0UL) /*!< Position of CRCPOLY field. */
#define RADIO_CRCPOLY_CRCPOLY_Msk (0xFFFFFFUL << RADIO_CRCPOLY_CRCPOLY_Pos) /*!< Bit mask of CRCPOLY field. */

/* Register: RADIO_CRCINIT */
/* Description: CRC initial value */

/* Bits 23..0 : CRC initial value */
#define RADIO_CRCINIT_CRCINIT_Pos (0UL) /*!< Position of CRCINIT field. */
#define RADIO_CRCINIT_CRCINIT_Msk (0xFFFFFFUL << RADIO_CRCINIT_CRCINIT_Pos) /*!< Bit mask of CRCINIT field. */

/* Register: RADIO_TIFS */
/* Description: Interframe spacing in us */

/* Bits 9..0 : Interframe spacing in us. */
#define RADIO_TIFS_TIFS_Pos (0UL) /*!< Position of TIFS field. */
#define RADIO_TIFS_TIFS_Msk (0x3FFUL << RADIO_TIFS_TIFS_Pos) /*!< Bit mask of TIFS field. */

/* Register: RADIO_RSSISAMPLE */
/* Description: RSSI sample */

/* Bits 6..0 : RSSI sample. */
#define RADIO_RSSISAMPLE_RSSISAMPLE_Pos (0UL) /*!< Position of RSSISAMPLE field. */
#define RADIO_RSSISAMPLE_RSSISAMPLE_Msk (0x7FUL << RADIO_RSSISAMPLE_RSSISAMPLE_Pos) /*!< Bit mask of RSSISAMPLE field. */

/* Register: RADIO_STATE */
/* Description: Current radio state */

/* Bits 3..0 : Current radio state */
#define RADIO_STATE_STATE_Pos (0UL) /*!< Position of STATE field. */
#define RADIO_STATE_STATE_Msk (0xFUL << RADIO_STATE_STATE_Pos) /*!< Bit mask of STATE field. */
#define RADIO_STATE_STATE_Disabled (0UL) /*!< RADIO is in the Disabled state */
#define RADIO_STATE_STATE_RxRu (1UL) /*!< RADIO is in the RXRU state */
#define RADIO_STATE_STATE_RxIdle (2UL) /*!< RADIO is in the RXIDLE state */
#define RADIO_STATE_STATE_Rx (3UL) /*!< RADIO is in the RX state */
#define RADIO_STATE_STATE_RxDisable (4UL) /*!< RADIO is in the RXDISABLED state */
#define RADIO_STATE_STATE_TxRu (9UL) /*!< RADIO is in the TXRU state */
#define RADIO_STATE_STATE_TxIdle (10UL) /*!< RADIO is in the TXIDLE state */
#define RADIO_STATE_STATE_Tx (11UL) /*!< RADIO is in the TX state */
#define RADIO_STATE_STATE_TxDisable (12UL) /*!< RADIO is in the TXDISABLED state */

/* Register: RADIO_DATAWHITEIV */
/* Description: Data whitening initial value */

/* Bits 6..0 : Data whitening initial value. Bit 6 is hardwired to '1', writing '0' to it has no effect, and it will always be read back and used by the device as '1'. */
#define RADIO_DATAWHITEIV_DATAWHITEIV_Pos (0UL) /*!< Position of DATAWHITEIV field. */
#define RADIO_DATAWHITEIV_DATAWHITEIV_Msk (0x7FUL << RADIO_DATAWHITEIV_DATAWHITEIV_Pos) /*!< Bit mask of DATAWHITEIV field. */

/* Register: RADIO_BCC */
/* Description: Bit counter compare */

/* Bits 31..0 : Bit counter compare */
#define RADIO_BCC_BCC_Pos (0UL) /*!< Position of BCC field. */
#define RADIO_BCC_BCC_Msk (0xFFFFFFFFUL << RADIO_BCC_BCC_Pos) /*!< Bit mask of BCC field. */

/* Register: RADIO_DAB */
/* Description: Description collection: Device address base segment n */

/* Bits 31..0 : Device address base segment n */
#define RADIO_DAB_DAB_Pos (0UL) /*!< Position of DAB field. */
#define RADIO_DAB_DAB_Msk (0xFFFFFFFFUL << RADIO_DAB_DAB_Pos) /*!< Bit mask of DAB field. */

/* Register: RADIO_DAP */
/* Description: Description collection: Device address prefix n */

/* Bits 15..0 : Device address prefix n */
#define RADIO_DAP_DAP_Pos (0UL) /*!< Position of DAP field. */
#define RADIO_DAP_DAP_Msk (0xFFFFUL << RADIO_DAP_DAP_Pos) /*!< Bit mask of DAP field. */

/* Register: RADIO_DACNF */
/* Description: Device address match configuration */

/* Bit 15 : TxAdd for device address 7 */
#define RADIO_DACNF_TXADD7_Pos (15UL) /*!< Position of TXADD7 field. */
#define RADIO_DACNF_TXADD7_Msk (0x1UL << RADIO_DACNF_TXADD7_Pos) /*!< Bit mask of TXADD7 field. */

/* Bit 14 : TxAdd for device address 6 */
#define RADIO_DACNF_TXADD6_Pos (14UL) /*!< Position of TXADD6 field. */
#define RADIO_DACNF_TXADD6_Msk (0x1UL << RADIO_DACNF_TXADD6_Pos) /*!< Bit mask of TXADD6 field. */

/* Bit 13 : TxAdd for device address 5 */
#define RADIO_DACNF_TXADD5_Pos (13UL) /*!< Position of TXADD5 field. */
#define RADIO_DACNF_TXADD5_Msk (0x1UL << RADIO_DACNF_TXADD5_Pos) /*!< Bit mask of TXADD5 field. */

/* Bit 12 : TxAdd for device address 4 */
#define RADIO_DACNF_TXADD4_Pos (12UL) /*!< Position of TXADD4 field. */
#define RADIO_DACNF_TXADD4_Msk (0x1UL << RADIO_DACNF_TXADD4_Pos) /*!< Bit mask of TXADD4 field. */

/* Bit 11 : TxAdd for device address 3 */
#define RADIO_DACNF_TXADD3_Pos (11UL) /*!< Position of TXADD3 field. */
#define RADIO_DACNF_TXADD3_Msk (0x1UL << RADIO_DACNF_TXADD3_Pos) /*!< Bit mask of TXADD3 field. */

/* Bit 10 : TxAdd for device address 2 */
#define RADIO_DACNF_TXADD2_Pos (10UL) /*!< Position of TXADD2 field. */
#define RADIO_DACNF_TXADD2_Msk (0x1UL << RADIO_DACNF_TXADD2_Pos) /*!< Bit mask of TXADD2 field. */

/* Bit 9 : TxAdd for device address 1 */
#define RADIO_DACNF_TXADD1_Pos (9UL) /*!< Position of TXADD1 field. */
#define RADIO_DACNF_TXADD1_Msk (0x1UL << RADIO_DACNF_TXADD1_Pos) /*!< Bit mask of TXADD1 field. */

/* Bit 8 : TxAdd for device address 0 */
#define RADIO_DACNF_TXADD0_Pos (8UL) /*!< Position of TXADD0 field. */
#define RADIO_DACNF_TXADD0_Msk (0x1UL << RADIO_DACNF_TXADD0_Pos) /*!< Bit mask of TXADD0 field. */

/* Bit 7 : Enable or disable device address matching using device address 7 */
#define RADIO_DACNF_ENA7_Pos (7UL) /*!< Position of ENA7 field. */
#define RADIO_DACNF_ENA7_Msk (0x1UL << RADIO_DACNF_ENA7_Pos) /*!< Bit mask of ENA7 field. */
#define RADIO_DACNF_ENA7_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA7_Enabled (1UL) /*!< Enabled */

/* Bit 6 : Enable or disable device address matching using device address 6 */
#define RADIO_DACNF_ENA6_Pos (6UL) /*!< Position of ENA6 field. */
#define RADIO_DACNF_ENA6_Msk (0x1UL << RADIO_DACNF_ENA6_Pos) /*!< Bit mask of ENA6 field. */
#define RADIO_DACNF_ENA6_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA6_Enabled (1UL) /*!< Enabled */

/* Bit 5 : Enable or disable device address matching using device address 5 */
#define RADIO_DACNF_ENA5_Pos (5UL) /*!< Position of ENA5 field. */
#define RADIO_DACNF_ENA5_Msk (0x1UL << RADIO_DACNF_ENA5_Pos) /*!< Bit mask of ENA5 field. */
#define RADIO_DACNF_ENA5_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA5_Enabled (1UL) /*!< Enabled */

/* Bit 4 : Enable or disable device address matching using device address 4 */
#define RADIO_DACNF_ENA4_Pos (4UL) /*!< Position of ENA4 field. */
#define RADIO_DACNF_ENA4_Msk (0x1UL << RADIO_DACNF_ENA4_Pos) /*!< Bit mask of ENA4 field. */
#define RADIO_DACNF_ENA4_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA4_Enabled (1UL) /*!< Enabled */

/* Bit 3 : Enable or disable device address matching using device address 3 */
#define RADIO_DACNF_ENA3_Pos (3UL) /*!< Position of ENA3 field. */
#define RADIO_DACNF_ENA3_Msk (0x1UL << RADIO_DACNF_ENA3_Pos) /*!< Bit mask of ENA3 field. */
#define RADIO_DACNF_ENA3_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA3_Enabled (1UL) /*!< Enabled */

/* Bit 2 : Enable or disable device address matching using device address 2 */
#define RADIO_DACNF_ENA2_Pos (2UL) /*!< Position of ENA2 field. */
#define RADIO_DACNF_ENA2_Msk (0x1UL << RADIO_DACNF_ENA2_Pos) /*!< Bit mask of ENA2 field. */
#define RADIO_DACNF_ENA2_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA2_Enabled (1UL) /*!< Enabled */

/* Bit 1 : Enable or disable device address matching using device address 1 */
#define RADIO_DACNF_ENA1_Pos (1UL) /*!< Position of ENA1 field. */
#define RADIO_DACNF_ENA1_Msk (0x1UL << RADIO_DACNF_ENA1_Pos) /*!< Bit mask of ENA1 field. */
#define RADIO_DACNF_ENA1_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA1_Enabled (1UL) /*!< Enabled */

/* Bit 0 : Enable or disable device address matching using device address 0 */
#define RADIO_DACNF_ENA0_Pos (0UL) /*!< Position of ENA0 field. */
#define RADIO_DACNF_ENA0_Msk (0x1UL << RADIO_DACNF_ENA0_Pos) /*!< Bit mask of ENA0 field. */
#define RADIO_DACNF_ENA0_Disabled (0UL) /*!< Disabled */
#define RADIO_DACNF_ENA0_Enabled (1UL) /*!< Enabled */

/* Register: RADIO_MHRMATCHCONF */
/* Description: Search pattern configuration */

/* Bits 31..0 : Search pattern configuration */
#define RADIO_MHRMATCHCONF_MHRMATCHCONF_Pos (0UL) /*!< Position of MHRMATCHCONF field. */
#define RADIO_MHRMATCHCONF_MHRMATCHCONF_Msk (0xFFFFFFFFUL << RADIO_MHRMATCHCONF_MHRMATCHCONF_Pos) /*!< Bit mask of MHRMATCHCONF field. */

/* Register: RADIO_MHRMATCHMAS */
/* Description: Pattern mask */

/* Bits 31..0 : Pattern mask */
#define RADIO_MHRMATCHMAS_MHRMATCHMAS_Pos (0UL) /*!< Position of MHRMATCHMAS field. */
#define RADIO_MHRMATCHMAS_MHRMATCHMAS_Msk (0xFFFFFFFFUL << RADIO_MHRMATCHMAS_MHRMATCHMAS_Pos) /*!< Bit mask of MHRMATCHMAS field. */

/* Register: RADIO_MODECNF0 */
/* Description: Radio mode configuration register 0 */

/* Bits 9..8 : Default TX value */
#define RADIO_MODECNF0_DTX_Pos (8UL) /*!< Position of DTX field. */
#define RADIO_MODECNF0_DTX_Msk (0x3UL << RADIO_MODECNF0_DTX_Pos) /*!< Bit mask of DTX field. */
#define RADIO_MODECNF0_DTX_B1 (0UL) /*!< Transmit '1' */
#define RADIO_MODECNF0_DTX_B0 (1UL) /*!< Transmit '0' */
#define RADIO_MODECNF0_DTX_Center (2UL) /*!< Transmit center frequency */

/* Bit 0 : Radio ramp-up time */
#define RADIO_MODECNF0_RU_Pos (0UL) /*!< Position of RU field. */
#define RADIO_MODECNF0_RU_Msk (0x1UL << RADIO_MODECNF0_RU_Pos) /*!< Bit mask of RU field. */
#define RADIO_MODECNF0_RU_Default (0UL) /*!< Default ramp-up time (tRXEN and tTXEN), compatible with firmware written for nRF51 */
#define RADIO_MODECNF0_RU_Fast (1UL) /*!< Fast ramp-up (tRXEN,FAST and tTXEN,FAST), see electrical specifications for more information */

/* Register: RADIO_SFD */
/* Description: IEEE 802.15.4 start of frame delimiter */

/* Bits 7..0 : IEEE 802.15.4 start of frame delimiter */
#define RADIO_SFD_SFD_Pos (0UL) /*!< Position of SFD field. */
#define RADIO_SFD_SFD_Msk (0xFFUL << RADIO_SFD_SFD_Pos) /*!< Bit mask of SFD field. */

/* Register: RADIO_EDCNT */
/* Description: IEEE 802.15.4 energy detect loop count */

/* Bits 20..0 : IEEE 802.15.4 energy detect loop count */
#define RADIO_EDCNT_EDCNT_Pos (0UL) /*!< Position of EDCNT field. */
#define RADIO_EDCNT_EDCNT_Msk (0x1FFFFFUL << RADIO_EDCNT_EDCNT_Pos) /*!< Bit mask of EDCNT field. */

/* Register: RADIO_EDSAMPLE */
/* Description: IEEE 802.15.4 energy detect level */

/* Bits 7..0 : IEEE 802.15.4 energy detect level */
#define RADIO_EDSAMPLE_EDLVL_Pos (0UL) /*!< Position of EDLVL field. */
#define RADIO_EDSAMPLE_EDLVL_Msk (0xFFUL << RADIO_EDSAMPLE_EDLVL_Pos) /*!< Bit mask of EDLVL field. */

/* Register: RADIO_CCACTRL */
/* Description: IEEE 802.15.4 clear channel assessment control */

/* Bits 31..24 : Limit for occurances above CCACORRTHRES. When not equal to zero the corrolator based signal detect is enabled. */
#define RADIO_CCACTRL_CCACORRCNT_Pos (24UL) /*!< Position of CCACORRCNT field. */
#define RADIO_CCACTRL_CCACORRCNT_Msk (0xFFUL << RADIO_CCACTRL_CCACORRCNT_Pos) /*!< Bit mask of CCACORRCNT field. */

/* Bits 23..16 : CCA correlator busy threshold. Only relevant to CarrierMode, CarrierAndEdMode, and CarrierOrEdMode. */
#define RADIO_CCACTRL_CCACORRTHRES_Pos (16UL) /*!< Position of CCACORRTHRES field. */
#define RADIO_CCACTRL_CCACORRTHRES_Msk (0xFFUL << RADIO_CCACTRL_CCACORRTHRES_Pos) /*!< Bit mask of CCACORRTHRES field. */

/* Bits 15..8 : CCA energy busy threshold. Used in all the CCA modes except CarrierMode. */
#define RADIO_CCACTRL_CCAEDTHRES_Pos (8UL) /*!< Position of CCAEDTHRES field. */
#define RADIO_CCACTRL_CCAEDTHRES_Msk (0xFFUL << RADIO_CCACTRL_CCAEDTHRES_Pos) /*!< Bit mask of CCAEDTHRES field. */

/* Bits 2..0 : CCA mode of operation */
#define RADIO_CCACTRL_CCAMODE_Pos (0UL) /*!< Position of CCAMODE field. */
#define RADIO_CCACTRL_CCAMODE_Msk (0x7UL << RADIO_CCACTRL_CCAMODE_Pos) /*!< Bit mask of CCAMODE field. */
#define RADIO_CCACTRL_CCAMODE_EdMode (0UL) /*!< Energy above threshold */
#define RADIO_CCACTRL_CCAMODE_CarrierMode (1UL) /*!< Carrier seen */
#define RADIO_CCACTRL_CCAMODE_CarrierAndEdMode (2UL) /*!< Energy above threshold AND carrier seen */
#define RADIO_CCACTRL_CCAMODE_CarrierOrEdMode (3UL) /*!< Energy above threshold OR carrier seen */
#define RADIO_CCACTRL_CCAMODE_EdModeTest1 (4UL) /*!< Energy above threshold test mode that will abort when first ED measurement over threshold is seen. No averaging. */

/* Register: RADIO_DFEMODE */
/* Description: Whether to use Angle-of-Arrival (AOA) or Angle-of-Departure (AOD) */

/* Bits 1..0 : Direction finding operation mode */
#define RADIO_DFEMODE_DFEOPMODE_Pos (0UL) /*!< Position of DFEOPMODE field. */
#define RADIO_DFEMODE_DFEOPMODE_Msk (0x3UL << RADIO_DFEMODE_DFEOPMODE_Pos) /*!< Bit mask of DFEOPMODE field. */
#define RADIO_DFEMODE_DFEOPMODE_Disabled (0UL) /*!< Direction finding mode disabled */
#define RADIO_DFEMODE_DFEOPMODE_AoD (2UL) /*!< Direction finding mode set to AoD */
#define RADIO_DFEMODE_DFEOPMODE_AoA (3UL) /*!< Direction finding mode set to AoA */

/* Register: RADIO_CTEINLINECONF */
/* Description: Configuration for CTE inline mode */

/* Bits 31..24 : S0 bit mask to set which bit to match */
#define RADIO_CTEINLINECONF_S0MASK_Pos (24UL) /*!< Position of S0MASK field. */
#define RADIO_CTEINLINECONF_S0MASK_Msk (0xFFUL << RADIO_CTEINLINECONF_S0MASK_Pos) /*!< Bit mask of S0MASK field. */

/* Bits 23..16 : S0 bit pattern to match */
#define RADIO_CTEINLINECONF_S0CONF_Pos (16UL) /*!< Position of S0CONF field. */
#define RADIO_CTEINLINECONF_S0CONF_Msk (0xFFUL << RADIO_CTEINLINECONF_S0CONF_Pos) /*!< Bit mask of S0CONF field. */

/* Bits 15..13 : Spacing between samples for the samples in the SWITCHING period when CTEINLINEMODE is set. */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_Pos (13UL) /*!< Position of CTEINLINERXMODE2US field. */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_Msk (0x7UL << RADIO_CTEINLINECONF_CTEINLINERXMODE2US_Pos) /*!< Bit mask of CTEINLINERXMODE2US field. */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_4us (1UL) /*!< 4 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_2us (2UL) /*!< 2 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_1us (3UL) /*!< 1 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_500ns (4UL) /*!< 0.5 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_250ns (5UL) /*!< 0.25 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE2US_125ns (6UL) /*!< 0.125 us */

/* Bits 12..10 : Spacing between samples for the samples in the SWITCHING period when CTEINLINEMODE is set. */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_Pos (10UL) /*!< Position of CTEINLINERXMODE1US field. */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_Msk (0x7UL << RADIO_CTEINLINECONF_CTEINLINERXMODE1US_Pos) /*!< Bit mask of CTEINLINERXMODE1US field. */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_4us (1UL) /*!< 4 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_2us (2UL) /*!< 2 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_1us (3UL) /*!< 1 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_500ns (4UL) /*!< 0.5 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_250ns (5UL) /*!< 0.25 us */
#define RADIO_CTEINLINECONF_CTEINLINERXMODE1US_125ns (6UL) /*!< 0.125 us */

/* Bits 7..6 : Max range of CTETime */
#define RADIO_CTEINLINECONF_CTETIMEVALIDRANGE_Pos (6UL) /*!< Position of CTETIMEVALIDRANGE field. */
#define RADIO_CTEINLINECONF_CTETIMEVALIDRANGE_Msk (0x3UL << RADIO_CTEINLINECONF_CTETIMEVALIDRANGE_Pos) /*!< Bit mask of CTETIMEVALIDRANGE field. */
#define RADIO_CTEINLINECONF_CTETIMEVALIDRANGE_20 (0UL) /*!< 20 in 8 us unit (default) Set to 20 if parsed CTETime is larger than 20 */
#define RADIO_CTEINLINECONF_CTETIMEVALIDRANGE_31 (1UL) /*!< 31 in 8 us unit */
#define RADIO_CTEINLINECONF_CTETIMEVALIDRANGE_63 (2UL) /*!< 63 in 8 us unit */

/* Bit 4 : Sampling/switching if CRC is not OK */
#define RADIO_CTEINLINECONF_CTEERRORHANDLING_Pos (4UL) /*!< Position of CTEERRORHANDLING field. */
#define RADIO_CTEINLINECONF_CTEERRORHANDLING_Msk (0x1UL << RADIO_CTEINLINECONF_CTEERRORHANDLING_Pos) /*!< Bit mask of CTEERRORHANDLING field. */
#define RADIO_CTEINLINECONF_CTEERRORHANDLING_No (0UL) /*!< No sampling and antenna switching when CRC is not OK */
#define RADIO_CTEINLINECONF_CTEERRORHANDLING_Yes (1UL) /*!< Sampling and antenna switching also when CRC is not OK */

/* Bit 3 : CTEInfo is S1 byte or not */
#define RADIO_CTEINLINECONF_CTEINFOINS1_Pos (3UL) /*!< Position of CTEINFOINS1 field. */
#define RADIO_CTEINLINECONF_CTEINFOINS1_Msk (0x1UL << RADIO_CTEINLINECONF_CTEINFOINS1_Pos) /*!< Bit mask of CTEINFOINS1 field. */
#define RADIO_CTEINLINECONF_CTEINFOINS1_NotInS1 (0UL) /*!< CTEInfo is NOT in S1 byte (advertising PDU) */
#define RADIO_CTEINLINECONF_CTEINFOINS1_InS1 (1UL) /*!< CTEInfo is in S1 byte (data PDU) */

/* Bit 0 : Enable parsing of CTEInfo from received packet in BLE modes */
#define RADIO_CTEINLINECONF_CTEINLINECTRLEN_Pos (0UL) /*!< Position of CTEINLINECTRLEN field. */
#define RADIO_CTEINLINECONF_CTEINLINECTRLEN_Msk (0x1UL << RADIO_CTEINLINECONF_CTEINLINECTRLEN_Pos) /*!< Bit mask of CTEINLINECTRLEN field. */
#define RADIO_CTEINLINECONF_CTEINLINECTRLEN_Disabled (0UL) /*!< Parsing of CTEInfo is disabled */
#define RADIO_CTEINLINECONF_CTEINLINECTRLEN_Enabled (1UL) /*!< Parsing of CTEInfo is enabled */

/* Register: RADIO_DFECTRL1 */
/* Description: Various configuration for Direction finding */

/* Bits 27..24 : Gain will be lowered by the specified number of gain steps at the start of CTE */
#define RADIO_DFECTRL1_AGCBACKOFFGAIN_Pos (24UL) /*!< Position of AGCBACKOFFGAIN field. */
#define RADIO_DFECTRL1_AGCBACKOFFGAIN_Msk (0xFUL << RADIO_DFECTRL1_AGCBACKOFFGAIN_Pos) /*!< Bit mask of AGCBACKOFFGAIN field. */

/* Bits 23..20 : Repeat each individual antenna pattern N times sequentially, i.e. P0, P0, P1, P1, P2, P2, P3, P3, etc. */
#define RADIO_DFECTRL1_REPEATPATTERN_Pos (20UL) /*!< Position of REPEATPATTERN field. */
#define RADIO_DFECTRL1_REPEATPATTERN_Msk (0xFUL << RADIO_DFECTRL1_REPEATPATTERN_Pos) /*!< Bit mask of REPEATPATTERN field. */
#define RADIO_DFECTRL1_REPEATPATTERN_NoRepeat (0UL) /*!< Do not repeat (1 time in total) */

/* Bits 18..16 : Interval between samples in the SWITCHING period when CTEINLINECTRLEN is 0 */
#define RADIO_DFECTRL1_TSAMPLESPACING_Pos (16UL) /*!< Position of TSAMPLESPACING field. */
#define RADIO_DFECTRL1_TSAMPLESPACING_Msk (0x7UL << RADIO_DFECTRL1_TSAMPLESPACING_Pos) /*!< Bit mask of TSAMPLESPACING field. */
#define RADIO_DFECTRL1_TSAMPLESPACING_4us (1UL) /*!< 4 us */
#define RADIO_DFECTRL1_TSAMPLESPACING_2us (2UL) /*!< 2 us */
#define RADIO_DFECTRL1_TSAMPLESPACING_1us (3UL) /*!< 1 us */
#define RADIO_DFECTRL1_TSAMPLESPACING_500ns (4UL) /*!< 0.5 us */
#define RADIO_DFECTRL1_TSAMPLESPACING_250ns (5UL) /*!< 0.25 us */
#define RADIO_DFECTRL1_TSAMPLESPACING_125ns (6UL) /*!< 0.125 us */

/* Bit 15 : Whether to sample I/Q or magnitude/phase */
#define RADIO_DFECTRL1_SAMPLETYPE_Pos (15UL) /*!< Position of SAMPLETYPE field. */
#define RADIO_DFECTRL1_SAMPLETYPE_Msk (0x1UL << RADIO_DFECTRL1_SAMPLETYPE_Pos) /*!< Bit mask of SAMPLETYPE field. */
#define RADIO_DFECTRL1_SAMPLETYPE_IQ (0UL) /*!< Complex samples in I and Q */
#define RADIO_DFECTRL1_SAMPLETYPE_MagPhase (1UL) /*!< Complex samples as magnitude and phase */

/* Bits 14..12 : Interval between samples in the REFERENCE period */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_Pos (12UL) /*!< Position of TSAMPLESPACINGREF field. */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_Msk (0x7UL << RADIO_DFECTRL1_TSAMPLESPACINGREF_Pos) /*!< Bit mask of TSAMPLESPACINGREF field. */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_4us (1UL) /*!< 4 us */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_2us (2UL) /*!< 2 us */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_1us (3UL) /*!< 1 us */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_500ns (4UL) /*!< 0.5 us */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_250ns (5UL) /*!< 0.25 us */
#define RADIO_DFECTRL1_TSAMPLESPACINGREF_125ns (6UL) /*!< 0.125 us */

/* Bits 10..8 : Interval between every time the antenna is changed in the SWITCHING state */
#define RADIO_DFECTRL1_TSWITCHSPACING_Pos (8UL) /*!< Position of TSWITCHSPACING field. */
#define RADIO_DFECTRL1_TSWITCHSPACING_Msk (0x7UL << RADIO_DFECTRL1_TSWITCHSPACING_Pos) /*!< Bit mask of TSWITCHSPACING field. */
#define RADIO_DFECTRL1_TSWITCHSPACING_4us (1UL) /*!< 4 us */
#define RADIO_DFECTRL1_TSWITCHSPACING_2us (2UL) /*!< 2 us */
#define RADIO_DFECTRL1_TSWITCHSPACING_1us (3UL) /*!< 1 us */

/* Bit 7 : Add CTE extension and do antenna switching/sampling in this extension */
#define RADIO_DFECTRL1_DFEINEXTENSION_Pos (7UL) /*!< Position of DFEINEXTENSION field. */
#define RADIO_DFECTRL1_DFEINEXTENSION_Msk (0x1UL << RADIO_DFECTRL1_DFEINEXTENSION_Pos) /*!< Bit mask of DFEINEXTENSION field. */
#define RADIO_DFECTRL1_DFEINEXTENSION_Payload (0UL) /*!< Antenna switching/sampling is done in the packet payload */
#define RADIO_DFECTRL1_DFEINEXTENSION_CRC (1UL) /*!< AoA/AoD procedure triggered at end of CRC */

/* Bits 5..0 : Length of the AoA/AoD procedure in number of 8 us units */
#define RADIO_DFECTRL1_NUMBEROF8US_Pos (0UL) /*!< Position of NUMBEROF8US field. */
#define RADIO_DFECTRL1_NUMBEROF8US_Msk (0x3FUL << RADIO_DFECTRL1_NUMBEROF8US_Pos) /*!< Bit mask of NUMBEROF8US field. */

/* Register: RADIO_DFECTRL2 */
/* Description: Start offset for Direction finding */

/* Bits 27..16 : Signed value offset in number of 16 MHz clock cycles for fine tuning of the sampling instant for all IQ samples. With TSAMPLEOFFSET=0 the first sample is taken immediately at the start of the reference period */
#define RADIO_DFECTRL2_TSAMPLEOFFSET_Pos (16UL) /*!< Position of TSAMPLEOFFSET field. */
#define RADIO_DFECTRL2_TSAMPLEOFFSET_Msk (0xFFFUL << RADIO_DFECTRL2_TSAMPLEOFFSET_Pos) /*!< Bit mask of TSAMPLEOFFSET field. */

/* Bits 12..0 : Signed value offset after the end of the CRC before starting switching in number of 16 MHz clock cycles */
#define RADIO_DFECTRL2_TSWITCHOFFSET_Pos (0UL) /*!< Position of TSWITCHOFFSET field. */
#define RADIO_DFECTRL2_TSWITCHOFFSET_Msk (0x1FFFUL << RADIO_DFECTRL2_TSWITCHOFFSET_Pos) /*!< Bit mask of TSWITCHOFFSET field. */

/* Register: RADIO_SWITCHPATTERN */
/* Description: GPIO patterns to be used for each antenna */

/* Bits 7..0 : Fill array of GPIO patterns for antenna control. */
#define RADIO_SWITCHPATTERN_SWITCHPATTERN_Pos (0UL) /*!< Position of SWITCHPATTERN field. */
#define RADIO_SWITCHPATTERN_SWITCHPATTERN_Msk (0xFFUL << RADIO_SWITCHPATTERN_SWITCHPATTERN_Pos) /*!< Bit mask of SWITCHPATTERN field. */

/* Register: RADIO_CLEARPATTERN */
/* Description: Clear the GPIO pattern array for antenna control */

/* Bit 0 : Clears GPIO pattern array for antenna control */
#define RADIO_CLEARPATTERN_CLEARPATTERN_Pos (0UL) /*!< Position of CLEARPATTERN field. */
#define RADIO_CLEARPATTERN_CLEARPATTERN_Msk (0x1UL << RADIO_CLEARPATTERN_CLEARPATTERN_Pos) /*!< Bit mask of CLEARPATTERN field. */
#define RADIO_CLEARPATTERN_CLEARPATTERN_Clear (1UL) /*!< Clear the GPIO pattern */

/* Register: RADIO_PSEL_DFEGPIO */
/* Description: Description collection: Pin select for DFE pin n */

/* Bit 31 : Connection */
#define RADIO_PSEL_DFEGPIO_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define RADIO_PSEL_DFEGPIO_CONNECT_Msk (0x1UL << RADIO_PSEL_DFEGPIO_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define RADIO_PSEL_DFEGPIO_CONNECT_Connected (0UL) /*!< Connect */
#define RADIO_PSEL_DFEGPIO_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define RADIO_PSEL_DFEGPIO_PORT_Pos (5UL) /*!< Position of PORT field. */
#define RADIO_PSEL_DFEGPIO_PORT_Msk (0x1UL << RADIO_PSEL_DFEGPIO_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define RADIO_PSEL_DFEGPIO_PIN_Pos (0UL) /*!< Position of PIN field. */
#define RADIO_PSEL_DFEGPIO_PIN_Msk (0x1FUL << RADIO_PSEL_DFEGPIO_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: RADIO_DFEPACKET_PTR */
/* Description: Data pointer */

/* Bits 31..0 : Data pointer */
#define RADIO_DFEPACKET_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define RADIO_DFEPACKET_PTR_PTR_Msk (0xFFFFFFFFUL << RADIO_DFEPACKET_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: RADIO_DFEPACKET_MAXCNT */
/* Description: Maximum number of buffer words to transfer */

/* Bits 13..0 : Maximum number of buffer words to transfer */
#define RADIO_DFEPACKET_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define RADIO_DFEPACKET_MAXCNT_MAXCNT_Msk (0x3FFFUL << RADIO_DFEPACKET_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: RADIO_DFEPACKET_AMOUNT */
/* Description: Number of samples transferred in the last transaction */

/* Bits 15..0 : Number of samples transferred in the last transaction */
#define RADIO_DFEPACKET_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define RADIO_DFEPACKET_AMOUNT_AMOUNT_Msk (0xFFFFUL << RADIO_DFEPACKET_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: RADIO_POWER */
/* Description: Peripheral power control */

/* Bit 0 : Peripheral power control. The peripheral and its registers will be reset to its initial state by switching the peripheral off and then back on again. */
#define RADIO_POWER_POWER_Pos (0UL) /*!< Position of POWER field. */
#define RADIO_POWER_POWER_Msk (0x1UL << RADIO_POWER_POWER_Pos) /*!< Bit mask of POWER field. */
#define RADIO_POWER_POWER_Disabled (0UL) /*!< Peripheral is powered off */
#define RADIO_POWER_POWER_Enabled (1UL) /*!< Peripheral is powered on */


/* Peripheral: RESET */
/* Description: Reset control */

/* Register: RESET_RESETREAS */
/* Description: Reset reason */

/* Bit 27 : Reset from network CTRL-AP detected */
#define RESET_RESETREAS_LCTRLAP_Pos (27UL) /*!< Position of LCTRLAP field. */
#define RESET_RESETREAS_LCTRLAP_Msk (0x1UL << RESET_RESETREAS_LCTRLAP_Pos) /*!< Bit mask of LCTRLAP field. */
#define RESET_RESETREAS_LCTRLAP_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_LCTRLAP_Detected (1UL) /*!< Detected */

/* Bit 26 : Reset after wakeup from System OFF mode due to VBUS rising into valid range */
#define RESET_RESETREAS_VBUS_Pos (26UL) /*!< Position of VBUS field. */
#define RESET_RESETREAS_VBUS_Msk (0x1UL << RESET_RESETREAS_VBUS_Pos) /*!< Bit mask of VBUS field. */
#define RESET_RESETREAS_VBUS_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_VBUS_Detected (1UL) /*!< Detected */

/* Bit 25 : Reset from application watchdog timer 1 detected */
#define RESET_RESETREAS_DOG1_Pos (25UL) /*!< Position of DOG1 field. */
#define RESET_RESETREAS_DOG1_Msk (0x1UL << RESET_RESETREAS_DOG1_Pos) /*!< Bit mask of DOG1 field. */
#define RESET_RESETREAS_DOG1_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_DOG1_Detected (1UL) /*!< Detected */

/* Bit 24 : Reset after wakeup from System OFF mode due to NFC field being detected */
#define RESET_RESETREAS_NFC_Pos (24UL) /*!< Position of NFC field. */
#define RESET_RESETREAS_NFC_Msk (0x1UL << RESET_RESETREAS_NFC_Pos) /*!< Bit mask of NFC field. */
#define RESET_RESETREAS_NFC_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_NFC_Detected (1UL) /*!< Detected */

/* Bit 23 : Force-OFF reset from application core detected */
#define RESET_RESETREAS_MFORCEOFF_Pos (23UL) /*!< Position of MFORCEOFF field. */
#define RESET_RESETREAS_MFORCEOFF_Msk (0x1UL << RESET_RESETREAS_MFORCEOFF_Pos) /*!< Bit mask of MFORCEOFF field. */
#define RESET_RESETREAS_MFORCEOFF_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_MFORCEOFF_Detected (1UL) /*!< Detected */

/* Bit 18 : Reset from network watchdog timer detected */
#define RESET_RESETREAS_LDOG_Pos (18UL) /*!< Position of LDOG field. */
#define RESET_RESETREAS_LDOG_Msk (0x1UL << RESET_RESETREAS_LDOG_Pos) /*!< Bit mask of LDOG field. */
#define RESET_RESETREAS_LDOG_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_LDOG_Detected (1UL) /*!< Detected */

/* Bit 17 : Reset from network CPU lockup detected */
#define RESET_RESETREAS_LLOCKUP_Pos (17UL) /*!< Position of LLOCKUP field. */
#define RESET_RESETREAS_LLOCKUP_Msk (0x1UL << RESET_RESETREAS_LLOCKUP_Pos) /*!< Bit mask of LLOCKUP field. */
#define RESET_RESETREAS_LLOCKUP_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_LLOCKUP_Detected (1UL) /*!< Detected */

/* Bit 16 : Reset from network soft reset detected */
#define RESET_RESETREAS_LSREQ_Pos (16UL) /*!< Position of LSREQ field. */
#define RESET_RESETREAS_LSREQ_Msk (0x1UL << RESET_RESETREAS_LSREQ_Pos) /*!< Bit mask of LSREQ field. */
#define RESET_RESETREAS_LSREQ_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_LSREQ_Detected (1UL) /*!< Detected */

/* Bit 7 : Reset due to wakeup from System OFF mode when wakeup is triggered by entering the Debug Interface mode */
#define RESET_RESETREAS_DIF_Pos (7UL) /*!< Position of DIF field. */
#define RESET_RESETREAS_DIF_Msk (0x1UL << RESET_RESETREAS_DIF_Pos) /*!< Bit mask of DIF field. */
#define RESET_RESETREAS_DIF_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_DIF_Detected (1UL) /*!< Detected */

/* Bit 6 : Reset due to wakeup from System OFF mode when wakeup is triggered by ANADETECT signal from LPCOMP */
#define RESET_RESETREAS_LPCOMP_Pos (6UL) /*!< Position of LPCOMP field. */
#define RESET_RESETREAS_LPCOMP_Msk (0x1UL << RESET_RESETREAS_LPCOMP_Pos) /*!< Bit mask of LPCOMP field. */
#define RESET_RESETREAS_LPCOMP_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_LPCOMP_Detected (1UL) /*!< Detected */

/* Bit 5 : Reset due to wakeup from System OFF mode when wakeup is triggered by DETECT signal from GPIO */
#define RESET_RESETREAS_OFF_Pos (5UL) /*!< Position of OFF field. */
#define RESET_RESETREAS_OFF_Msk (0x1UL << RESET_RESETREAS_OFF_Pos) /*!< Bit mask of OFF field. */
#define RESET_RESETREAS_OFF_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_OFF_Detected (1UL) /*!< Detected */

/* Bit 4 : Reset from application CPU lockup detected */
#define RESET_RESETREAS_LOCKUP_Pos (4UL) /*!< Position of LOCKUP field. */
#define RESET_RESETREAS_LOCKUP_Msk (0x1UL << RESET_RESETREAS_LOCKUP_Pos) /*!< Bit mask of LOCKUP field. */
#define RESET_RESETREAS_LOCKUP_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_LOCKUP_Detected (1UL) /*!< Detected */

/* Bit 3 : Reset from application soft reset detected */
#define RESET_RESETREAS_SREQ_Pos (3UL) /*!< Position of SREQ field. */
#define RESET_RESETREAS_SREQ_Msk (0x1UL << RESET_RESETREAS_SREQ_Pos) /*!< Bit mask of SREQ field. */
#define RESET_RESETREAS_SREQ_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_SREQ_Detected (1UL) /*!< Detected */

/* Bit 2 : Reset from application CTRL-AP detected */
#define RESET_RESETREAS_CTRLAP_Pos (2UL) /*!< Position of CTRLAP field. */
#define RESET_RESETREAS_CTRLAP_Msk (0x1UL << RESET_RESETREAS_CTRLAP_Pos) /*!< Bit mask of CTRLAP field. */
#define RESET_RESETREAS_CTRLAP_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_CTRLAP_Detected (1UL) /*!< Detected */

/* Bit 1 : Reset from application watchdog timer 0 detected */
#define RESET_RESETREAS_DOG0_Pos (1UL) /*!< Position of DOG0 field. */
#define RESET_RESETREAS_DOG0_Msk (0x1UL << RESET_RESETREAS_DOG0_Pos) /*!< Bit mask of DOG0 field. */
#define RESET_RESETREAS_DOG0_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_DOG0_Detected (1UL) /*!< Detected */

/* Bit 0 : Reset from pin reset detected */
#define RESET_RESETREAS_RESETPIN_Pos (0UL) /*!< Position of RESETPIN field. */
#define RESET_RESETREAS_RESETPIN_Msk (0x1UL << RESET_RESETREAS_RESETPIN_Pos) /*!< Bit mask of RESETPIN field. */
#define RESET_RESETREAS_RESETPIN_NotDetected (0UL) /*!< Not detected */
#define RESET_RESETREAS_RESETPIN_Detected (1UL) /*!< Detected */


/* Peripheral: RNG */
/* Description: Random Number Generator */

/* Register: RNG_TASKS_START */
/* Description: Task starting the random number generator */

/* Bit 0 : Task starting the random number generator */
#define RNG_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define RNG_TASKS_START_TASKS_START_Msk (0x1UL << RNG_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define RNG_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: RNG_TASKS_STOP */
/* Description: Task stopping the random number generator */

/* Bit 0 : Task stopping the random number generator */
#define RNG_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define RNG_TASKS_STOP_TASKS_STOP_Msk (0x1UL << RNG_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define RNG_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: RNG_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define RNG_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define RNG_SUBSCRIBE_START_EN_Msk (0x1UL << RNG_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define RNG_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define RNG_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define RNG_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RNG_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << RNG_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RNG_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define RNG_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define RNG_SUBSCRIBE_STOP_EN_Msk (0x1UL << RNG_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define RNG_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define RNG_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define RNG_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RNG_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << RNG_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RNG_EVENTS_VALRDY */
/* Description: Event being generated for every new random number written to the VALUE register */

/* Bit 0 : Event being generated for every new random number written to the VALUE register */
#define RNG_EVENTS_VALRDY_EVENTS_VALRDY_Pos (0UL) /*!< Position of EVENTS_VALRDY field. */
#define RNG_EVENTS_VALRDY_EVENTS_VALRDY_Msk (0x1UL << RNG_EVENTS_VALRDY_EVENTS_VALRDY_Pos) /*!< Bit mask of EVENTS_VALRDY field. */
#define RNG_EVENTS_VALRDY_EVENTS_VALRDY_NotGenerated (0UL) /*!< Event not generated */
#define RNG_EVENTS_VALRDY_EVENTS_VALRDY_Generated (1UL) /*!< Event generated */

/* Register: RNG_PUBLISH_VALRDY */
/* Description: Publish configuration for event VALRDY */

/* Bit 31 :   */
#define RNG_PUBLISH_VALRDY_EN_Pos (31UL) /*!< Position of EN field. */
#define RNG_PUBLISH_VALRDY_EN_Msk (0x1UL << RNG_PUBLISH_VALRDY_EN_Pos) /*!< Bit mask of EN field. */
#define RNG_PUBLISH_VALRDY_EN_Disabled (0UL) /*!< Disable publishing */
#define RNG_PUBLISH_VALRDY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event VALRDY will publish to. */
#define RNG_PUBLISH_VALRDY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RNG_PUBLISH_VALRDY_CHIDX_Msk (0xFFUL << RNG_PUBLISH_VALRDY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RNG_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 0 : Shortcut between event VALRDY and task STOP */
#define RNG_SHORTS_VALRDY_STOP_Pos (0UL) /*!< Position of VALRDY_STOP field. */
#define RNG_SHORTS_VALRDY_STOP_Msk (0x1UL << RNG_SHORTS_VALRDY_STOP_Pos) /*!< Bit mask of VALRDY_STOP field. */
#define RNG_SHORTS_VALRDY_STOP_Disabled (0UL) /*!< Disable shortcut */
#define RNG_SHORTS_VALRDY_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Register: RNG_INTENSET */
/* Description: Enable interrupt */

/* Bit 0 : Write '1' to enable interrupt for event VALRDY */
#define RNG_INTENSET_VALRDY_Pos (0UL) /*!< Position of VALRDY field. */
#define RNG_INTENSET_VALRDY_Msk (0x1UL << RNG_INTENSET_VALRDY_Pos) /*!< Bit mask of VALRDY field. */
#define RNG_INTENSET_VALRDY_Disabled (0UL) /*!< Read: Disabled */
#define RNG_INTENSET_VALRDY_Enabled (1UL) /*!< Read: Enabled */
#define RNG_INTENSET_VALRDY_Set (1UL) /*!< Enable */

/* Register: RNG_INTENCLR */
/* Description: Disable interrupt */

/* Bit 0 : Write '1' to disable interrupt for event VALRDY */
#define RNG_INTENCLR_VALRDY_Pos (0UL) /*!< Position of VALRDY field. */
#define RNG_INTENCLR_VALRDY_Msk (0x1UL << RNG_INTENCLR_VALRDY_Pos) /*!< Bit mask of VALRDY field. */
#define RNG_INTENCLR_VALRDY_Disabled (0UL) /*!< Read: Disabled */
#define RNG_INTENCLR_VALRDY_Enabled (1UL) /*!< Read: Enabled */
#define RNG_INTENCLR_VALRDY_Clear (1UL) /*!< Disable */

/* Register: RNG_CONFIG */
/* Description: Configuration register */

/* Bit 0 : Bias correction */
#define RNG_CONFIG_DERCEN_Pos (0UL) /*!< Position of DERCEN field. */
#define RNG_CONFIG_DERCEN_Msk (0x1UL << RNG_CONFIG_DERCEN_Pos) /*!< Bit mask of DERCEN field. */
#define RNG_CONFIG_DERCEN_Disabled (0UL) /*!< Disabled */
#define RNG_CONFIG_DERCEN_Enabled (1UL) /*!< Enabled */

/* Register: RNG_VALUE */
/* Description: Output random number */

/* Bits 7..0 : Generated random number */
#define RNG_VALUE_VALUE_Pos (0UL) /*!< Position of VALUE field. */
#define RNG_VALUE_VALUE_Msk (0xFFUL << RNG_VALUE_VALUE_Pos) /*!< Bit mask of VALUE field. */


/* Peripheral: RTC */
/* Description: Real-time counter 0 */

/* Register: RTC_TASKS_START */
/* Description: Start RTC counter */

/* Bit 0 : Start RTC counter */
#define RTC_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define RTC_TASKS_START_TASKS_START_Msk (0x1UL << RTC_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define RTC_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: RTC_TASKS_STOP */
/* Description: Stop RTC counter */

/* Bit 0 : Stop RTC counter */
#define RTC_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define RTC_TASKS_STOP_TASKS_STOP_Msk (0x1UL << RTC_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define RTC_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: RTC_TASKS_CLEAR */
/* Description: Clear RTC counter */

/* Bit 0 : Clear RTC counter */
#define RTC_TASKS_CLEAR_TASKS_CLEAR_Pos (0UL) /*!< Position of TASKS_CLEAR field. */
#define RTC_TASKS_CLEAR_TASKS_CLEAR_Msk (0x1UL << RTC_TASKS_CLEAR_TASKS_CLEAR_Pos) /*!< Bit mask of TASKS_CLEAR field. */
#define RTC_TASKS_CLEAR_TASKS_CLEAR_Trigger (1UL) /*!< Trigger task */

/* Register: RTC_TASKS_TRIGOVRFLW */
/* Description: Set counter to 0xFFFFF0 */

/* Bit 0 : Set counter to 0xFFFFF0 */
#define RTC_TASKS_TRIGOVRFLW_TASKS_TRIGOVRFLW_Pos (0UL) /*!< Position of TASKS_TRIGOVRFLW field. */
#define RTC_TASKS_TRIGOVRFLW_TASKS_TRIGOVRFLW_Msk (0x1UL << RTC_TASKS_TRIGOVRFLW_TASKS_TRIGOVRFLW_Pos) /*!< Bit mask of TASKS_TRIGOVRFLW field. */
#define RTC_TASKS_TRIGOVRFLW_TASKS_TRIGOVRFLW_Trigger (1UL) /*!< Trigger task */

/* Register: RTC_TASKS_CAPTURE */
/* Description: Description collection: Capture RTC counter to CC[n] register */

/* Bit 0 : Capture RTC counter to CC[n] register */
#define RTC_TASKS_CAPTURE_TASKS_CAPTURE_Pos (0UL) /*!< Position of TASKS_CAPTURE field. */
#define RTC_TASKS_CAPTURE_TASKS_CAPTURE_Msk (0x1UL << RTC_TASKS_CAPTURE_TASKS_CAPTURE_Pos) /*!< Bit mask of TASKS_CAPTURE field. */
#define RTC_TASKS_CAPTURE_TASKS_CAPTURE_Trigger (1UL) /*!< Trigger task */

/* Register: RTC_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define RTC_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_SUBSCRIBE_START_EN_Msk (0x1UL << RTC_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define RTC_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define RTC_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << RTC_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define RTC_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_SUBSCRIBE_STOP_EN_Msk (0x1UL << RTC_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define RTC_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define RTC_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << RTC_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_SUBSCRIBE_CLEAR */
/* Description: Subscribe configuration for task CLEAR */

/* Bit 31 :   */
#define RTC_SUBSCRIBE_CLEAR_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_SUBSCRIBE_CLEAR_EN_Msk (0x1UL << RTC_SUBSCRIBE_CLEAR_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_SUBSCRIBE_CLEAR_EN_Disabled (0UL) /*!< Disable subscription */
#define RTC_SUBSCRIBE_CLEAR_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CLEAR will subscribe to */
#define RTC_SUBSCRIBE_CLEAR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_SUBSCRIBE_CLEAR_CHIDX_Msk (0xFFUL << RTC_SUBSCRIBE_CLEAR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_SUBSCRIBE_TRIGOVRFLW */
/* Description: Subscribe configuration for task TRIGOVRFLW */

/* Bit 31 :   */
#define RTC_SUBSCRIBE_TRIGOVRFLW_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_SUBSCRIBE_TRIGOVRFLW_EN_Msk (0x1UL << RTC_SUBSCRIBE_TRIGOVRFLW_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_SUBSCRIBE_TRIGOVRFLW_EN_Disabled (0UL) /*!< Disable subscription */
#define RTC_SUBSCRIBE_TRIGOVRFLW_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task TRIGOVRFLW will subscribe to */
#define RTC_SUBSCRIBE_TRIGOVRFLW_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_SUBSCRIBE_TRIGOVRFLW_CHIDX_Msk (0xFFUL << RTC_SUBSCRIBE_TRIGOVRFLW_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_SUBSCRIBE_CAPTURE */
/* Description: Description collection: Subscribe configuration for task CAPTURE[n] */

/* Bit 31 :   */
#define RTC_SUBSCRIBE_CAPTURE_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_SUBSCRIBE_CAPTURE_EN_Msk (0x1UL << RTC_SUBSCRIBE_CAPTURE_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_SUBSCRIBE_CAPTURE_EN_Disabled (0UL) /*!< Disable subscription */
#define RTC_SUBSCRIBE_CAPTURE_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CAPTURE[n] will subscribe to */
#define RTC_SUBSCRIBE_CAPTURE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_SUBSCRIBE_CAPTURE_CHIDX_Msk (0xFFUL << RTC_SUBSCRIBE_CAPTURE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_EVENTS_TICK */
/* Description: Event on counter increment */

/* Bit 0 : Event on counter increment */
#define RTC_EVENTS_TICK_EVENTS_TICK_Pos (0UL) /*!< Position of EVENTS_TICK field. */
#define RTC_EVENTS_TICK_EVENTS_TICK_Msk (0x1UL << RTC_EVENTS_TICK_EVENTS_TICK_Pos) /*!< Bit mask of EVENTS_TICK field. */
#define RTC_EVENTS_TICK_EVENTS_TICK_NotGenerated (0UL) /*!< Event not generated */
#define RTC_EVENTS_TICK_EVENTS_TICK_Generated (1UL) /*!< Event generated */

/* Register: RTC_EVENTS_OVRFLW */
/* Description: Event on counter overflow */

/* Bit 0 : Event on counter overflow */
#define RTC_EVENTS_OVRFLW_EVENTS_OVRFLW_Pos (0UL) /*!< Position of EVENTS_OVRFLW field. */
#define RTC_EVENTS_OVRFLW_EVENTS_OVRFLW_Msk (0x1UL << RTC_EVENTS_OVRFLW_EVENTS_OVRFLW_Pos) /*!< Bit mask of EVENTS_OVRFLW field. */
#define RTC_EVENTS_OVRFLW_EVENTS_OVRFLW_NotGenerated (0UL) /*!< Event not generated */
#define RTC_EVENTS_OVRFLW_EVENTS_OVRFLW_Generated (1UL) /*!< Event generated */

/* Register: RTC_EVENTS_COMPARE */
/* Description: Description collection: Compare event on CC[n] match */

/* Bit 0 : Compare event on CC[n] match */
#define RTC_EVENTS_COMPARE_EVENTS_COMPARE_Pos (0UL) /*!< Position of EVENTS_COMPARE field. */
#define RTC_EVENTS_COMPARE_EVENTS_COMPARE_Msk (0x1UL << RTC_EVENTS_COMPARE_EVENTS_COMPARE_Pos) /*!< Bit mask of EVENTS_COMPARE field. */
#define RTC_EVENTS_COMPARE_EVENTS_COMPARE_NotGenerated (0UL) /*!< Event not generated */
#define RTC_EVENTS_COMPARE_EVENTS_COMPARE_Generated (1UL) /*!< Event generated */

/* Register: RTC_PUBLISH_TICK */
/* Description: Publish configuration for event TICK */

/* Bit 31 :   */
#define RTC_PUBLISH_TICK_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_PUBLISH_TICK_EN_Msk (0x1UL << RTC_PUBLISH_TICK_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_PUBLISH_TICK_EN_Disabled (0UL) /*!< Disable publishing */
#define RTC_PUBLISH_TICK_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TICK will publish to. */
#define RTC_PUBLISH_TICK_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_PUBLISH_TICK_CHIDX_Msk (0xFFUL << RTC_PUBLISH_TICK_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_PUBLISH_OVRFLW */
/* Description: Publish configuration for event OVRFLW */

/* Bit 31 :   */
#define RTC_PUBLISH_OVRFLW_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_PUBLISH_OVRFLW_EN_Msk (0x1UL << RTC_PUBLISH_OVRFLW_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_PUBLISH_OVRFLW_EN_Disabled (0UL) /*!< Disable publishing */
#define RTC_PUBLISH_OVRFLW_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event OVRFLW will publish to. */
#define RTC_PUBLISH_OVRFLW_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_PUBLISH_OVRFLW_CHIDX_Msk (0xFFUL << RTC_PUBLISH_OVRFLW_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_PUBLISH_COMPARE */
/* Description: Description collection: Publish configuration for event COMPARE[n] */

/* Bit 31 :   */
#define RTC_PUBLISH_COMPARE_EN_Pos (31UL) /*!< Position of EN field. */
#define RTC_PUBLISH_COMPARE_EN_Msk (0x1UL << RTC_PUBLISH_COMPARE_EN_Pos) /*!< Bit mask of EN field. */
#define RTC_PUBLISH_COMPARE_EN_Disabled (0UL) /*!< Disable publishing */
#define RTC_PUBLISH_COMPARE_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event COMPARE[n] will publish to. */
#define RTC_PUBLISH_COMPARE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define RTC_PUBLISH_COMPARE_CHIDX_Msk (0xFFUL << RTC_PUBLISH_COMPARE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: RTC_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 3 : Shortcut between event COMPARE[3] and task CLEAR */
#define RTC_SHORTS_COMPARE3_CLEAR_Pos (3UL) /*!< Position of COMPARE3_CLEAR field. */
#define RTC_SHORTS_COMPARE3_CLEAR_Msk (0x1UL << RTC_SHORTS_COMPARE3_CLEAR_Pos) /*!< Bit mask of COMPARE3_CLEAR field. */
#define RTC_SHORTS_COMPARE3_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define RTC_SHORTS_COMPARE3_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 2 : Shortcut between event COMPARE[2] and task CLEAR */
#define RTC_SHORTS_COMPARE2_CLEAR_Pos (2UL) /*!< Position of COMPARE2_CLEAR field. */
#define RTC_SHORTS_COMPARE2_CLEAR_Msk (0x1UL << RTC_SHORTS_COMPARE2_CLEAR_Pos) /*!< Bit mask of COMPARE2_CLEAR field. */
#define RTC_SHORTS_COMPARE2_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define RTC_SHORTS_COMPARE2_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 1 : Shortcut between event COMPARE[1] and task CLEAR */
#define RTC_SHORTS_COMPARE1_CLEAR_Pos (1UL) /*!< Position of COMPARE1_CLEAR field. */
#define RTC_SHORTS_COMPARE1_CLEAR_Msk (0x1UL << RTC_SHORTS_COMPARE1_CLEAR_Pos) /*!< Bit mask of COMPARE1_CLEAR field. */
#define RTC_SHORTS_COMPARE1_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define RTC_SHORTS_COMPARE1_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 0 : Shortcut between event COMPARE[0] and task CLEAR */
#define RTC_SHORTS_COMPARE0_CLEAR_Pos (0UL) /*!< Position of COMPARE0_CLEAR field. */
#define RTC_SHORTS_COMPARE0_CLEAR_Msk (0x1UL << RTC_SHORTS_COMPARE0_CLEAR_Pos) /*!< Bit mask of COMPARE0_CLEAR field. */
#define RTC_SHORTS_COMPARE0_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define RTC_SHORTS_COMPARE0_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Register: RTC_INTENSET */
/* Description: Enable interrupt */

/* Bit 19 : Write '1' to enable interrupt for event COMPARE[3] */
#define RTC_INTENSET_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define RTC_INTENSET_COMPARE3_Msk (0x1UL << RTC_INTENSET_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define RTC_INTENSET_COMPARE3_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENSET_COMPARE3_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENSET_COMPARE3_Set (1UL) /*!< Enable */

/* Bit 18 : Write '1' to enable interrupt for event COMPARE[2] */
#define RTC_INTENSET_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define RTC_INTENSET_COMPARE2_Msk (0x1UL << RTC_INTENSET_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define RTC_INTENSET_COMPARE2_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENSET_COMPARE2_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENSET_COMPARE2_Set (1UL) /*!< Enable */

/* Bit 17 : Write '1' to enable interrupt for event COMPARE[1] */
#define RTC_INTENSET_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define RTC_INTENSET_COMPARE1_Msk (0x1UL << RTC_INTENSET_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define RTC_INTENSET_COMPARE1_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENSET_COMPARE1_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENSET_COMPARE1_Set (1UL) /*!< Enable */

/* Bit 16 : Write '1' to enable interrupt for event COMPARE[0] */
#define RTC_INTENSET_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define RTC_INTENSET_COMPARE0_Msk (0x1UL << RTC_INTENSET_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define RTC_INTENSET_COMPARE0_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENSET_COMPARE0_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENSET_COMPARE0_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event OVRFLW */
#define RTC_INTENSET_OVRFLW_Pos (1UL) /*!< Position of OVRFLW field. */
#define RTC_INTENSET_OVRFLW_Msk (0x1UL << RTC_INTENSET_OVRFLW_Pos) /*!< Bit mask of OVRFLW field. */
#define RTC_INTENSET_OVRFLW_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENSET_OVRFLW_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENSET_OVRFLW_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event TICK */
#define RTC_INTENSET_TICK_Pos (0UL) /*!< Position of TICK field. */
#define RTC_INTENSET_TICK_Msk (0x1UL << RTC_INTENSET_TICK_Pos) /*!< Bit mask of TICK field. */
#define RTC_INTENSET_TICK_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENSET_TICK_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENSET_TICK_Set (1UL) /*!< Enable */

/* Register: RTC_INTENCLR */
/* Description: Disable interrupt */

/* Bit 19 : Write '1' to disable interrupt for event COMPARE[3] */
#define RTC_INTENCLR_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define RTC_INTENCLR_COMPARE3_Msk (0x1UL << RTC_INTENCLR_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define RTC_INTENCLR_COMPARE3_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENCLR_COMPARE3_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENCLR_COMPARE3_Clear (1UL) /*!< Disable */

/* Bit 18 : Write '1' to disable interrupt for event COMPARE[2] */
#define RTC_INTENCLR_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define RTC_INTENCLR_COMPARE2_Msk (0x1UL << RTC_INTENCLR_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define RTC_INTENCLR_COMPARE2_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENCLR_COMPARE2_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENCLR_COMPARE2_Clear (1UL) /*!< Disable */

/* Bit 17 : Write '1' to disable interrupt for event COMPARE[1] */
#define RTC_INTENCLR_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define RTC_INTENCLR_COMPARE1_Msk (0x1UL << RTC_INTENCLR_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define RTC_INTENCLR_COMPARE1_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENCLR_COMPARE1_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENCLR_COMPARE1_Clear (1UL) /*!< Disable */

/* Bit 16 : Write '1' to disable interrupt for event COMPARE[0] */
#define RTC_INTENCLR_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define RTC_INTENCLR_COMPARE0_Msk (0x1UL << RTC_INTENCLR_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define RTC_INTENCLR_COMPARE0_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENCLR_COMPARE0_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENCLR_COMPARE0_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event OVRFLW */
#define RTC_INTENCLR_OVRFLW_Pos (1UL) /*!< Position of OVRFLW field. */
#define RTC_INTENCLR_OVRFLW_Msk (0x1UL << RTC_INTENCLR_OVRFLW_Pos) /*!< Bit mask of OVRFLW field. */
#define RTC_INTENCLR_OVRFLW_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENCLR_OVRFLW_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENCLR_OVRFLW_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event TICK */
#define RTC_INTENCLR_TICK_Pos (0UL) /*!< Position of TICK field. */
#define RTC_INTENCLR_TICK_Msk (0x1UL << RTC_INTENCLR_TICK_Pos) /*!< Bit mask of TICK field. */
#define RTC_INTENCLR_TICK_Disabled (0UL) /*!< Read: Disabled */
#define RTC_INTENCLR_TICK_Enabled (1UL) /*!< Read: Enabled */
#define RTC_INTENCLR_TICK_Clear (1UL) /*!< Disable */

/* Register: RTC_EVTEN */
/* Description: Enable or disable event routing */

/* Bit 19 : Enable or disable event routing for event COMPARE[3] */
#define RTC_EVTEN_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define RTC_EVTEN_COMPARE3_Msk (0x1UL << RTC_EVTEN_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define RTC_EVTEN_COMPARE3_Disabled (0UL) /*!< Disable */
#define RTC_EVTEN_COMPARE3_Enabled (1UL) /*!< Enable */

/* Bit 18 : Enable or disable event routing for event COMPARE[2] */
#define RTC_EVTEN_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define RTC_EVTEN_COMPARE2_Msk (0x1UL << RTC_EVTEN_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define RTC_EVTEN_COMPARE2_Disabled (0UL) /*!< Disable */
#define RTC_EVTEN_COMPARE2_Enabled (1UL) /*!< Enable */

/* Bit 17 : Enable or disable event routing for event COMPARE[1] */
#define RTC_EVTEN_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define RTC_EVTEN_COMPARE1_Msk (0x1UL << RTC_EVTEN_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define RTC_EVTEN_COMPARE1_Disabled (0UL) /*!< Disable */
#define RTC_EVTEN_COMPARE1_Enabled (1UL) /*!< Enable */

/* Bit 16 : Enable or disable event routing for event COMPARE[0] */
#define RTC_EVTEN_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define RTC_EVTEN_COMPARE0_Msk (0x1UL << RTC_EVTEN_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define RTC_EVTEN_COMPARE0_Disabled (0UL) /*!< Disable */
#define RTC_EVTEN_COMPARE0_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable event routing for event OVRFLW */
#define RTC_EVTEN_OVRFLW_Pos (1UL) /*!< Position of OVRFLW field. */
#define RTC_EVTEN_OVRFLW_Msk (0x1UL << RTC_EVTEN_OVRFLW_Pos) /*!< Bit mask of OVRFLW field. */
#define RTC_EVTEN_OVRFLW_Disabled (0UL) /*!< Disable */
#define RTC_EVTEN_OVRFLW_Enabled (1UL) /*!< Enable */

/* Bit 0 : Enable or disable event routing for event TICK */
#define RTC_EVTEN_TICK_Pos (0UL) /*!< Position of TICK field. */
#define RTC_EVTEN_TICK_Msk (0x1UL << RTC_EVTEN_TICK_Pos) /*!< Bit mask of TICK field. */
#define RTC_EVTEN_TICK_Disabled (0UL) /*!< Disable */
#define RTC_EVTEN_TICK_Enabled (1UL) /*!< Enable */

/* Register: RTC_EVTENSET */
/* Description: Enable event routing */

/* Bit 19 : Write '1' to enable event routing for event COMPARE[3] */
#define RTC_EVTENSET_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define RTC_EVTENSET_COMPARE3_Msk (0x1UL << RTC_EVTENSET_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define RTC_EVTENSET_COMPARE3_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENSET_COMPARE3_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENSET_COMPARE3_Set (1UL) /*!< Enable */

/* Bit 18 : Write '1' to enable event routing for event COMPARE[2] */
#define RTC_EVTENSET_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define RTC_EVTENSET_COMPARE2_Msk (0x1UL << RTC_EVTENSET_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define RTC_EVTENSET_COMPARE2_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENSET_COMPARE2_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENSET_COMPARE2_Set (1UL) /*!< Enable */

/* Bit 17 : Write '1' to enable event routing for event COMPARE[1] */
#define RTC_EVTENSET_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define RTC_EVTENSET_COMPARE1_Msk (0x1UL << RTC_EVTENSET_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define RTC_EVTENSET_COMPARE1_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENSET_COMPARE1_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENSET_COMPARE1_Set (1UL) /*!< Enable */

/* Bit 16 : Write '1' to enable event routing for event COMPARE[0] */
#define RTC_EVTENSET_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define RTC_EVTENSET_COMPARE0_Msk (0x1UL << RTC_EVTENSET_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define RTC_EVTENSET_COMPARE0_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENSET_COMPARE0_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENSET_COMPARE0_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable event routing for event OVRFLW */
#define RTC_EVTENSET_OVRFLW_Pos (1UL) /*!< Position of OVRFLW field. */
#define RTC_EVTENSET_OVRFLW_Msk (0x1UL << RTC_EVTENSET_OVRFLW_Pos) /*!< Bit mask of OVRFLW field. */
#define RTC_EVTENSET_OVRFLW_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENSET_OVRFLW_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENSET_OVRFLW_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable event routing for event TICK */
#define RTC_EVTENSET_TICK_Pos (0UL) /*!< Position of TICK field. */
#define RTC_EVTENSET_TICK_Msk (0x1UL << RTC_EVTENSET_TICK_Pos) /*!< Bit mask of TICK field. */
#define RTC_EVTENSET_TICK_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENSET_TICK_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENSET_TICK_Set (1UL) /*!< Enable */

/* Register: RTC_EVTENCLR */
/* Description: Disable event routing */

/* Bit 19 : Write '1' to disable event routing for event COMPARE[3] */
#define RTC_EVTENCLR_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define RTC_EVTENCLR_COMPARE3_Msk (0x1UL << RTC_EVTENCLR_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define RTC_EVTENCLR_COMPARE3_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENCLR_COMPARE3_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENCLR_COMPARE3_Clear (1UL) /*!< Disable */

/* Bit 18 : Write '1' to disable event routing for event COMPARE[2] */
#define RTC_EVTENCLR_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define RTC_EVTENCLR_COMPARE2_Msk (0x1UL << RTC_EVTENCLR_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define RTC_EVTENCLR_COMPARE2_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENCLR_COMPARE2_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENCLR_COMPARE2_Clear (1UL) /*!< Disable */

/* Bit 17 : Write '1' to disable event routing for event COMPARE[1] */
#define RTC_EVTENCLR_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define RTC_EVTENCLR_COMPARE1_Msk (0x1UL << RTC_EVTENCLR_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define RTC_EVTENCLR_COMPARE1_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENCLR_COMPARE1_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENCLR_COMPARE1_Clear (1UL) /*!< Disable */

/* Bit 16 : Write '1' to disable event routing for event COMPARE[0] */
#define RTC_EVTENCLR_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define RTC_EVTENCLR_COMPARE0_Msk (0x1UL << RTC_EVTENCLR_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define RTC_EVTENCLR_COMPARE0_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENCLR_COMPARE0_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENCLR_COMPARE0_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable event routing for event OVRFLW */
#define RTC_EVTENCLR_OVRFLW_Pos (1UL) /*!< Position of OVRFLW field. */
#define RTC_EVTENCLR_OVRFLW_Msk (0x1UL << RTC_EVTENCLR_OVRFLW_Pos) /*!< Bit mask of OVRFLW field. */
#define RTC_EVTENCLR_OVRFLW_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENCLR_OVRFLW_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENCLR_OVRFLW_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable event routing for event TICK */
#define RTC_EVTENCLR_TICK_Pos (0UL) /*!< Position of TICK field. */
#define RTC_EVTENCLR_TICK_Msk (0x1UL << RTC_EVTENCLR_TICK_Pos) /*!< Bit mask of TICK field. */
#define RTC_EVTENCLR_TICK_Disabled (0UL) /*!< Read: Disabled */
#define RTC_EVTENCLR_TICK_Enabled (1UL) /*!< Read: Enabled */
#define RTC_EVTENCLR_TICK_Clear (1UL) /*!< Disable */

/* Register: RTC_COUNTER */
/* Description: Current counter value */

/* Bits 23..0 : Counter value */
#define RTC_COUNTER_COUNTER_Pos (0UL) /*!< Position of COUNTER field. */
#define RTC_COUNTER_COUNTER_Msk (0xFFFFFFUL << RTC_COUNTER_COUNTER_Pos) /*!< Bit mask of COUNTER field. */

/* Register: RTC_PRESCALER */
/* Description: 12-bit prescaler for counter frequency (32768 / (PRESCALER + 1)). Must be written when RTC is stopped. */

/* Bits 11..0 : Prescaler value */
#define RTC_PRESCALER_PRESCALER_Pos (0UL) /*!< Position of PRESCALER field. */
#define RTC_PRESCALER_PRESCALER_Msk (0xFFFUL << RTC_PRESCALER_PRESCALER_Pos) /*!< Bit mask of PRESCALER field. */

/* Register: RTC_CC */
/* Description: Description collection: Compare register n */

/* Bits 23..0 : Compare value */
#define RTC_CC_COMPARE_Pos (0UL) /*!< Position of COMPARE field. */
#define RTC_CC_COMPARE_Msk (0xFFFFFFUL << RTC_CC_COMPARE_Pos) /*!< Bit mask of COMPARE field. */


/* Peripheral: SPIM */
/* Description: Serial Peripheral Interface Master with EasyDMA */

/* Register: SPIM_TASKS_START */
/* Description: Start SPI transaction */

/* Bit 0 : Start SPI transaction */
#define SPIM_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define SPIM_TASKS_START_TASKS_START_Msk (0x1UL << SPIM_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define SPIM_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: SPIM_TASKS_STOP */
/* Description: Stop SPI transaction */

/* Bit 0 : Stop SPI transaction */
#define SPIM_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define SPIM_TASKS_STOP_TASKS_STOP_Msk (0x1UL << SPIM_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define SPIM_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: SPIM_TASKS_SUSPEND */
/* Description: Suspend SPI transaction */

/* Bit 0 : Suspend SPI transaction */
#define SPIM_TASKS_SUSPEND_TASKS_SUSPEND_Pos (0UL) /*!< Position of TASKS_SUSPEND field. */
#define SPIM_TASKS_SUSPEND_TASKS_SUSPEND_Msk (0x1UL << SPIM_TASKS_SUSPEND_TASKS_SUSPEND_Pos) /*!< Bit mask of TASKS_SUSPEND field. */
#define SPIM_TASKS_SUSPEND_TASKS_SUSPEND_Trigger (1UL) /*!< Trigger task */

/* Register: SPIM_TASKS_RESUME */
/* Description: Resume SPI transaction */

/* Bit 0 : Resume SPI transaction */
#define SPIM_TASKS_RESUME_TASKS_RESUME_Pos (0UL) /*!< Position of TASKS_RESUME field. */
#define SPIM_TASKS_RESUME_TASKS_RESUME_Msk (0x1UL << SPIM_TASKS_RESUME_TASKS_RESUME_Pos) /*!< Bit mask of TASKS_RESUME field. */
#define SPIM_TASKS_RESUME_TASKS_RESUME_Trigger (1UL) /*!< Trigger task */

/* Register: SPIM_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define SPIM_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_SUBSCRIBE_START_EN_Msk (0x1UL << SPIM_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define SPIM_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define SPIM_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << SPIM_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define SPIM_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_SUBSCRIBE_STOP_EN_Msk (0x1UL << SPIM_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define SPIM_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define SPIM_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << SPIM_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_SUBSCRIBE_SUSPEND */
/* Description: Subscribe configuration for task SUSPEND */

/* Bit 31 :   */
#define SPIM_SUBSCRIBE_SUSPEND_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_SUBSCRIBE_SUSPEND_EN_Msk (0x1UL << SPIM_SUBSCRIBE_SUSPEND_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_SUBSCRIBE_SUSPEND_EN_Disabled (0UL) /*!< Disable subscription */
#define SPIM_SUBSCRIBE_SUSPEND_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task SUSPEND will subscribe to */
#define SPIM_SUBSCRIBE_SUSPEND_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_SUBSCRIBE_SUSPEND_CHIDX_Msk (0xFFUL << SPIM_SUBSCRIBE_SUSPEND_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_SUBSCRIBE_RESUME */
/* Description: Subscribe configuration for task RESUME */

/* Bit 31 :   */
#define SPIM_SUBSCRIBE_RESUME_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_SUBSCRIBE_RESUME_EN_Msk (0x1UL << SPIM_SUBSCRIBE_RESUME_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_SUBSCRIBE_RESUME_EN_Disabled (0UL) /*!< Disable subscription */
#define SPIM_SUBSCRIBE_RESUME_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RESUME will subscribe to */
#define SPIM_SUBSCRIBE_RESUME_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_SUBSCRIBE_RESUME_CHIDX_Msk (0xFFUL << SPIM_SUBSCRIBE_RESUME_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_EVENTS_STOPPED */
/* Description: SPI transaction has stopped */

/* Bit 0 : SPI transaction has stopped */
#define SPIM_EVENTS_STOPPED_EVENTS_STOPPED_Pos (0UL) /*!< Position of EVENTS_STOPPED field. */
#define SPIM_EVENTS_STOPPED_EVENTS_STOPPED_Msk (0x1UL << SPIM_EVENTS_STOPPED_EVENTS_STOPPED_Pos) /*!< Bit mask of EVENTS_STOPPED field. */
#define SPIM_EVENTS_STOPPED_EVENTS_STOPPED_NotGenerated (0UL) /*!< Event not generated */
#define SPIM_EVENTS_STOPPED_EVENTS_STOPPED_Generated (1UL) /*!< Event generated */

/* Register: SPIM_EVENTS_ENDRX */
/* Description: End of RXD buffer reached */

/* Bit 0 : End of RXD buffer reached */
#define SPIM_EVENTS_ENDRX_EVENTS_ENDRX_Pos (0UL) /*!< Position of EVENTS_ENDRX field. */
#define SPIM_EVENTS_ENDRX_EVENTS_ENDRX_Msk (0x1UL << SPIM_EVENTS_ENDRX_EVENTS_ENDRX_Pos) /*!< Bit mask of EVENTS_ENDRX field. */
#define SPIM_EVENTS_ENDRX_EVENTS_ENDRX_NotGenerated (0UL) /*!< Event not generated */
#define SPIM_EVENTS_ENDRX_EVENTS_ENDRX_Generated (1UL) /*!< Event generated */

/* Register: SPIM_EVENTS_END */
/* Description: End of RXD buffer and TXD buffer reached */

/* Bit 0 : End of RXD buffer and TXD buffer reached */
#define SPIM_EVENTS_END_EVENTS_END_Pos (0UL) /*!< Position of EVENTS_END field. */
#define SPIM_EVENTS_END_EVENTS_END_Msk (0x1UL << SPIM_EVENTS_END_EVENTS_END_Pos) /*!< Bit mask of EVENTS_END field. */
#define SPIM_EVENTS_END_EVENTS_END_NotGenerated (0UL) /*!< Event not generated */
#define SPIM_EVENTS_END_EVENTS_END_Generated (1UL) /*!< Event generated */

/* Register: SPIM_EVENTS_ENDTX */
/* Description: End of TXD buffer reached */

/* Bit 0 : End of TXD buffer reached */
#define SPIM_EVENTS_ENDTX_EVENTS_ENDTX_Pos (0UL) /*!< Position of EVENTS_ENDTX field. */
#define SPIM_EVENTS_ENDTX_EVENTS_ENDTX_Msk (0x1UL << SPIM_EVENTS_ENDTX_EVENTS_ENDTX_Pos) /*!< Bit mask of EVENTS_ENDTX field. */
#define SPIM_EVENTS_ENDTX_EVENTS_ENDTX_NotGenerated (0UL) /*!< Event not generated */
#define SPIM_EVENTS_ENDTX_EVENTS_ENDTX_Generated (1UL) /*!< Event generated */

/* Register: SPIM_EVENTS_STARTED */
/* Description: Transaction started */

/* Bit 0 : Transaction started */
#define SPIM_EVENTS_STARTED_EVENTS_STARTED_Pos (0UL) /*!< Position of EVENTS_STARTED field. */
#define SPIM_EVENTS_STARTED_EVENTS_STARTED_Msk (0x1UL << SPIM_EVENTS_STARTED_EVENTS_STARTED_Pos) /*!< Bit mask of EVENTS_STARTED field. */
#define SPIM_EVENTS_STARTED_EVENTS_STARTED_NotGenerated (0UL) /*!< Event not generated */
#define SPIM_EVENTS_STARTED_EVENTS_STARTED_Generated (1UL) /*!< Event generated */

/* Register: SPIM_PUBLISH_STOPPED */
/* Description: Publish configuration for event STOPPED */

/* Bit 31 :   */
#define SPIM_PUBLISH_STOPPED_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_PUBLISH_STOPPED_EN_Msk (0x1UL << SPIM_PUBLISH_STOPPED_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_PUBLISH_STOPPED_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIM_PUBLISH_STOPPED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event STOPPED will publish to. */
#define SPIM_PUBLISH_STOPPED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_PUBLISH_STOPPED_CHIDX_Msk (0xFFUL << SPIM_PUBLISH_STOPPED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_PUBLISH_ENDRX */
/* Description: Publish configuration for event ENDRX */

/* Bit 31 :   */
#define SPIM_PUBLISH_ENDRX_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_PUBLISH_ENDRX_EN_Msk (0x1UL << SPIM_PUBLISH_ENDRX_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_PUBLISH_ENDRX_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIM_PUBLISH_ENDRX_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDRX will publish to. */
#define SPIM_PUBLISH_ENDRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_PUBLISH_ENDRX_CHIDX_Msk (0xFFUL << SPIM_PUBLISH_ENDRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_PUBLISH_END */
/* Description: Publish configuration for event END */

/* Bit 31 :   */
#define SPIM_PUBLISH_END_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_PUBLISH_END_EN_Msk (0x1UL << SPIM_PUBLISH_END_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_PUBLISH_END_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIM_PUBLISH_END_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event END will publish to. */
#define SPIM_PUBLISH_END_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_PUBLISH_END_CHIDX_Msk (0xFFUL << SPIM_PUBLISH_END_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_PUBLISH_ENDTX */
/* Description: Publish configuration for event ENDTX */

/* Bit 31 :   */
#define SPIM_PUBLISH_ENDTX_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_PUBLISH_ENDTX_EN_Msk (0x1UL << SPIM_PUBLISH_ENDTX_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_PUBLISH_ENDTX_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIM_PUBLISH_ENDTX_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDTX will publish to. */
#define SPIM_PUBLISH_ENDTX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_PUBLISH_ENDTX_CHIDX_Msk (0xFFUL << SPIM_PUBLISH_ENDTX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_PUBLISH_STARTED */
/* Description: Publish configuration for event STARTED */

/* Bit 31 :   */
#define SPIM_PUBLISH_STARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIM_PUBLISH_STARTED_EN_Msk (0x1UL << SPIM_PUBLISH_STARTED_EN_Pos) /*!< Bit mask of EN field. */
#define SPIM_PUBLISH_STARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIM_PUBLISH_STARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event STARTED will publish to. */
#define SPIM_PUBLISH_STARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIM_PUBLISH_STARTED_CHIDX_Msk (0xFFUL << SPIM_PUBLISH_STARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIM_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 17 : Shortcut between event END and task START */
#define SPIM_SHORTS_END_START_Pos (17UL) /*!< Position of END_START field. */
#define SPIM_SHORTS_END_START_Msk (0x1UL << SPIM_SHORTS_END_START_Pos) /*!< Bit mask of END_START field. */
#define SPIM_SHORTS_END_START_Disabled (0UL) /*!< Disable shortcut */
#define SPIM_SHORTS_END_START_Enabled (1UL) /*!< Enable shortcut */

/* Register: SPIM_INTENSET */
/* Description: Enable interrupt */

/* Bit 19 : Write '1' to enable interrupt for event STARTED */
#define SPIM_INTENSET_STARTED_Pos (19UL) /*!< Position of STARTED field. */
#define SPIM_INTENSET_STARTED_Msk (0x1UL << SPIM_INTENSET_STARTED_Pos) /*!< Bit mask of STARTED field. */
#define SPIM_INTENSET_STARTED_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENSET_STARTED_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENSET_STARTED_Set (1UL) /*!< Enable */

/* Bit 8 : Write '1' to enable interrupt for event ENDTX */
#define SPIM_INTENSET_ENDTX_Pos (8UL) /*!< Position of ENDTX field. */
#define SPIM_INTENSET_ENDTX_Msk (0x1UL << SPIM_INTENSET_ENDTX_Pos) /*!< Bit mask of ENDTX field. */
#define SPIM_INTENSET_ENDTX_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENSET_ENDTX_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENSET_ENDTX_Set (1UL) /*!< Enable */

/* Bit 6 : Write '1' to enable interrupt for event END */
#define SPIM_INTENSET_END_Pos (6UL) /*!< Position of END field. */
#define SPIM_INTENSET_END_Msk (0x1UL << SPIM_INTENSET_END_Pos) /*!< Bit mask of END field. */
#define SPIM_INTENSET_END_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENSET_END_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENSET_END_Set (1UL) /*!< Enable */

/* Bit 4 : Write '1' to enable interrupt for event ENDRX */
#define SPIM_INTENSET_ENDRX_Pos (4UL) /*!< Position of ENDRX field. */
#define SPIM_INTENSET_ENDRX_Msk (0x1UL << SPIM_INTENSET_ENDRX_Pos) /*!< Bit mask of ENDRX field. */
#define SPIM_INTENSET_ENDRX_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENSET_ENDRX_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENSET_ENDRX_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event STOPPED */
#define SPIM_INTENSET_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define SPIM_INTENSET_STOPPED_Msk (0x1UL << SPIM_INTENSET_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define SPIM_INTENSET_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENSET_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENSET_STOPPED_Set (1UL) /*!< Enable */

/* Register: SPIM_INTENCLR */
/* Description: Disable interrupt */

/* Bit 19 : Write '1' to disable interrupt for event STARTED */
#define SPIM_INTENCLR_STARTED_Pos (19UL) /*!< Position of STARTED field. */
#define SPIM_INTENCLR_STARTED_Msk (0x1UL << SPIM_INTENCLR_STARTED_Pos) /*!< Bit mask of STARTED field. */
#define SPIM_INTENCLR_STARTED_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENCLR_STARTED_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENCLR_STARTED_Clear (1UL) /*!< Disable */

/* Bit 8 : Write '1' to disable interrupt for event ENDTX */
#define SPIM_INTENCLR_ENDTX_Pos (8UL) /*!< Position of ENDTX field. */
#define SPIM_INTENCLR_ENDTX_Msk (0x1UL << SPIM_INTENCLR_ENDTX_Pos) /*!< Bit mask of ENDTX field. */
#define SPIM_INTENCLR_ENDTX_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENCLR_ENDTX_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENCLR_ENDTX_Clear (1UL) /*!< Disable */

/* Bit 6 : Write '1' to disable interrupt for event END */
#define SPIM_INTENCLR_END_Pos (6UL) /*!< Position of END field. */
#define SPIM_INTENCLR_END_Msk (0x1UL << SPIM_INTENCLR_END_Pos) /*!< Bit mask of END field. */
#define SPIM_INTENCLR_END_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENCLR_END_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENCLR_END_Clear (1UL) /*!< Disable */

/* Bit 4 : Write '1' to disable interrupt for event ENDRX */
#define SPIM_INTENCLR_ENDRX_Pos (4UL) /*!< Position of ENDRX field. */
#define SPIM_INTENCLR_ENDRX_Msk (0x1UL << SPIM_INTENCLR_ENDRX_Pos) /*!< Bit mask of ENDRX field. */
#define SPIM_INTENCLR_ENDRX_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENCLR_ENDRX_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENCLR_ENDRX_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event STOPPED */
#define SPIM_INTENCLR_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define SPIM_INTENCLR_STOPPED_Msk (0x1UL << SPIM_INTENCLR_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define SPIM_INTENCLR_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define SPIM_INTENCLR_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define SPIM_INTENCLR_STOPPED_Clear (1UL) /*!< Disable */

/* Register: SPIM_STALLSTAT */
/* Description: Stall status for EasyDMA RAM accesses. The fields in this register are set to STALL by hardware whenever a stall occurres and can be cleared (set to NOSTALL) by the CPU. */

/* Bit 1 : Stall status for EasyDMA RAM writes */
#define SPIM_STALLSTAT_RX_Pos (1UL) /*!< Position of RX field. */
#define SPIM_STALLSTAT_RX_Msk (0x1UL << SPIM_STALLSTAT_RX_Pos) /*!< Bit mask of RX field. */
#define SPIM_STALLSTAT_RX_NOSTALL (0UL) /*!< No stall */
#define SPIM_STALLSTAT_RX_STALL (1UL) /*!< A stall has occurred */

/* Bit 0 : Stall status for EasyDMA RAM reads */
#define SPIM_STALLSTAT_TX_Pos (0UL) /*!< Position of TX field. */
#define SPIM_STALLSTAT_TX_Msk (0x1UL << SPIM_STALLSTAT_TX_Pos) /*!< Bit mask of TX field. */
#define SPIM_STALLSTAT_TX_NOSTALL (0UL) /*!< No stall */
#define SPIM_STALLSTAT_TX_STALL (1UL) /*!< A stall has occurred */

/* Register: SPIM_ENABLE */
/* Description: Enable SPIM */

/* Bits 3..0 : Enable or disable SPIM */
#define SPIM_ENABLE_ENABLE_Pos (0UL) /*!< Position of ENABLE field. */
#define SPIM_ENABLE_ENABLE_Msk (0xFUL << SPIM_ENABLE_ENABLE_Pos) /*!< Bit mask of ENABLE field. */
#define SPIM_ENABLE_ENABLE_Disabled (0UL) /*!< Disable SPIM */
#define SPIM_ENABLE_ENABLE_Enabled (7UL) /*!< Enable SPIM */

/* Register: SPIM_PSEL_SCK */
/* Description: Pin select for SCK */

/* Bit 31 : Connection */
#define SPIM_PSEL_SCK_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIM_PSEL_SCK_CONNECT_Msk (0x1UL << SPIM_PSEL_SCK_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIM_PSEL_SCK_CONNECT_Connected (0UL) /*!< Connect */
#define SPIM_PSEL_SCK_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIM_PSEL_SCK_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIM_PSEL_SCK_PORT_Msk (0x1UL << SPIM_PSEL_SCK_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIM_PSEL_SCK_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIM_PSEL_SCK_PIN_Msk (0x1FUL << SPIM_PSEL_SCK_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIM_PSEL_MOSI */
/* Description: Pin select for MOSI signal */

/* Bit 31 : Connection */
#define SPIM_PSEL_MOSI_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIM_PSEL_MOSI_CONNECT_Msk (0x1UL << SPIM_PSEL_MOSI_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIM_PSEL_MOSI_CONNECT_Connected (0UL) /*!< Connect */
#define SPIM_PSEL_MOSI_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIM_PSEL_MOSI_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIM_PSEL_MOSI_PORT_Msk (0x1UL << SPIM_PSEL_MOSI_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIM_PSEL_MOSI_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIM_PSEL_MOSI_PIN_Msk (0x1FUL << SPIM_PSEL_MOSI_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIM_PSEL_MISO */
/* Description: Pin select for MISO signal */

/* Bit 31 : Connection */
#define SPIM_PSEL_MISO_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIM_PSEL_MISO_CONNECT_Msk (0x1UL << SPIM_PSEL_MISO_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIM_PSEL_MISO_CONNECT_Connected (0UL) /*!< Connect */
#define SPIM_PSEL_MISO_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIM_PSEL_MISO_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIM_PSEL_MISO_PORT_Msk (0x1UL << SPIM_PSEL_MISO_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIM_PSEL_MISO_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIM_PSEL_MISO_PIN_Msk (0x1FUL << SPIM_PSEL_MISO_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIM_PSEL_CSN */
/* Description: Pin select for CSN */

/* Bit 31 : Connection */
#define SPIM_PSEL_CSN_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIM_PSEL_CSN_CONNECT_Msk (0x1UL << SPIM_PSEL_CSN_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIM_PSEL_CSN_CONNECT_Connected (0UL) /*!< Connect */
#define SPIM_PSEL_CSN_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIM_PSEL_CSN_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIM_PSEL_CSN_PORT_Msk (0x1UL << SPIM_PSEL_CSN_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIM_PSEL_CSN_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIM_PSEL_CSN_PIN_Msk (0x1FUL << SPIM_PSEL_CSN_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIM_FREQUENCY */
/* Description: SPI frequency. Accuracy depends on the HFCLK source selected. */

/* Bits 31..0 : SPI master data rate */
#define SPIM_FREQUENCY_FREQUENCY_Pos (0UL) /*!< Position of FREQUENCY field. */
#define SPIM_FREQUENCY_FREQUENCY_Msk (0xFFFFFFFFUL << SPIM_FREQUENCY_FREQUENCY_Pos) /*!< Bit mask of FREQUENCY field. */
#define SPIM_FREQUENCY_FREQUENCY_K125 (0x02000000UL) /*!< 125 kbps */
#define SPIM_FREQUENCY_FREQUENCY_K250 (0x04000000UL) /*!< 250 kbps */
#define SPIM_FREQUENCY_FREQUENCY_K500 (0x08000000UL) /*!< 500 kbps */
#define SPIM_FREQUENCY_FREQUENCY_M16 (0x0A000000UL) /*!< 16 Mbps */
#define SPIM_FREQUENCY_FREQUENCY_M1 (0x10000000UL) /*!< 1 Mbps */
#define SPIM_FREQUENCY_FREQUENCY_M32 (0x14000000UL) /*!< 32 Mbps */
#define SPIM_FREQUENCY_FREQUENCY_M2 (0x20000000UL) /*!< 2 Mbps */
#define SPIM_FREQUENCY_FREQUENCY_M4 (0x40000000UL) /*!< 4 Mbps */
#define SPIM_FREQUENCY_FREQUENCY_M8 (0x80000000UL) /*!< 8 Mbps */

/* Register: SPIM_RXD_PTR */
/* Description: Data pointer */

/* Bits 31..0 : Data pointer */
#define SPIM_RXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define SPIM_RXD_PTR_PTR_Msk (0xFFFFFFFFUL << SPIM_RXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: SPIM_RXD_MAXCNT */
/* Description: Maximum number of bytes in receive buffer */

/* Bits 15..0 : Maximum number of bytes in receive buffer */
#define SPIM_RXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define SPIM_RXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << SPIM_RXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: SPIM_RXD_AMOUNT */
/* Description: Number of bytes transferred in the last transaction */

/* Bits 15..0 : Number of bytes transferred in the last transaction */
#define SPIM_RXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define SPIM_RXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << SPIM_RXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: SPIM_RXD_LIST */
/* Description: EasyDMA list type */

/* Bits 1..0 : List type */
#define SPIM_RXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define SPIM_RXD_LIST_LIST_Msk (0x3UL << SPIM_RXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define SPIM_RXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define SPIM_RXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: SPIM_TXD_PTR */
/* Description: Data pointer */

/* Bits 31..0 : Data pointer */
#define SPIM_TXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define SPIM_TXD_PTR_PTR_Msk (0xFFFFFFFFUL << SPIM_TXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: SPIM_TXD_MAXCNT */
/* Description: Number of bytes in transmit buffer */

/* Bits 15..0 : Maximum number of bytes in transmit buffer */
#define SPIM_TXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define SPIM_TXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << SPIM_TXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: SPIM_TXD_AMOUNT */
/* Description: Number of bytes transferred in the last transaction */

/* Bits 15..0 : Number of bytes transferred in the last transaction */
#define SPIM_TXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define SPIM_TXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << SPIM_TXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: SPIM_TXD_LIST */
/* Description: EasyDMA list type */

/* Bits 1..0 : List type */
#define SPIM_TXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define SPIM_TXD_LIST_LIST_Msk (0x3UL << SPIM_TXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define SPIM_TXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define SPIM_TXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: SPIM_CONFIG */
/* Description: Configuration register */

/* Bit 2 : Serial clock (SCK) polarity */
#define SPIM_CONFIG_CPOL_Pos (2UL) /*!< Position of CPOL field. */
#define SPIM_CONFIG_CPOL_Msk (0x1UL << SPIM_CONFIG_CPOL_Pos) /*!< Bit mask of CPOL field. */
#define SPIM_CONFIG_CPOL_ActiveHigh (0UL) /*!< Active high */
#define SPIM_CONFIG_CPOL_ActiveLow (1UL) /*!< Active low */

/* Bit 1 : Serial clock (SCK) phase */
#define SPIM_CONFIG_CPHA_Pos (1UL) /*!< Position of CPHA field. */
#define SPIM_CONFIG_CPHA_Msk (0x1UL << SPIM_CONFIG_CPHA_Pos) /*!< Bit mask of CPHA field. */
#define SPIM_CONFIG_CPHA_Leading (0UL) /*!< Sample on leading edge of clock, shift serial data on trailing edge */
#define SPIM_CONFIG_CPHA_Trailing (1UL) /*!< Sample on trailing edge of clock, shift serial data on leading edge */

/* Bit 0 : Bit order */
#define SPIM_CONFIG_ORDER_Pos (0UL) /*!< Position of ORDER field. */
#define SPIM_CONFIG_ORDER_Msk (0x1UL << SPIM_CONFIG_ORDER_Pos) /*!< Bit mask of ORDER field. */
#define SPIM_CONFIG_ORDER_MsbFirst (0UL) /*!< Most significant bit shifted out first */
#define SPIM_CONFIG_ORDER_LsbFirst (1UL) /*!< Least significant bit shifted out first */

/* Register: SPIM_IFTIMING_RXDELAY */
/* Description: Sample delay for input serial data on MISO */

/* Bits 2..0 : Sample delay for input serial data on MISO. The value specifies the number of 64 MHz clock cycles (15.625 ns) delay from the the sampling edge of SCK (leading edge for CONFIG.CPHA = 0, trailing edge for CONFIG.CPHA = 1) until the input serial data is sampled. As en example, if RXDELAY = 0 and CONFIG.CPHA = 0, the input serial data is sampled on the rising edge of SCK. */
#define SPIM_IFTIMING_RXDELAY_RXDELAY_Pos (0UL) /*!< Position of RXDELAY field. */
#define SPIM_IFTIMING_RXDELAY_RXDELAY_Msk (0x7UL << SPIM_IFTIMING_RXDELAY_RXDELAY_Pos) /*!< Bit mask of RXDELAY field. */

/* Register: SPIM_IFTIMING_CSNDUR */
/* Description: Minimum duration between edge of CSN and edge of SCK. When SHORTS.END_START is used, this is also the minimum duration CSN must stay high between transactions. */

/* Bits 7..0 : Minimum duration between edge of CSN and edge of SCK. When SHORTS.END_START is used, this is the minimum duration CSN must stay high between transactions. The value is specified in number of 64 MHz clock cycles (15.625 ns). */
#define SPIM_IFTIMING_CSNDUR_CSNDUR_Pos (0UL) /*!< Position of CSNDUR field. */
#define SPIM_IFTIMING_CSNDUR_CSNDUR_Msk (0xFFUL << SPIM_IFTIMING_CSNDUR_CSNDUR_Pos) /*!< Bit mask of CSNDUR field. */

/* Register: SPIM_CSNPOL */
/* Description: Polarity of CSN output */

/* Bit 0 : Polarity of CSN output */
#define SPIM_CSNPOL_CSNPOL_Pos (0UL) /*!< Position of CSNPOL field. */
#define SPIM_CSNPOL_CSNPOL_Msk (0x1UL << SPIM_CSNPOL_CSNPOL_Pos) /*!< Bit mask of CSNPOL field. */
#define SPIM_CSNPOL_CSNPOL_LOW (0UL) /*!< Active low (idle state high) */
#define SPIM_CSNPOL_CSNPOL_HIGH (1UL) /*!< Active high (idle state low) */

/* Register: SPIM_PSELDCX */
/* Description: Pin select for DCX signal */

/* Bit 31 : Connection */
#define SPIM_PSELDCX_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIM_PSELDCX_CONNECT_Msk (0x1UL << SPIM_PSELDCX_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIM_PSELDCX_CONNECT_Connected (0UL) /*!< Connect */
#define SPIM_PSELDCX_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIM_PSELDCX_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIM_PSELDCX_PORT_Msk (0x1UL << SPIM_PSELDCX_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIM_PSELDCX_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIM_PSELDCX_PIN_Msk (0x1FUL << SPIM_PSELDCX_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIM_DCXCNT */
/* Description: DCX configuration */

/* Bits 3..0 : This register specifies the number of command bytes preceding the data bytes. The PSEL.DCX line will be low during transmission of command bytes and high during transmission of data bytes. Value 0xF indicates that all bytes are command bytes. */
#define SPIM_DCXCNT_DCXCNT_Pos (0UL) /*!< Position of DCXCNT field. */
#define SPIM_DCXCNT_DCXCNT_Msk (0xFUL << SPIM_DCXCNT_DCXCNT_Pos) /*!< Bit mask of DCXCNT field. */

/* Register: SPIM_ORC */
/* Description: Byte transmitted after TXD.MAXCNT bytes have been transmitted in the case when RXD.MAXCNT is greater than TXD.MAXCNT */

/* Bits 7..0 : Byte transmitted after TXD.MAXCNT bytes have been transmitted in the case when RXD.MAXCNT is greater than TXD.MAXCNT. */
#define SPIM_ORC_ORC_Pos (0UL) /*!< Position of ORC field. */
#define SPIM_ORC_ORC_Msk (0xFFUL << SPIM_ORC_ORC_Pos) /*!< Bit mask of ORC field. */


/* Peripheral: SPIS */
/* Description: SPI Slave */

/* Register: SPIS_TASKS_ACQUIRE */
/* Description: Acquire SPI semaphore */

/* Bit 0 : Acquire SPI semaphore */
#define SPIS_TASKS_ACQUIRE_TASKS_ACQUIRE_Pos (0UL) /*!< Position of TASKS_ACQUIRE field. */
#define SPIS_TASKS_ACQUIRE_TASKS_ACQUIRE_Msk (0x1UL << SPIS_TASKS_ACQUIRE_TASKS_ACQUIRE_Pos) /*!< Bit mask of TASKS_ACQUIRE field. */
#define SPIS_TASKS_ACQUIRE_TASKS_ACQUIRE_Trigger (1UL) /*!< Trigger task */

/* Register: SPIS_TASKS_RELEASE */
/* Description: Release SPI semaphore, enabling the SPI slave to acquire it */

/* Bit 0 : Release SPI semaphore, enabling the SPI slave to acquire it */
#define SPIS_TASKS_RELEASE_TASKS_RELEASE_Pos (0UL) /*!< Position of TASKS_RELEASE field. */
#define SPIS_TASKS_RELEASE_TASKS_RELEASE_Msk (0x1UL << SPIS_TASKS_RELEASE_TASKS_RELEASE_Pos) /*!< Bit mask of TASKS_RELEASE field. */
#define SPIS_TASKS_RELEASE_TASKS_RELEASE_Trigger (1UL) /*!< Trigger task */

/* Register: SPIS_SUBSCRIBE_ACQUIRE */
/* Description: Subscribe configuration for task ACQUIRE */

/* Bit 31 :   */
#define SPIS_SUBSCRIBE_ACQUIRE_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIS_SUBSCRIBE_ACQUIRE_EN_Msk (0x1UL << SPIS_SUBSCRIBE_ACQUIRE_EN_Pos) /*!< Bit mask of EN field. */
#define SPIS_SUBSCRIBE_ACQUIRE_EN_Disabled (0UL) /*!< Disable subscription */
#define SPIS_SUBSCRIBE_ACQUIRE_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task ACQUIRE will subscribe to */
#define SPIS_SUBSCRIBE_ACQUIRE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIS_SUBSCRIBE_ACQUIRE_CHIDX_Msk (0xFFUL << SPIS_SUBSCRIBE_ACQUIRE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIS_SUBSCRIBE_RELEASE */
/* Description: Subscribe configuration for task RELEASE */

/* Bit 31 :   */
#define SPIS_SUBSCRIBE_RELEASE_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIS_SUBSCRIBE_RELEASE_EN_Msk (0x1UL << SPIS_SUBSCRIBE_RELEASE_EN_Pos) /*!< Bit mask of EN field. */
#define SPIS_SUBSCRIBE_RELEASE_EN_Disabled (0UL) /*!< Disable subscription */
#define SPIS_SUBSCRIBE_RELEASE_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RELEASE will subscribe to */
#define SPIS_SUBSCRIBE_RELEASE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIS_SUBSCRIBE_RELEASE_CHIDX_Msk (0xFFUL << SPIS_SUBSCRIBE_RELEASE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIS_EVENTS_END */
/* Description: Granted transaction completed */

/* Bit 0 : Granted transaction completed */
#define SPIS_EVENTS_END_EVENTS_END_Pos (0UL) /*!< Position of EVENTS_END field. */
#define SPIS_EVENTS_END_EVENTS_END_Msk (0x1UL << SPIS_EVENTS_END_EVENTS_END_Pos) /*!< Bit mask of EVENTS_END field. */
#define SPIS_EVENTS_END_EVENTS_END_NotGenerated (0UL) /*!< Event not generated */
#define SPIS_EVENTS_END_EVENTS_END_Generated (1UL) /*!< Event generated */

/* Register: SPIS_EVENTS_ENDRX */
/* Description: End of RXD buffer reached */

/* Bit 0 : End of RXD buffer reached */
#define SPIS_EVENTS_ENDRX_EVENTS_ENDRX_Pos (0UL) /*!< Position of EVENTS_ENDRX field. */
#define SPIS_EVENTS_ENDRX_EVENTS_ENDRX_Msk (0x1UL << SPIS_EVENTS_ENDRX_EVENTS_ENDRX_Pos) /*!< Bit mask of EVENTS_ENDRX field. */
#define SPIS_EVENTS_ENDRX_EVENTS_ENDRX_NotGenerated (0UL) /*!< Event not generated */
#define SPIS_EVENTS_ENDRX_EVENTS_ENDRX_Generated (1UL) /*!< Event generated */

/* Register: SPIS_EVENTS_ACQUIRED */
/* Description: Semaphore acquired */

/* Bit 0 : Semaphore acquired */
#define SPIS_EVENTS_ACQUIRED_EVENTS_ACQUIRED_Pos (0UL) /*!< Position of EVENTS_ACQUIRED field. */
#define SPIS_EVENTS_ACQUIRED_EVENTS_ACQUIRED_Msk (0x1UL << SPIS_EVENTS_ACQUIRED_EVENTS_ACQUIRED_Pos) /*!< Bit mask of EVENTS_ACQUIRED field. */
#define SPIS_EVENTS_ACQUIRED_EVENTS_ACQUIRED_NotGenerated (0UL) /*!< Event not generated */
#define SPIS_EVENTS_ACQUIRED_EVENTS_ACQUIRED_Generated (1UL) /*!< Event generated */

/* Register: SPIS_PUBLISH_END */
/* Description: Publish configuration for event END */

/* Bit 31 :   */
#define SPIS_PUBLISH_END_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIS_PUBLISH_END_EN_Msk (0x1UL << SPIS_PUBLISH_END_EN_Pos) /*!< Bit mask of EN field. */
#define SPIS_PUBLISH_END_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIS_PUBLISH_END_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event END will publish to. */
#define SPIS_PUBLISH_END_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIS_PUBLISH_END_CHIDX_Msk (0xFFUL << SPIS_PUBLISH_END_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIS_PUBLISH_ENDRX */
/* Description: Publish configuration for event ENDRX */

/* Bit 31 :   */
#define SPIS_PUBLISH_ENDRX_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIS_PUBLISH_ENDRX_EN_Msk (0x1UL << SPIS_PUBLISH_ENDRX_EN_Pos) /*!< Bit mask of EN field. */
#define SPIS_PUBLISH_ENDRX_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIS_PUBLISH_ENDRX_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDRX will publish to. */
#define SPIS_PUBLISH_ENDRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIS_PUBLISH_ENDRX_CHIDX_Msk (0xFFUL << SPIS_PUBLISH_ENDRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIS_PUBLISH_ACQUIRED */
/* Description: Publish configuration for event ACQUIRED */

/* Bit 31 :   */
#define SPIS_PUBLISH_ACQUIRED_EN_Pos (31UL) /*!< Position of EN field. */
#define SPIS_PUBLISH_ACQUIRED_EN_Msk (0x1UL << SPIS_PUBLISH_ACQUIRED_EN_Pos) /*!< Bit mask of EN field. */
#define SPIS_PUBLISH_ACQUIRED_EN_Disabled (0UL) /*!< Disable publishing */
#define SPIS_PUBLISH_ACQUIRED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ACQUIRED will publish to. */
#define SPIS_PUBLISH_ACQUIRED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define SPIS_PUBLISH_ACQUIRED_CHIDX_Msk (0xFFUL << SPIS_PUBLISH_ACQUIRED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: SPIS_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 2 : Shortcut between event END and task ACQUIRE */
#define SPIS_SHORTS_END_ACQUIRE_Pos (2UL) /*!< Position of END_ACQUIRE field. */
#define SPIS_SHORTS_END_ACQUIRE_Msk (0x1UL << SPIS_SHORTS_END_ACQUIRE_Pos) /*!< Bit mask of END_ACQUIRE field. */
#define SPIS_SHORTS_END_ACQUIRE_Disabled (0UL) /*!< Disable shortcut */
#define SPIS_SHORTS_END_ACQUIRE_Enabled (1UL) /*!< Enable shortcut */

/* Register: SPIS_INTENSET */
/* Description: Enable interrupt */

/* Bit 10 : Write '1' to enable interrupt for event ACQUIRED */
#define SPIS_INTENSET_ACQUIRED_Pos (10UL) /*!< Position of ACQUIRED field. */
#define SPIS_INTENSET_ACQUIRED_Msk (0x1UL << SPIS_INTENSET_ACQUIRED_Pos) /*!< Bit mask of ACQUIRED field. */
#define SPIS_INTENSET_ACQUIRED_Disabled (0UL) /*!< Read: Disabled */
#define SPIS_INTENSET_ACQUIRED_Enabled (1UL) /*!< Read: Enabled */
#define SPIS_INTENSET_ACQUIRED_Set (1UL) /*!< Enable */

/* Bit 4 : Write '1' to enable interrupt for event ENDRX */
#define SPIS_INTENSET_ENDRX_Pos (4UL) /*!< Position of ENDRX field. */
#define SPIS_INTENSET_ENDRX_Msk (0x1UL << SPIS_INTENSET_ENDRX_Pos) /*!< Bit mask of ENDRX field. */
#define SPIS_INTENSET_ENDRX_Disabled (0UL) /*!< Read: Disabled */
#define SPIS_INTENSET_ENDRX_Enabled (1UL) /*!< Read: Enabled */
#define SPIS_INTENSET_ENDRX_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event END */
#define SPIS_INTENSET_END_Pos (1UL) /*!< Position of END field. */
#define SPIS_INTENSET_END_Msk (0x1UL << SPIS_INTENSET_END_Pos) /*!< Bit mask of END field. */
#define SPIS_INTENSET_END_Disabled (0UL) /*!< Read: Disabled */
#define SPIS_INTENSET_END_Enabled (1UL) /*!< Read: Enabled */
#define SPIS_INTENSET_END_Set (1UL) /*!< Enable */

/* Register: SPIS_INTENCLR */
/* Description: Disable interrupt */

/* Bit 10 : Write '1' to disable interrupt for event ACQUIRED */
#define SPIS_INTENCLR_ACQUIRED_Pos (10UL) /*!< Position of ACQUIRED field. */
#define SPIS_INTENCLR_ACQUIRED_Msk (0x1UL << SPIS_INTENCLR_ACQUIRED_Pos) /*!< Bit mask of ACQUIRED field. */
#define SPIS_INTENCLR_ACQUIRED_Disabled (0UL) /*!< Read: Disabled */
#define SPIS_INTENCLR_ACQUIRED_Enabled (1UL) /*!< Read: Enabled */
#define SPIS_INTENCLR_ACQUIRED_Clear (1UL) /*!< Disable */

/* Bit 4 : Write '1' to disable interrupt for event ENDRX */
#define SPIS_INTENCLR_ENDRX_Pos (4UL) /*!< Position of ENDRX field. */
#define SPIS_INTENCLR_ENDRX_Msk (0x1UL << SPIS_INTENCLR_ENDRX_Pos) /*!< Bit mask of ENDRX field. */
#define SPIS_INTENCLR_ENDRX_Disabled (0UL) /*!< Read: Disabled */
#define SPIS_INTENCLR_ENDRX_Enabled (1UL) /*!< Read: Enabled */
#define SPIS_INTENCLR_ENDRX_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event END */
#define SPIS_INTENCLR_END_Pos (1UL) /*!< Position of END field. */
#define SPIS_INTENCLR_END_Msk (0x1UL << SPIS_INTENCLR_END_Pos) /*!< Bit mask of END field. */
#define SPIS_INTENCLR_END_Disabled (0UL) /*!< Read: Disabled */
#define SPIS_INTENCLR_END_Enabled (1UL) /*!< Read: Enabled */
#define SPIS_INTENCLR_END_Clear (1UL) /*!< Disable */

/* Register: SPIS_SEMSTAT */
/* Description: Semaphore status register */

/* Bits 1..0 : Semaphore status */
#define SPIS_SEMSTAT_SEMSTAT_Pos (0UL) /*!< Position of SEMSTAT field. */
#define SPIS_SEMSTAT_SEMSTAT_Msk (0x3UL << SPIS_SEMSTAT_SEMSTAT_Pos) /*!< Bit mask of SEMSTAT field. */
#define SPIS_SEMSTAT_SEMSTAT_Free (0UL) /*!< Semaphore is free */
#define SPIS_SEMSTAT_SEMSTAT_CPU (1UL) /*!< Semaphore is assigned to CPU */
#define SPIS_SEMSTAT_SEMSTAT_SPIS (2UL) /*!< Semaphore is assigned to SPI slave */
#define SPIS_SEMSTAT_SEMSTAT_CPUPending (3UL) /*!< Semaphore is assigned to SPI but a handover to the CPU is pending */

/* Register: SPIS_STATUS */
/* Description: Status from last transaction */

/* Bit 1 : RX buffer overflow detected, and prevented */
#define SPIS_STATUS_OVERFLOW_Pos (1UL) /*!< Position of OVERFLOW field. */
#define SPIS_STATUS_OVERFLOW_Msk (0x1UL << SPIS_STATUS_OVERFLOW_Pos) /*!< Bit mask of OVERFLOW field. */
#define SPIS_STATUS_OVERFLOW_NotPresent (0UL) /*!< Read: error not present */
#define SPIS_STATUS_OVERFLOW_Present (1UL) /*!< Read: error present */
#define SPIS_STATUS_OVERFLOW_Clear (1UL) /*!< Write: clear error on writing '1' */

/* Bit 0 : TX buffer over-read detected, and prevented */
#define SPIS_STATUS_OVERREAD_Pos (0UL) /*!< Position of OVERREAD field. */
#define SPIS_STATUS_OVERREAD_Msk (0x1UL << SPIS_STATUS_OVERREAD_Pos) /*!< Bit mask of OVERREAD field. */
#define SPIS_STATUS_OVERREAD_NotPresent (0UL) /*!< Read: error not present */
#define SPIS_STATUS_OVERREAD_Present (1UL) /*!< Read: error present */
#define SPIS_STATUS_OVERREAD_Clear (1UL) /*!< Write: clear error on writing '1' */

/* Register: SPIS_ENABLE */
/* Description: Enable SPI slave */

/* Bits 3..0 : Enable or disable SPI slave */
#define SPIS_ENABLE_ENABLE_Pos (0UL) /*!< Position of ENABLE field. */
#define SPIS_ENABLE_ENABLE_Msk (0xFUL << SPIS_ENABLE_ENABLE_Pos) /*!< Bit mask of ENABLE field. */
#define SPIS_ENABLE_ENABLE_Disabled (0UL) /*!< Disable SPI slave */
#define SPIS_ENABLE_ENABLE_Enabled (2UL) /*!< Enable SPI slave */

/* Register: SPIS_PSEL_SCK */
/* Description: Pin select for SCK */

/* Bit 31 : Connection */
#define SPIS_PSEL_SCK_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIS_PSEL_SCK_CONNECT_Msk (0x1UL << SPIS_PSEL_SCK_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIS_PSEL_SCK_CONNECT_Connected (0UL) /*!< Connect */
#define SPIS_PSEL_SCK_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIS_PSEL_SCK_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIS_PSEL_SCK_PORT_Msk (0x1UL << SPIS_PSEL_SCK_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIS_PSEL_SCK_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIS_PSEL_SCK_PIN_Msk (0x1FUL << SPIS_PSEL_SCK_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIS_PSEL_MISO */
/* Description: Pin select for MISO signal */

/* Bit 31 : Connection */
#define SPIS_PSEL_MISO_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIS_PSEL_MISO_CONNECT_Msk (0x1UL << SPIS_PSEL_MISO_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIS_PSEL_MISO_CONNECT_Connected (0UL) /*!< Connect */
#define SPIS_PSEL_MISO_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIS_PSEL_MISO_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIS_PSEL_MISO_PORT_Msk (0x1UL << SPIS_PSEL_MISO_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIS_PSEL_MISO_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIS_PSEL_MISO_PIN_Msk (0x1FUL << SPIS_PSEL_MISO_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIS_PSEL_MOSI */
/* Description: Pin select for MOSI signal */

/* Bit 31 : Connection */
#define SPIS_PSEL_MOSI_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIS_PSEL_MOSI_CONNECT_Msk (0x1UL << SPIS_PSEL_MOSI_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIS_PSEL_MOSI_CONNECT_Connected (0UL) /*!< Connect */
#define SPIS_PSEL_MOSI_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIS_PSEL_MOSI_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIS_PSEL_MOSI_PORT_Msk (0x1UL << SPIS_PSEL_MOSI_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIS_PSEL_MOSI_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIS_PSEL_MOSI_PIN_Msk (0x1FUL << SPIS_PSEL_MOSI_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIS_PSEL_CSN */
/* Description: Pin select for CSN signal */

/* Bit 31 : Connection */
#define SPIS_PSEL_CSN_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define SPIS_PSEL_CSN_CONNECT_Msk (0x1UL << SPIS_PSEL_CSN_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define SPIS_PSEL_CSN_CONNECT_Connected (0UL) /*!< Connect */
#define SPIS_PSEL_CSN_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define SPIS_PSEL_CSN_PORT_Pos (5UL) /*!< Position of PORT field. */
#define SPIS_PSEL_CSN_PORT_Msk (0x1UL << SPIS_PSEL_CSN_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define SPIS_PSEL_CSN_PIN_Pos (0UL) /*!< Position of PIN field. */
#define SPIS_PSEL_CSN_PIN_Msk (0x1FUL << SPIS_PSEL_CSN_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: SPIS_RXD_PTR */
/* Description: RXD data pointer */

/* Bits 31..0 : RXD data pointer */
#define SPIS_RXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define SPIS_RXD_PTR_PTR_Msk (0xFFFFFFFFUL << SPIS_RXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: SPIS_RXD_MAXCNT */
/* Description: Maximum number of bytes in receive buffer */

/* Bits 15..0 : Maximum number of bytes in receive buffer */
#define SPIS_RXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define SPIS_RXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << SPIS_RXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: SPIS_RXD_AMOUNT */
/* Description: Number of bytes received in last granted transaction */

/* Bits 15..0 : Number of bytes received in the last granted transaction */
#define SPIS_RXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define SPIS_RXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << SPIS_RXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: SPIS_RXD_LIST */
/* Description: EasyDMA list type */

/* Bits 1..0 : List type */
#define SPIS_RXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define SPIS_RXD_LIST_LIST_Msk (0x3UL << SPIS_RXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define SPIS_RXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define SPIS_RXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: SPIS_TXD_PTR */
/* Description: TXD data pointer */

/* Bits 31..0 : TXD data pointer */
#define SPIS_TXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define SPIS_TXD_PTR_PTR_Msk (0xFFFFFFFFUL << SPIS_TXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: SPIS_TXD_MAXCNT */
/* Description: Maximum number of bytes in transmit buffer */

/* Bits 15..0 : Maximum number of bytes in transmit buffer */
#define SPIS_TXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define SPIS_TXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << SPIS_TXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: SPIS_TXD_AMOUNT */
/* Description: Number of bytes transmitted in last granted transaction */

/* Bits 15..0 : Number of bytes transmitted in last granted transaction */
#define SPIS_TXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define SPIS_TXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << SPIS_TXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: SPIS_TXD_LIST */
/* Description: EasyDMA list type */

/* Bits 1..0 : List type */
#define SPIS_TXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define SPIS_TXD_LIST_LIST_Msk (0x3UL << SPIS_TXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define SPIS_TXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define SPIS_TXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: SPIS_CONFIG */
/* Description: Configuration register */

/* Bit 2 : Serial clock (SCK) polarity */
#define SPIS_CONFIG_CPOL_Pos (2UL) /*!< Position of CPOL field. */
#define SPIS_CONFIG_CPOL_Msk (0x1UL << SPIS_CONFIG_CPOL_Pos) /*!< Bit mask of CPOL field. */
#define SPIS_CONFIG_CPOL_ActiveHigh (0UL) /*!< Active high */
#define SPIS_CONFIG_CPOL_ActiveLow (1UL) /*!< Active low */

/* Bit 1 : Serial clock (SCK) phase */
#define SPIS_CONFIG_CPHA_Pos (1UL) /*!< Position of CPHA field. */
#define SPIS_CONFIG_CPHA_Msk (0x1UL << SPIS_CONFIG_CPHA_Pos) /*!< Bit mask of CPHA field. */
#define SPIS_CONFIG_CPHA_Leading (0UL) /*!< Sample on leading edge of clock, shift serial data on trailing edge */
#define SPIS_CONFIG_CPHA_Trailing (1UL) /*!< Sample on trailing edge of clock, shift serial data on leading edge */

/* Bit 0 : Bit order */
#define SPIS_CONFIG_ORDER_Pos (0UL) /*!< Position of ORDER field. */
#define SPIS_CONFIG_ORDER_Msk (0x1UL << SPIS_CONFIG_ORDER_Pos) /*!< Bit mask of ORDER field. */
#define SPIS_CONFIG_ORDER_MsbFirst (0UL) /*!< Most significant bit shifted out first */
#define SPIS_CONFIG_ORDER_LsbFirst (1UL) /*!< Least significant bit shifted out first */

/* Register: SPIS_DEF */
/* Description: Default character. Character clocked out in case of an ignored transaction. */

/* Bits 7..0 : Default character. Character clocked out in case of an ignored transaction. */
#define SPIS_DEF_DEF_Pos (0UL) /*!< Position of DEF field. */
#define SPIS_DEF_DEF_Msk (0xFFUL << SPIS_DEF_DEF_Pos) /*!< Bit mask of DEF field. */

/* Register: SPIS_ORC */
/* Description: Over-read character */

/* Bits 7..0 : Over-read character. Character clocked out after an over-read of the transmit buffer. */
#define SPIS_ORC_ORC_Pos (0UL) /*!< Position of ORC field. */
#define SPIS_ORC_ORC_Msk (0xFFUL << SPIS_ORC_ORC_Pos) /*!< Bit mask of ORC field. */


/* Peripheral: TEMP */
/* Description: Temperature Sensor */

/* Register: TEMP_TASKS_START */
/* Description: Start temperature measurement */

/* Bit 0 : Start temperature measurement */
#define TEMP_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define TEMP_TASKS_START_TASKS_START_Msk (0x1UL << TEMP_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define TEMP_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: TEMP_TASKS_STOP */
/* Description: Stop temperature measurement */

/* Bit 0 : Stop temperature measurement */
#define TEMP_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define TEMP_TASKS_STOP_TASKS_STOP_Msk (0x1UL << TEMP_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define TEMP_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: TEMP_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define TEMP_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define TEMP_SUBSCRIBE_START_EN_Msk (0x1UL << TEMP_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define TEMP_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define TEMP_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define TEMP_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TEMP_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << TEMP_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TEMP_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define TEMP_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define TEMP_SUBSCRIBE_STOP_EN_Msk (0x1UL << TEMP_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define TEMP_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define TEMP_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define TEMP_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TEMP_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << TEMP_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TEMP_EVENTS_DATARDY */
/* Description: Temperature measurement complete, data ready */

/* Bit 0 : Temperature measurement complete, data ready */
#define TEMP_EVENTS_DATARDY_EVENTS_DATARDY_Pos (0UL) /*!< Position of EVENTS_DATARDY field. */
#define TEMP_EVENTS_DATARDY_EVENTS_DATARDY_Msk (0x1UL << TEMP_EVENTS_DATARDY_EVENTS_DATARDY_Pos) /*!< Bit mask of EVENTS_DATARDY field. */
#define TEMP_EVENTS_DATARDY_EVENTS_DATARDY_NotGenerated (0UL) /*!< Event not generated */
#define TEMP_EVENTS_DATARDY_EVENTS_DATARDY_Generated (1UL) /*!< Event generated */

/* Register: TEMP_PUBLISH_DATARDY */
/* Description: Publish configuration for event DATARDY */

/* Bit 31 :   */
#define TEMP_PUBLISH_DATARDY_EN_Pos (31UL) /*!< Position of EN field. */
#define TEMP_PUBLISH_DATARDY_EN_Msk (0x1UL << TEMP_PUBLISH_DATARDY_EN_Pos) /*!< Bit mask of EN field. */
#define TEMP_PUBLISH_DATARDY_EN_Disabled (0UL) /*!< Disable publishing */
#define TEMP_PUBLISH_DATARDY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event DATARDY will publish to. */
#define TEMP_PUBLISH_DATARDY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TEMP_PUBLISH_DATARDY_CHIDX_Msk (0xFFUL << TEMP_PUBLISH_DATARDY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TEMP_INTENSET */
/* Description: Enable interrupt */

/* Bit 0 : Write '1' to enable interrupt for event DATARDY */
#define TEMP_INTENSET_DATARDY_Pos (0UL) /*!< Position of DATARDY field. */
#define TEMP_INTENSET_DATARDY_Msk (0x1UL << TEMP_INTENSET_DATARDY_Pos) /*!< Bit mask of DATARDY field. */
#define TEMP_INTENSET_DATARDY_Disabled (0UL) /*!< Read: Disabled */
#define TEMP_INTENSET_DATARDY_Enabled (1UL) /*!< Read: Enabled */
#define TEMP_INTENSET_DATARDY_Set (1UL) /*!< Enable */

/* Register: TEMP_INTENCLR */
/* Description: Disable interrupt */

/* Bit 0 : Write '1' to disable interrupt for event DATARDY */
#define TEMP_INTENCLR_DATARDY_Pos (0UL) /*!< Position of DATARDY field. */
#define TEMP_INTENCLR_DATARDY_Msk (0x1UL << TEMP_INTENCLR_DATARDY_Pos) /*!< Bit mask of DATARDY field. */
#define TEMP_INTENCLR_DATARDY_Disabled (0UL) /*!< Read: Disabled */
#define TEMP_INTENCLR_DATARDY_Enabled (1UL) /*!< Read: Enabled */
#define TEMP_INTENCLR_DATARDY_Clear (1UL) /*!< Disable */

/* Register: TEMP_TEMP */
/* Description: Temperature in degC (0.25deg steps) */

/* Bits 31..0 : Temperature in degC (0.25deg steps) */
#define TEMP_TEMP_TEMP_Pos (0UL) /*!< Position of TEMP field. */
#define TEMP_TEMP_TEMP_Msk (0xFFFFFFFFUL << TEMP_TEMP_TEMP_Pos) /*!< Bit mask of TEMP field. */

/* Register: TEMP_A0 */
/* Description: Slope of first piecewise linear function */

/* Bits 11..0 : Slope of first piecewise linear function */
#define TEMP_A0_A0_Pos (0UL) /*!< Position of A0 field. */
#define TEMP_A0_A0_Msk (0xFFFUL << TEMP_A0_A0_Pos) /*!< Bit mask of A0 field. */

/* Register: TEMP_A1 */
/* Description: Slope of second piecewise linear function */

/* Bits 11..0 : Slope of second piecewise linear function */
#define TEMP_A1_A1_Pos (0UL) /*!< Position of A1 field. */
#define TEMP_A1_A1_Msk (0xFFFUL << TEMP_A1_A1_Pos) /*!< Bit mask of A1 field. */

/* Register: TEMP_A2 */
/* Description: Slope of third piecewise linear function */

/* Bits 11..0 : Slope of third piecewise linear function */
#define TEMP_A2_A2_Pos (0UL) /*!< Position of A2 field. */
#define TEMP_A2_A2_Msk (0xFFFUL << TEMP_A2_A2_Pos) /*!< Bit mask of A2 field. */

/* Register: TEMP_A3 */
/* Description: Slope of fourth piecewise linear function */

/* Bits 11..0 : Slope of fourth piecewise linear function */
#define TEMP_A3_A3_Pos (0UL) /*!< Position of A3 field. */
#define TEMP_A3_A3_Msk (0xFFFUL << TEMP_A3_A3_Pos) /*!< Bit mask of A3 field. */

/* Register: TEMP_A4 */
/* Description: Slope of fifth piecewise linear function */

/* Bits 11..0 : Slope of fifth piecewise linear function */
#define TEMP_A4_A4_Pos (0UL) /*!< Position of A4 field. */
#define TEMP_A4_A4_Msk (0xFFFUL << TEMP_A4_A4_Pos) /*!< Bit mask of A4 field. */

/* Register: TEMP_A5 */
/* Description: Slope of sixth piecewise linear function */

/* Bits 11..0 : Slope of sixth piecewise linear function */
#define TEMP_A5_A5_Pos (0UL) /*!< Position of A5 field. */
#define TEMP_A5_A5_Msk (0xFFFUL << TEMP_A5_A5_Pos) /*!< Bit mask of A5 field. */

/* Register: TEMP_B0 */
/* Description: y-intercept of first piecewise linear function */

/* Bits 11..0 : y-intercept of first piecewise linear function */
#define TEMP_B0_B0_Pos (0UL) /*!< Position of B0 field. */
#define TEMP_B0_B0_Msk (0xFFFUL << TEMP_B0_B0_Pos) /*!< Bit mask of B0 field. */

/* Register: TEMP_B1 */
/* Description: y-intercept of second piecewise linear function */

/* Bits 11..0 : y-intercept of second piecewise linear function */
#define TEMP_B1_B1_Pos (0UL) /*!< Position of B1 field. */
#define TEMP_B1_B1_Msk (0xFFFUL << TEMP_B1_B1_Pos) /*!< Bit mask of B1 field. */

/* Register: TEMP_B2 */
/* Description: y-intercept of third piecewise linear function */

/* Bits 11..0 : y-intercept of third piecewise linear function */
#define TEMP_B2_B2_Pos (0UL) /*!< Position of B2 field. */
#define TEMP_B2_B2_Msk (0xFFFUL << TEMP_B2_B2_Pos) /*!< Bit mask of B2 field. */

/* Register: TEMP_B3 */
/* Description: y-intercept of fourth piecewise linear function */

/* Bits 11..0 : y-intercept of fourth piecewise linear function */
#define TEMP_B3_B3_Pos (0UL) /*!< Position of B3 field. */
#define TEMP_B3_B3_Msk (0xFFFUL << TEMP_B3_B3_Pos) /*!< Bit mask of B3 field. */

/* Register: TEMP_B4 */
/* Description: y-intercept of fifth piecewise linear function */

/* Bits 11..0 : y-intercept of fifth piecewise linear function */
#define TEMP_B4_B4_Pos (0UL) /*!< Position of B4 field. */
#define TEMP_B4_B4_Msk (0xFFFUL << TEMP_B4_B4_Pos) /*!< Bit mask of B4 field. */

/* Register: TEMP_B5 */
/* Description: y-intercept of sixth piecewise linear function */

/* Bits 11..0 : y-intercept of sixth piecewise linear function */
#define TEMP_B5_B5_Pos (0UL) /*!< Position of B5 field. */
#define TEMP_B5_B5_Msk (0xFFFUL << TEMP_B5_B5_Pos) /*!< Bit mask of B5 field. */

/* Register: TEMP_T0 */
/* Description: Endpoint of first piecewise linear function */

/* Bits 7..0 : Endpoint of first piecewise linear function */
#define TEMP_T0_T0_Pos (0UL) /*!< Position of T0 field. */
#define TEMP_T0_T0_Msk (0xFFUL << TEMP_T0_T0_Pos) /*!< Bit mask of T0 field. */

/* Register: TEMP_T1 */
/* Description: Endpoint of second piecewise linear function */

/* Bits 7..0 : Endpoint of second piecewise linear function */
#define TEMP_T1_T1_Pos (0UL) /*!< Position of T1 field. */
#define TEMP_T1_T1_Msk (0xFFUL << TEMP_T1_T1_Pos) /*!< Bit mask of T1 field. */

/* Register: TEMP_T2 */
/* Description: Endpoint of third piecewise linear function */

/* Bits 7..0 : Endpoint of third piecewise linear function */
#define TEMP_T2_T2_Pos (0UL) /*!< Position of T2 field. */
#define TEMP_T2_T2_Msk (0xFFUL << TEMP_T2_T2_Pos) /*!< Bit mask of T2 field. */

/* Register: TEMP_T3 */
/* Description: Endpoint of fourth piecewise linear function */

/* Bits 7..0 : Endpoint of fourth piecewise linear function */
#define TEMP_T3_T3_Pos (0UL) /*!< Position of T3 field. */
#define TEMP_T3_T3_Msk (0xFFUL << TEMP_T3_T3_Pos) /*!< Bit mask of T3 field. */

/* Register: TEMP_T4 */
/* Description: Endpoint of fifth piecewise linear function */

/* Bits 7..0 : Endpoint of fifth piecewise linear function */
#define TEMP_T4_T4_Pos (0UL) /*!< Position of T4 field. */
#define TEMP_T4_T4_Msk (0xFFUL << TEMP_T4_T4_Pos) /*!< Bit mask of T4 field. */


/* Peripheral: TIMER */
/* Description: Timer/Counter 0 */

/* Register: TIMER_TASKS_START */
/* Description: Start Timer */

/* Bit 0 : Start Timer */
#define TIMER_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define TIMER_TASKS_START_TASKS_START_Msk (0x1UL << TIMER_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define TIMER_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: TIMER_TASKS_STOP */
/* Description: Stop Timer */

/* Bit 0 : Stop Timer */
#define TIMER_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define TIMER_TASKS_STOP_TASKS_STOP_Msk (0x1UL << TIMER_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define TIMER_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: TIMER_TASKS_COUNT */
/* Description: Increment Timer (Counter mode only) */

/* Bit 0 : Increment Timer (Counter mode only) */
#define TIMER_TASKS_COUNT_TASKS_COUNT_Pos (0UL) /*!< Position of TASKS_COUNT field. */
#define TIMER_TASKS_COUNT_TASKS_COUNT_Msk (0x1UL << TIMER_TASKS_COUNT_TASKS_COUNT_Pos) /*!< Bit mask of TASKS_COUNT field. */
#define TIMER_TASKS_COUNT_TASKS_COUNT_Trigger (1UL) /*!< Trigger task */

/* Register: TIMER_TASKS_CLEAR */
/* Description: Clear time */

/* Bit 0 : Clear time */
#define TIMER_TASKS_CLEAR_TASKS_CLEAR_Pos (0UL) /*!< Position of TASKS_CLEAR field. */
#define TIMER_TASKS_CLEAR_TASKS_CLEAR_Msk (0x1UL << TIMER_TASKS_CLEAR_TASKS_CLEAR_Pos) /*!< Bit mask of TASKS_CLEAR field. */
#define TIMER_TASKS_CLEAR_TASKS_CLEAR_Trigger (1UL) /*!< Trigger task */

/* Register: TIMER_TASKS_SHUTDOWN */
/* Description: Deprecated register - Shut down timer */

/* Bit 0 : Deprecated field -  Shut down timer */
#define TIMER_TASKS_SHUTDOWN_TASKS_SHUTDOWN_Pos (0UL) /*!< Position of TASKS_SHUTDOWN field. */
#define TIMER_TASKS_SHUTDOWN_TASKS_SHUTDOWN_Msk (0x1UL << TIMER_TASKS_SHUTDOWN_TASKS_SHUTDOWN_Pos) /*!< Bit mask of TASKS_SHUTDOWN field. */
#define TIMER_TASKS_SHUTDOWN_TASKS_SHUTDOWN_Trigger (1UL) /*!< Trigger task */

/* Register: TIMER_TASKS_CAPTURE */
/* Description: Description collection: Capture Timer value to CC[n] register */

/* Bit 0 : Capture Timer value to CC[n] register */
#define TIMER_TASKS_CAPTURE_TASKS_CAPTURE_Pos (0UL) /*!< Position of TASKS_CAPTURE field. */
#define TIMER_TASKS_CAPTURE_TASKS_CAPTURE_Msk (0x1UL << TIMER_TASKS_CAPTURE_TASKS_CAPTURE_Pos) /*!< Bit mask of TASKS_CAPTURE field. */
#define TIMER_TASKS_CAPTURE_TASKS_CAPTURE_Trigger (1UL) /*!< Trigger task */

/* Register: TIMER_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define TIMER_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define TIMER_SUBSCRIBE_START_EN_Msk (0x1UL << TIMER_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define TIMER_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define TIMER_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define TIMER_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TIMER_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << TIMER_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TIMER_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define TIMER_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define TIMER_SUBSCRIBE_STOP_EN_Msk (0x1UL << TIMER_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define TIMER_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define TIMER_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define TIMER_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TIMER_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << TIMER_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TIMER_SUBSCRIBE_COUNT */
/* Description: Subscribe configuration for task COUNT */

/* Bit 31 :   */
#define TIMER_SUBSCRIBE_COUNT_EN_Pos (31UL) /*!< Position of EN field. */
#define TIMER_SUBSCRIBE_COUNT_EN_Msk (0x1UL << TIMER_SUBSCRIBE_COUNT_EN_Pos) /*!< Bit mask of EN field. */
#define TIMER_SUBSCRIBE_COUNT_EN_Disabled (0UL) /*!< Disable subscription */
#define TIMER_SUBSCRIBE_COUNT_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task COUNT will subscribe to */
#define TIMER_SUBSCRIBE_COUNT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TIMER_SUBSCRIBE_COUNT_CHIDX_Msk (0xFFUL << TIMER_SUBSCRIBE_COUNT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TIMER_SUBSCRIBE_CLEAR */
/* Description: Subscribe configuration for task CLEAR */

/* Bit 31 :   */
#define TIMER_SUBSCRIBE_CLEAR_EN_Pos (31UL) /*!< Position of EN field. */
#define TIMER_SUBSCRIBE_CLEAR_EN_Msk (0x1UL << TIMER_SUBSCRIBE_CLEAR_EN_Pos) /*!< Bit mask of EN field. */
#define TIMER_SUBSCRIBE_CLEAR_EN_Disabled (0UL) /*!< Disable subscription */
#define TIMER_SUBSCRIBE_CLEAR_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CLEAR will subscribe to */
#define TIMER_SUBSCRIBE_CLEAR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TIMER_SUBSCRIBE_CLEAR_CHIDX_Msk (0xFFUL << TIMER_SUBSCRIBE_CLEAR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TIMER_SUBSCRIBE_SHUTDOWN */
/* Description: Deprecated register - Subscribe configuration for task SHUTDOWN */

/* Bit 31 :   */
#define TIMER_SUBSCRIBE_SHUTDOWN_EN_Pos (31UL) /*!< Position of EN field. */
#define TIMER_SUBSCRIBE_SHUTDOWN_EN_Msk (0x1UL << TIMER_SUBSCRIBE_SHUTDOWN_EN_Pos) /*!< Bit mask of EN field. */
#define TIMER_SUBSCRIBE_SHUTDOWN_EN_Disabled (0UL) /*!< Disable subscription */
#define TIMER_SUBSCRIBE_SHUTDOWN_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task SHUTDOWN will subscribe to */
#define TIMER_SUBSCRIBE_SHUTDOWN_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TIMER_SUBSCRIBE_SHUTDOWN_CHIDX_Msk (0xFFUL << TIMER_SUBSCRIBE_SHUTDOWN_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TIMER_SUBSCRIBE_CAPTURE */
/* Description: Description collection: Subscribe configuration for task CAPTURE[n] */

/* Bit 31 :   */
#define TIMER_SUBSCRIBE_CAPTURE_EN_Pos (31UL) /*!< Position of EN field. */
#define TIMER_SUBSCRIBE_CAPTURE_EN_Msk (0x1UL << TIMER_SUBSCRIBE_CAPTURE_EN_Pos) /*!< Bit mask of EN field. */
#define TIMER_SUBSCRIBE_CAPTURE_EN_Disabled (0UL) /*!< Disable subscription */
#define TIMER_SUBSCRIBE_CAPTURE_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task CAPTURE[n] will subscribe to */
#define TIMER_SUBSCRIBE_CAPTURE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TIMER_SUBSCRIBE_CAPTURE_CHIDX_Msk (0xFFUL << TIMER_SUBSCRIBE_CAPTURE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TIMER_EVENTS_COMPARE */
/* Description: Description collection: Compare event on CC[n] match */

/* Bit 0 : Compare event on CC[n] match */
#define TIMER_EVENTS_COMPARE_EVENTS_COMPARE_Pos (0UL) /*!< Position of EVENTS_COMPARE field. */
#define TIMER_EVENTS_COMPARE_EVENTS_COMPARE_Msk (0x1UL << TIMER_EVENTS_COMPARE_EVENTS_COMPARE_Pos) /*!< Bit mask of EVENTS_COMPARE field. */
#define TIMER_EVENTS_COMPARE_EVENTS_COMPARE_NotGenerated (0UL) /*!< Event not generated */
#define TIMER_EVENTS_COMPARE_EVENTS_COMPARE_Generated (1UL) /*!< Event generated */

/* Register: TIMER_PUBLISH_COMPARE */
/* Description: Description collection: Publish configuration for event COMPARE[n] */

/* Bit 31 :   */
#define TIMER_PUBLISH_COMPARE_EN_Pos (31UL) /*!< Position of EN field. */
#define TIMER_PUBLISH_COMPARE_EN_Msk (0x1UL << TIMER_PUBLISH_COMPARE_EN_Pos) /*!< Bit mask of EN field. */
#define TIMER_PUBLISH_COMPARE_EN_Disabled (0UL) /*!< Disable publishing */
#define TIMER_PUBLISH_COMPARE_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event COMPARE[n] will publish to. */
#define TIMER_PUBLISH_COMPARE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TIMER_PUBLISH_COMPARE_CHIDX_Msk (0xFFUL << TIMER_PUBLISH_COMPARE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TIMER_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 23 : Shortcut between event COMPARE[7] and task STOP */
#define TIMER_SHORTS_COMPARE7_STOP_Pos (23UL) /*!< Position of COMPARE7_STOP field. */
#define TIMER_SHORTS_COMPARE7_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE7_STOP_Pos) /*!< Bit mask of COMPARE7_STOP field. */
#define TIMER_SHORTS_COMPARE7_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE7_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 22 : Shortcut between event COMPARE[6] and task STOP */
#define TIMER_SHORTS_COMPARE6_STOP_Pos (22UL) /*!< Position of COMPARE6_STOP field. */
#define TIMER_SHORTS_COMPARE6_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE6_STOP_Pos) /*!< Bit mask of COMPARE6_STOP field. */
#define TIMER_SHORTS_COMPARE6_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE6_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 21 : Shortcut between event COMPARE[5] and task STOP */
#define TIMER_SHORTS_COMPARE5_STOP_Pos (21UL) /*!< Position of COMPARE5_STOP field. */
#define TIMER_SHORTS_COMPARE5_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE5_STOP_Pos) /*!< Bit mask of COMPARE5_STOP field. */
#define TIMER_SHORTS_COMPARE5_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE5_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 20 : Shortcut between event COMPARE[4] and task STOP */
#define TIMER_SHORTS_COMPARE4_STOP_Pos (20UL) /*!< Position of COMPARE4_STOP field. */
#define TIMER_SHORTS_COMPARE4_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE4_STOP_Pos) /*!< Bit mask of COMPARE4_STOP field. */
#define TIMER_SHORTS_COMPARE4_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE4_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 19 : Shortcut between event COMPARE[3] and task STOP */
#define TIMER_SHORTS_COMPARE3_STOP_Pos (19UL) /*!< Position of COMPARE3_STOP field. */
#define TIMER_SHORTS_COMPARE3_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE3_STOP_Pos) /*!< Bit mask of COMPARE3_STOP field. */
#define TIMER_SHORTS_COMPARE3_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE3_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 18 : Shortcut between event COMPARE[2] and task STOP */
#define TIMER_SHORTS_COMPARE2_STOP_Pos (18UL) /*!< Position of COMPARE2_STOP field. */
#define TIMER_SHORTS_COMPARE2_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE2_STOP_Pos) /*!< Bit mask of COMPARE2_STOP field. */
#define TIMER_SHORTS_COMPARE2_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE2_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 17 : Shortcut between event COMPARE[1] and task STOP */
#define TIMER_SHORTS_COMPARE1_STOP_Pos (17UL) /*!< Position of COMPARE1_STOP field. */
#define TIMER_SHORTS_COMPARE1_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE1_STOP_Pos) /*!< Bit mask of COMPARE1_STOP field. */
#define TIMER_SHORTS_COMPARE1_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE1_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 16 : Shortcut between event COMPARE[0] and task STOP */
#define TIMER_SHORTS_COMPARE0_STOP_Pos (16UL) /*!< Position of COMPARE0_STOP field. */
#define TIMER_SHORTS_COMPARE0_STOP_Msk (0x1UL << TIMER_SHORTS_COMPARE0_STOP_Pos) /*!< Bit mask of COMPARE0_STOP field. */
#define TIMER_SHORTS_COMPARE0_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE0_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 7 : Shortcut between event COMPARE[7] and task CLEAR */
#define TIMER_SHORTS_COMPARE7_CLEAR_Pos (7UL) /*!< Position of COMPARE7_CLEAR field. */
#define TIMER_SHORTS_COMPARE7_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE7_CLEAR_Pos) /*!< Bit mask of COMPARE7_CLEAR field. */
#define TIMER_SHORTS_COMPARE7_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE7_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 6 : Shortcut between event COMPARE[6] and task CLEAR */
#define TIMER_SHORTS_COMPARE6_CLEAR_Pos (6UL) /*!< Position of COMPARE6_CLEAR field. */
#define TIMER_SHORTS_COMPARE6_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE6_CLEAR_Pos) /*!< Bit mask of COMPARE6_CLEAR field. */
#define TIMER_SHORTS_COMPARE6_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE6_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 5 : Shortcut between event COMPARE[5] and task CLEAR */
#define TIMER_SHORTS_COMPARE5_CLEAR_Pos (5UL) /*!< Position of COMPARE5_CLEAR field. */
#define TIMER_SHORTS_COMPARE5_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE5_CLEAR_Pos) /*!< Bit mask of COMPARE5_CLEAR field. */
#define TIMER_SHORTS_COMPARE5_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE5_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 4 : Shortcut between event COMPARE[4] and task CLEAR */
#define TIMER_SHORTS_COMPARE4_CLEAR_Pos (4UL) /*!< Position of COMPARE4_CLEAR field. */
#define TIMER_SHORTS_COMPARE4_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE4_CLEAR_Pos) /*!< Bit mask of COMPARE4_CLEAR field. */
#define TIMER_SHORTS_COMPARE4_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE4_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 3 : Shortcut between event COMPARE[3] and task CLEAR */
#define TIMER_SHORTS_COMPARE3_CLEAR_Pos (3UL) /*!< Position of COMPARE3_CLEAR field. */
#define TIMER_SHORTS_COMPARE3_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE3_CLEAR_Pos) /*!< Bit mask of COMPARE3_CLEAR field. */
#define TIMER_SHORTS_COMPARE3_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE3_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 2 : Shortcut between event COMPARE[2] and task CLEAR */
#define TIMER_SHORTS_COMPARE2_CLEAR_Pos (2UL) /*!< Position of COMPARE2_CLEAR field. */
#define TIMER_SHORTS_COMPARE2_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE2_CLEAR_Pos) /*!< Bit mask of COMPARE2_CLEAR field. */
#define TIMER_SHORTS_COMPARE2_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE2_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 1 : Shortcut between event COMPARE[1] and task CLEAR */
#define TIMER_SHORTS_COMPARE1_CLEAR_Pos (1UL) /*!< Position of COMPARE1_CLEAR field. */
#define TIMER_SHORTS_COMPARE1_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE1_CLEAR_Pos) /*!< Bit mask of COMPARE1_CLEAR field. */
#define TIMER_SHORTS_COMPARE1_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE1_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Bit 0 : Shortcut between event COMPARE[0] and task CLEAR */
#define TIMER_SHORTS_COMPARE0_CLEAR_Pos (0UL) /*!< Position of COMPARE0_CLEAR field. */
#define TIMER_SHORTS_COMPARE0_CLEAR_Msk (0x1UL << TIMER_SHORTS_COMPARE0_CLEAR_Pos) /*!< Bit mask of COMPARE0_CLEAR field. */
#define TIMER_SHORTS_COMPARE0_CLEAR_Disabled (0UL) /*!< Disable shortcut */
#define TIMER_SHORTS_COMPARE0_CLEAR_Enabled (1UL) /*!< Enable shortcut */

/* Register: TIMER_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 23 : Enable or disable interrupt for event COMPARE[7] */
#define TIMER_INTEN_COMPARE7_Pos (23UL) /*!< Position of COMPARE7 field. */
#define TIMER_INTEN_COMPARE7_Msk (0x1UL << TIMER_INTEN_COMPARE7_Pos) /*!< Bit mask of COMPARE7 field. */
#define TIMER_INTEN_COMPARE7_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE7_Enabled (1UL) /*!< Enable */

/* Bit 22 : Enable or disable interrupt for event COMPARE[6] */
#define TIMER_INTEN_COMPARE6_Pos (22UL) /*!< Position of COMPARE6 field. */
#define TIMER_INTEN_COMPARE6_Msk (0x1UL << TIMER_INTEN_COMPARE6_Pos) /*!< Bit mask of COMPARE6 field. */
#define TIMER_INTEN_COMPARE6_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE6_Enabled (1UL) /*!< Enable */

/* Bit 21 : Enable or disable interrupt for event COMPARE[5] */
#define TIMER_INTEN_COMPARE5_Pos (21UL) /*!< Position of COMPARE5 field. */
#define TIMER_INTEN_COMPARE5_Msk (0x1UL << TIMER_INTEN_COMPARE5_Pos) /*!< Bit mask of COMPARE5 field. */
#define TIMER_INTEN_COMPARE5_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE5_Enabled (1UL) /*!< Enable */

/* Bit 20 : Enable or disable interrupt for event COMPARE[4] */
#define TIMER_INTEN_COMPARE4_Pos (20UL) /*!< Position of COMPARE4 field. */
#define TIMER_INTEN_COMPARE4_Msk (0x1UL << TIMER_INTEN_COMPARE4_Pos) /*!< Bit mask of COMPARE4 field. */
#define TIMER_INTEN_COMPARE4_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE4_Enabled (1UL) /*!< Enable */

/* Bit 19 : Enable or disable interrupt for event COMPARE[3] */
#define TIMER_INTEN_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define TIMER_INTEN_COMPARE3_Msk (0x1UL << TIMER_INTEN_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define TIMER_INTEN_COMPARE3_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE3_Enabled (1UL) /*!< Enable */

/* Bit 18 : Enable or disable interrupt for event COMPARE[2] */
#define TIMER_INTEN_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define TIMER_INTEN_COMPARE2_Msk (0x1UL << TIMER_INTEN_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define TIMER_INTEN_COMPARE2_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE2_Enabled (1UL) /*!< Enable */

/* Bit 17 : Enable or disable interrupt for event COMPARE[1] */
#define TIMER_INTEN_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define TIMER_INTEN_COMPARE1_Msk (0x1UL << TIMER_INTEN_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define TIMER_INTEN_COMPARE1_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE1_Enabled (1UL) /*!< Enable */

/* Bit 16 : Enable or disable interrupt for event COMPARE[0] */
#define TIMER_INTEN_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define TIMER_INTEN_COMPARE0_Msk (0x1UL << TIMER_INTEN_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define TIMER_INTEN_COMPARE0_Disabled (0UL) /*!< Disable */
#define TIMER_INTEN_COMPARE0_Enabled (1UL) /*!< Enable */

/* Register: TIMER_INTENSET */
/* Description: Enable interrupt */

/* Bit 23 : Write '1' to enable interrupt for event COMPARE[7] */
#define TIMER_INTENSET_COMPARE7_Pos (23UL) /*!< Position of COMPARE7 field. */
#define TIMER_INTENSET_COMPARE7_Msk (0x1UL << TIMER_INTENSET_COMPARE7_Pos) /*!< Bit mask of COMPARE7 field. */
#define TIMER_INTENSET_COMPARE7_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE7_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE7_Set (1UL) /*!< Enable */

/* Bit 22 : Write '1' to enable interrupt for event COMPARE[6] */
#define TIMER_INTENSET_COMPARE6_Pos (22UL) /*!< Position of COMPARE6 field. */
#define TIMER_INTENSET_COMPARE6_Msk (0x1UL << TIMER_INTENSET_COMPARE6_Pos) /*!< Bit mask of COMPARE6 field. */
#define TIMER_INTENSET_COMPARE6_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE6_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE6_Set (1UL) /*!< Enable */

/* Bit 21 : Write '1' to enable interrupt for event COMPARE[5] */
#define TIMER_INTENSET_COMPARE5_Pos (21UL) /*!< Position of COMPARE5 field. */
#define TIMER_INTENSET_COMPARE5_Msk (0x1UL << TIMER_INTENSET_COMPARE5_Pos) /*!< Bit mask of COMPARE5 field. */
#define TIMER_INTENSET_COMPARE5_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE5_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE5_Set (1UL) /*!< Enable */

/* Bit 20 : Write '1' to enable interrupt for event COMPARE[4] */
#define TIMER_INTENSET_COMPARE4_Pos (20UL) /*!< Position of COMPARE4 field. */
#define TIMER_INTENSET_COMPARE4_Msk (0x1UL << TIMER_INTENSET_COMPARE4_Pos) /*!< Bit mask of COMPARE4 field. */
#define TIMER_INTENSET_COMPARE4_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE4_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE4_Set (1UL) /*!< Enable */

/* Bit 19 : Write '1' to enable interrupt for event COMPARE[3] */
#define TIMER_INTENSET_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define TIMER_INTENSET_COMPARE3_Msk (0x1UL << TIMER_INTENSET_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define TIMER_INTENSET_COMPARE3_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE3_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE3_Set (1UL) /*!< Enable */

/* Bit 18 : Write '1' to enable interrupt for event COMPARE[2] */
#define TIMER_INTENSET_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define TIMER_INTENSET_COMPARE2_Msk (0x1UL << TIMER_INTENSET_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define TIMER_INTENSET_COMPARE2_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE2_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE2_Set (1UL) /*!< Enable */

/* Bit 17 : Write '1' to enable interrupt for event COMPARE[1] */
#define TIMER_INTENSET_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define TIMER_INTENSET_COMPARE1_Msk (0x1UL << TIMER_INTENSET_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define TIMER_INTENSET_COMPARE1_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE1_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE1_Set (1UL) /*!< Enable */

/* Bit 16 : Write '1' to enable interrupt for event COMPARE[0] */
#define TIMER_INTENSET_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define TIMER_INTENSET_COMPARE0_Msk (0x1UL << TIMER_INTENSET_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define TIMER_INTENSET_COMPARE0_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENSET_COMPARE0_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENSET_COMPARE0_Set (1UL) /*!< Enable */

/* Register: TIMER_INTENCLR */
/* Description: Disable interrupt */

/* Bit 23 : Write '1' to disable interrupt for event COMPARE[7] */
#define TIMER_INTENCLR_COMPARE7_Pos (23UL) /*!< Position of COMPARE7 field. */
#define TIMER_INTENCLR_COMPARE7_Msk (0x1UL << TIMER_INTENCLR_COMPARE7_Pos) /*!< Bit mask of COMPARE7 field. */
#define TIMER_INTENCLR_COMPARE7_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE7_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE7_Clear (1UL) /*!< Disable */

/* Bit 22 : Write '1' to disable interrupt for event COMPARE[6] */
#define TIMER_INTENCLR_COMPARE6_Pos (22UL) /*!< Position of COMPARE6 field. */
#define TIMER_INTENCLR_COMPARE6_Msk (0x1UL << TIMER_INTENCLR_COMPARE6_Pos) /*!< Bit mask of COMPARE6 field. */
#define TIMER_INTENCLR_COMPARE6_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE6_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE6_Clear (1UL) /*!< Disable */

/* Bit 21 : Write '1' to disable interrupt for event COMPARE[5] */
#define TIMER_INTENCLR_COMPARE5_Pos (21UL) /*!< Position of COMPARE5 field. */
#define TIMER_INTENCLR_COMPARE5_Msk (0x1UL << TIMER_INTENCLR_COMPARE5_Pos) /*!< Bit mask of COMPARE5 field. */
#define TIMER_INTENCLR_COMPARE5_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE5_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE5_Clear (1UL) /*!< Disable */

/* Bit 20 : Write '1' to disable interrupt for event COMPARE[4] */
#define TIMER_INTENCLR_COMPARE4_Pos (20UL) /*!< Position of COMPARE4 field. */
#define TIMER_INTENCLR_COMPARE4_Msk (0x1UL << TIMER_INTENCLR_COMPARE4_Pos) /*!< Bit mask of COMPARE4 field. */
#define TIMER_INTENCLR_COMPARE4_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE4_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE4_Clear (1UL) /*!< Disable */

/* Bit 19 : Write '1' to disable interrupt for event COMPARE[3] */
#define TIMER_INTENCLR_COMPARE3_Pos (19UL) /*!< Position of COMPARE3 field. */
#define TIMER_INTENCLR_COMPARE3_Msk (0x1UL << TIMER_INTENCLR_COMPARE3_Pos) /*!< Bit mask of COMPARE3 field. */
#define TIMER_INTENCLR_COMPARE3_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE3_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE3_Clear (1UL) /*!< Disable */

/* Bit 18 : Write '1' to disable interrupt for event COMPARE[2] */
#define TIMER_INTENCLR_COMPARE2_Pos (18UL) /*!< Position of COMPARE2 field. */
#define TIMER_INTENCLR_COMPARE2_Msk (0x1UL << TIMER_INTENCLR_COMPARE2_Pos) /*!< Bit mask of COMPARE2 field. */
#define TIMER_INTENCLR_COMPARE2_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE2_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE2_Clear (1UL) /*!< Disable */

/* Bit 17 : Write '1' to disable interrupt for event COMPARE[1] */
#define TIMER_INTENCLR_COMPARE1_Pos (17UL) /*!< Position of COMPARE1 field. */
#define TIMER_INTENCLR_COMPARE1_Msk (0x1UL << TIMER_INTENCLR_COMPARE1_Pos) /*!< Bit mask of COMPARE1 field. */
#define TIMER_INTENCLR_COMPARE1_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE1_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE1_Clear (1UL) /*!< Disable */

/* Bit 16 : Write '1' to disable interrupt for event COMPARE[0] */
#define TIMER_INTENCLR_COMPARE0_Pos (16UL) /*!< Position of COMPARE0 field. */
#define TIMER_INTENCLR_COMPARE0_Msk (0x1UL << TIMER_INTENCLR_COMPARE0_Pos) /*!< Bit mask of COMPARE0 field. */
#define TIMER_INTENCLR_COMPARE0_Disabled (0UL) /*!< Read: Disabled */
#define TIMER_INTENCLR_COMPARE0_Enabled (1UL) /*!< Read: Enabled */
#define TIMER_INTENCLR_COMPARE0_Clear (1UL) /*!< Disable */

/* Register: TIMER_MODE */
/* Description: Timer mode selection */

/* Bits 1..0 : Timer mode */
#define TIMER_MODE_MODE_Pos (0UL) /*!< Position of MODE field. */
#define TIMER_MODE_MODE_Msk (0x3UL << TIMER_MODE_MODE_Pos) /*!< Bit mask of MODE field. */
#define TIMER_MODE_MODE_Timer (0UL) /*!< Select Timer mode */
#define TIMER_MODE_MODE_Counter (1UL) /*!< Deprecated enumerator -  Select Counter mode */
#define TIMER_MODE_MODE_LowPowerCounter (2UL) /*!< Select Low Power Counter mode */

/* Register: TIMER_BITMODE */
/* Description: Configure the number of bits used by the TIMER */

/* Bits 1..0 : Timer bit width */
#define TIMER_BITMODE_BITMODE_Pos (0UL) /*!< Position of BITMODE field. */
#define TIMER_BITMODE_BITMODE_Msk (0x3UL << TIMER_BITMODE_BITMODE_Pos) /*!< Bit mask of BITMODE field. */
#define TIMER_BITMODE_BITMODE_16Bit (0UL) /*!< 16 bit timer bit width */
#define TIMER_BITMODE_BITMODE_08Bit (1UL) /*!< 8 bit timer bit width */
#define TIMER_BITMODE_BITMODE_24Bit (2UL) /*!< 24 bit timer bit width */
#define TIMER_BITMODE_BITMODE_32Bit (3UL) /*!< 32 bit timer bit width */

/* Register: TIMER_PRESCALER */
/* Description: Timer prescaler register */

/* Bits 3..0 : Prescaler value */
#define TIMER_PRESCALER_PRESCALER_Pos (0UL) /*!< Position of PRESCALER field. */
#define TIMER_PRESCALER_PRESCALER_Msk (0xFUL << TIMER_PRESCALER_PRESCALER_Pos) /*!< Bit mask of PRESCALER field. */

/* Register: TIMER_CC */
/* Description: Description collection: Capture/Compare register n */

/* Bits 31..0 : Capture/Compare value */
#define TIMER_CC_CC_Pos (0UL) /*!< Position of CC field. */
#define TIMER_CC_CC_Msk (0xFFFFFFFFUL << TIMER_CC_CC_Pos) /*!< Bit mask of CC field. */

/* Register: TIMER_ONESHOTEN */
/* Description: Description collection: Enable one-shot operation for Capture/Compare channel n */

/* Bit 0 : Enable one-shot operation */
#define TIMER_ONESHOTEN_ONESHOTEN_Pos (0UL) /*!< Position of ONESHOTEN field. */
#define TIMER_ONESHOTEN_ONESHOTEN_Msk (0x1UL << TIMER_ONESHOTEN_ONESHOTEN_Pos) /*!< Bit mask of ONESHOTEN field. */
#define TIMER_ONESHOTEN_ONESHOTEN_Disable (0UL) /*!< Disable one-shot operation */
#define TIMER_ONESHOTEN_ONESHOTEN_Enable (1UL) /*!< Enable one-shot operation */


/* Peripheral: TWIM */
/* Description: I2C compatible Two-Wire Master Interface with EasyDMA */

/* Register: TWIM_TASKS_STARTRX */
/* Description: Start TWI receive sequence */

/* Bit 0 : Start TWI receive sequence */
#define TWIM_TASKS_STARTRX_TASKS_STARTRX_Pos (0UL) /*!< Position of TASKS_STARTRX field. */
#define TWIM_TASKS_STARTRX_TASKS_STARTRX_Msk (0x1UL << TWIM_TASKS_STARTRX_TASKS_STARTRX_Pos) /*!< Bit mask of TASKS_STARTRX field. */
#define TWIM_TASKS_STARTRX_TASKS_STARTRX_Trigger (1UL) /*!< Trigger task */

/* Register: TWIM_TASKS_STARTTX */
/* Description: Start TWI transmit sequence */

/* Bit 0 : Start TWI transmit sequence */
#define TWIM_TASKS_STARTTX_TASKS_STARTTX_Pos (0UL) /*!< Position of TASKS_STARTTX field. */
#define TWIM_TASKS_STARTTX_TASKS_STARTTX_Msk (0x1UL << TWIM_TASKS_STARTTX_TASKS_STARTTX_Pos) /*!< Bit mask of TASKS_STARTTX field. */
#define TWIM_TASKS_STARTTX_TASKS_STARTTX_Trigger (1UL) /*!< Trigger task */

/* Register: TWIM_TASKS_STOP */
/* Description: Stop TWI transaction. Must be issued while the TWI master is not suspended. */

/* Bit 0 : Stop TWI transaction. Must be issued while the TWI master is not suspended. */
#define TWIM_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define TWIM_TASKS_STOP_TASKS_STOP_Msk (0x1UL << TWIM_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define TWIM_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: TWIM_TASKS_SUSPEND */
/* Description: Suspend TWI transaction */

/* Bit 0 : Suspend TWI transaction */
#define TWIM_TASKS_SUSPEND_TASKS_SUSPEND_Pos (0UL) /*!< Position of TASKS_SUSPEND field. */
#define TWIM_TASKS_SUSPEND_TASKS_SUSPEND_Msk (0x1UL << TWIM_TASKS_SUSPEND_TASKS_SUSPEND_Pos) /*!< Bit mask of TASKS_SUSPEND field. */
#define TWIM_TASKS_SUSPEND_TASKS_SUSPEND_Trigger (1UL) /*!< Trigger task */

/* Register: TWIM_TASKS_RESUME */
/* Description: Resume TWI transaction */

/* Bit 0 : Resume TWI transaction */
#define TWIM_TASKS_RESUME_TASKS_RESUME_Pos (0UL) /*!< Position of TASKS_RESUME field. */
#define TWIM_TASKS_RESUME_TASKS_RESUME_Msk (0x1UL << TWIM_TASKS_RESUME_TASKS_RESUME_Pos) /*!< Bit mask of TASKS_RESUME field. */
#define TWIM_TASKS_RESUME_TASKS_RESUME_Trigger (1UL) /*!< Trigger task */

/* Register: TWIM_SUBSCRIBE_STARTRX */
/* Description: Subscribe configuration for task STARTRX */

/* Bit 31 :   */
#define TWIM_SUBSCRIBE_STARTRX_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_SUBSCRIBE_STARTRX_EN_Msk (0x1UL << TWIM_SUBSCRIBE_STARTRX_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_SUBSCRIBE_STARTRX_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIM_SUBSCRIBE_STARTRX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STARTRX will subscribe to */
#define TWIM_SUBSCRIBE_STARTRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_SUBSCRIBE_STARTRX_CHIDX_Msk (0xFFUL << TWIM_SUBSCRIBE_STARTRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_SUBSCRIBE_STARTTX */
/* Description: Subscribe configuration for task STARTTX */

/* Bit 31 :   */
#define TWIM_SUBSCRIBE_STARTTX_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_SUBSCRIBE_STARTTX_EN_Msk (0x1UL << TWIM_SUBSCRIBE_STARTTX_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_SUBSCRIBE_STARTTX_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIM_SUBSCRIBE_STARTTX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STARTTX will subscribe to */
#define TWIM_SUBSCRIBE_STARTTX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_SUBSCRIBE_STARTTX_CHIDX_Msk (0xFFUL << TWIM_SUBSCRIBE_STARTTX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define TWIM_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_SUBSCRIBE_STOP_EN_Msk (0x1UL << TWIM_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIM_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define TWIM_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << TWIM_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_SUBSCRIBE_SUSPEND */
/* Description: Subscribe configuration for task SUSPEND */

/* Bit 31 :   */
#define TWIM_SUBSCRIBE_SUSPEND_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_SUBSCRIBE_SUSPEND_EN_Msk (0x1UL << TWIM_SUBSCRIBE_SUSPEND_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_SUBSCRIBE_SUSPEND_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIM_SUBSCRIBE_SUSPEND_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task SUSPEND will subscribe to */
#define TWIM_SUBSCRIBE_SUSPEND_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_SUBSCRIBE_SUSPEND_CHIDX_Msk (0xFFUL << TWIM_SUBSCRIBE_SUSPEND_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_SUBSCRIBE_RESUME */
/* Description: Subscribe configuration for task RESUME */

/* Bit 31 :   */
#define TWIM_SUBSCRIBE_RESUME_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_SUBSCRIBE_RESUME_EN_Msk (0x1UL << TWIM_SUBSCRIBE_RESUME_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_SUBSCRIBE_RESUME_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIM_SUBSCRIBE_RESUME_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RESUME will subscribe to */
#define TWIM_SUBSCRIBE_RESUME_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_SUBSCRIBE_RESUME_CHIDX_Msk (0xFFUL << TWIM_SUBSCRIBE_RESUME_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_EVENTS_STOPPED */
/* Description: TWI stopped */

/* Bit 0 : TWI stopped */
#define TWIM_EVENTS_STOPPED_EVENTS_STOPPED_Pos (0UL) /*!< Position of EVENTS_STOPPED field. */
#define TWIM_EVENTS_STOPPED_EVENTS_STOPPED_Msk (0x1UL << TWIM_EVENTS_STOPPED_EVENTS_STOPPED_Pos) /*!< Bit mask of EVENTS_STOPPED field. */
#define TWIM_EVENTS_STOPPED_EVENTS_STOPPED_NotGenerated (0UL) /*!< Event not generated */
#define TWIM_EVENTS_STOPPED_EVENTS_STOPPED_Generated (1UL) /*!< Event generated */

/* Register: TWIM_EVENTS_ERROR */
/* Description: TWI error */

/* Bit 0 : TWI error */
#define TWIM_EVENTS_ERROR_EVENTS_ERROR_Pos (0UL) /*!< Position of EVENTS_ERROR field. */
#define TWIM_EVENTS_ERROR_EVENTS_ERROR_Msk (0x1UL << TWIM_EVENTS_ERROR_EVENTS_ERROR_Pos) /*!< Bit mask of EVENTS_ERROR field. */
#define TWIM_EVENTS_ERROR_EVENTS_ERROR_NotGenerated (0UL) /*!< Event not generated */
#define TWIM_EVENTS_ERROR_EVENTS_ERROR_Generated (1UL) /*!< Event generated */

/* Register: TWIM_EVENTS_SUSPENDED */
/* Description: SUSPEND task has been issued, TWI traffic is now suspended. */

/* Bit 0 : SUSPEND task has been issued, TWI traffic is now suspended. */
#define TWIM_EVENTS_SUSPENDED_EVENTS_SUSPENDED_Pos (0UL) /*!< Position of EVENTS_SUSPENDED field. */
#define TWIM_EVENTS_SUSPENDED_EVENTS_SUSPENDED_Msk (0x1UL << TWIM_EVENTS_SUSPENDED_EVENTS_SUSPENDED_Pos) /*!< Bit mask of EVENTS_SUSPENDED field. */
#define TWIM_EVENTS_SUSPENDED_EVENTS_SUSPENDED_NotGenerated (0UL) /*!< Event not generated */
#define TWIM_EVENTS_SUSPENDED_EVENTS_SUSPENDED_Generated (1UL) /*!< Event generated */

/* Register: TWIM_EVENTS_RXSTARTED */
/* Description: Receive sequence started */

/* Bit 0 : Receive sequence started */
#define TWIM_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Pos (0UL) /*!< Position of EVENTS_RXSTARTED field. */
#define TWIM_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Msk (0x1UL << TWIM_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Pos) /*!< Bit mask of EVENTS_RXSTARTED field. */
#define TWIM_EVENTS_RXSTARTED_EVENTS_RXSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define TWIM_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Generated (1UL) /*!< Event generated */

/* Register: TWIM_EVENTS_TXSTARTED */
/* Description: Transmit sequence started */

/* Bit 0 : Transmit sequence started */
#define TWIM_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Pos (0UL) /*!< Position of EVENTS_TXSTARTED field. */
#define TWIM_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Msk (0x1UL << TWIM_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Pos) /*!< Bit mask of EVENTS_TXSTARTED field. */
#define TWIM_EVENTS_TXSTARTED_EVENTS_TXSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define TWIM_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Generated (1UL) /*!< Event generated */

/* Register: TWIM_EVENTS_LASTRX */
/* Description: Byte boundary, starting to receive the last byte */

/* Bit 0 : Byte boundary, starting to receive the last byte */
#define TWIM_EVENTS_LASTRX_EVENTS_LASTRX_Pos (0UL) /*!< Position of EVENTS_LASTRX field. */
#define TWIM_EVENTS_LASTRX_EVENTS_LASTRX_Msk (0x1UL << TWIM_EVENTS_LASTRX_EVENTS_LASTRX_Pos) /*!< Bit mask of EVENTS_LASTRX field. */
#define TWIM_EVENTS_LASTRX_EVENTS_LASTRX_NotGenerated (0UL) /*!< Event not generated */
#define TWIM_EVENTS_LASTRX_EVENTS_LASTRX_Generated (1UL) /*!< Event generated */

/* Register: TWIM_EVENTS_LASTTX */
/* Description: Byte boundary, starting to transmit the last byte */

/* Bit 0 : Byte boundary, starting to transmit the last byte */
#define TWIM_EVENTS_LASTTX_EVENTS_LASTTX_Pos (0UL) /*!< Position of EVENTS_LASTTX field. */
#define TWIM_EVENTS_LASTTX_EVENTS_LASTTX_Msk (0x1UL << TWIM_EVENTS_LASTTX_EVENTS_LASTTX_Pos) /*!< Bit mask of EVENTS_LASTTX field. */
#define TWIM_EVENTS_LASTTX_EVENTS_LASTTX_NotGenerated (0UL) /*!< Event not generated */
#define TWIM_EVENTS_LASTTX_EVENTS_LASTTX_Generated (1UL) /*!< Event generated */

/* Register: TWIM_PUBLISH_STOPPED */
/* Description: Publish configuration for event STOPPED */

/* Bit 31 :   */
#define TWIM_PUBLISH_STOPPED_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_PUBLISH_STOPPED_EN_Msk (0x1UL << TWIM_PUBLISH_STOPPED_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_PUBLISH_STOPPED_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIM_PUBLISH_STOPPED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event STOPPED will publish to. */
#define TWIM_PUBLISH_STOPPED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_PUBLISH_STOPPED_CHIDX_Msk (0xFFUL << TWIM_PUBLISH_STOPPED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_PUBLISH_ERROR */
/* Description: Publish configuration for event ERROR */

/* Bit 31 :   */
#define TWIM_PUBLISH_ERROR_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_PUBLISH_ERROR_EN_Msk (0x1UL << TWIM_PUBLISH_ERROR_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_PUBLISH_ERROR_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIM_PUBLISH_ERROR_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ERROR will publish to. */
#define TWIM_PUBLISH_ERROR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_PUBLISH_ERROR_CHIDX_Msk (0xFFUL << TWIM_PUBLISH_ERROR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_PUBLISH_SUSPENDED */
/* Description: Publish configuration for event SUSPENDED */

/* Bit 31 :   */
#define TWIM_PUBLISH_SUSPENDED_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_PUBLISH_SUSPENDED_EN_Msk (0x1UL << TWIM_PUBLISH_SUSPENDED_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_PUBLISH_SUSPENDED_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIM_PUBLISH_SUSPENDED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event SUSPENDED will publish to. */
#define TWIM_PUBLISH_SUSPENDED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_PUBLISH_SUSPENDED_CHIDX_Msk (0xFFUL << TWIM_PUBLISH_SUSPENDED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_PUBLISH_RXSTARTED */
/* Description: Publish configuration for event RXSTARTED */

/* Bit 31 :   */
#define TWIM_PUBLISH_RXSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_PUBLISH_RXSTARTED_EN_Msk (0x1UL << TWIM_PUBLISH_RXSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_PUBLISH_RXSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIM_PUBLISH_RXSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RXSTARTED will publish to. */
#define TWIM_PUBLISH_RXSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_PUBLISH_RXSTARTED_CHIDX_Msk (0xFFUL << TWIM_PUBLISH_RXSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_PUBLISH_TXSTARTED */
/* Description: Publish configuration for event TXSTARTED */

/* Bit 31 :   */
#define TWIM_PUBLISH_TXSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_PUBLISH_TXSTARTED_EN_Msk (0x1UL << TWIM_PUBLISH_TXSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_PUBLISH_TXSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIM_PUBLISH_TXSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TXSTARTED will publish to. */
#define TWIM_PUBLISH_TXSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_PUBLISH_TXSTARTED_CHIDX_Msk (0xFFUL << TWIM_PUBLISH_TXSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_PUBLISH_LASTRX */
/* Description: Publish configuration for event LASTRX */

/* Bit 31 :   */
#define TWIM_PUBLISH_LASTRX_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_PUBLISH_LASTRX_EN_Msk (0x1UL << TWIM_PUBLISH_LASTRX_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_PUBLISH_LASTRX_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIM_PUBLISH_LASTRX_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event LASTRX will publish to. */
#define TWIM_PUBLISH_LASTRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_PUBLISH_LASTRX_CHIDX_Msk (0xFFUL << TWIM_PUBLISH_LASTRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_PUBLISH_LASTTX */
/* Description: Publish configuration for event LASTTX */

/* Bit 31 :   */
#define TWIM_PUBLISH_LASTTX_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIM_PUBLISH_LASTTX_EN_Msk (0x1UL << TWIM_PUBLISH_LASTTX_EN_Pos) /*!< Bit mask of EN field. */
#define TWIM_PUBLISH_LASTTX_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIM_PUBLISH_LASTTX_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event LASTTX will publish to. */
#define TWIM_PUBLISH_LASTTX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIM_PUBLISH_LASTTX_CHIDX_Msk (0xFFUL << TWIM_PUBLISH_LASTTX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIM_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 12 : Shortcut between event LASTRX and task STOP */
#define TWIM_SHORTS_LASTRX_STOP_Pos (12UL) /*!< Position of LASTRX_STOP field. */
#define TWIM_SHORTS_LASTRX_STOP_Msk (0x1UL << TWIM_SHORTS_LASTRX_STOP_Pos) /*!< Bit mask of LASTRX_STOP field. */
#define TWIM_SHORTS_LASTRX_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TWIM_SHORTS_LASTRX_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 10 : Shortcut between event LASTRX and task STARTTX */
#define TWIM_SHORTS_LASTRX_STARTTX_Pos (10UL) /*!< Position of LASTRX_STARTTX field. */
#define TWIM_SHORTS_LASTRX_STARTTX_Msk (0x1UL << TWIM_SHORTS_LASTRX_STARTTX_Pos) /*!< Bit mask of LASTRX_STARTTX field. */
#define TWIM_SHORTS_LASTRX_STARTTX_Disabled (0UL) /*!< Disable shortcut */
#define TWIM_SHORTS_LASTRX_STARTTX_Enabled (1UL) /*!< Enable shortcut */

/* Bit 9 : Shortcut between event LASTTX and task STOP */
#define TWIM_SHORTS_LASTTX_STOP_Pos (9UL) /*!< Position of LASTTX_STOP field. */
#define TWIM_SHORTS_LASTTX_STOP_Msk (0x1UL << TWIM_SHORTS_LASTTX_STOP_Pos) /*!< Bit mask of LASTTX_STOP field. */
#define TWIM_SHORTS_LASTTX_STOP_Disabled (0UL) /*!< Disable shortcut */
#define TWIM_SHORTS_LASTTX_STOP_Enabled (1UL) /*!< Enable shortcut */

/* Bit 8 : Shortcut between event LASTTX and task SUSPEND */
#define TWIM_SHORTS_LASTTX_SUSPEND_Pos (8UL) /*!< Position of LASTTX_SUSPEND field. */
#define TWIM_SHORTS_LASTTX_SUSPEND_Msk (0x1UL << TWIM_SHORTS_LASTTX_SUSPEND_Pos) /*!< Bit mask of LASTTX_SUSPEND field. */
#define TWIM_SHORTS_LASTTX_SUSPEND_Disabled (0UL) /*!< Disable shortcut */
#define TWIM_SHORTS_LASTTX_SUSPEND_Enabled (1UL) /*!< Enable shortcut */

/* Bit 7 : Shortcut between event LASTTX and task STARTRX */
#define TWIM_SHORTS_LASTTX_STARTRX_Pos (7UL) /*!< Position of LASTTX_STARTRX field. */
#define TWIM_SHORTS_LASTTX_STARTRX_Msk (0x1UL << TWIM_SHORTS_LASTTX_STARTRX_Pos) /*!< Bit mask of LASTTX_STARTRX field. */
#define TWIM_SHORTS_LASTTX_STARTRX_Disabled (0UL) /*!< Disable shortcut */
#define TWIM_SHORTS_LASTTX_STARTRX_Enabled (1UL) /*!< Enable shortcut */

/* Register: TWIM_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 24 : Enable or disable interrupt for event LASTTX */
#define TWIM_INTEN_LASTTX_Pos (24UL) /*!< Position of LASTTX field. */
#define TWIM_INTEN_LASTTX_Msk (0x1UL << TWIM_INTEN_LASTTX_Pos) /*!< Bit mask of LASTTX field. */
#define TWIM_INTEN_LASTTX_Disabled (0UL) /*!< Disable */
#define TWIM_INTEN_LASTTX_Enabled (1UL) /*!< Enable */

/* Bit 23 : Enable or disable interrupt for event LASTRX */
#define TWIM_INTEN_LASTRX_Pos (23UL) /*!< Position of LASTRX field. */
#define TWIM_INTEN_LASTRX_Msk (0x1UL << TWIM_INTEN_LASTRX_Pos) /*!< Bit mask of LASTRX field. */
#define TWIM_INTEN_LASTRX_Disabled (0UL) /*!< Disable */
#define TWIM_INTEN_LASTRX_Enabled (1UL) /*!< Enable */

/* Bit 20 : Enable or disable interrupt for event TXSTARTED */
#define TWIM_INTEN_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define TWIM_INTEN_TXSTARTED_Msk (0x1UL << TWIM_INTEN_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define TWIM_INTEN_TXSTARTED_Disabled (0UL) /*!< Disable */
#define TWIM_INTEN_TXSTARTED_Enabled (1UL) /*!< Enable */

/* Bit 19 : Enable or disable interrupt for event RXSTARTED */
#define TWIM_INTEN_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define TWIM_INTEN_RXSTARTED_Msk (0x1UL << TWIM_INTEN_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define TWIM_INTEN_RXSTARTED_Disabled (0UL) /*!< Disable */
#define TWIM_INTEN_RXSTARTED_Enabled (1UL) /*!< Enable */

/* Bit 18 : Enable or disable interrupt for event SUSPENDED */
#define TWIM_INTEN_SUSPENDED_Pos (18UL) /*!< Position of SUSPENDED field. */
#define TWIM_INTEN_SUSPENDED_Msk (0x1UL << TWIM_INTEN_SUSPENDED_Pos) /*!< Bit mask of SUSPENDED field. */
#define TWIM_INTEN_SUSPENDED_Disabled (0UL) /*!< Disable */
#define TWIM_INTEN_SUSPENDED_Enabled (1UL) /*!< Enable */

/* Bit 9 : Enable or disable interrupt for event ERROR */
#define TWIM_INTEN_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define TWIM_INTEN_ERROR_Msk (0x1UL << TWIM_INTEN_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define TWIM_INTEN_ERROR_Disabled (0UL) /*!< Disable */
#define TWIM_INTEN_ERROR_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable interrupt for event STOPPED */
#define TWIM_INTEN_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define TWIM_INTEN_STOPPED_Msk (0x1UL << TWIM_INTEN_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define TWIM_INTEN_STOPPED_Disabled (0UL) /*!< Disable */
#define TWIM_INTEN_STOPPED_Enabled (1UL) /*!< Enable */

/* Register: TWIM_INTENSET */
/* Description: Enable interrupt */

/* Bit 24 : Write '1' to enable interrupt for event LASTTX */
#define TWIM_INTENSET_LASTTX_Pos (24UL) /*!< Position of LASTTX field. */
#define TWIM_INTENSET_LASTTX_Msk (0x1UL << TWIM_INTENSET_LASTTX_Pos) /*!< Bit mask of LASTTX field. */
#define TWIM_INTENSET_LASTTX_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENSET_LASTTX_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENSET_LASTTX_Set (1UL) /*!< Enable */

/* Bit 23 : Write '1' to enable interrupt for event LASTRX */
#define TWIM_INTENSET_LASTRX_Pos (23UL) /*!< Position of LASTRX field. */
#define TWIM_INTENSET_LASTRX_Msk (0x1UL << TWIM_INTENSET_LASTRX_Pos) /*!< Bit mask of LASTRX field. */
#define TWIM_INTENSET_LASTRX_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENSET_LASTRX_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENSET_LASTRX_Set (1UL) /*!< Enable */

/* Bit 20 : Write '1' to enable interrupt for event TXSTARTED */
#define TWIM_INTENSET_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define TWIM_INTENSET_TXSTARTED_Msk (0x1UL << TWIM_INTENSET_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define TWIM_INTENSET_TXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENSET_TXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENSET_TXSTARTED_Set (1UL) /*!< Enable */

/* Bit 19 : Write '1' to enable interrupt for event RXSTARTED */
#define TWIM_INTENSET_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define TWIM_INTENSET_RXSTARTED_Msk (0x1UL << TWIM_INTENSET_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define TWIM_INTENSET_RXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENSET_RXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENSET_RXSTARTED_Set (1UL) /*!< Enable */

/* Bit 18 : Write '1' to enable interrupt for event SUSPENDED */
#define TWIM_INTENSET_SUSPENDED_Pos (18UL) /*!< Position of SUSPENDED field. */
#define TWIM_INTENSET_SUSPENDED_Msk (0x1UL << TWIM_INTENSET_SUSPENDED_Pos) /*!< Bit mask of SUSPENDED field. */
#define TWIM_INTENSET_SUSPENDED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENSET_SUSPENDED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENSET_SUSPENDED_Set (1UL) /*!< Enable */

/* Bit 9 : Write '1' to enable interrupt for event ERROR */
#define TWIM_INTENSET_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define TWIM_INTENSET_ERROR_Msk (0x1UL << TWIM_INTENSET_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define TWIM_INTENSET_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENSET_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENSET_ERROR_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event STOPPED */
#define TWIM_INTENSET_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define TWIM_INTENSET_STOPPED_Msk (0x1UL << TWIM_INTENSET_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define TWIM_INTENSET_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENSET_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENSET_STOPPED_Set (1UL) /*!< Enable */

/* Register: TWIM_INTENCLR */
/* Description: Disable interrupt */

/* Bit 24 : Write '1' to disable interrupt for event LASTTX */
#define TWIM_INTENCLR_LASTTX_Pos (24UL) /*!< Position of LASTTX field. */
#define TWIM_INTENCLR_LASTTX_Msk (0x1UL << TWIM_INTENCLR_LASTTX_Pos) /*!< Bit mask of LASTTX field. */
#define TWIM_INTENCLR_LASTTX_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENCLR_LASTTX_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENCLR_LASTTX_Clear (1UL) /*!< Disable */

/* Bit 23 : Write '1' to disable interrupt for event LASTRX */
#define TWIM_INTENCLR_LASTRX_Pos (23UL) /*!< Position of LASTRX field. */
#define TWIM_INTENCLR_LASTRX_Msk (0x1UL << TWIM_INTENCLR_LASTRX_Pos) /*!< Bit mask of LASTRX field. */
#define TWIM_INTENCLR_LASTRX_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENCLR_LASTRX_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENCLR_LASTRX_Clear (1UL) /*!< Disable */

/* Bit 20 : Write '1' to disable interrupt for event TXSTARTED */
#define TWIM_INTENCLR_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define TWIM_INTENCLR_TXSTARTED_Msk (0x1UL << TWIM_INTENCLR_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define TWIM_INTENCLR_TXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENCLR_TXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENCLR_TXSTARTED_Clear (1UL) /*!< Disable */

/* Bit 19 : Write '1' to disable interrupt for event RXSTARTED */
#define TWIM_INTENCLR_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define TWIM_INTENCLR_RXSTARTED_Msk (0x1UL << TWIM_INTENCLR_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define TWIM_INTENCLR_RXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENCLR_RXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENCLR_RXSTARTED_Clear (1UL) /*!< Disable */

/* Bit 18 : Write '1' to disable interrupt for event SUSPENDED */
#define TWIM_INTENCLR_SUSPENDED_Pos (18UL) /*!< Position of SUSPENDED field. */
#define TWIM_INTENCLR_SUSPENDED_Msk (0x1UL << TWIM_INTENCLR_SUSPENDED_Pos) /*!< Bit mask of SUSPENDED field. */
#define TWIM_INTENCLR_SUSPENDED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENCLR_SUSPENDED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENCLR_SUSPENDED_Clear (1UL) /*!< Disable */

/* Bit 9 : Write '1' to disable interrupt for event ERROR */
#define TWIM_INTENCLR_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define TWIM_INTENCLR_ERROR_Msk (0x1UL << TWIM_INTENCLR_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define TWIM_INTENCLR_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENCLR_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENCLR_ERROR_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event STOPPED */
#define TWIM_INTENCLR_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define TWIM_INTENCLR_STOPPED_Msk (0x1UL << TWIM_INTENCLR_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define TWIM_INTENCLR_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define TWIM_INTENCLR_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define TWIM_INTENCLR_STOPPED_Clear (1UL) /*!< Disable */

/* Register: TWIM_ERRORSRC */
/* Description: Error source */

/* Bit 2 : NACK received after sending a data byte (write '1' to clear) */
#define TWIM_ERRORSRC_DNACK_Pos (2UL) /*!< Position of DNACK field. */
#define TWIM_ERRORSRC_DNACK_Msk (0x1UL << TWIM_ERRORSRC_DNACK_Pos) /*!< Bit mask of DNACK field. */
#define TWIM_ERRORSRC_DNACK_NotReceived (0UL) /*!< Error did not occur */
#define TWIM_ERRORSRC_DNACK_Received (1UL) /*!< Error occurred */

/* Bit 1 : NACK received after sending the address (write '1' to clear) */
#define TWIM_ERRORSRC_ANACK_Pos (1UL) /*!< Position of ANACK field. */
#define TWIM_ERRORSRC_ANACK_Msk (0x1UL << TWIM_ERRORSRC_ANACK_Pos) /*!< Bit mask of ANACK field. */
#define TWIM_ERRORSRC_ANACK_NotReceived (0UL) /*!< Error did not occur */
#define TWIM_ERRORSRC_ANACK_Received (1UL) /*!< Error occurred */

/* Bit 0 : Overrun error */
#define TWIM_ERRORSRC_OVERRUN_Pos (0UL) /*!< Position of OVERRUN field. */
#define TWIM_ERRORSRC_OVERRUN_Msk (0x1UL << TWIM_ERRORSRC_OVERRUN_Pos) /*!< Bit mask of OVERRUN field. */
#define TWIM_ERRORSRC_OVERRUN_NotReceived (0UL) /*!< Error did not occur */
#define TWIM_ERRORSRC_OVERRUN_Received (1UL) /*!< Error occurred */

/* Register: TWIM_ENABLE */
/* Description: Enable TWIM */

/* Bits 3..0 : Enable or disable TWIM */
#define TWIM_ENABLE_ENABLE_Pos (0UL) /*!< Position of ENABLE field. */
#define TWIM_ENABLE_ENABLE_Msk (0xFUL << TWIM_ENABLE_ENABLE_Pos) /*!< Bit mask of ENABLE field. */
#define TWIM_ENABLE_ENABLE_Disabled (0UL) /*!< Disable TWIM */
#define TWIM_ENABLE_ENABLE_Enabled (6UL) /*!< Enable TWIM */

/* Register: TWIM_PSEL_SCL */
/* Description: Pin select for SCL signal */

/* Bit 31 : Connection */
#define TWIM_PSEL_SCL_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define TWIM_PSEL_SCL_CONNECT_Msk (0x1UL << TWIM_PSEL_SCL_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define TWIM_PSEL_SCL_CONNECT_Connected (0UL) /*!< Connect */
#define TWIM_PSEL_SCL_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define TWIM_PSEL_SCL_PORT_Pos (5UL) /*!< Position of PORT field. */
#define TWIM_PSEL_SCL_PORT_Msk (0x1UL << TWIM_PSEL_SCL_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define TWIM_PSEL_SCL_PIN_Pos (0UL) /*!< Position of PIN field. */
#define TWIM_PSEL_SCL_PIN_Msk (0x1FUL << TWIM_PSEL_SCL_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: TWIM_PSEL_SDA */
/* Description: Pin select for SDA signal */

/* Bit 31 : Connection */
#define TWIM_PSEL_SDA_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define TWIM_PSEL_SDA_CONNECT_Msk (0x1UL << TWIM_PSEL_SDA_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define TWIM_PSEL_SDA_CONNECT_Connected (0UL) /*!< Connect */
#define TWIM_PSEL_SDA_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define TWIM_PSEL_SDA_PORT_Pos (5UL) /*!< Position of PORT field. */
#define TWIM_PSEL_SDA_PORT_Msk (0x1UL << TWIM_PSEL_SDA_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define TWIM_PSEL_SDA_PIN_Pos (0UL) /*!< Position of PIN field. */
#define TWIM_PSEL_SDA_PIN_Msk (0x1FUL << TWIM_PSEL_SDA_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: TWIM_FREQUENCY */
/* Description: TWI frequency. Accuracy depends on the HFCLK source selected. */

/* Bits 31..0 : TWI master clock frequency */
#define TWIM_FREQUENCY_FREQUENCY_Pos (0UL) /*!< Position of FREQUENCY field. */
#define TWIM_FREQUENCY_FREQUENCY_Msk (0xFFFFFFFFUL << TWIM_FREQUENCY_FREQUENCY_Pos) /*!< Bit mask of FREQUENCY field. */
#define TWIM_FREQUENCY_FREQUENCY_K100 (0x01980000UL) /*!< 100 kbps */
#define TWIM_FREQUENCY_FREQUENCY_K250 (0x04000000UL) /*!< 250 kbps */
#define TWIM_FREQUENCY_FREQUENCY_K400 (0x06400000UL) /*!< 400 kbps */
#define TWIM_FREQUENCY_FREQUENCY_K1000 (0x0FF00000UL) /*!< 1000 kbps */

/* Register: TWIM_RXD_PTR */
/* Description: Data pointer */

/* Bits 31..0 : Data pointer */
#define TWIM_RXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define TWIM_RXD_PTR_PTR_Msk (0xFFFFFFFFUL << TWIM_RXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: TWIM_RXD_MAXCNT */
/* Description: Maximum number of bytes in receive buffer */

/* Bits 15..0 : Maximum number of bytes in receive buffer */
#define TWIM_RXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define TWIM_RXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << TWIM_RXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: TWIM_RXD_AMOUNT */
/* Description: Number of bytes transferred in the last transaction */

/* Bits 15..0 : Number of bytes transferred in the last transaction. In case of NACK error, includes the NACK'ed byte. */
#define TWIM_RXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define TWIM_RXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << TWIM_RXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: TWIM_RXD_LIST */
/* Description: EasyDMA list type */

/* Bits 2..0 : List type */
#define TWIM_RXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define TWIM_RXD_LIST_LIST_Msk (0x7UL << TWIM_RXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define TWIM_RXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define TWIM_RXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: TWIM_TXD_PTR */
/* Description: Data pointer */

/* Bits 31..0 : Data pointer */
#define TWIM_TXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define TWIM_TXD_PTR_PTR_Msk (0xFFFFFFFFUL << TWIM_TXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: TWIM_TXD_MAXCNT */
/* Description: Maximum number of bytes in transmit buffer */

/* Bits 15..0 : Maximum number of bytes in transmit buffer */
#define TWIM_TXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define TWIM_TXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << TWIM_TXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: TWIM_TXD_AMOUNT */
/* Description: Number of bytes transferred in the last transaction */

/* Bits 15..0 : Number of bytes transferred in the last transaction. In case of NACK error, includes the NACK'ed byte. */
#define TWIM_TXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define TWIM_TXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << TWIM_TXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: TWIM_TXD_LIST */
/* Description: EasyDMA list type */

/* Bits 2..0 : List type */
#define TWIM_TXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define TWIM_TXD_LIST_LIST_Msk (0x7UL << TWIM_TXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define TWIM_TXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define TWIM_TXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: TWIM_ADDRESS */
/* Description: Address used in the TWI transfer */

/* Bits 6..0 : Address used in the TWI transfer */
#define TWIM_ADDRESS_ADDRESS_Pos (0UL) /*!< Position of ADDRESS field. */
#define TWIM_ADDRESS_ADDRESS_Msk (0x7FUL << TWIM_ADDRESS_ADDRESS_Pos) /*!< Bit mask of ADDRESS field. */


/* Peripheral: TWIS */
/* Description: I2C compatible Two-Wire Slave Interface with EasyDMA */

/* Register: TWIS_TASKS_STOP */
/* Description: Stop TWI transaction */

/* Bit 0 : Stop TWI transaction */
#define TWIS_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define TWIS_TASKS_STOP_TASKS_STOP_Msk (0x1UL << TWIS_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define TWIS_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: TWIS_TASKS_SUSPEND */
/* Description: Suspend TWI transaction */

/* Bit 0 : Suspend TWI transaction */
#define TWIS_TASKS_SUSPEND_TASKS_SUSPEND_Pos (0UL) /*!< Position of TASKS_SUSPEND field. */
#define TWIS_TASKS_SUSPEND_TASKS_SUSPEND_Msk (0x1UL << TWIS_TASKS_SUSPEND_TASKS_SUSPEND_Pos) /*!< Bit mask of TASKS_SUSPEND field. */
#define TWIS_TASKS_SUSPEND_TASKS_SUSPEND_Trigger (1UL) /*!< Trigger task */

/* Register: TWIS_TASKS_RESUME */
/* Description: Resume TWI transaction */

/* Bit 0 : Resume TWI transaction */
#define TWIS_TASKS_RESUME_TASKS_RESUME_Pos (0UL) /*!< Position of TASKS_RESUME field. */
#define TWIS_TASKS_RESUME_TASKS_RESUME_Msk (0x1UL << TWIS_TASKS_RESUME_TASKS_RESUME_Pos) /*!< Bit mask of TASKS_RESUME field. */
#define TWIS_TASKS_RESUME_TASKS_RESUME_Trigger (1UL) /*!< Trigger task */

/* Register: TWIS_TASKS_PREPARERX */
/* Description: Prepare the TWI slave to respond to a write command */

/* Bit 0 : Prepare the TWI slave to respond to a write command */
#define TWIS_TASKS_PREPARERX_TASKS_PREPARERX_Pos (0UL) /*!< Position of TASKS_PREPARERX field. */
#define TWIS_TASKS_PREPARERX_TASKS_PREPARERX_Msk (0x1UL << TWIS_TASKS_PREPARERX_TASKS_PREPARERX_Pos) /*!< Bit mask of TASKS_PREPARERX field. */
#define TWIS_TASKS_PREPARERX_TASKS_PREPARERX_Trigger (1UL) /*!< Trigger task */

/* Register: TWIS_TASKS_PREPARETX */
/* Description: Prepare the TWI slave to respond to a read command */

/* Bit 0 : Prepare the TWI slave to respond to a read command */
#define TWIS_TASKS_PREPARETX_TASKS_PREPARETX_Pos (0UL) /*!< Position of TASKS_PREPARETX field. */
#define TWIS_TASKS_PREPARETX_TASKS_PREPARETX_Msk (0x1UL << TWIS_TASKS_PREPARETX_TASKS_PREPARETX_Pos) /*!< Bit mask of TASKS_PREPARETX field. */
#define TWIS_TASKS_PREPARETX_TASKS_PREPARETX_Trigger (1UL) /*!< Trigger task */

/* Register: TWIS_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define TWIS_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_SUBSCRIBE_STOP_EN_Msk (0x1UL << TWIS_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIS_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define TWIS_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << TWIS_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_SUBSCRIBE_SUSPEND */
/* Description: Subscribe configuration for task SUSPEND */

/* Bit 31 :   */
#define TWIS_SUBSCRIBE_SUSPEND_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_SUBSCRIBE_SUSPEND_EN_Msk (0x1UL << TWIS_SUBSCRIBE_SUSPEND_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_SUBSCRIBE_SUSPEND_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIS_SUBSCRIBE_SUSPEND_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task SUSPEND will subscribe to */
#define TWIS_SUBSCRIBE_SUSPEND_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_SUBSCRIBE_SUSPEND_CHIDX_Msk (0xFFUL << TWIS_SUBSCRIBE_SUSPEND_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_SUBSCRIBE_RESUME */
/* Description: Subscribe configuration for task RESUME */

/* Bit 31 :   */
#define TWIS_SUBSCRIBE_RESUME_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_SUBSCRIBE_RESUME_EN_Msk (0x1UL << TWIS_SUBSCRIBE_RESUME_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_SUBSCRIBE_RESUME_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIS_SUBSCRIBE_RESUME_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task RESUME will subscribe to */
#define TWIS_SUBSCRIBE_RESUME_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_SUBSCRIBE_RESUME_CHIDX_Msk (0xFFUL << TWIS_SUBSCRIBE_RESUME_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_SUBSCRIBE_PREPARERX */
/* Description: Subscribe configuration for task PREPARERX */

/* Bit 31 :   */
#define TWIS_SUBSCRIBE_PREPARERX_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_SUBSCRIBE_PREPARERX_EN_Msk (0x1UL << TWIS_SUBSCRIBE_PREPARERX_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_SUBSCRIBE_PREPARERX_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIS_SUBSCRIBE_PREPARERX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task PREPARERX will subscribe to */
#define TWIS_SUBSCRIBE_PREPARERX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_SUBSCRIBE_PREPARERX_CHIDX_Msk (0xFFUL << TWIS_SUBSCRIBE_PREPARERX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_SUBSCRIBE_PREPARETX */
/* Description: Subscribe configuration for task PREPARETX */

/* Bit 31 :   */
#define TWIS_SUBSCRIBE_PREPARETX_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_SUBSCRIBE_PREPARETX_EN_Msk (0x1UL << TWIS_SUBSCRIBE_PREPARETX_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_SUBSCRIBE_PREPARETX_EN_Disabled (0UL) /*!< Disable subscription */
#define TWIS_SUBSCRIBE_PREPARETX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task PREPARETX will subscribe to */
#define TWIS_SUBSCRIBE_PREPARETX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_SUBSCRIBE_PREPARETX_CHIDX_Msk (0xFFUL << TWIS_SUBSCRIBE_PREPARETX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_EVENTS_STOPPED */
/* Description: TWI stopped */

/* Bit 0 : TWI stopped */
#define TWIS_EVENTS_STOPPED_EVENTS_STOPPED_Pos (0UL) /*!< Position of EVENTS_STOPPED field. */
#define TWIS_EVENTS_STOPPED_EVENTS_STOPPED_Msk (0x1UL << TWIS_EVENTS_STOPPED_EVENTS_STOPPED_Pos) /*!< Bit mask of EVENTS_STOPPED field. */
#define TWIS_EVENTS_STOPPED_EVENTS_STOPPED_NotGenerated (0UL) /*!< Event not generated */
#define TWIS_EVENTS_STOPPED_EVENTS_STOPPED_Generated (1UL) /*!< Event generated */

/* Register: TWIS_EVENTS_ERROR */
/* Description: TWI error */

/* Bit 0 : TWI error */
#define TWIS_EVENTS_ERROR_EVENTS_ERROR_Pos (0UL) /*!< Position of EVENTS_ERROR field. */
#define TWIS_EVENTS_ERROR_EVENTS_ERROR_Msk (0x1UL << TWIS_EVENTS_ERROR_EVENTS_ERROR_Pos) /*!< Bit mask of EVENTS_ERROR field. */
#define TWIS_EVENTS_ERROR_EVENTS_ERROR_NotGenerated (0UL) /*!< Event not generated */
#define TWIS_EVENTS_ERROR_EVENTS_ERROR_Generated (1UL) /*!< Event generated */

/* Register: TWIS_EVENTS_RXSTARTED */
/* Description: Receive sequence started */

/* Bit 0 : Receive sequence started */
#define TWIS_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Pos (0UL) /*!< Position of EVENTS_RXSTARTED field. */
#define TWIS_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Msk (0x1UL << TWIS_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Pos) /*!< Bit mask of EVENTS_RXSTARTED field. */
#define TWIS_EVENTS_RXSTARTED_EVENTS_RXSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define TWIS_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Generated (1UL) /*!< Event generated */

/* Register: TWIS_EVENTS_TXSTARTED */
/* Description: Transmit sequence started */

/* Bit 0 : Transmit sequence started */
#define TWIS_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Pos (0UL) /*!< Position of EVENTS_TXSTARTED field. */
#define TWIS_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Msk (0x1UL << TWIS_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Pos) /*!< Bit mask of EVENTS_TXSTARTED field. */
#define TWIS_EVENTS_TXSTARTED_EVENTS_TXSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define TWIS_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Generated (1UL) /*!< Event generated */

/* Register: TWIS_EVENTS_WRITE */
/* Description: Write command received */

/* Bit 0 : Write command received */
#define TWIS_EVENTS_WRITE_EVENTS_WRITE_Pos (0UL) /*!< Position of EVENTS_WRITE field. */
#define TWIS_EVENTS_WRITE_EVENTS_WRITE_Msk (0x1UL << TWIS_EVENTS_WRITE_EVENTS_WRITE_Pos) /*!< Bit mask of EVENTS_WRITE field. */
#define TWIS_EVENTS_WRITE_EVENTS_WRITE_NotGenerated (0UL) /*!< Event not generated */
#define TWIS_EVENTS_WRITE_EVENTS_WRITE_Generated (1UL) /*!< Event generated */

/* Register: TWIS_EVENTS_READ */
/* Description: Read command received */

/* Bit 0 : Read command received */
#define TWIS_EVENTS_READ_EVENTS_READ_Pos (0UL) /*!< Position of EVENTS_READ field. */
#define TWIS_EVENTS_READ_EVENTS_READ_Msk (0x1UL << TWIS_EVENTS_READ_EVENTS_READ_Pos) /*!< Bit mask of EVENTS_READ field. */
#define TWIS_EVENTS_READ_EVENTS_READ_NotGenerated (0UL) /*!< Event not generated */
#define TWIS_EVENTS_READ_EVENTS_READ_Generated (1UL) /*!< Event generated */

/* Register: TWIS_PUBLISH_STOPPED */
/* Description: Publish configuration for event STOPPED */

/* Bit 31 :   */
#define TWIS_PUBLISH_STOPPED_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_PUBLISH_STOPPED_EN_Msk (0x1UL << TWIS_PUBLISH_STOPPED_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_PUBLISH_STOPPED_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIS_PUBLISH_STOPPED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event STOPPED will publish to. */
#define TWIS_PUBLISH_STOPPED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_PUBLISH_STOPPED_CHIDX_Msk (0xFFUL << TWIS_PUBLISH_STOPPED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_PUBLISH_ERROR */
/* Description: Publish configuration for event ERROR */

/* Bit 31 :   */
#define TWIS_PUBLISH_ERROR_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_PUBLISH_ERROR_EN_Msk (0x1UL << TWIS_PUBLISH_ERROR_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_PUBLISH_ERROR_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIS_PUBLISH_ERROR_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ERROR will publish to. */
#define TWIS_PUBLISH_ERROR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_PUBLISH_ERROR_CHIDX_Msk (0xFFUL << TWIS_PUBLISH_ERROR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_PUBLISH_RXSTARTED */
/* Description: Publish configuration for event RXSTARTED */

/* Bit 31 :   */
#define TWIS_PUBLISH_RXSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_PUBLISH_RXSTARTED_EN_Msk (0x1UL << TWIS_PUBLISH_RXSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_PUBLISH_RXSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIS_PUBLISH_RXSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RXSTARTED will publish to. */
#define TWIS_PUBLISH_RXSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_PUBLISH_RXSTARTED_CHIDX_Msk (0xFFUL << TWIS_PUBLISH_RXSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_PUBLISH_TXSTARTED */
/* Description: Publish configuration for event TXSTARTED */

/* Bit 31 :   */
#define TWIS_PUBLISH_TXSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_PUBLISH_TXSTARTED_EN_Msk (0x1UL << TWIS_PUBLISH_TXSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_PUBLISH_TXSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIS_PUBLISH_TXSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TXSTARTED will publish to. */
#define TWIS_PUBLISH_TXSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_PUBLISH_TXSTARTED_CHIDX_Msk (0xFFUL << TWIS_PUBLISH_TXSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_PUBLISH_WRITE */
/* Description: Publish configuration for event WRITE */

/* Bit 31 :   */
#define TWIS_PUBLISH_WRITE_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_PUBLISH_WRITE_EN_Msk (0x1UL << TWIS_PUBLISH_WRITE_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_PUBLISH_WRITE_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIS_PUBLISH_WRITE_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event WRITE will publish to. */
#define TWIS_PUBLISH_WRITE_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_PUBLISH_WRITE_CHIDX_Msk (0xFFUL << TWIS_PUBLISH_WRITE_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_PUBLISH_READ */
/* Description: Publish configuration for event READ */

/* Bit 31 :   */
#define TWIS_PUBLISH_READ_EN_Pos (31UL) /*!< Position of EN field. */
#define TWIS_PUBLISH_READ_EN_Msk (0x1UL << TWIS_PUBLISH_READ_EN_Pos) /*!< Bit mask of EN field. */
#define TWIS_PUBLISH_READ_EN_Disabled (0UL) /*!< Disable publishing */
#define TWIS_PUBLISH_READ_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event READ will publish to. */
#define TWIS_PUBLISH_READ_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define TWIS_PUBLISH_READ_CHIDX_Msk (0xFFUL << TWIS_PUBLISH_READ_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: TWIS_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 14 : Shortcut between event READ and task SUSPEND */
#define TWIS_SHORTS_READ_SUSPEND_Pos (14UL) /*!< Position of READ_SUSPEND field. */
#define TWIS_SHORTS_READ_SUSPEND_Msk (0x1UL << TWIS_SHORTS_READ_SUSPEND_Pos) /*!< Bit mask of READ_SUSPEND field. */
#define TWIS_SHORTS_READ_SUSPEND_Disabled (0UL) /*!< Disable shortcut */
#define TWIS_SHORTS_READ_SUSPEND_Enabled (1UL) /*!< Enable shortcut */

/* Bit 13 : Shortcut between event WRITE and task SUSPEND */
#define TWIS_SHORTS_WRITE_SUSPEND_Pos (13UL) /*!< Position of WRITE_SUSPEND field. */
#define TWIS_SHORTS_WRITE_SUSPEND_Msk (0x1UL << TWIS_SHORTS_WRITE_SUSPEND_Pos) /*!< Bit mask of WRITE_SUSPEND field. */
#define TWIS_SHORTS_WRITE_SUSPEND_Disabled (0UL) /*!< Disable shortcut */
#define TWIS_SHORTS_WRITE_SUSPEND_Enabled (1UL) /*!< Enable shortcut */

/* Register: TWIS_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 26 : Enable or disable interrupt for event READ */
#define TWIS_INTEN_READ_Pos (26UL) /*!< Position of READ field. */
#define TWIS_INTEN_READ_Msk (0x1UL << TWIS_INTEN_READ_Pos) /*!< Bit mask of READ field. */
#define TWIS_INTEN_READ_Disabled (0UL) /*!< Disable */
#define TWIS_INTEN_READ_Enabled (1UL) /*!< Enable */

/* Bit 25 : Enable or disable interrupt for event WRITE */
#define TWIS_INTEN_WRITE_Pos (25UL) /*!< Position of WRITE field. */
#define TWIS_INTEN_WRITE_Msk (0x1UL << TWIS_INTEN_WRITE_Pos) /*!< Bit mask of WRITE field. */
#define TWIS_INTEN_WRITE_Disabled (0UL) /*!< Disable */
#define TWIS_INTEN_WRITE_Enabled (1UL) /*!< Enable */

/* Bit 20 : Enable or disable interrupt for event TXSTARTED */
#define TWIS_INTEN_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define TWIS_INTEN_TXSTARTED_Msk (0x1UL << TWIS_INTEN_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define TWIS_INTEN_TXSTARTED_Disabled (0UL) /*!< Disable */
#define TWIS_INTEN_TXSTARTED_Enabled (1UL) /*!< Enable */

/* Bit 19 : Enable or disable interrupt for event RXSTARTED */
#define TWIS_INTEN_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define TWIS_INTEN_RXSTARTED_Msk (0x1UL << TWIS_INTEN_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define TWIS_INTEN_RXSTARTED_Disabled (0UL) /*!< Disable */
#define TWIS_INTEN_RXSTARTED_Enabled (1UL) /*!< Enable */

/* Bit 9 : Enable or disable interrupt for event ERROR */
#define TWIS_INTEN_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define TWIS_INTEN_ERROR_Msk (0x1UL << TWIS_INTEN_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define TWIS_INTEN_ERROR_Disabled (0UL) /*!< Disable */
#define TWIS_INTEN_ERROR_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable interrupt for event STOPPED */
#define TWIS_INTEN_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define TWIS_INTEN_STOPPED_Msk (0x1UL << TWIS_INTEN_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define TWIS_INTEN_STOPPED_Disabled (0UL) /*!< Disable */
#define TWIS_INTEN_STOPPED_Enabled (1UL) /*!< Enable */

/* Register: TWIS_INTENSET */
/* Description: Enable interrupt */

/* Bit 26 : Write '1' to enable interrupt for event READ */
#define TWIS_INTENSET_READ_Pos (26UL) /*!< Position of READ field. */
#define TWIS_INTENSET_READ_Msk (0x1UL << TWIS_INTENSET_READ_Pos) /*!< Bit mask of READ field. */
#define TWIS_INTENSET_READ_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENSET_READ_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENSET_READ_Set (1UL) /*!< Enable */

/* Bit 25 : Write '1' to enable interrupt for event WRITE */
#define TWIS_INTENSET_WRITE_Pos (25UL) /*!< Position of WRITE field. */
#define TWIS_INTENSET_WRITE_Msk (0x1UL << TWIS_INTENSET_WRITE_Pos) /*!< Bit mask of WRITE field. */
#define TWIS_INTENSET_WRITE_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENSET_WRITE_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENSET_WRITE_Set (1UL) /*!< Enable */

/* Bit 20 : Write '1' to enable interrupt for event TXSTARTED */
#define TWIS_INTENSET_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define TWIS_INTENSET_TXSTARTED_Msk (0x1UL << TWIS_INTENSET_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define TWIS_INTENSET_TXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENSET_TXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENSET_TXSTARTED_Set (1UL) /*!< Enable */

/* Bit 19 : Write '1' to enable interrupt for event RXSTARTED */
#define TWIS_INTENSET_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define TWIS_INTENSET_RXSTARTED_Msk (0x1UL << TWIS_INTENSET_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define TWIS_INTENSET_RXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENSET_RXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENSET_RXSTARTED_Set (1UL) /*!< Enable */

/* Bit 9 : Write '1' to enable interrupt for event ERROR */
#define TWIS_INTENSET_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define TWIS_INTENSET_ERROR_Msk (0x1UL << TWIS_INTENSET_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define TWIS_INTENSET_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENSET_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENSET_ERROR_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event STOPPED */
#define TWIS_INTENSET_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define TWIS_INTENSET_STOPPED_Msk (0x1UL << TWIS_INTENSET_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define TWIS_INTENSET_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENSET_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENSET_STOPPED_Set (1UL) /*!< Enable */

/* Register: TWIS_INTENCLR */
/* Description: Disable interrupt */

/* Bit 26 : Write '1' to disable interrupt for event READ */
#define TWIS_INTENCLR_READ_Pos (26UL) /*!< Position of READ field. */
#define TWIS_INTENCLR_READ_Msk (0x1UL << TWIS_INTENCLR_READ_Pos) /*!< Bit mask of READ field. */
#define TWIS_INTENCLR_READ_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENCLR_READ_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENCLR_READ_Clear (1UL) /*!< Disable */

/* Bit 25 : Write '1' to disable interrupt for event WRITE */
#define TWIS_INTENCLR_WRITE_Pos (25UL) /*!< Position of WRITE field. */
#define TWIS_INTENCLR_WRITE_Msk (0x1UL << TWIS_INTENCLR_WRITE_Pos) /*!< Bit mask of WRITE field. */
#define TWIS_INTENCLR_WRITE_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENCLR_WRITE_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENCLR_WRITE_Clear (1UL) /*!< Disable */

/* Bit 20 : Write '1' to disable interrupt for event TXSTARTED */
#define TWIS_INTENCLR_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define TWIS_INTENCLR_TXSTARTED_Msk (0x1UL << TWIS_INTENCLR_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define TWIS_INTENCLR_TXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENCLR_TXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENCLR_TXSTARTED_Clear (1UL) /*!< Disable */

/* Bit 19 : Write '1' to disable interrupt for event RXSTARTED */
#define TWIS_INTENCLR_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define TWIS_INTENCLR_RXSTARTED_Msk (0x1UL << TWIS_INTENCLR_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define TWIS_INTENCLR_RXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENCLR_RXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENCLR_RXSTARTED_Clear (1UL) /*!< Disable */

/* Bit 9 : Write '1' to disable interrupt for event ERROR */
#define TWIS_INTENCLR_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define TWIS_INTENCLR_ERROR_Msk (0x1UL << TWIS_INTENCLR_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define TWIS_INTENCLR_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENCLR_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENCLR_ERROR_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event STOPPED */
#define TWIS_INTENCLR_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define TWIS_INTENCLR_STOPPED_Msk (0x1UL << TWIS_INTENCLR_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define TWIS_INTENCLR_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define TWIS_INTENCLR_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define TWIS_INTENCLR_STOPPED_Clear (1UL) /*!< Disable */

/* Register: TWIS_ERRORSRC */
/* Description: Error source */

/* Bit 3 : TX buffer over-read detected, and prevented */
#define TWIS_ERRORSRC_OVERREAD_Pos (3UL) /*!< Position of OVERREAD field. */
#define TWIS_ERRORSRC_OVERREAD_Msk (0x1UL << TWIS_ERRORSRC_OVERREAD_Pos) /*!< Bit mask of OVERREAD field. */
#define TWIS_ERRORSRC_OVERREAD_NotDetected (0UL) /*!< Error did not occur */
#define TWIS_ERRORSRC_OVERREAD_Detected (1UL) /*!< Error occurred */

/* Bit 2 : NACK sent after receiving a data byte */
#define TWIS_ERRORSRC_DNACK_Pos (2UL) /*!< Position of DNACK field. */
#define TWIS_ERRORSRC_DNACK_Msk (0x1UL << TWIS_ERRORSRC_DNACK_Pos) /*!< Bit mask of DNACK field. */
#define TWIS_ERRORSRC_DNACK_NotReceived (0UL) /*!< Error did not occur */
#define TWIS_ERRORSRC_DNACK_Received (1UL) /*!< Error occurred */

/* Bit 0 : RX buffer overflow detected, and prevented */
#define TWIS_ERRORSRC_OVERFLOW_Pos (0UL) /*!< Position of OVERFLOW field. */
#define TWIS_ERRORSRC_OVERFLOW_Msk (0x1UL << TWIS_ERRORSRC_OVERFLOW_Pos) /*!< Bit mask of OVERFLOW field. */
#define TWIS_ERRORSRC_OVERFLOW_NotDetected (0UL) /*!< Error did not occur */
#define TWIS_ERRORSRC_OVERFLOW_Detected (1UL) /*!< Error occurred */

/* Register: TWIS_MATCH */
/* Description: Status register indicating which address had a match */

/* Bit 0 : Indication of which address in {ADDRESS} that matched the incoming address */
#define TWIS_MATCH_MATCH_Pos (0UL) /*!< Position of MATCH field. */
#define TWIS_MATCH_MATCH_Msk (0x1UL << TWIS_MATCH_MATCH_Pos) /*!< Bit mask of MATCH field. */

/* Register: TWIS_ENABLE */
/* Description: Enable TWIS */

/* Bits 3..0 : Enable or disable TWIS */
#define TWIS_ENABLE_ENABLE_Pos (0UL) /*!< Position of ENABLE field. */
#define TWIS_ENABLE_ENABLE_Msk (0xFUL << TWIS_ENABLE_ENABLE_Pos) /*!< Bit mask of ENABLE field. */
#define TWIS_ENABLE_ENABLE_Disabled (0UL) /*!< Disable TWIS */
#define TWIS_ENABLE_ENABLE_Enabled (9UL) /*!< Enable TWIS */

/* Register: TWIS_PSEL_SCL */
/* Description: Pin select for SCL signal */

/* Bit 31 : Connection */
#define TWIS_PSEL_SCL_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define TWIS_PSEL_SCL_CONNECT_Msk (0x1UL << TWIS_PSEL_SCL_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define TWIS_PSEL_SCL_CONNECT_Connected (0UL) /*!< Connect */
#define TWIS_PSEL_SCL_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define TWIS_PSEL_SCL_PORT_Pos (5UL) /*!< Position of PORT field. */
#define TWIS_PSEL_SCL_PORT_Msk (0x1UL << TWIS_PSEL_SCL_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define TWIS_PSEL_SCL_PIN_Pos (0UL) /*!< Position of PIN field. */
#define TWIS_PSEL_SCL_PIN_Msk (0x1FUL << TWIS_PSEL_SCL_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: TWIS_PSEL_SDA */
/* Description: Pin select for SDA signal */

/* Bit 31 : Connection */
#define TWIS_PSEL_SDA_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define TWIS_PSEL_SDA_CONNECT_Msk (0x1UL << TWIS_PSEL_SDA_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define TWIS_PSEL_SDA_CONNECT_Connected (0UL) /*!< Connect */
#define TWIS_PSEL_SDA_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define TWIS_PSEL_SDA_PORT_Pos (5UL) /*!< Position of PORT field. */
#define TWIS_PSEL_SDA_PORT_Msk (0x1UL << TWIS_PSEL_SDA_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define TWIS_PSEL_SDA_PIN_Pos (0UL) /*!< Position of PIN field. */
#define TWIS_PSEL_SDA_PIN_Msk (0x1FUL << TWIS_PSEL_SDA_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: TWIS_RXD_PTR */
/* Description: RXD Data pointer */

/* Bits 31..0 : RXD Data pointer */
#define TWIS_RXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define TWIS_RXD_PTR_PTR_Msk (0xFFFFFFFFUL << TWIS_RXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: TWIS_RXD_MAXCNT */
/* Description: Maximum number of bytes in RXD buffer */

/* Bits 15..0 : Maximum number of bytes in RXD buffer */
#define TWIS_RXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define TWIS_RXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << TWIS_RXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: TWIS_RXD_AMOUNT */
/* Description: Number of bytes transferred in the last RXD transaction */

/* Bits 15..0 : Number of bytes transferred in the last RXD transaction */
#define TWIS_RXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define TWIS_RXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << TWIS_RXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: TWIS_RXD_LIST */
/* Description: EasyDMA list type */

/* Bits 1..0 : List type */
#define TWIS_RXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define TWIS_RXD_LIST_LIST_Msk (0x3UL << TWIS_RXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define TWIS_RXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define TWIS_RXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: TWIS_TXD_PTR */
/* Description: TXD Data pointer */

/* Bits 31..0 : TXD Data pointer */
#define TWIS_TXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define TWIS_TXD_PTR_PTR_Msk (0xFFFFFFFFUL << TWIS_TXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: TWIS_TXD_MAXCNT */
/* Description: Maximum number of bytes in TXD buffer */

/* Bits 15..0 : Maximum number of bytes in TXD buffer */
#define TWIS_TXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define TWIS_TXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << TWIS_TXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: TWIS_TXD_AMOUNT */
/* Description: Number of bytes transferred in the last TXD transaction */

/* Bits 15..0 : Number of bytes transferred in the last TXD transaction */
#define TWIS_TXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define TWIS_TXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << TWIS_TXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: TWIS_TXD_LIST */
/* Description: EasyDMA list type */

/* Bits 1..0 : List type */
#define TWIS_TXD_LIST_LIST_Pos (0UL) /*!< Position of LIST field. */
#define TWIS_TXD_LIST_LIST_Msk (0x3UL << TWIS_TXD_LIST_LIST_Pos) /*!< Bit mask of LIST field. */
#define TWIS_TXD_LIST_LIST_Disabled (0UL) /*!< Disable EasyDMA list */
#define TWIS_TXD_LIST_LIST_ArrayList (1UL) /*!< Use array list */

/* Register: TWIS_ADDRESS */
/* Description: Description collection: TWI slave address n */

/* Bits 6..0 : TWI slave address */
#define TWIS_ADDRESS_ADDRESS_Pos (0UL) /*!< Position of ADDRESS field. */
#define TWIS_ADDRESS_ADDRESS_Msk (0x7FUL << TWIS_ADDRESS_ADDRESS_Pos) /*!< Bit mask of ADDRESS field. */

/* Register: TWIS_CONFIG */
/* Description: Configuration register for the address match mechanism */

/* Bit 1 : Enable or disable address matching on ADDRESS[1] */
#define TWIS_CONFIG_ADDRESS1_Pos (1UL) /*!< Position of ADDRESS1 field. */
#define TWIS_CONFIG_ADDRESS1_Msk (0x1UL << TWIS_CONFIG_ADDRESS1_Pos) /*!< Bit mask of ADDRESS1 field. */
#define TWIS_CONFIG_ADDRESS1_Disabled (0UL) /*!< Disabled */
#define TWIS_CONFIG_ADDRESS1_Enabled (1UL) /*!< Enabled */

/* Bit 0 : Enable or disable address matching on ADDRESS[0] */
#define TWIS_CONFIG_ADDRESS0_Pos (0UL) /*!< Position of ADDRESS0 field. */
#define TWIS_CONFIG_ADDRESS0_Msk (0x1UL << TWIS_CONFIG_ADDRESS0_Pos) /*!< Bit mask of ADDRESS0 field. */
#define TWIS_CONFIG_ADDRESS0_Disabled (0UL) /*!< Disabled */
#define TWIS_CONFIG_ADDRESS0_Enabled (1UL) /*!< Enabled */

/* Register: TWIS_ORC */
/* Description: Over-read character. Character sent out in case of an over-read of the transmit buffer. */

/* Bits 7..0 : Over-read character. Character sent out in case of an over-read of the transmit buffer. */
#define TWIS_ORC_ORC_Pos (0UL) /*!< Position of ORC field. */
#define TWIS_ORC_ORC_Msk (0xFFUL << TWIS_ORC_ORC_Pos) /*!< Bit mask of ORC field. */


/* Peripheral: UARTE */
/* Description: UART with EasyDMA */

/* Register: UARTE_TASKS_STARTRX */
/* Description: Start UART receiver */

/* Bit 0 : Start UART receiver */
#define UARTE_TASKS_STARTRX_TASKS_STARTRX_Pos (0UL) /*!< Position of TASKS_STARTRX field. */
#define UARTE_TASKS_STARTRX_TASKS_STARTRX_Msk (0x1UL << UARTE_TASKS_STARTRX_TASKS_STARTRX_Pos) /*!< Bit mask of TASKS_STARTRX field. */
#define UARTE_TASKS_STARTRX_TASKS_STARTRX_Trigger (1UL) /*!< Trigger task */

/* Register: UARTE_TASKS_STOPRX */
/* Description: Stop UART receiver */

/* Bit 0 : Stop UART receiver */
#define UARTE_TASKS_STOPRX_TASKS_STOPRX_Pos (0UL) /*!< Position of TASKS_STOPRX field. */
#define UARTE_TASKS_STOPRX_TASKS_STOPRX_Msk (0x1UL << UARTE_TASKS_STOPRX_TASKS_STOPRX_Pos) /*!< Bit mask of TASKS_STOPRX field. */
#define UARTE_TASKS_STOPRX_TASKS_STOPRX_Trigger (1UL) /*!< Trigger task */

/* Register: UARTE_TASKS_STARTTX */
/* Description: Start UART transmitter */

/* Bit 0 : Start UART transmitter */
#define UARTE_TASKS_STARTTX_TASKS_STARTTX_Pos (0UL) /*!< Position of TASKS_STARTTX field. */
#define UARTE_TASKS_STARTTX_TASKS_STARTTX_Msk (0x1UL << UARTE_TASKS_STARTTX_TASKS_STARTTX_Pos) /*!< Bit mask of TASKS_STARTTX field. */
#define UARTE_TASKS_STARTTX_TASKS_STARTTX_Trigger (1UL) /*!< Trigger task */

/* Register: UARTE_TASKS_STOPTX */
/* Description: Stop UART transmitter */

/* Bit 0 : Stop UART transmitter */
#define UARTE_TASKS_STOPTX_TASKS_STOPTX_Pos (0UL) /*!< Position of TASKS_STOPTX field. */
#define UARTE_TASKS_STOPTX_TASKS_STOPTX_Msk (0x1UL << UARTE_TASKS_STOPTX_TASKS_STOPTX_Pos) /*!< Bit mask of TASKS_STOPTX field. */
#define UARTE_TASKS_STOPTX_TASKS_STOPTX_Trigger (1UL) /*!< Trigger task */

/* Register: UARTE_TASKS_FLUSHRX */
/* Description: Flush RX FIFO into RX buffer */

/* Bit 0 : Flush RX FIFO into RX buffer */
#define UARTE_TASKS_FLUSHRX_TASKS_FLUSHRX_Pos (0UL) /*!< Position of TASKS_FLUSHRX field. */
#define UARTE_TASKS_FLUSHRX_TASKS_FLUSHRX_Msk (0x1UL << UARTE_TASKS_FLUSHRX_TASKS_FLUSHRX_Pos) /*!< Bit mask of TASKS_FLUSHRX field. */
#define UARTE_TASKS_FLUSHRX_TASKS_FLUSHRX_Trigger (1UL) /*!< Trigger task */

/* Register: UARTE_SUBSCRIBE_STARTRX */
/* Description: Subscribe configuration for task STARTRX */

/* Bit 31 :   */
#define UARTE_SUBSCRIBE_STARTRX_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_SUBSCRIBE_STARTRX_EN_Msk (0x1UL << UARTE_SUBSCRIBE_STARTRX_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_SUBSCRIBE_STARTRX_EN_Disabled (0UL) /*!< Disable subscription */
#define UARTE_SUBSCRIBE_STARTRX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STARTRX will subscribe to */
#define UARTE_SUBSCRIBE_STARTRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_SUBSCRIBE_STARTRX_CHIDX_Msk (0xFFUL << UARTE_SUBSCRIBE_STARTRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_SUBSCRIBE_STOPRX */
/* Description: Subscribe configuration for task STOPRX */

/* Bit 31 :   */
#define UARTE_SUBSCRIBE_STOPRX_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_SUBSCRIBE_STOPRX_EN_Msk (0x1UL << UARTE_SUBSCRIBE_STOPRX_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_SUBSCRIBE_STOPRX_EN_Disabled (0UL) /*!< Disable subscription */
#define UARTE_SUBSCRIBE_STOPRX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOPRX will subscribe to */
#define UARTE_SUBSCRIBE_STOPRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_SUBSCRIBE_STOPRX_CHIDX_Msk (0xFFUL << UARTE_SUBSCRIBE_STOPRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_SUBSCRIBE_STARTTX */
/* Description: Subscribe configuration for task STARTTX */

/* Bit 31 :   */
#define UARTE_SUBSCRIBE_STARTTX_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_SUBSCRIBE_STARTTX_EN_Msk (0x1UL << UARTE_SUBSCRIBE_STARTTX_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_SUBSCRIBE_STARTTX_EN_Disabled (0UL) /*!< Disable subscription */
#define UARTE_SUBSCRIBE_STARTTX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STARTTX will subscribe to */
#define UARTE_SUBSCRIBE_STARTTX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_SUBSCRIBE_STARTTX_CHIDX_Msk (0xFFUL << UARTE_SUBSCRIBE_STARTTX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_SUBSCRIBE_STOPTX */
/* Description: Subscribe configuration for task STOPTX */

/* Bit 31 :   */
#define UARTE_SUBSCRIBE_STOPTX_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_SUBSCRIBE_STOPTX_EN_Msk (0x1UL << UARTE_SUBSCRIBE_STOPTX_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_SUBSCRIBE_STOPTX_EN_Disabled (0UL) /*!< Disable subscription */
#define UARTE_SUBSCRIBE_STOPTX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOPTX will subscribe to */
#define UARTE_SUBSCRIBE_STOPTX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_SUBSCRIBE_STOPTX_CHIDX_Msk (0xFFUL << UARTE_SUBSCRIBE_STOPTX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_SUBSCRIBE_FLUSHRX */
/* Description: Subscribe configuration for task FLUSHRX */

/* Bit 31 :   */
#define UARTE_SUBSCRIBE_FLUSHRX_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_SUBSCRIBE_FLUSHRX_EN_Msk (0x1UL << UARTE_SUBSCRIBE_FLUSHRX_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_SUBSCRIBE_FLUSHRX_EN_Disabled (0UL) /*!< Disable subscription */
#define UARTE_SUBSCRIBE_FLUSHRX_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task FLUSHRX will subscribe to */
#define UARTE_SUBSCRIBE_FLUSHRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_SUBSCRIBE_FLUSHRX_CHIDX_Msk (0xFFUL << UARTE_SUBSCRIBE_FLUSHRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_EVENTS_CTS */
/* Description: CTS is activated (set low). Clear To Send. */

/* Bit 0 : CTS is activated (set low). Clear To Send. */
#define UARTE_EVENTS_CTS_EVENTS_CTS_Pos (0UL) /*!< Position of EVENTS_CTS field. */
#define UARTE_EVENTS_CTS_EVENTS_CTS_Msk (0x1UL << UARTE_EVENTS_CTS_EVENTS_CTS_Pos) /*!< Bit mask of EVENTS_CTS field. */
#define UARTE_EVENTS_CTS_EVENTS_CTS_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_CTS_EVENTS_CTS_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_NCTS */
/* Description: CTS is deactivated (set high). Not Clear To Send. */

/* Bit 0 : CTS is deactivated (set high). Not Clear To Send. */
#define UARTE_EVENTS_NCTS_EVENTS_NCTS_Pos (0UL) /*!< Position of EVENTS_NCTS field. */
#define UARTE_EVENTS_NCTS_EVENTS_NCTS_Msk (0x1UL << UARTE_EVENTS_NCTS_EVENTS_NCTS_Pos) /*!< Bit mask of EVENTS_NCTS field. */
#define UARTE_EVENTS_NCTS_EVENTS_NCTS_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_NCTS_EVENTS_NCTS_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_RXDRDY */
/* Description: Data received in RXD (but potentially not yet transferred to Data RAM) */

/* Bit 0 : Data received in RXD (but potentially not yet transferred to Data RAM) */
#define UARTE_EVENTS_RXDRDY_EVENTS_RXDRDY_Pos (0UL) /*!< Position of EVENTS_RXDRDY field. */
#define UARTE_EVENTS_RXDRDY_EVENTS_RXDRDY_Msk (0x1UL << UARTE_EVENTS_RXDRDY_EVENTS_RXDRDY_Pos) /*!< Bit mask of EVENTS_RXDRDY field. */
#define UARTE_EVENTS_RXDRDY_EVENTS_RXDRDY_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_RXDRDY_EVENTS_RXDRDY_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_ENDRX */
/* Description: Receive buffer is filled up */

/* Bit 0 : Receive buffer is filled up */
#define UARTE_EVENTS_ENDRX_EVENTS_ENDRX_Pos (0UL) /*!< Position of EVENTS_ENDRX field. */
#define UARTE_EVENTS_ENDRX_EVENTS_ENDRX_Msk (0x1UL << UARTE_EVENTS_ENDRX_EVENTS_ENDRX_Pos) /*!< Bit mask of EVENTS_ENDRX field. */
#define UARTE_EVENTS_ENDRX_EVENTS_ENDRX_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_ENDRX_EVENTS_ENDRX_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_TXDRDY */
/* Description: Data sent from TXD */

/* Bit 0 : Data sent from TXD */
#define UARTE_EVENTS_TXDRDY_EVENTS_TXDRDY_Pos (0UL) /*!< Position of EVENTS_TXDRDY field. */
#define UARTE_EVENTS_TXDRDY_EVENTS_TXDRDY_Msk (0x1UL << UARTE_EVENTS_TXDRDY_EVENTS_TXDRDY_Pos) /*!< Bit mask of EVENTS_TXDRDY field. */
#define UARTE_EVENTS_TXDRDY_EVENTS_TXDRDY_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_TXDRDY_EVENTS_TXDRDY_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_ENDTX */
/* Description: Last TX byte transmitted */

/* Bit 0 : Last TX byte transmitted */
#define UARTE_EVENTS_ENDTX_EVENTS_ENDTX_Pos (0UL) /*!< Position of EVENTS_ENDTX field. */
#define UARTE_EVENTS_ENDTX_EVENTS_ENDTX_Msk (0x1UL << UARTE_EVENTS_ENDTX_EVENTS_ENDTX_Pos) /*!< Bit mask of EVENTS_ENDTX field. */
#define UARTE_EVENTS_ENDTX_EVENTS_ENDTX_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_ENDTX_EVENTS_ENDTX_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_ERROR */
/* Description: Error detected */

/* Bit 0 : Error detected */
#define UARTE_EVENTS_ERROR_EVENTS_ERROR_Pos (0UL) /*!< Position of EVENTS_ERROR field. */
#define UARTE_EVENTS_ERROR_EVENTS_ERROR_Msk (0x1UL << UARTE_EVENTS_ERROR_EVENTS_ERROR_Pos) /*!< Bit mask of EVENTS_ERROR field. */
#define UARTE_EVENTS_ERROR_EVENTS_ERROR_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_ERROR_EVENTS_ERROR_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_RXTO */
/* Description: Receiver timeout */

/* Bit 0 : Receiver timeout */
#define UARTE_EVENTS_RXTO_EVENTS_RXTO_Pos (0UL) /*!< Position of EVENTS_RXTO field. */
#define UARTE_EVENTS_RXTO_EVENTS_RXTO_Msk (0x1UL << UARTE_EVENTS_RXTO_EVENTS_RXTO_Pos) /*!< Bit mask of EVENTS_RXTO field. */
#define UARTE_EVENTS_RXTO_EVENTS_RXTO_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_RXTO_EVENTS_RXTO_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_RXSTARTED */
/* Description: UART receiver has started */

/* Bit 0 : UART receiver has started */
#define UARTE_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Pos (0UL) /*!< Position of EVENTS_RXSTARTED field. */
#define UARTE_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Msk (0x1UL << UARTE_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Pos) /*!< Bit mask of EVENTS_RXSTARTED field. */
#define UARTE_EVENTS_RXSTARTED_EVENTS_RXSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_RXSTARTED_EVENTS_RXSTARTED_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_TXSTARTED */
/* Description: UART transmitter has started */

/* Bit 0 : UART transmitter has started */
#define UARTE_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Pos (0UL) /*!< Position of EVENTS_TXSTARTED field. */
#define UARTE_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Msk (0x1UL << UARTE_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Pos) /*!< Bit mask of EVENTS_TXSTARTED field. */
#define UARTE_EVENTS_TXSTARTED_EVENTS_TXSTARTED_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_TXSTARTED_EVENTS_TXSTARTED_Generated (1UL) /*!< Event generated */

/* Register: UARTE_EVENTS_TXSTOPPED */
/* Description: Transmitter stopped */

/* Bit 0 : Transmitter stopped */
#define UARTE_EVENTS_TXSTOPPED_EVENTS_TXSTOPPED_Pos (0UL) /*!< Position of EVENTS_TXSTOPPED field. */
#define UARTE_EVENTS_TXSTOPPED_EVENTS_TXSTOPPED_Msk (0x1UL << UARTE_EVENTS_TXSTOPPED_EVENTS_TXSTOPPED_Pos) /*!< Bit mask of EVENTS_TXSTOPPED field. */
#define UARTE_EVENTS_TXSTOPPED_EVENTS_TXSTOPPED_NotGenerated (0UL) /*!< Event not generated */
#define UARTE_EVENTS_TXSTOPPED_EVENTS_TXSTOPPED_Generated (1UL) /*!< Event generated */

/* Register: UARTE_PUBLISH_CTS */
/* Description: Publish configuration for event CTS */

/* Bit 31 :   */
#define UARTE_PUBLISH_CTS_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_CTS_EN_Msk (0x1UL << UARTE_PUBLISH_CTS_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_CTS_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_CTS_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event CTS will publish to. */
#define UARTE_PUBLISH_CTS_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_CTS_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_CTS_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_NCTS */
/* Description: Publish configuration for event NCTS */

/* Bit 31 :   */
#define UARTE_PUBLISH_NCTS_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_NCTS_EN_Msk (0x1UL << UARTE_PUBLISH_NCTS_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_NCTS_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_NCTS_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event NCTS will publish to. */
#define UARTE_PUBLISH_NCTS_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_NCTS_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_NCTS_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_RXDRDY */
/* Description: Publish configuration for event RXDRDY */

/* Bit 31 :   */
#define UARTE_PUBLISH_RXDRDY_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_RXDRDY_EN_Msk (0x1UL << UARTE_PUBLISH_RXDRDY_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_RXDRDY_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_RXDRDY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RXDRDY will publish to. */
#define UARTE_PUBLISH_RXDRDY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_RXDRDY_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_RXDRDY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_ENDRX */
/* Description: Publish configuration for event ENDRX */

/* Bit 31 :   */
#define UARTE_PUBLISH_ENDRX_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_ENDRX_EN_Msk (0x1UL << UARTE_PUBLISH_ENDRX_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_ENDRX_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_ENDRX_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDRX will publish to. */
#define UARTE_PUBLISH_ENDRX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_ENDRX_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_ENDRX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_TXDRDY */
/* Description: Publish configuration for event TXDRDY */

/* Bit 31 :   */
#define UARTE_PUBLISH_TXDRDY_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_TXDRDY_EN_Msk (0x1UL << UARTE_PUBLISH_TXDRDY_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_TXDRDY_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_TXDRDY_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TXDRDY will publish to. */
#define UARTE_PUBLISH_TXDRDY_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_TXDRDY_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_TXDRDY_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_ENDTX */
/* Description: Publish configuration for event ENDTX */

/* Bit 31 :   */
#define UARTE_PUBLISH_ENDTX_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_ENDTX_EN_Msk (0x1UL << UARTE_PUBLISH_ENDTX_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_ENDTX_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_ENDTX_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ENDTX will publish to. */
#define UARTE_PUBLISH_ENDTX_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_ENDTX_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_ENDTX_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_ERROR */
/* Description: Publish configuration for event ERROR */

/* Bit 31 :   */
#define UARTE_PUBLISH_ERROR_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_ERROR_EN_Msk (0x1UL << UARTE_PUBLISH_ERROR_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_ERROR_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_ERROR_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event ERROR will publish to. */
#define UARTE_PUBLISH_ERROR_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_ERROR_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_ERROR_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_RXTO */
/* Description: Publish configuration for event RXTO */

/* Bit 31 :   */
#define UARTE_PUBLISH_RXTO_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_RXTO_EN_Msk (0x1UL << UARTE_PUBLISH_RXTO_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_RXTO_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_RXTO_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RXTO will publish to. */
#define UARTE_PUBLISH_RXTO_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_RXTO_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_RXTO_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_RXSTARTED */
/* Description: Publish configuration for event RXSTARTED */

/* Bit 31 :   */
#define UARTE_PUBLISH_RXSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_RXSTARTED_EN_Msk (0x1UL << UARTE_PUBLISH_RXSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_RXSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_RXSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event RXSTARTED will publish to. */
#define UARTE_PUBLISH_RXSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_RXSTARTED_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_RXSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_TXSTARTED */
/* Description: Publish configuration for event TXSTARTED */

/* Bit 31 :   */
#define UARTE_PUBLISH_TXSTARTED_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_TXSTARTED_EN_Msk (0x1UL << UARTE_PUBLISH_TXSTARTED_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_TXSTARTED_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_TXSTARTED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TXSTARTED will publish to. */
#define UARTE_PUBLISH_TXSTARTED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_TXSTARTED_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_TXSTARTED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_PUBLISH_TXSTOPPED */
/* Description: Publish configuration for event TXSTOPPED */

/* Bit 31 :   */
#define UARTE_PUBLISH_TXSTOPPED_EN_Pos (31UL) /*!< Position of EN field. */
#define UARTE_PUBLISH_TXSTOPPED_EN_Msk (0x1UL << UARTE_PUBLISH_TXSTOPPED_EN_Pos) /*!< Bit mask of EN field. */
#define UARTE_PUBLISH_TXSTOPPED_EN_Disabled (0UL) /*!< Disable publishing */
#define UARTE_PUBLISH_TXSTOPPED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TXSTOPPED will publish to. */
#define UARTE_PUBLISH_TXSTOPPED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define UARTE_PUBLISH_TXSTOPPED_CHIDX_Msk (0xFFUL << UARTE_PUBLISH_TXSTOPPED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: UARTE_SHORTS */
/* Description: Shortcuts between local events and tasks */

/* Bit 6 : Shortcut between event ENDRX and task STOPRX */
#define UARTE_SHORTS_ENDRX_STOPRX_Pos (6UL) /*!< Position of ENDRX_STOPRX field. */
#define UARTE_SHORTS_ENDRX_STOPRX_Msk (0x1UL << UARTE_SHORTS_ENDRX_STOPRX_Pos) /*!< Bit mask of ENDRX_STOPRX field. */
#define UARTE_SHORTS_ENDRX_STOPRX_Disabled (0UL) /*!< Disable shortcut */
#define UARTE_SHORTS_ENDRX_STOPRX_Enabled (1UL) /*!< Enable shortcut */

/* Bit 5 : Shortcut between event ENDRX and task STARTRX */
#define UARTE_SHORTS_ENDRX_STARTRX_Pos (5UL) /*!< Position of ENDRX_STARTRX field. */
#define UARTE_SHORTS_ENDRX_STARTRX_Msk (0x1UL << UARTE_SHORTS_ENDRX_STARTRX_Pos) /*!< Bit mask of ENDRX_STARTRX field. */
#define UARTE_SHORTS_ENDRX_STARTRX_Disabled (0UL) /*!< Disable shortcut */
#define UARTE_SHORTS_ENDRX_STARTRX_Enabled (1UL) /*!< Enable shortcut */

/* Register: UARTE_INTEN */
/* Description: Enable or disable interrupt */

/* Bit 22 : Enable or disable interrupt for event TXSTOPPED */
#define UARTE_INTEN_TXSTOPPED_Pos (22UL) /*!< Position of TXSTOPPED field. */
#define UARTE_INTEN_TXSTOPPED_Msk (0x1UL << UARTE_INTEN_TXSTOPPED_Pos) /*!< Bit mask of TXSTOPPED field. */
#define UARTE_INTEN_TXSTOPPED_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_TXSTOPPED_Enabled (1UL) /*!< Enable */

/* Bit 20 : Enable or disable interrupt for event TXSTARTED */
#define UARTE_INTEN_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define UARTE_INTEN_TXSTARTED_Msk (0x1UL << UARTE_INTEN_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define UARTE_INTEN_TXSTARTED_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_TXSTARTED_Enabled (1UL) /*!< Enable */

/* Bit 19 : Enable or disable interrupt for event RXSTARTED */
#define UARTE_INTEN_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define UARTE_INTEN_RXSTARTED_Msk (0x1UL << UARTE_INTEN_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define UARTE_INTEN_RXSTARTED_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_RXSTARTED_Enabled (1UL) /*!< Enable */

/* Bit 17 : Enable or disable interrupt for event RXTO */
#define UARTE_INTEN_RXTO_Pos (17UL) /*!< Position of RXTO field. */
#define UARTE_INTEN_RXTO_Msk (0x1UL << UARTE_INTEN_RXTO_Pos) /*!< Bit mask of RXTO field. */
#define UARTE_INTEN_RXTO_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_RXTO_Enabled (1UL) /*!< Enable */

/* Bit 9 : Enable or disable interrupt for event ERROR */
#define UARTE_INTEN_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define UARTE_INTEN_ERROR_Msk (0x1UL << UARTE_INTEN_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define UARTE_INTEN_ERROR_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_ERROR_Enabled (1UL) /*!< Enable */

/* Bit 8 : Enable or disable interrupt for event ENDTX */
#define UARTE_INTEN_ENDTX_Pos (8UL) /*!< Position of ENDTX field. */
#define UARTE_INTEN_ENDTX_Msk (0x1UL << UARTE_INTEN_ENDTX_Pos) /*!< Bit mask of ENDTX field. */
#define UARTE_INTEN_ENDTX_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_ENDTX_Enabled (1UL) /*!< Enable */

/* Bit 7 : Enable or disable interrupt for event TXDRDY */
#define UARTE_INTEN_TXDRDY_Pos (7UL) /*!< Position of TXDRDY field. */
#define UARTE_INTEN_TXDRDY_Msk (0x1UL << UARTE_INTEN_TXDRDY_Pos) /*!< Bit mask of TXDRDY field. */
#define UARTE_INTEN_TXDRDY_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_TXDRDY_Enabled (1UL) /*!< Enable */

/* Bit 4 : Enable or disable interrupt for event ENDRX */
#define UARTE_INTEN_ENDRX_Pos (4UL) /*!< Position of ENDRX field. */
#define UARTE_INTEN_ENDRX_Msk (0x1UL << UARTE_INTEN_ENDRX_Pos) /*!< Bit mask of ENDRX field. */
#define UARTE_INTEN_ENDRX_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_ENDRX_Enabled (1UL) /*!< Enable */

/* Bit 2 : Enable or disable interrupt for event RXDRDY */
#define UARTE_INTEN_RXDRDY_Pos (2UL) /*!< Position of RXDRDY field. */
#define UARTE_INTEN_RXDRDY_Msk (0x1UL << UARTE_INTEN_RXDRDY_Pos) /*!< Bit mask of RXDRDY field. */
#define UARTE_INTEN_RXDRDY_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_RXDRDY_Enabled (1UL) /*!< Enable */

/* Bit 1 : Enable or disable interrupt for event NCTS */
#define UARTE_INTEN_NCTS_Pos (1UL) /*!< Position of NCTS field. */
#define UARTE_INTEN_NCTS_Msk (0x1UL << UARTE_INTEN_NCTS_Pos) /*!< Bit mask of NCTS field. */
#define UARTE_INTEN_NCTS_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_NCTS_Enabled (1UL) /*!< Enable */

/* Bit 0 : Enable or disable interrupt for event CTS */
#define UARTE_INTEN_CTS_Pos (0UL) /*!< Position of CTS field. */
#define UARTE_INTEN_CTS_Msk (0x1UL << UARTE_INTEN_CTS_Pos) /*!< Bit mask of CTS field. */
#define UARTE_INTEN_CTS_Disabled (0UL) /*!< Disable */
#define UARTE_INTEN_CTS_Enabled (1UL) /*!< Enable */

/* Register: UARTE_INTENSET */
/* Description: Enable interrupt */

/* Bit 22 : Write '1' to enable interrupt for event TXSTOPPED */
#define UARTE_INTENSET_TXSTOPPED_Pos (22UL) /*!< Position of TXSTOPPED field. */
#define UARTE_INTENSET_TXSTOPPED_Msk (0x1UL << UARTE_INTENSET_TXSTOPPED_Pos) /*!< Bit mask of TXSTOPPED field. */
#define UARTE_INTENSET_TXSTOPPED_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_TXSTOPPED_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_TXSTOPPED_Set (1UL) /*!< Enable */

/* Bit 20 : Write '1' to enable interrupt for event TXSTARTED */
#define UARTE_INTENSET_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define UARTE_INTENSET_TXSTARTED_Msk (0x1UL << UARTE_INTENSET_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define UARTE_INTENSET_TXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_TXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_TXSTARTED_Set (1UL) /*!< Enable */

/* Bit 19 : Write '1' to enable interrupt for event RXSTARTED */
#define UARTE_INTENSET_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define UARTE_INTENSET_RXSTARTED_Msk (0x1UL << UARTE_INTENSET_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define UARTE_INTENSET_RXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_RXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_RXSTARTED_Set (1UL) /*!< Enable */

/* Bit 17 : Write '1' to enable interrupt for event RXTO */
#define UARTE_INTENSET_RXTO_Pos (17UL) /*!< Position of RXTO field. */
#define UARTE_INTENSET_RXTO_Msk (0x1UL << UARTE_INTENSET_RXTO_Pos) /*!< Bit mask of RXTO field. */
#define UARTE_INTENSET_RXTO_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_RXTO_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_RXTO_Set (1UL) /*!< Enable */

/* Bit 9 : Write '1' to enable interrupt for event ERROR */
#define UARTE_INTENSET_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define UARTE_INTENSET_ERROR_Msk (0x1UL << UARTE_INTENSET_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define UARTE_INTENSET_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_ERROR_Set (1UL) /*!< Enable */

/* Bit 8 : Write '1' to enable interrupt for event ENDTX */
#define UARTE_INTENSET_ENDTX_Pos (8UL) /*!< Position of ENDTX field. */
#define UARTE_INTENSET_ENDTX_Msk (0x1UL << UARTE_INTENSET_ENDTX_Pos) /*!< Bit mask of ENDTX field. */
#define UARTE_INTENSET_ENDTX_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_ENDTX_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_ENDTX_Set (1UL) /*!< Enable */

/* Bit 7 : Write '1' to enable interrupt for event TXDRDY */
#define UARTE_INTENSET_TXDRDY_Pos (7UL) /*!< Position of TXDRDY field. */
#define UARTE_INTENSET_TXDRDY_Msk (0x1UL << UARTE_INTENSET_TXDRDY_Pos) /*!< Bit mask of TXDRDY field. */
#define UARTE_INTENSET_TXDRDY_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_TXDRDY_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_TXDRDY_Set (1UL) /*!< Enable */

/* Bit 4 : Write '1' to enable interrupt for event ENDRX */
#define UARTE_INTENSET_ENDRX_Pos (4UL) /*!< Position of ENDRX field. */
#define UARTE_INTENSET_ENDRX_Msk (0x1UL << UARTE_INTENSET_ENDRX_Pos) /*!< Bit mask of ENDRX field. */
#define UARTE_INTENSET_ENDRX_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_ENDRX_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_ENDRX_Set (1UL) /*!< Enable */

/* Bit 2 : Write '1' to enable interrupt for event RXDRDY */
#define UARTE_INTENSET_RXDRDY_Pos (2UL) /*!< Position of RXDRDY field. */
#define UARTE_INTENSET_RXDRDY_Msk (0x1UL << UARTE_INTENSET_RXDRDY_Pos) /*!< Bit mask of RXDRDY field. */
#define UARTE_INTENSET_RXDRDY_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_RXDRDY_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_RXDRDY_Set (1UL) /*!< Enable */

/* Bit 1 : Write '1' to enable interrupt for event NCTS */
#define UARTE_INTENSET_NCTS_Pos (1UL) /*!< Position of NCTS field. */
#define UARTE_INTENSET_NCTS_Msk (0x1UL << UARTE_INTENSET_NCTS_Pos) /*!< Bit mask of NCTS field. */
#define UARTE_INTENSET_NCTS_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_NCTS_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_NCTS_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event CTS */
#define UARTE_INTENSET_CTS_Pos (0UL) /*!< Position of CTS field. */
#define UARTE_INTENSET_CTS_Msk (0x1UL << UARTE_INTENSET_CTS_Pos) /*!< Bit mask of CTS field. */
#define UARTE_INTENSET_CTS_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENSET_CTS_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENSET_CTS_Set (1UL) /*!< Enable */

/* Register: UARTE_INTENCLR */
/* Description: Disable interrupt */

/* Bit 22 : Write '1' to disable interrupt for event TXSTOPPED */
#define UARTE_INTENCLR_TXSTOPPED_Pos (22UL) /*!< Position of TXSTOPPED field. */
#define UARTE_INTENCLR_TXSTOPPED_Msk (0x1UL << UARTE_INTENCLR_TXSTOPPED_Pos) /*!< Bit mask of TXSTOPPED field. */
#define UARTE_INTENCLR_TXSTOPPED_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_TXSTOPPED_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_TXSTOPPED_Clear (1UL) /*!< Disable */

/* Bit 20 : Write '1' to disable interrupt for event TXSTARTED */
#define UARTE_INTENCLR_TXSTARTED_Pos (20UL) /*!< Position of TXSTARTED field. */
#define UARTE_INTENCLR_TXSTARTED_Msk (0x1UL << UARTE_INTENCLR_TXSTARTED_Pos) /*!< Bit mask of TXSTARTED field. */
#define UARTE_INTENCLR_TXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_TXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_TXSTARTED_Clear (1UL) /*!< Disable */

/* Bit 19 : Write '1' to disable interrupt for event RXSTARTED */
#define UARTE_INTENCLR_RXSTARTED_Pos (19UL) /*!< Position of RXSTARTED field. */
#define UARTE_INTENCLR_RXSTARTED_Msk (0x1UL << UARTE_INTENCLR_RXSTARTED_Pos) /*!< Bit mask of RXSTARTED field. */
#define UARTE_INTENCLR_RXSTARTED_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_RXSTARTED_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_RXSTARTED_Clear (1UL) /*!< Disable */

/* Bit 17 : Write '1' to disable interrupt for event RXTO */
#define UARTE_INTENCLR_RXTO_Pos (17UL) /*!< Position of RXTO field. */
#define UARTE_INTENCLR_RXTO_Msk (0x1UL << UARTE_INTENCLR_RXTO_Pos) /*!< Bit mask of RXTO field. */
#define UARTE_INTENCLR_RXTO_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_RXTO_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_RXTO_Clear (1UL) /*!< Disable */

/* Bit 9 : Write '1' to disable interrupt for event ERROR */
#define UARTE_INTENCLR_ERROR_Pos (9UL) /*!< Position of ERROR field. */
#define UARTE_INTENCLR_ERROR_Msk (0x1UL << UARTE_INTENCLR_ERROR_Pos) /*!< Bit mask of ERROR field. */
#define UARTE_INTENCLR_ERROR_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_ERROR_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_ERROR_Clear (1UL) /*!< Disable */

/* Bit 8 : Write '1' to disable interrupt for event ENDTX */
#define UARTE_INTENCLR_ENDTX_Pos (8UL) /*!< Position of ENDTX field. */
#define UARTE_INTENCLR_ENDTX_Msk (0x1UL << UARTE_INTENCLR_ENDTX_Pos) /*!< Bit mask of ENDTX field. */
#define UARTE_INTENCLR_ENDTX_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_ENDTX_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_ENDTX_Clear (1UL) /*!< Disable */

/* Bit 7 : Write '1' to disable interrupt for event TXDRDY */
#define UARTE_INTENCLR_TXDRDY_Pos (7UL) /*!< Position of TXDRDY field. */
#define UARTE_INTENCLR_TXDRDY_Msk (0x1UL << UARTE_INTENCLR_TXDRDY_Pos) /*!< Bit mask of TXDRDY field. */
#define UARTE_INTENCLR_TXDRDY_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_TXDRDY_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_TXDRDY_Clear (1UL) /*!< Disable */

/* Bit 4 : Write '1' to disable interrupt for event ENDRX */
#define UARTE_INTENCLR_ENDRX_Pos (4UL) /*!< Position of ENDRX field. */
#define UARTE_INTENCLR_ENDRX_Msk (0x1UL << UARTE_INTENCLR_ENDRX_Pos) /*!< Bit mask of ENDRX field. */
#define UARTE_INTENCLR_ENDRX_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_ENDRX_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_ENDRX_Clear (1UL) /*!< Disable */

/* Bit 2 : Write '1' to disable interrupt for event RXDRDY */
#define UARTE_INTENCLR_RXDRDY_Pos (2UL) /*!< Position of RXDRDY field. */
#define UARTE_INTENCLR_RXDRDY_Msk (0x1UL << UARTE_INTENCLR_RXDRDY_Pos) /*!< Bit mask of RXDRDY field. */
#define UARTE_INTENCLR_RXDRDY_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_RXDRDY_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_RXDRDY_Clear (1UL) /*!< Disable */

/* Bit 1 : Write '1' to disable interrupt for event NCTS */
#define UARTE_INTENCLR_NCTS_Pos (1UL) /*!< Position of NCTS field. */
#define UARTE_INTENCLR_NCTS_Msk (0x1UL << UARTE_INTENCLR_NCTS_Pos) /*!< Bit mask of NCTS field. */
#define UARTE_INTENCLR_NCTS_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_NCTS_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_NCTS_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event CTS */
#define UARTE_INTENCLR_CTS_Pos (0UL) /*!< Position of CTS field. */
#define UARTE_INTENCLR_CTS_Msk (0x1UL << UARTE_INTENCLR_CTS_Pos) /*!< Bit mask of CTS field. */
#define UARTE_INTENCLR_CTS_Disabled (0UL) /*!< Read: Disabled */
#define UARTE_INTENCLR_CTS_Enabled (1UL) /*!< Read: Enabled */
#define UARTE_INTENCLR_CTS_Clear (1UL) /*!< Disable */

/* Register: UARTE_ERRORSRC */
/* Description: Error source */

/* Bit 3 : Break condition */
#define UARTE_ERRORSRC_BREAK_Pos (3UL) /*!< Position of BREAK field. */
#define UARTE_ERRORSRC_BREAK_Msk (0x1UL << UARTE_ERRORSRC_BREAK_Pos) /*!< Bit mask of BREAK field. */
#define UARTE_ERRORSRC_BREAK_NotPresent (0UL) /*!< Read: error not present */
#define UARTE_ERRORSRC_BREAK_Present (1UL) /*!< Read: error present */

/* Bit 2 : Framing error occurred */
#define UARTE_ERRORSRC_FRAMING_Pos (2UL) /*!< Position of FRAMING field. */
#define UARTE_ERRORSRC_FRAMING_Msk (0x1UL << UARTE_ERRORSRC_FRAMING_Pos) /*!< Bit mask of FRAMING field. */
#define UARTE_ERRORSRC_FRAMING_NotPresent (0UL) /*!< Read: error not present */
#define UARTE_ERRORSRC_FRAMING_Present (1UL) /*!< Read: error present */

/* Bit 1 : Parity error */
#define UARTE_ERRORSRC_PARITY_Pos (1UL) /*!< Position of PARITY field. */
#define UARTE_ERRORSRC_PARITY_Msk (0x1UL << UARTE_ERRORSRC_PARITY_Pos) /*!< Bit mask of PARITY field. */
#define UARTE_ERRORSRC_PARITY_NotPresent (0UL) /*!< Read: error not present */
#define UARTE_ERRORSRC_PARITY_Present (1UL) /*!< Read: error present */

/* Bit 0 : Overrun error */
#define UARTE_ERRORSRC_OVERRUN_Pos (0UL) /*!< Position of OVERRUN field. */
#define UARTE_ERRORSRC_OVERRUN_Msk (0x1UL << UARTE_ERRORSRC_OVERRUN_Pos) /*!< Bit mask of OVERRUN field. */
#define UARTE_ERRORSRC_OVERRUN_NotPresent (0UL) /*!< Read: error not present */
#define UARTE_ERRORSRC_OVERRUN_Present (1UL) /*!< Read: error present */

/* Register: UARTE_ENABLE */
/* Description: Enable UART */

/* Bits 3..0 : Enable or disable UARTE */
#define UARTE_ENABLE_ENABLE_Pos (0UL) /*!< Position of ENABLE field. */
#define UARTE_ENABLE_ENABLE_Msk (0xFUL << UARTE_ENABLE_ENABLE_Pos) /*!< Bit mask of ENABLE field. */
#define UARTE_ENABLE_ENABLE_Disabled (0UL) /*!< Disable UARTE */
#define UARTE_ENABLE_ENABLE_Enabled (8UL) /*!< Enable UARTE */

/* Register: UARTE_PSEL_RTS */
/* Description: Pin select for RTS signal */

/* Bit 31 : Connection */
#define UARTE_PSEL_RTS_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define UARTE_PSEL_RTS_CONNECT_Msk (0x1UL << UARTE_PSEL_RTS_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define UARTE_PSEL_RTS_CONNECT_Connected (0UL) /*!< Connect */
#define UARTE_PSEL_RTS_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define UARTE_PSEL_RTS_PORT_Pos (5UL) /*!< Position of PORT field. */
#define UARTE_PSEL_RTS_PORT_Msk (0x1UL << UARTE_PSEL_RTS_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define UARTE_PSEL_RTS_PIN_Pos (0UL) /*!< Position of PIN field. */
#define UARTE_PSEL_RTS_PIN_Msk (0x1FUL << UARTE_PSEL_RTS_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: UARTE_PSEL_TXD */
/* Description: Pin select for TXD signal */

/* Bit 31 : Connection */
#define UARTE_PSEL_TXD_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define UARTE_PSEL_TXD_CONNECT_Msk (0x1UL << UARTE_PSEL_TXD_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define UARTE_PSEL_TXD_CONNECT_Connected (0UL) /*!< Connect */
#define UARTE_PSEL_TXD_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define UARTE_PSEL_TXD_PORT_Pos (5UL) /*!< Position of PORT field. */
#define UARTE_PSEL_TXD_PORT_Msk (0x1UL << UARTE_PSEL_TXD_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define UARTE_PSEL_TXD_PIN_Pos (0UL) /*!< Position of PIN field. */
#define UARTE_PSEL_TXD_PIN_Msk (0x1FUL << UARTE_PSEL_TXD_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: UARTE_PSEL_CTS */
/* Description: Pin select for CTS signal */

/* Bit 31 : Connection */
#define UARTE_PSEL_CTS_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define UARTE_PSEL_CTS_CONNECT_Msk (0x1UL << UARTE_PSEL_CTS_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define UARTE_PSEL_CTS_CONNECT_Connected (0UL) /*!< Connect */
#define UARTE_PSEL_CTS_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define UARTE_PSEL_CTS_PORT_Pos (5UL) /*!< Position of PORT field. */
#define UARTE_PSEL_CTS_PORT_Msk (0x1UL << UARTE_PSEL_CTS_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define UARTE_PSEL_CTS_PIN_Pos (0UL) /*!< Position of PIN field. */
#define UARTE_PSEL_CTS_PIN_Msk (0x1FUL << UARTE_PSEL_CTS_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: UARTE_PSEL_RXD */
/* Description: Pin select for RXD signal */

/* Bit 31 : Connection */
#define UARTE_PSEL_RXD_CONNECT_Pos (31UL) /*!< Position of CONNECT field. */
#define UARTE_PSEL_RXD_CONNECT_Msk (0x1UL << UARTE_PSEL_RXD_CONNECT_Pos) /*!< Bit mask of CONNECT field. */
#define UARTE_PSEL_RXD_CONNECT_Connected (0UL) /*!< Connect */
#define UARTE_PSEL_RXD_CONNECT_Disconnected (1UL) /*!< Disconnect */

/* Bit 5 : Port number */
#define UARTE_PSEL_RXD_PORT_Pos (5UL) /*!< Position of PORT field. */
#define UARTE_PSEL_RXD_PORT_Msk (0x1UL << UARTE_PSEL_RXD_PORT_Pos) /*!< Bit mask of PORT field. */

/* Bits 4..0 : Pin number */
#define UARTE_PSEL_RXD_PIN_Pos (0UL) /*!< Position of PIN field. */
#define UARTE_PSEL_RXD_PIN_Msk (0x1FUL << UARTE_PSEL_RXD_PIN_Pos) /*!< Bit mask of PIN field. */

/* Register: UARTE_BAUDRATE */
/* Description: Baud rate. Accuracy depends on the HFCLK source selected. */

/* Bits 31..0 : Baud rate */
#define UARTE_BAUDRATE_BAUDRATE_Pos (0UL) /*!< Position of BAUDRATE field. */
#define UARTE_BAUDRATE_BAUDRATE_Msk (0xFFFFFFFFUL << UARTE_BAUDRATE_BAUDRATE_Pos) /*!< Bit mask of BAUDRATE field. */
#define UARTE_BAUDRATE_BAUDRATE_Baud1200 (0x0004F000UL) /*!< 1200 baud (actual rate: 1205) */
#define UARTE_BAUDRATE_BAUDRATE_Baud2400 (0x0009D000UL) /*!< 2400 baud (actual rate: 2396) */
#define UARTE_BAUDRATE_BAUDRATE_Baud4800 (0x0013B000UL) /*!< 4800 baud (actual rate: 4808) */
#define UARTE_BAUDRATE_BAUDRATE_Baud9600 (0x00275000UL) /*!< 9600 baud (actual rate: 9598) */
#define UARTE_BAUDRATE_BAUDRATE_Baud14400 (0x003AF000UL) /*!< 14400 baud (actual rate: 14401) */
#define UARTE_BAUDRATE_BAUDRATE_Baud19200 (0x004EA000UL) /*!< 19200 baud (actual rate: 19208) */
#define UARTE_BAUDRATE_BAUDRATE_Baud28800 (0x0075C000UL) /*!< 28800 baud (actual rate: 28777) */
#define UARTE_BAUDRATE_BAUDRATE_Baud31250 (0x00800000UL) /*!< 31250 baud */
#define UARTE_BAUDRATE_BAUDRATE_Baud38400 (0x009D0000UL) /*!< 38400 baud (actual rate: 38369) */
#define UARTE_BAUDRATE_BAUDRATE_Baud56000 (0x00E50000UL) /*!< 56000 baud (actual rate: 55944) */
#define UARTE_BAUDRATE_BAUDRATE_Baud57600 (0x00EB0000UL) /*!< 57600 baud (actual rate: 57554) */
#define UARTE_BAUDRATE_BAUDRATE_Baud76800 (0x013A9000UL) /*!< 76800 baud (actual rate: 76923) */
#define UARTE_BAUDRATE_BAUDRATE_Baud115200 (0x01D60000UL) /*!< 115200 baud (actual rate: 115108) */
#define UARTE_BAUDRATE_BAUDRATE_Baud230400 (0x03B00000UL) /*!< 230400 baud (actual rate: 231884) */
#define UARTE_BAUDRATE_BAUDRATE_Baud250000 (0x04000000UL) /*!< 250000 baud */
#define UARTE_BAUDRATE_BAUDRATE_Baud460800 (0x07400000UL) /*!< 460800 baud (actual rate: 457143) */
#define UARTE_BAUDRATE_BAUDRATE_Baud921600 (0x0F000000UL) /*!< 921600 baud (actual rate: 941176) */
#define UARTE_BAUDRATE_BAUDRATE_Baud1M (0x10000000UL) /*!< 1 megabaud */

/* Register: UARTE_RXD_PTR */
/* Description: Data pointer */

/* Bits 31..0 : Data pointer */
#define UARTE_RXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define UARTE_RXD_PTR_PTR_Msk (0xFFFFFFFFUL << UARTE_RXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: UARTE_RXD_MAXCNT */
/* Description: Maximum number of bytes in receive buffer */

/* Bits 15..0 : Maximum number of bytes in receive buffer */
#define UARTE_RXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define UARTE_RXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << UARTE_RXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: UARTE_RXD_AMOUNT */
/* Description: Number of bytes transferred in the last transaction */

/* Bits 15..0 : Number of bytes transferred in the last transaction */
#define UARTE_RXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define UARTE_RXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << UARTE_RXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: UARTE_TXD_PTR */
/* Description: Data pointer */

/* Bits 31..0 : Data pointer */
#define UARTE_TXD_PTR_PTR_Pos (0UL) /*!< Position of PTR field. */
#define UARTE_TXD_PTR_PTR_Msk (0xFFFFFFFFUL << UARTE_TXD_PTR_PTR_Pos) /*!< Bit mask of PTR field. */

/* Register: UARTE_TXD_MAXCNT */
/* Description: Maximum number of bytes in transmit buffer */

/* Bits 15..0 : Maximum number of bytes in transmit buffer */
#define UARTE_TXD_MAXCNT_MAXCNT_Pos (0UL) /*!< Position of MAXCNT field. */
#define UARTE_TXD_MAXCNT_MAXCNT_Msk (0xFFFFUL << UARTE_TXD_MAXCNT_MAXCNT_Pos) /*!< Bit mask of MAXCNT field. */

/* Register: UARTE_TXD_AMOUNT */
/* Description: Number of bytes transferred in the last transaction */

/* Bits 15..0 : Number of bytes transferred in the last transaction */
#define UARTE_TXD_AMOUNT_AMOUNT_Pos (0UL) /*!< Position of AMOUNT field. */
#define UARTE_TXD_AMOUNT_AMOUNT_Msk (0xFFFFUL << UARTE_TXD_AMOUNT_AMOUNT_Pos) /*!< Bit mask of AMOUNT field. */

/* Register: UARTE_CONFIG */
/* Description: Configuration of parity and hardware flow control */

/* Bit 8 : Even or odd parity type */
#define UARTE_CONFIG_PARITYTYPE_Pos (8UL) /*!< Position of PARITYTYPE field. */
#define UARTE_CONFIG_PARITYTYPE_Msk (0x1UL << UARTE_CONFIG_PARITYTYPE_Pos) /*!< Bit mask of PARITYTYPE field. */
#define UARTE_CONFIG_PARITYTYPE_Even (0UL) /*!< Even parity */
#define UARTE_CONFIG_PARITYTYPE_Odd (1UL) /*!< Odd parity */

/* Bit 4 : Stop bits */
#define UARTE_CONFIG_STOP_Pos (4UL) /*!< Position of STOP field. */
#define UARTE_CONFIG_STOP_Msk (0x1UL << UARTE_CONFIG_STOP_Pos) /*!< Bit mask of STOP field. */
#define UARTE_CONFIG_STOP_One (0UL) /*!< One stop bit */
#define UARTE_CONFIG_STOP_Two (1UL) /*!< Two stop bits */

/* Bits 3..1 : Parity */
#define UARTE_CONFIG_PARITY_Pos (1UL) /*!< Position of PARITY field. */
#define UARTE_CONFIG_PARITY_Msk (0x7UL << UARTE_CONFIG_PARITY_Pos) /*!< Bit mask of PARITY field. */
#define UARTE_CONFIG_PARITY_Excluded (0x0UL) /*!< Exclude parity bit */
#define UARTE_CONFIG_PARITY_Included (0x7UL) /*!< Include even parity bit */

/* Bit 0 : Hardware flow control */
#define UARTE_CONFIG_HWFC_Pos (0UL) /*!< Position of HWFC field. */
#define UARTE_CONFIG_HWFC_Msk (0x1UL << UARTE_CONFIG_HWFC_Pos) /*!< Bit mask of HWFC field. */
#define UARTE_CONFIG_HWFC_Disabled (0UL) /*!< Disabled */
#define UARTE_CONFIG_HWFC_Enabled (1UL) /*!< Enabled */


/* Peripheral: UICR */
/* Description: User Information Configuration Registers */

/* Register: UICR_APPROTECT */
/* Description: Access port protection */

/* Bits 31..0 : Blocks debugger read/write access to all CPU registers and memory mapped
        addresses. */
#define UICR_APPROTECT_PALL_Pos (0UL) /*!< Position of PALL field. */
#define UICR_APPROTECT_PALL_Msk (0xFFFFFFFFUL << UICR_APPROTECT_PALL_Pos) /*!< Bit mask of PALL field. */
#define UICR_APPROTECT_PALL_Protected (0x00000000UL) /*!< Protected */
#define UICR_APPROTECT_PALL_Unprotected (0x50FA50FAUL) /*!< Unprotected */

/* Register: UICR_ERASEPROTECT */
/* Description: Erase protection */

/* Bits 31..0 : Blocks NVMC ERASEALL and CTRLAP ERASEALL functionality. Using any value except Unprotected will lead to the protection being enabled. */
#define UICR_ERASEPROTECT_PALL_Pos (0UL) /*!< Position of PALL field. */
#define UICR_ERASEPROTECT_PALL_Msk (0xFFFFFFFFUL << UICR_ERASEPROTECT_PALL_Pos) /*!< Bit mask of PALL field. */
#define UICR_ERASEPROTECT_PALL_Protected (0x00000000UL) /*!< Protected */
#define UICR_ERASEPROTECT_PALL_Unprotected (0xFFFFFFFFUL) /*!< Unprotected */

/* Register: UICR_NRFFW */
/* Description: Description collection: Reserved for Nordic firmware design */

/* Bits 31..0 : Reserved for Nordic firmware design */
#define UICR_NRFFW_NRFFW_Pos (0UL) /*!< Position of NRFFW field. */
#define UICR_NRFFW_NRFFW_Msk (0xFFFFFFFFUL << UICR_NRFFW_NRFFW_Pos) /*!< Bit mask of NRFFW field. */

/* Register: UICR_CUSTOMER */
/* Description: Description collection: Reserved for customer */

/* Bits 31..0 : Reserved for customer */
#define UICR_CUSTOMER_CUSTOMER_Pos (0UL) /*!< Position of CUSTOMER field. */
#define UICR_CUSTOMER_CUSTOMER_Msk (0xFFFFFFFFUL << UICR_CUSTOMER_CUSTOMER_Pos) /*!< Bit mask of CUSTOMER field. */


/* Peripheral: VMC */
/* Description: Volatile Memory controller */

/* Register: VMC_RAM_POWER */
/* Description: Description cluster: RAM[n] power control register */

/* Bit 19 : Keep retention on RAM section S3 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWER_S3RETENTION_Pos (19UL) /*!< Position of S3RETENTION field. */
#define VMC_RAM_POWER_S3RETENTION_Msk (0x1UL << VMC_RAM_POWER_S3RETENTION_Pos) /*!< Bit mask of S3RETENTION field. */
#define VMC_RAM_POWER_S3RETENTION_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S3RETENTION_On (1UL) /*!< On */

/* Bit 18 : Keep retention on RAM section S2 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWER_S2RETENTION_Pos (18UL) /*!< Position of S2RETENTION field. */
#define VMC_RAM_POWER_S2RETENTION_Msk (0x1UL << VMC_RAM_POWER_S2RETENTION_Pos) /*!< Bit mask of S2RETENTION field. */
#define VMC_RAM_POWER_S2RETENTION_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S2RETENTION_On (1UL) /*!< On */

/* Bit 17 : Keep retention on RAM section S1 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWER_S1RETENTION_Pos (17UL) /*!< Position of S1RETENTION field. */
#define VMC_RAM_POWER_S1RETENTION_Msk (0x1UL << VMC_RAM_POWER_S1RETENTION_Pos) /*!< Bit mask of S1RETENTION field. */
#define VMC_RAM_POWER_S1RETENTION_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S1RETENTION_On (1UL) /*!< On */

/* Bit 16 : Keep retention on RAM section S0 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWER_S0RETENTION_Pos (16UL) /*!< Position of S0RETENTION field. */
#define VMC_RAM_POWER_S0RETENTION_Msk (0x1UL << VMC_RAM_POWER_S0RETENTION_Pos) /*!< Bit mask of S0RETENTION field. */
#define VMC_RAM_POWER_S0RETENTION_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S0RETENTION_On (1UL) /*!< On */

/* Bit 3 : Keep RAM section S3 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWER_S3POWER_Pos (3UL) /*!< Position of S3POWER field. */
#define VMC_RAM_POWER_S3POWER_Msk (0x1UL << VMC_RAM_POWER_S3POWER_Pos) /*!< Bit mask of S3POWER field. */
#define VMC_RAM_POWER_S3POWER_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S3POWER_On (1UL) /*!< On */

/* Bit 2 : Keep RAM section S2 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWER_S2POWER_Pos (2UL) /*!< Position of S2POWER field. */
#define VMC_RAM_POWER_S2POWER_Msk (0x1UL << VMC_RAM_POWER_S2POWER_Pos) /*!< Bit mask of S2POWER field. */
#define VMC_RAM_POWER_S2POWER_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S2POWER_On (1UL) /*!< On */

/* Bit 1 : Keep RAM section S1 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWER_S1POWER_Pos (1UL) /*!< Position of S1POWER field. */
#define VMC_RAM_POWER_S1POWER_Msk (0x1UL << VMC_RAM_POWER_S1POWER_Pos) /*!< Bit mask of S1POWER field. */
#define VMC_RAM_POWER_S1POWER_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S1POWER_On (1UL) /*!< On */

/* Bit 0 : Keep RAM section S0 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWER_S0POWER_Pos (0UL) /*!< Position of S0POWER field. */
#define VMC_RAM_POWER_S0POWER_Msk (0x1UL << VMC_RAM_POWER_S0POWER_Pos) /*!< Bit mask of S0POWER field. */
#define VMC_RAM_POWER_S0POWER_Off (0UL) /*!< Off */
#define VMC_RAM_POWER_S0POWER_On (1UL) /*!< On */

/* Register: VMC_RAM_POWERSET */
/* Description: Description cluster: RAM[n] power control set register */

/* Bit 19 : Keep retention on RAM section S3 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERSET_S3RETENTION_Pos (19UL) /*!< Position of S3RETENTION field. */
#define VMC_RAM_POWERSET_S3RETENTION_Msk (0x1UL << VMC_RAM_POWERSET_S3RETENTION_Pos) /*!< Bit mask of S3RETENTION field. */
#define VMC_RAM_POWERSET_S3RETENTION_On (1UL) /*!< On */

/* Bit 18 : Keep retention on RAM section S2 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERSET_S2RETENTION_Pos (18UL) /*!< Position of S2RETENTION field. */
#define VMC_RAM_POWERSET_S2RETENTION_Msk (0x1UL << VMC_RAM_POWERSET_S2RETENTION_Pos) /*!< Bit mask of S2RETENTION field. */
#define VMC_RAM_POWERSET_S2RETENTION_On (1UL) /*!< On */

/* Bit 17 : Keep retention on RAM section S1 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERSET_S1RETENTION_Pos (17UL) /*!< Position of S1RETENTION field. */
#define VMC_RAM_POWERSET_S1RETENTION_Msk (0x1UL << VMC_RAM_POWERSET_S1RETENTION_Pos) /*!< Bit mask of S1RETENTION field. */
#define VMC_RAM_POWERSET_S1RETENTION_On (1UL) /*!< On */

/* Bit 16 : Keep retention on RAM section S0 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERSET_S0RETENTION_Pos (16UL) /*!< Position of S0RETENTION field. */
#define VMC_RAM_POWERSET_S0RETENTION_Msk (0x1UL << VMC_RAM_POWERSET_S0RETENTION_Pos) /*!< Bit mask of S0RETENTION field. */
#define VMC_RAM_POWERSET_S0RETENTION_On (1UL) /*!< On */

/* Bit 3 : Keep RAM section S3 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERSET_S3POWER_Pos (3UL) /*!< Position of S3POWER field. */
#define VMC_RAM_POWERSET_S3POWER_Msk (0x1UL << VMC_RAM_POWERSET_S3POWER_Pos) /*!< Bit mask of S3POWER field. */
#define VMC_RAM_POWERSET_S3POWER_On (1UL) /*!< On */

/* Bit 2 : Keep RAM section S2 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERSET_S2POWER_Pos (2UL) /*!< Position of S2POWER field. */
#define VMC_RAM_POWERSET_S2POWER_Msk (0x1UL << VMC_RAM_POWERSET_S2POWER_Pos) /*!< Bit mask of S2POWER field. */
#define VMC_RAM_POWERSET_S2POWER_On (1UL) /*!< On */

/* Bit 1 : Keep RAM section S1 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERSET_S1POWER_Pos (1UL) /*!< Position of S1POWER field. */
#define VMC_RAM_POWERSET_S1POWER_Msk (0x1UL << VMC_RAM_POWERSET_S1POWER_Pos) /*!< Bit mask of S1POWER field. */
#define VMC_RAM_POWERSET_S1POWER_On (1UL) /*!< On */

/* Bit 0 : Keep RAM section S0 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERSET_S0POWER_Pos (0UL) /*!< Position of S0POWER field. */
#define VMC_RAM_POWERSET_S0POWER_Msk (0x1UL << VMC_RAM_POWERSET_S0POWER_Pos) /*!< Bit mask of S0POWER field. */
#define VMC_RAM_POWERSET_S0POWER_On (1UL) /*!< On */

/* Register: VMC_RAM_POWERCLR */
/* Description: Description cluster: RAM[n] power control clear register */

/* Bit 19 : Keep retention on RAM section S3 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERCLR_S3RETENTION_Pos (19UL) /*!< Position of S3RETENTION field. */
#define VMC_RAM_POWERCLR_S3RETENTION_Msk (0x1UL << VMC_RAM_POWERCLR_S3RETENTION_Pos) /*!< Bit mask of S3RETENTION field. */
#define VMC_RAM_POWERCLR_S3RETENTION_Off (1UL) /*!< Off */

/* Bit 18 : Keep retention on RAM section S2 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERCLR_S2RETENTION_Pos (18UL) /*!< Position of S2RETENTION field. */
#define VMC_RAM_POWERCLR_S2RETENTION_Msk (0x1UL << VMC_RAM_POWERCLR_S2RETENTION_Pos) /*!< Bit mask of S2RETENTION field. */
#define VMC_RAM_POWERCLR_S2RETENTION_Off (1UL) /*!< Off */

/* Bit 17 : Keep retention on RAM section S1 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERCLR_S1RETENTION_Pos (17UL) /*!< Position of S1RETENTION field. */
#define VMC_RAM_POWERCLR_S1RETENTION_Msk (0x1UL << VMC_RAM_POWERCLR_S1RETENTION_Pos) /*!< Bit mask of S1RETENTION field. */
#define VMC_RAM_POWERCLR_S1RETENTION_Off (1UL) /*!< Off */

/* Bit 16 : Keep retention on RAM section S0 of RAM[n] when RAM section is switched off */
#define VMC_RAM_POWERCLR_S0RETENTION_Pos (16UL) /*!< Position of S0RETENTION field. */
#define VMC_RAM_POWERCLR_S0RETENTION_Msk (0x1UL << VMC_RAM_POWERCLR_S0RETENTION_Pos) /*!< Bit mask of S0RETENTION field. */
#define VMC_RAM_POWERCLR_S0RETENTION_Off (1UL) /*!< Off */

/* Bit 3 : Keep RAM section S3 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERCLR_S3POWER_Pos (3UL) /*!< Position of S3POWER field. */
#define VMC_RAM_POWERCLR_S3POWER_Msk (0x1UL << VMC_RAM_POWERCLR_S3POWER_Pos) /*!< Bit mask of S3POWER field. */
#define VMC_RAM_POWERCLR_S3POWER_Off (1UL) /*!< Off */

/* Bit 2 : Keep RAM section S2 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERCLR_S2POWER_Pos (2UL) /*!< Position of S2POWER field. */
#define VMC_RAM_POWERCLR_S2POWER_Msk (0x1UL << VMC_RAM_POWERCLR_S2POWER_Pos) /*!< Bit mask of S2POWER field. */
#define VMC_RAM_POWERCLR_S2POWER_Off (1UL) /*!< Off */

/* Bit 1 : Keep RAM section S1 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERCLR_S1POWER_Pos (1UL) /*!< Position of S1POWER field. */
#define VMC_RAM_POWERCLR_S1POWER_Msk (0x1UL << VMC_RAM_POWERCLR_S1POWER_Pos) /*!< Bit mask of S1POWER field. */
#define VMC_RAM_POWERCLR_S1POWER_Off (1UL) /*!< Off */

/* Bit 0 : Keep RAM section S0 of RAM[n] on or off in System ON mode */
#define VMC_RAM_POWERCLR_S0POWER_Pos (0UL) /*!< Position of S0POWER field. */
#define VMC_RAM_POWERCLR_S0POWER_Msk (0x1UL << VMC_RAM_POWERCLR_S0POWER_Pos) /*!< Bit mask of S0POWER field. */
#define VMC_RAM_POWERCLR_S0POWER_Off (1UL) /*!< Off */


/* Peripheral: VREQCTRL */
/* Description: Voltage request control */

/* Register: VREQCTRL_VREGRADIO_VREQH */
/* Description: Request high voltage on RADIO After requesting high voltage, the user must wait until VREQHREADY is set to Ready */

/* Bit 0 : Request high voltage */
#define VREQCTRL_VREGRADIO_VREQH_VREQH_Pos (0UL) /*!< Position of VREQH field. */
#define VREQCTRL_VREGRADIO_VREQH_VREQH_Msk (0x1UL << VREQCTRL_VREGRADIO_VREQH_VREQH_Pos) /*!< Bit mask of VREQH field. */
#define VREQCTRL_VREGRADIO_VREQH_VREQH_Disabled (0UL) /*!< Disable */
#define VREQCTRL_VREGRADIO_VREQH_VREQH_Enabled (1UL) /*!< Enable */

/* Register: VREQCTRL_VREGRADIO_VREQHREADY */
/* Description: High voltage on RADIO is ready */

/* Bit 0 : RADIO is ready to operate on high voltage */
#define VREQCTRL_VREGRADIO_VREQHREADY_READY_Pos (0UL) /*!< Position of READY field. */
#define VREQCTRL_VREGRADIO_VREQHREADY_READY_Msk (0x1UL << VREQCTRL_VREGRADIO_VREQHREADY_READY_Pos) /*!< Bit mask of READY field. */
#define VREQCTRL_VREGRADIO_VREQHREADY_READY_NotReady (0UL) /*!< Not ready */
#define VREQCTRL_VREGRADIO_VREQHREADY_READY_Ready (1UL) /*!< Ready */


/* Peripheral: WDT */
/* Description: Watchdog Timer */

/* Register: WDT_TASKS_START */
/* Description: Start WDT */

/* Bit 0 : Start WDT */
#define WDT_TASKS_START_TASKS_START_Pos (0UL) /*!< Position of TASKS_START field. */
#define WDT_TASKS_START_TASKS_START_Msk (0x1UL << WDT_TASKS_START_TASKS_START_Pos) /*!< Bit mask of TASKS_START field. */
#define WDT_TASKS_START_TASKS_START_Trigger (1UL) /*!< Trigger task */

/* Register: WDT_TASKS_STOP */
/* Description: Stop WDT */

/* Bit 0 : Stop WDT */
#define WDT_TASKS_STOP_TASKS_STOP_Pos (0UL) /*!< Position of TASKS_STOP field. */
#define WDT_TASKS_STOP_TASKS_STOP_Msk (0x1UL << WDT_TASKS_STOP_TASKS_STOP_Pos) /*!< Bit mask of TASKS_STOP field. */
#define WDT_TASKS_STOP_TASKS_STOP_Trigger (1UL) /*!< Trigger task */

/* Register: WDT_SUBSCRIBE_START */
/* Description: Subscribe configuration for task START */

/* Bit 31 :   */
#define WDT_SUBSCRIBE_START_EN_Pos (31UL) /*!< Position of EN field. */
#define WDT_SUBSCRIBE_START_EN_Msk (0x1UL << WDT_SUBSCRIBE_START_EN_Pos) /*!< Bit mask of EN field. */
#define WDT_SUBSCRIBE_START_EN_Disabled (0UL) /*!< Disable subscription */
#define WDT_SUBSCRIBE_START_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task START will subscribe to */
#define WDT_SUBSCRIBE_START_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define WDT_SUBSCRIBE_START_CHIDX_Msk (0xFFUL << WDT_SUBSCRIBE_START_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: WDT_SUBSCRIBE_STOP */
/* Description: Subscribe configuration for task STOP */

/* Bit 31 :   */
#define WDT_SUBSCRIBE_STOP_EN_Pos (31UL) /*!< Position of EN field. */
#define WDT_SUBSCRIBE_STOP_EN_Msk (0x1UL << WDT_SUBSCRIBE_STOP_EN_Pos) /*!< Bit mask of EN field. */
#define WDT_SUBSCRIBE_STOP_EN_Disabled (0UL) /*!< Disable subscription */
#define WDT_SUBSCRIBE_STOP_EN_Enabled (1UL) /*!< Enable subscription */

/* Bits 7..0 : DPPI channel that task STOP will subscribe to */
#define WDT_SUBSCRIBE_STOP_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define WDT_SUBSCRIBE_STOP_CHIDX_Msk (0xFFUL << WDT_SUBSCRIBE_STOP_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: WDT_EVENTS_TIMEOUT */
/* Description: Watchdog timeout */

/* Bit 0 : Watchdog timeout */
#define WDT_EVENTS_TIMEOUT_EVENTS_TIMEOUT_Pos (0UL) /*!< Position of EVENTS_TIMEOUT field. */
#define WDT_EVENTS_TIMEOUT_EVENTS_TIMEOUT_Msk (0x1UL << WDT_EVENTS_TIMEOUT_EVENTS_TIMEOUT_Pos) /*!< Bit mask of EVENTS_TIMEOUT field. */
#define WDT_EVENTS_TIMEOUT_EVENTS_TIMEOUT_NotGenerated (0UL) /*!< Event not generated */
#define WDT_EVENTS_TIMEOUT_EVENTS_TIMEOUT_Generated (1UL) /*!< Event generated */

/* Register: WDT_EVENTS_STOPPED */
/* Description: Watchdog stopped */

/* Bit 0 : Watchdog stopped */
#define WDT_EVENTS_STOPPED_EVENTS_STOPPED_Pos (0UL) /*!< Position of EVENTS_STOPPED field. */
#define WDT_EVENTS_STOPPED_EVENTS_STOPPED_Msk (0x1UL << WDT_EVENTS_STOPPED_EVENTS_STOPPED_Pos) /*!< Bit mask of EVENTS_STOPPED field. */
#define WDT_EVENTS_STOPPED_EVENTS_STOPPED_NotGenerated (0UL) /*!< Event not generated */
#define WDT_EVENTS_STOPPED_EVENTS_STOPPED_Generated (1UL) /*!< Event generated */

/* Register: WDT_PUBLISH_TIMEOUT */
/* Description: Publish configuration for event TIMEOUT */

/* Bit 31 :   */
#define WDT_PUBLISH_TIMEOUT_EN_Pos (31UL) /*!< Position of EN field. */
#define WDT_PUBLISH_TIMEOUT_EN_Msk (0x1UL << WDT_PUBLISH_TIMEOUT_EN_Pos) /*!< Bit mask of EN field. */
#define WDT_PUBLISH_TIMEOUT_EN_Disabled (0UL) /*!< Disable publishing */
#define WDT_PUBLISH_TIMEOUT_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event TIMEOUT will publish to. */
#define WDT_PUBLISH_TIMEOUT_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define WDT_PUBLISH_TIMEOUT_CHIDX_Msk (0xFFUL << WDT_PUBLISH_TIMEOUT_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: WDT_PUBLISH_STOPPED */
/* Description: Publish configuration for event STOPPED */

/* Bit 31 :   */
#define WDT_PUBLISH_STOPPED_EN_Pos (31UL) /*!< Position of EN field. */
#define WDT_PUBLISH_STOPPED_EN_Msk (0x1UL << WDT_PUBLISH_STOPPED_EN_Pos) /*!< Bit mask of EN field. */
#define WDT_PUBLISH_STOPPED_EN_Disabled (0UL) /*!< Disable publishing */
#define WDT_PUBLISH_STOPPED_EN_Enabled (1UL) /*!< Enable publishing */

/* Bits 7..0 : DPPI channel that event STOPPED will publish to. */
#define WDT_PUBLISH_STOPPED_CHIDX_Pos (0UL) /*!< Position of CHIDX field. */
#define WDT_PUBLISH_STOPPED_CHIDX_Msk (0xFFUL << WDT_PUBLISH_STOPPED_CHIDX_Pos) /*!< Bit mask of CHIDX field. */

/* Register: WDT_INTENSET */
/* Description: Enable interrupt */

/* Bit 1 : Write '1' to enable interrupt for event STOPPED */
#define WDT_INTENSET_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define WDT_INTENSET_STOPPED_Msk (0x1UL << WDT_INTENSET_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define WDT_INTENSET_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define WDT_INTENSET_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define WDT_INTENSET_STOPPED_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event TIMEOUT */
#define WDT_INTENSET_TIMEOUT_Pos (0UL) /*!< Position of TIMEOUT field. */
#define WDT_INTENSET_TIMEOUT_Msk (0x1UL << WDT_INTENSET_TIMEOUT_Pos) /*!< Bit mask of TIMEOUT field. */
#define WDT_INTENSET_TIMEOUT_Disabled (0UL) /*!< Read: Disabled */
#define WDT_INTENSET_TIMEOUT_Enabled (1UL) /*!< Read: Enabled */
#define WDT_INTENSET_TIMEOUT_Set (1UL) /*!< Enable */

/* Register: WDT_INTENCLR */
/* Description: Disable interrupt */

/* Bit 1 : Write '1' to disable interrupt for event STOPPED */
#define WDT_INTENCLR_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define WDT_INTENCLR_STOPPED_Msk (0x1UL << WDT_INTENCLR_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define WDT_INTENCLR_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define WDT_INTENCLR_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define WDT_INTENCLR_STOPPED_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event TIMEOUT */
#define WDT_INTENCLR_TIMEOUT_Pos (0UL) /*!< Position of TIMEOUT field. */
#define WDT_INTENCLR_TIMEOUT_Msk (0x1UL << WDT_INTENCLR_TIMEOUT_Pos) /*!< Bit mask of TIMEOUT field. */
#define WDT_INTENCLR_TIMEOUT_Disabled (0UL) /*!< Read: Disabled */
#define WDT_INTENCLR_TIMEOUT_Enabled (1UL) /*!< Read: Enabled */
#define WDT_INTENCLR_TIMEOUT_Clear (1UL) /*!< Disable */

/* Register: WDT_NMIENSET */
/* Description: Enable interrupt */

/* Bit 1 : Write '1' to enable interrupt for event STOPPED */
#define WDT_NMIENSET_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define WDT_NMIENSET_STOPPED_Msk (0x1UL << WDT_NMIENSET_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define WDT_NMIENSET_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define WDT_NMIENSET_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define WDT_NMIENSET_STOPPED_Set (1UL) /*!< Enable */

/* Bit 0 : Write '1' to enable interrupt for event TIMEOUT */
#define WDT_NMIENSET_TIMEOUT_Pos (0UL) /*!< Position of TIMEOUT field. */
#define WDT_NMIENSET_TIMEOUT_Msk (0x1UL << WDT_NMIENSET_TIMEOUT_Pos) /*!< Bit mask of TIMEOUT field. */
#define WDT_NMIENSET_TIMEOUT_Disabled (0UL) /*!< Read: Disabled */
#define WDT_NMIENSET_TIMEOUT_Enabled (1UL) /*!< Read: Enabled */
#define WDT_NMIENSET_TIMEOUT_Set (1UL) /*!< Enable */

/* Register: WDT_NMIENCLR */
/* Description: Disable interrupt */

/* Bit 1 : Write '1' to disable interrupt for event STOPPED */
#define WDT_NMIENCLR_STOPPED_Pos (1UL) /*!< Position of STOPPED field. */
#define WDT_NMIENCLR_STOPPED_Msk (0x1UL << WDT_NMIENCLR_STOPPED_Pos) /*!< Bit mask of STOPPED field. */
#define WDT_NMIENCLR_STOPPED_Disabled (0UL) /*!< Read: Disabled */
#define WDT_NMIENCLR_STOPPED_Enabled (1UL) /*!< Read: Enabled */
#define WDT_NMIENCLR_STOPPED_Clear (1UL) /*!< Disable */

/* Bit 0 : Write '1' to disable interrupt for event TIMEOUT */
#define WDT_NMIENCLR_TIMEOUT_Pos (0UL) /*!< Position of TIMEOUT field. */
#define WDT_NMIENCLR_TIMEOUT_Msk (0x1UL << WDT_NMIENCLR_TIMEOUT_Pos) /*!< Bit mask of TIMEOUT field. */
#define WDT_NMIENCLR_TIMEOUT_Disabled (0UL) /*!< Read: Disabled */
#define WDT_NMIENCLR_TIMEOUT_Enabled (1UL) /*!< Read: Enabled */
#define WDT_NMIENCLR_TIMEOUT_Clear (1UL) /*!< Disable */

/* Register: WDT_RUNSTATUS */
/* Description: Run status */

/* Bit 0 : Indicates whether or not WDT is running */
#define WDT_RUNSTATUS_RUNSTATUSWDT_Pos (0UL) /*!< Position of RUNSTATUSWDT field. */
#define WDT_RUNSTATUS_RUNSTATUSWDT_Msk (0x1UL << WDT_RUNSTATUS_RUNSTATUSWDT_Pos) /*!< Bit mask of RUNSTATUSWDT field. */
#define WDT_RUNSTATUS_RUNSTATUSWDT_NotRunning (0UL) /*!< Watchdog is not running */
#define WDT_RUNSTATUS_RUNSTATUSWDT_Running (1UL) /*!< Watchdog is running */

/* Register: WDT_REQSTATUS */
/* Description: Request status */

/* Bit 7 : Request status for RR[7] register */
#define WDT_REQSTATUS_RR7_Pos (7UL) /*!< Position of RR7 field. */
#define WDT_REQSTATUS_RR7_Msk (0x1UL << WDT_REQSTATUS_RR7_Pos) /*!< Bit mask of RR7 field. */
#define WDT_REQSTATUS_RR7_DisabledOrRequested (0UL) /*!< RR[7] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR7_EnabledAndUnrequested (1UL) /*!< RR[7] register is enabled, and are not yet requesting reload */

/* Bit 6 : Request status for RR[6] register */
#define WDT_REQSTATUS_RR6_Pos (6UL) /*!< Position of RR6 field. */
#define WDT_REQSTATUS_RR6_Msk (0x1UL << WDT_REQSTATUS_RR6_Pos) /*!< Bit mask of RR6 field. */
#define WDT_REQSTATUS_RR6_DisabledOrRequested (0UL) /*!< RR[6] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR6_EnabledAndUnrequested (1UL) /*!< RR[6] register is enabled, and are not yet requesting reload */

/* Bit 5 : Request status for RR[5] register */
#define WDT_REQSTATUS_RR5_Pos (5UL) /*!< Position of RR5 field. */
#define WDT_REQSTATUS_RR5_Msk (0x1UL << WDT_REQSTATUS_RR5_Pos) /*!< Bit mask of RR5 field. */
#define WDT_REQSTATUS_RR5_DisabledOrRequested (0UL) /*!< RR[5] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR5_EnabledAndUnrequested (1UL) /*!< RR[5] register is enabled, and are not yet requesting reload */

/* Bit 4 : Request status for RR[4] register */
#define WDT_REQSTATUS_RR4_Pos (4UL) /*!< Position of RR4 field. */
#define WDT_REQSTATUS_RR4_Msk (0x1UL << WDT_REQSTATUS_RR4_Pos) /*!< Bit mask of RR4 field. */
#define WDT_REQSTATUS_RR4_DisabledOrRequested (0UL) /*!< RR[4] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR4_EnabledAndUnrequested (1UL) /*!< RR[4] register is enabled, and are not yet requesting reload */

/* Bit 3 : Request status for RR[3] register */
#define WDT_REQSTATUS_RR3_Pos (3UL) /*!< Position of RR3 field. */
#define WDT_REQSTATUS_RR3_Msk (0x1UL << WDT_REQSTATUS_RR3_Pos) /*!< Bit mask of RR3 field. */
#define WDT_REQSTATUS_RR3_DisabledOrRequested (0UL) /*!< RR[3] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR3_EnabledAndUnrequested (1UL) /*!< RR[3] register is enabled, and are not yet requesting reload */

/* Bit 2 : Request status for RR[2] register */
#define WDT_REQSTATUS_RR2_Pos (2UL) /*!< Position of RR2 field. */
#define WDT_REQSTATUS_RR2_Msk (0x1UL << WDT_REQSTATUS_RR2_Pos) /*!< Bit mask of RR2 field. */
#define WDT_REQSTATUS_RR2_DisabledOrRequested (0UL) /*!< RR[2] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR2_EnabledAndUnrequested (1UL) /*!< RR[2] register is enabled, and are not yet requesting reload */

/* Bit 1 : Request status for RR[1] register */
#define WDT_REQSTATUS_RR1_Pos (1UL) /*!< Position of RR1 field. */
#define WDT_REQSTATUS_RR1_Msk (0x1UL << WDT_REQSTATUS_RR1_Pos) /*!< Bit mask of RR1 field. */
#define WDT_REQSTATUS_RR1_DisabledOrRequested (0UL) /*!< RR[1] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR1_EnabledAndUnrequested (1UL) /*!< RR[1] register is enabled, and are not yet requesting reload */

/* Bit 0 : Request status for RR[0] register */
#define WDT_REQSTATUS_RR0_Pos (0UL) /*!< Position of RR0 field. */
#define WDT_REQSTATUS_RR0_Msk (0x1UL << WDT_REQSTATUS_RR0_Pos) /*!< Bit mask of RR0 field. */
#define WDT_REQSTATUS_RR0_DisabledOrRequested (0UL) /*!< RR[0] register is not enabled, or are already requesting reload */
#define WDT_REQSTATUS_RR0_EnabledAndUnrequested (1UL) /*!< RR[0] register is enabled, and are not yet requesting reload */

/* Register: WDT_CRV */
/* Description: Counter reload value */

/* Bits 31..0 : Counter reload value in number of cycles of the 32.768 kHz clock */
#define WDT_CRV_CRV_Pos (0UL) /*!< Position of CRV field. */
#define WDT_CRV_CRV_Msk (0xFFFFFFFFUL << WDT_CRV_CRV_Pos) /*!< Bit mask of CRV field. */

/* Register: WDT_RREN */
/* Description: Enable register for reload request registers */

/* Bit 7 : Enable or disable RR[7] register */
#define WDT_RREN_RR7_Pos (7UL) /*!< Position of RR7 field. */
#define WDT_RREN_RR7_Msk (0x1UL << WDT_RREN_RR7_Pos) /*!< Bit mask of RR7 field. */
#define WDT_RREN_RR7_Disabled (0UL) /*!< Disable RR[7] register */
#define WDT_RREN_RR7_Enabled (1UL) /*!< Enable RR[7] register */

/* Bit 6 : Enable or disable RR[6] register */
#define WDT_RREN_RR6_Pos (6UL) /*!< Position of RR6 field. */
#define WDT_RREN_RR6_Msk (0x1UL << WDT_RREN_RR6_Pos) /*!< Bit mask of RR6 field. */
#define WDT_RREN_RR6_Disabled (0UL) /*!< Disable RR[6] register */
#define WDT_RREN_RR6_Enabled (1UL) /*!< Enable RR[6] register */

/* Bit 5 : Enable or disable RR[5] register */
#define WDT_RREN_RR5_Pos (5UL) /*!< Position of RR5 field. */
#define WDT_RREN_RR5_Msk (0x1UL << WDT_RREN_RR5_Pos) /*!< Bit mask of RR5 field. */
#define WDT_RREN_RR5_Disabled (0UL) /*!< Disable RR[5] register */
#define WDT_RREN_RR5_Enabled (1UL) /*!< Enable RR[5] register */

/* Bit 4 : Enable or disable RR[4] register */
#define WDT_RREN_RR4_Pos (4UL) /*!< Position of RR4 field. */
#define WDT_RREN_RR4_Msk (0x1UL << WDT_RREN_RR4_Pos) /*!< Bit mask of RR4 field. */
#define WDT_RREN_RR4_Disabled (0UL) /*!< Disable RR[4] register */
#define WDT_RREN_RR4_Enabled (1UL) /*!< Enable RR[4] register */

/* Bit 3 : Enable or disable RR[3] register */
#define WDT_RREN_RR3_Pos (3UL) /*!< Position of RR3 field. */
#define WDT_RREN_RR3_Msk (0x1UL << WDT_RREN_RR3_Pos) /*!< Bit mask of RR3 field. */
#define WDT_RREN_RR3_Disabled (0UL) /*!< Disable RR[3] register */
#define WDT_RREN_RR3_Enabled (1UL) /*!< Enable RR[3] register */

/* Bit 2 : Enable or disable RR[2] register */
#define WDT_RREN_RR2_Pos (2UL) /*!< Position of RR2 field. */
#define WDT_RREN_RR2_Msk (0x1UL << WDT_RREN_RR2_Pos) /*!< Bit mask of RR2 field. */
#define WDT_RREN_RR2_Disabled (0UL) /*!< Disable RR[2] register */
#define WDT_RREN_RR2_Enabled (1UL) /*!< Enable RR[2] register */

/* Bit 1 : Enable or disable RR[1] register */
#define WDT_RREN_RR1_Pos (1UL) /*!< Position of RR1 field. */
#define WDT_RREN_RR1_Msk (0x1UL << WDT_RREN_RR1_Pos) /*!< Bit mask of RR1 field. */
#define WDT_RREN_RR1_Disabled (0UL) /*!< Disable RR[1] register */
#define WDT_RREN_RR1_Enabled (1UL) /*!< Enable RR[1] register */

/* Bit 0 : Enable or disable RR[0] register */
#define WDT_RREN_RR0_Pos (0UL) /*!< Position of RR0 field. */
#define WDT_RREN_RR0_Msk (0x1UL << WDT_RREN_RR0_Pos) /*!< Bit mask of RR0 field. */
#define WDT_RREN_RR0_Disabled (0UL) /*!< Disable RR[0] register */
#define WDT_RREN_RR0_Enabled (1UL) /*!< Enable RR[0] register */

/* Register: WDT_CONFIG */
/* Description: Configuration register */

/* Bit 6 : Allow stopping WDT */
#define WDT_CONFIG_STOPEN_Pos (6UL) /*!< Position of STOPEN field. */
#define WDT_CONFIG_STOPEN_Msk (0x1UL << WDT_CONFIG_STOPEN_Pos) /*!< Bit mask of STOPEN field. */
#define WDT_CONFIG_STOPEN_Disable (0UL) /*!< Do not allow stopping WDT */
#define WDT_CONFIG_STOPEN_Enable (1UL) /*!< Allow stopping WDT */

/* Bit 3 : Configure WDT to either be paused, or kept running, while the CPU is halted by the debugger */
#define WDT_CONFIG_HALT_Pos (3UL) /*!< Position of HALT field. */
#define WDT_CONFIG_HALT_Msk (0x1UL << WDT_CONFIG_HALT_Pos) /*!< Bit mask of HALT field. */
#define WDT_CONFIG_HALT_Pause (0UL) /*!< Pause WDT while the CPU is halted by the debugger */
#define WDT_CONFIG_HALT_Run (1UL) /*!< Keep WDT running while the CPU is halted by the debugger */

/* Bit 0 : Configure WDT to either be paused, or kept running, while the CPU is sleeping */
#define WDT_CONFIG_SLEEP_Pos (0UL) /*!< Position of SLEEP field. */
#define WDT_CONFIG_SLEEP_Msk (0x1UL << WDT_CONFIG_SLEEP_Pos) /*!< Bit mask of SLEEP field. */
#define WDT_CONFIG_SLEEP_Pause (0UL) /*!< Pause WDT while the CPU is sleeping */
#define WDT_CONFIG_SLEEP_Run (1UL) /*!< Keep WDT running while the CPU is sleeping */

/* Register: WDT_TSEN */
/* Description: Task stop enable */

/* Bits 31..0 : Allow stopping WDT */
#define WDT_TSEN_TSEN_Pos (0UL) /*!< Position of TSEN field. */
#define WDT_TSEN_TSEN_Msk (0xFFFFFFFFUL << WDT_TSEN_TSEN_Pos) /*!< Bit mask of TSEN field. */
#define WDT_TSEN_TSEN_Enable (0x6E524635UL) /*!< Value to allow stopping WDT */

/* Register: WDT_RR */
/* Description: Description collection: Reload request n */

/* Bits 31..0 : Reload request register */
#define WDT_RR_RR_Pos (0UL) /*!< Position of RR field. */
#define WDT_RR_RR_Msk (0xFFFFFFFFUL << WDT_RR_RR_Pos) /*!< Bit mask of RR field. */
#define WDT_RR_RR_Reload (0x6E524635UL) /*!< Value to request a reload of the watchdog timer */


/*lint --flb "Leave library region" */
#endif
