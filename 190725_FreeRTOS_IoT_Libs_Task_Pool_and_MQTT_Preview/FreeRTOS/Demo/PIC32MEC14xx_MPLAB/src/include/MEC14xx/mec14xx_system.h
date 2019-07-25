/*****************************************************************************
* (c) 2014 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/

/** @file mec14xx_system.h
 *MEC14xx System header
 */
/** @defgroup MEC14xx system
 */

#ifndef __SYSTEM_MEC14xx_H 
#define __SYSTEM_MEC14xx_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include "appcfg.h"
#include "platform.h"

/**
 * Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *         Initialize the System and update the SystemCoreClock variable.
 */
void SystemInit (void);

uint32_t sys_code_sram_base(void);
uint8_t sys_valid_sram_addr(void * const p);
uint8_t sys_valid_sram_range(void * const p, const uint32_t byte_len);
void sys_cpu_en_timer(uint32_t counts, uint8_t ien);

uint32_t cpu_microsecond_interval(uint32_t start_count);
uint32_t cpu_microsecond_count(void);
#define CPU_US_DELTA(x) cpu_microsecond_interval(x)


#ifdef __cplusplus
}
#endif

#endif /* __SYSTEM_MEC14xx_H */

/**   @}
 */
