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

/** @file mec14xx_system.c
 *MEC14xx system functions
 */
/** @defgroup MEC14xx System
 *  @{
 */



#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_system.h"
#include "MEC14xx/mec14xx_jtvic.h"




/**
 * Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *         Initialize the System.
 */
void SystemInit (void)
{
    
    PCR->PROC_CLOCK_CNTRL = (PCR_CLOCK_DIVIDER);
    
}
/*---------------------------------------------------------------------------*/

uint32_t sys_code_sram_base(void)
{
#if MEC14XX_DEVID  == MEC1418_DEVID
    return (uint32_t)(MEC1418_ICODE_PSRAM_BASE);
#else
    return (uint32_t)(MEC1404_ICODE_PSRAM_BASE);
#endif
}
/*---------------------------------------------------------------------------*/

uint8_t sys_valid_sram_addr(void * const p)
{
    uint32_t base;
    
    base = sys_code_sram_base();
        
    if ((uint32_t)p >= base) {
        if ((uint32_t)p < (MEC14XX_DCODE_VSRAM_LIMIT)) {
            return 1u;
        }
    }
    return 0u;
}
/*---------------------------------------------------------------------------*/

uint8_t sys_valid_sram_range(void * const p, const uint32_t byte_len)
{
    uint32_t base;

    base = sys_code_sram_base();

    if ((uint32_t)p >= base) {
        if (((uint32_t)p + byte_len) < (MEC14XX_DCODE_VSRAM_LIMIT)) {
            return 1u;
        }
    }
    return 0u;
}
/*---------------------------------------------------------------------------*/

void sys_cpu_en_timer(uint32_t counts, uint8_t ien)
{
    /* Disable Counter by setting DC bit to 1 in CP0.Cause */
    _CP0_BIS_CAUSE(_CP0_CAUSE_DC_MASK);

    _CP0_SET_COUNT(counts);
    if (ien) {
        jtvic_en_source(MEC14xx_GIRQ24_ID, 0, 0);
    } else {
        jtvic_dis_clr_source(MEC14xx_GIRQ24_ID, 0, 1);
    }

    /* Enable Counter */
    _CP0_BIC_CAUSE(_CP0_CAUSE_DC_MASK);

}
/*---------------------------------------------------------------------------*/

uint32_t cpu_microsecond_count(void)
{
    return _CP0_GET_COUNT();
}
/*---------------------------------------------------------------------------*/

/*
 * Assumes M14K CPU is running at clock divide by 1 (48MHz)
 * 1us = 48 counts. 
 * NOTE: We need to find out from DE what the pipeline rate is. 
 * M14K counter ticks at pipeline rate. 
 */
uint32_t cpu_microsecond_interval(uint32_t start_count)
{
    uint32_t curr_count;
    
    curr_count = _CP0_GET_COUNT();
    if (curr_count >= start_count) {
        return ((curr_count - start_count) >> 4)/ 3ul;
    } else {
        return (((0xFFFFFFFFul - start_count) + curr_count) >> 4) / 3ul;
    }
}
/*---------------------------------------------------------------------------*/

/* end mec14xx_system.c */
/**   @}
 */

