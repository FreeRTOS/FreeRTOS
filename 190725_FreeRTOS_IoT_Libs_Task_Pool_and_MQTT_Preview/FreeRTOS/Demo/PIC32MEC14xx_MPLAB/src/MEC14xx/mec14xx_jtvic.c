/*****************************************************************************
* © 2014 Microchip Technology Inc. and its subsidiaries.
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

/** @file mec14xx_jtvic.c
 *MEC14xx JTVIC
 */
/** @defgroup MEC14xx Peripherals JTVIC
 *  @{
 */


#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_jtvic.h"


void jtvic_init(const JTVIC_CFG *ih_table, uint32_t disagg_bitmap, uint32_t cflags)
{
    uint32_t d;
    uint8_t i, j, pidx;

    JTVIC_CTRL->w = (1ul << 0);  // Soft-Reset
    d = 0ul;
    if ( cflags & (1ul << 0) ) 
    {
        d = (1ul << 8);
    }
    JTVIC_CTRL->w = d;  // HW does not automatically clear Soft-Reset

    for (i = 0u; i < (MEC14xx_NUM_JTVIC_INTS); i++) {
        pidx = i << 2;
        for (j = 0u; j < 4u; j++) {
            JTVIC_PRI->REG32[pidx+j] = (uint32_t)(ih_table[i].pri[j]);
        }
        d = ih_table[i].isr_addr & ~(1ul << 0);
        if (disagg_bitmap & (1ul << i)) {
            d |= (1ul << 0);    // dis-aggregate this GIRQ
        }
        JTVIC_ACTRL->REG32[i] = d;
    }
    
    JTVIC_GROUP_EN_SET->w = 0xFFFFFFFFul;   // Enable GIRQ08 - GIRQ18 (all)
    
}

/* Clear JTVIC GIRQn source bit
 *
 */
void jtvic_clr_source(uint8_t girq_num, uint8_t bit_num)
{
    if (girq_num < (MEC14xx_NUM_JTVIC_INTS))
    {
        bit_num &= 0x1Fu;
        JTVIC_GIRQ->REGS[girq_num].SOURCE = (1ul << bit_num);
    }
}


/* Disable GIRQn source with optional clearing of source.
 * girq_num = [0, 18], 0=GIRQ08, 1=GIRQ09, ..., 18=GIRQ26
 * bit_num = [0, 31]
 */
void jtvic_dis_clr_source(uint8_t girq_num, uint8_t bit_num, uint8_t clr_src)
{
    if (girq_num < (MEC14xx_NUM_JTVIC_INTS))
    {
        bit_num &= 0x1Fu;
        JTVIC_GIRQ->REGS[girq_num].EN_CLR = (1ul << bit_num);
        if ( 0 != clr_src )
        {
            JTVIC_GIRQ->REGS[girq_num].SOURCE = (1ul << bit_num);
        }
    }
}


/* Enable with optional source clear before enable.
 * girq_num = [0, 18], 0=GIRQ08, 1=GIRQ09, ..., 18=GIRQ26
 * bit_num = [0, 31]
 */
void jtvic_en_source(uint8_t girq_num, uint8_t bit_num, uint8_t clr_src)
{
    if (girq_num < (MEC14xx_NUM_JTVIC_INTS))
    {
        bit_num &= 0x1Fu;
        if ( 0 != clr_src )
        {
            JTVIC_GIRQ->REGS[girq_num].SOURCE = (1ul << bit_num);
        }
        JTVIC_GIRQ->REGS[girq_num].EN_SET = (1ul << bit_num);
    }
}


/* end mec14xx_jtvic.c */
/**   @}
 */

