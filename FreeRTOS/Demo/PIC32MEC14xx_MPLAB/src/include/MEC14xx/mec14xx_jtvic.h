/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
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

/** @file mec14xx_jtvic.h
 *MEC14xx JTVIC HW defines
 */
/** @defgroup MEC14xx Peripherals JTVIC
 */

#ifndef _MEC14XX_JTVIC_H
#define _MEC14XX_JTVIC_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define JTVIC_PRI1          0
#define JTVIC_PRI3          1
#define JTVIC_PRI5          2
#define JTVIC_PRI7          3

/* Each JTVIC GIRQx has 4 32-bit priority registers where each nibble 
 * encodes one of four priorities.
 * Generate JTVIC GIRQx Priority Register value for field number b with 
 * priority p 
 * b is the field [0,7]
 * p is the priority 0=IPL1, 1=IPL3, 2=IPL5, 3=IPL7
 */
#define JTVIC_PRI_VAL(b,p) ((uint32_t)((p) & 0x03) << (((b) & 0x07) << 2))

#define JTVIC_GIRQ_NPRI_REGS     (4)
typedef struct {
    uint32_t isr_addr;
    uint32_t pri[JTVIC_GIRQ_NPRI_REGS];
} JTVIC_CFG;

#define JTVIC_FLAG_DISAGR_SPACING_8      (0)
#define JTVIC_FLAG_DISAGR_SPACING_512    (1ul << 0)

#define JTVIC_NO_CLR_SRC    (0)
#define JTVIC_CLR_SRC       (1)

void jtvic_init(const JTVIC_CFG *ih_table, uint32_t disagg_bitmap, uint32_t cflags);
void jtvic_clr_source(uint8_t girq_num, uint8_t bit_num);
void jtvic_dis_clr_source(uint8_t girq_num, uint8_t bit_num, uint8_t clr_src);
void jtvic_en_source(uint8_t girq_num, uint8_t bit_num, uint8_t clr_src);


#ifdef __cplusplus
}
#endif

#endif // #ifndef _MEC14XX_JTVIC_H
/* end mec14XX_jtvic.h */
/**   @}
 */
