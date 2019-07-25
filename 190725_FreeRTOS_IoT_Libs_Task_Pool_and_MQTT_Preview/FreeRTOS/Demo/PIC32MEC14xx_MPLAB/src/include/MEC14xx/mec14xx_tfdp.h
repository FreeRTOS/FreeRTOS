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


/** @file mec14xx_tfdp.h
 *MEC14xx TRACE FIFO Data Port definitions
 */
/** @defgroup MEC14xx Peripherals TFDP
 */

#ifndef _MEC14XX_TFDP_H
#define _MEC14XX_TFDP_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define TFDP_NUM_INSTANCES  (1u)

#define TFDP_FRAME_START   (0xFD)
    
    
//
// Offset +00h TFDP Data Register: 8-bit R/W
//     
#define TFDP_DATA_REG_OFS       (0ul)
#define TFDP_DATA_REG_MASK      (0xFFul)

//
// Offset +04h TFDP Control Register 8-bit R/W
//
#define TFDP_CTRL_REG_OFS           (0x04ul)
#define TFDP_CTRL_REG_MASK          (0x7Ful)
//
#define TFDP_CTRL_ENABLE_BITPOS     (0u)
#define TFDP_CTRL_EDGE_SEL_BITPOS   (1u)
#define TFDP_CTRL_DIVSEL_BITPOS     (2ul)
#define TFDP_CTRL_IP_DELAY_BITPOS   (4ul)
// Enable/disable
#define TFDP_CTRL_ENABLE            (1u << (TFDP_CTRL_ENABLE_BITPOS))
// Select clock edge data on which data is shifted out
#define TFDP_CTRL_RISING_EDGE       (0u << (TFDP_CTRL_EDGE_SEL_BITPOS))
#define TFDP_CTRL_FALLING_EDGE      (1u << (TFDP_CTRL_EDGE_SEL_BITPOS))
// TFDP Clock divisor
#define TFDP_CTRL_CLK_DIV2          (0u << (TFDP_CTRL_DIVSEL_BITPOS))
#define TFDP_CTRL_CLK_DIV4          (1u << (TFDP_CTRL_DIVSEL_BITPOS))
#define TFDP_CTRL_CLK_DIV8          (2u << (TFDP_CTRL_DIVSEL_BITPOS))
#define TFDP_CTRL_CLK_DIV2_RSVD     (3u << (TFDP_CTRL_DIVSEL_BITPOS))
// Number of clocks to delay between each byte
// Note: this will affect time TFDP block holds off CPU on next 
// write to TFDP data register.
#define TFDP_CTRL_IP_1CLKS          (0u << (TFDP_CTRL_IP_DELAY_BITPOS))
#define TFDP_CTRL_IP_2CLKS          (1u << (TFDP_CTRL_IP_DELAY_BITPOS))
#define TFDP_CTRL_IP_3CLKS          (2u << (TFDP_CTRL_IP_DELAY_BITPOS))
#define TFDP_CTRL_IP_4CLKS          (3u << (TFDP_CTRL_IP_DELAY_BITPOS))
#define TFDP_CTRL_IP_5CLKS          (4u << (TFDP_CTRL_IP_DELAY_BITPOS))
#define TFDP_CTRL_IP_6CLKS          (5u << (TFDP_CTRL_IP_DELAY_BITPOS))
#define TFDP_CTRL_IP_7CLKS          (6u << (TFDP_CTRL_IP_DELAY_BITPOS))
#define TFDP_CTRL_IP_8CLKS          (7u << (TFDP_CTRL_IP_DELAY_BITPOS))


#ifdef __cplusplus
}
#endif

#endif // #ifndef _MEC14XX_TFDP_H
/* end mec14xx_tfdp.h */
/**   @}
 */

