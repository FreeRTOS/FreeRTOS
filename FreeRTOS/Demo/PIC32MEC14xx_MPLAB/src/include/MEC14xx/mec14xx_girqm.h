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

/** @file mec14xx_girqm.h
 *MEC14xx JTVIC Disaggregation Control Flags
 */
/** @defgroup MEC14xx interrupt
 */

/*
 * This file is intended to be included in both C source and assembly language
 * files. The assembly language C pre-processor cannot handle complex macros.
 * Keep it simple!
 */

/* Include FreeRTOS configuration settings.
 * These include porting layer switches affecting interrupt aggregation 
 * of GIRQ23 & GIRQ24 
 */
#include "FreeRTOSConfig.h"

/*
 * Set to 0 for Aggregated GIRQ
 * Set to 1 for Dis-aggregated(Jump Table) GIRQ
 */

#define GIRQ08_DISAGG   (0)
#define GIRQ09_DISAGG   (0)
#define GIRQ10_DISAGG   (0)
#define GIRQ11_DISAGG   (0)
#define GIRQ12_DISAGG   (0)
#define GIRQ13_DISAGG   (0)
#define GIRQ14_DISAGG   (0)
#define GIRQ15_DISAGG   (0)
#define GIRQ16_DISAGG   (0)
#define GIRQ17_DISAGG   (0)
#define GIRQ18_DISAGG   (0)
#define GIRQ19_DISAGG   (0)
#define GIRQ20_DISAGG   (0)
#define GIRQ21_DISAGG   (0)
#define GIRQ22_DISAGG   (0)

#if configTIMERS_DISAGGREGATED_ISRS == 0
#define GIRQ23_DISAGG   (0)
#else
#define GIRQ23_DISAGG   (1)
#endif

#if configCPU_DISAGGREGATED_ISRS == 0
#define GIRQ24_DISAGG   (0)
#else
#define GIRQ24_DISAGG   (1)
#endif

#define GIRQ25_DISAGG   (0)
#define GIRQ26_DISAGG   (0)



/*
 * Aggregated/Dis-aggrated bit-map
 */
#define JTVIC_DISAGR_BITMAP ( ((GIRQ08_DISAGG)<<0) + \
    ((GIRQ09_DISAGG)<<1) + ((GIRQ10_DISAGG)<<2) + \
    ((GIRQ11_DISAGG)<<3) + ((GIRQ12_DISAGG)<<4) + \
    ((GIRQ13_DISAGG)<<5) + ((GIRQ14_DISAGG)<<6) + \
    ((GIRQ15_DISAGG)<<7) + ((GIRQ16_DISAGG)<<8) + \
    ((GIRQ17_DISAGG)<<9) + ((GIRQ18_DISAGG)<<10) + \
    ((GIRQ19_DISAGG)<<11) + ((GIRQ20_DISAGG)<<12) + \
    ((GIRQ21_DISAGG)<<13) + ((GIRQ22_DISAGG)<<14) + \
    ((GIRQ23_DISAGG)<<15) + ((GIRQ24_DISAGG)<<16) + \
    ((GIRQ25_DISAGG)<<17) + ((GIRQ26_DISAGG)<<18) )


#define GIRQ08_NUM_SOURCES  (23)
#define GIRQ08_SRC_MASK     (0x007FFFFFul)

#define GIRQ09_NUM_SOURCES  (31)
#define GIRQ09_SRC_MASK     (0x7FFFFFFFul)

#define GIRQ10_NUM_SOURCES  (24)
#define GIRQ10_SRC_MASK     (0x00FFFFFFul)

#define GIRQ11_NUM_SOURCES  (30)
#define GIRQ11_SRC_MASK     (0x7FFFFFFEul)

#define GIRQ12_NUM_SOURCES  (3)
#define GIRQ12_SRC_MASK     (0x00000007ul)

#define GIRQ13_NUM_SOURCES  (7)
#define GIRQ13_SRC_MASK     (0x0000007Ful)

#define GIRQ14_NUM_SOURCES  (6)
#define GIRQ14_SRC_MASK     (0x0000003Ful)

#define GIRQ15_NUM_SOURCES  (19)
#define GIRQ15_SRC_MASK     (0x0007FFFFul)

#define GIRQ16_NUM_SOURCES  (10)
#define GIRQ16_SRC_MASK     (0x000003FFul)

#define GIRQ17_NUM_SOURCES  (11)
#define GIRQ17_SRC_MASK     (0x000007FFul)

#define GIRQ18_NUM_SOURCES  (1)
#define GIRQ18_SRC_MASK     (0x00000001ul)

#define GIRQ19_NUM_SOURCES  (9)
#define GIRQ19_SRC_MASK     (0x000001FFul)

#define GIRQ20_NUM_SOURCES  (6)
#define GIRQ20_SRC_MASK     (0x0000003Ful)

#define GIRQ21_NUM_SOURCES  (3)
#define GIRQ21_SRC_MASK     (0x00000007ul)

#define GIRQ22_NUM_SOURCES  (10)
#define GIRQ22_SRC_MASK     (0x000003FFul)

#define GIRQ23_NUM_SOURCES  (14)
#define GIRQ23_SRC_MASK     (0x00003FFFul)

#define GIRQ24_NUM_SOURCES  (3)
#define GIRQ24_SRC_MASK     (0x00000007ul)

#define GIRQ25_NUM_SOURCES  (28)
#define GIRQ25_SRC_MASK     (0x0FFFFFFFul)

#define GIRQ26_NUM_SOURCES  (12)
#define GIRQ26_SRC_MASK     (0x00000FFFul)

/**   @}
 */
