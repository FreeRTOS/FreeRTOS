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

/** @file mec14xx_girqs.h
 *MEC14xx Interrupt Table Header
 */
/** @defgroup MEC14xx interrupt
 */



#ifndef _MEC14XX_GIRQS_H 
#define _MEC14XX_GIRQS_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

#include "mec14xx.h"
#include "mec14xx_jtvic.h"
#include "mec14xx_girqm.h"

#define GIRQ08_SRC00_PRI    JTVIC_PRI1
#define GIRQ08_SRC01_PRI    JTVIC_PRI1
#define GIRQ08_SRC02_PRI    JTVIC_PRI1
#define GIRQ08_SRC03_PRI    JTVIC_PRI1
#define GIRQ08_SRC04_PRI    JTVIC_PRI1
#define GIRQ08_SRC05_PRI    JTVIC_PRI1
#define GIRQ08_SRC06_PRI    JTVIC_PRI1
#define GIRQ08_SRC07_PRI    JTVIC_PRI1
#define GIRQ08_SRC08_PRI    JTVIC_PRI1
#define GIRQ08_SRC09_PRI    JTVIC_PRI1
#define GIRQ08_SRC10_PRI    JTVIC_PRI1
#define GIRQ08_SRC11_PRI    JTVIC_PRI1
#define GIRQ08_SRC12_PRI    JTVIC_PRI1
#define GIRQ08_SRC13_PRI    JTVIC_PRI1
#define GIRQ08_SRC14_PRI    JTVIC_PRI1
#define GIRQ08_SRC15_PRI    JTVIC_PRI1
#define GIRQ08_SRC16_PRI    JTVIC_PRI1
#define GIRQ08_SRC17_PRI    JTVIC_PRI1
#define GIRQ08_SRC18_PRI    JTVIC_PRI1
#define GIRQ08_SRC19_PRI    JTVIC_PRI1
#define GIRQ08_SRC20_PRI    JTVIC_PRI1
#define GIRQ08_SRC21_PRI    JTVIC_PRI1
#define GIRQ08_SRC22_PRI    JTVIC_PRI1


#define GIRQ08_PRI_A (JTVIC_PRI_VAL(0, GIRQ08_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ08_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ08_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ08_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ08_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ08_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ08_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ08_SRC07_PRI))

#define GIRQ08_PRI_B (JTVIC_PRI_VAL(0, GIRQ08_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ08_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ08_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ08_SRC11_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ08_SRC12_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ08_SRC13_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ08_SRC14_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ08_SRC15_PRI))

#define GIRQ08_PRI_C (JTVIC_PRI_VAL(0, GIRQ08_SRC16_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ08_SRC17_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ08_SRC18_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ08_SRC19_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ08_SRC20_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ08_SRC21_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ08_SRC22_PRI) )

#define GIRQ08_PRI_D (0ul)


/*
 * GIRQ09
 */
#define GIRQ09_SRC00_PRI    JTVIC_PRI1
#define GIRQ09_SRC01_PRI    JTVIC_PRI1
#define GIRQ09_SRC02_PRI    JTVIC_PRI1
#define GIRQ09_SRC03_PRI    JTVIC_PRI1
#define GIRQ09_SRC04_PRI    JTVIC_PRI1
#define GIRQ09_SRC05_PRI    JTVIC_PRI1
#define GIRQ09_SRC06_PRI    JTVIC_PRI1
#define GIRQ09_SRC07_PRI    JTVIC_PRI1
#define GIRQ09_SRC08_PRI    JTVIC_PRI1
#define GIRQ09_SRC09_PRI    JTVIC_PRI1
#define GIRQ09_SRC10_PRI    JTVIC_PRI1
#define GIRQ09_SRC11_PRI    JTVIC_PRI1
#define GIRQ09_SRC12_PRI    JTVIC_PRI1
#define GIRQ09_SRC13_PRI    JTVIC_PRI1
#define GIRQ09_SRC14_PRI    JTVIC_PRI1
#define GIRQ09_SRC15_PRI    JTVIC_PRI1
#define GIRQ09_SRC16_PRI    JTVIC_PRI1
#define GIRQ09_SRC17_PRI    JTVIC_PRI1
#define GIRQ09_SRC18_PRI    JTVIC_PRI1
#define GIRQ09_SRC19_PRI    JTVIC_PRI1
#define GIRQ09_SRC20_PRI    JTVIC_PRI1
#define GIRQ09_SRC21_PRI    JTVIC_PRI1
#define GIRQ09_SRC22_PRI    JTVIC_PRI1
#define GIRQ09_SRC23_PRI    JTVIC_PRI1
#define GIRQ09_SRC24_PRI    JTVIC_PRI1
#define GIRQ09_SRC25_PRI    JTVIC_PRI1
#define GIRQ09_SRC26_PRI    JTVIC_PRI1
#define GIRQ09_SRC27_PRI    JTVIC_PRI1
#define GIRQ09_SRC28_PRI    JTVIC_PRI1
#define GIRQ09_SRC29_PRI    JTVIC_PRI1
#define GIRQ09_SRC30_PRI    JTVIC_PRI1


#define GIRQ09_PRI_A (JTVIC_PRI_VAL(0, GIRQ09_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ09_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ09_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ09_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ09_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ09_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ09_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ09_SRC07_PRI))

#define GIRQ09_PRI_B (JTVIC_PRI_VAL(0, GIRQ09_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ09_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ09_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ09_SRC11_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ09_SRC12_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ09_SRC13_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ09_SRC14_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ09_SRC15_PRI))

#define GIRQ09_PRI_C (JTVIC_PRI_VAL(0, GIRQ09_SRC16_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ09_SRC17_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ09_SRC18_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ09_SRC19_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ09_SRC20_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ09_SRC21_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ09_SRC22_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ09_SRC23_PRI))

#define GIRQ09_PRI_D (JTVIC_PRI_VAL(0, GIRQ09_SRC24_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ09_SRC25_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ09_SRC26_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ09_SRC27_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ09_SRC28_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ09_SRC29_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ09_SRC30_PRI) )


/*
 * GIRQ10
 */
#define GIRQ10_SRC00_PRI    JTVIC_PRI1
#define GIRQ10_SRC01_PRI    JTVIC_PRI1
#define GIRQ10_SRC02_PRI    JTVIC_PRI1
#define GIRQ10_SRC03_PRI    JTVIC_PRI1
#define GIRQ10_SRC04_PRI    JTVIC_PRI1
#define GIRQ10_SRC05_PRI    JTVIC_PRI1
#define GIRQ10_SRC06_PRI    JTVIC_PRI1
#define GIRQ10_SRC07_PRI    JTVIC_PRI1
#define GIRQ10_SRC08_PRI    JTVIC_PRI1
#define GIRQ10_SRC09_PRI    JTVIC_PRI1
#define GIRQ10_SRC10_PRI    JTVIC_PRI1
#define GIRQ10_SRC11_PRI    JTVIC_PRI1
#define GIRQ10_SRC12_PRI    JTVIC_PRI7
#define GIRQ10_SRC13_PRI    JTVIC_PRI1
#define GIRQ10_SRC14_PRI    JTVIC_PRI1
#define GIRQ10_SRC15_PRI    JTVIC_PRI1
#define GIRQ10_SRC16_PRI    JTVIC_PRI1
#define GIRQ10_SRC17_PRI    JTVIC_PRI1
#define GIRQ10_SRC18_PRI    JTVIC_PRI1
#define GIRQ10_SRC19_PRI    JTVIC_PRI1
#define GIRQ10_SRC20_PRI    JTVIC_PRI1
/* Sources [21:22] Reserved */
#define GIRQ10_SRC23_PRI    JTVIC_PRI1


#define GIRQ10_PRI_A (JTVIC_PRI_VAL(0, GIRQ10_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ10_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ10_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ10_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ10_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ10_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ10_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ10_SRC07_PRI))

#define GIRQ10_PRI_B (JTVIC_PRI_VAL(0, GIRQ10_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ10_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ10_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ10_SRC11_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ10_SRC12_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ10_SRC13_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ10_SRC14_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ10_SRC15_PRI))

#define GIRQ10_PRI_C (JTVIC_PRI_VAL(0, GIRQ10_SRC16_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ10_SRC17_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ10_SRC18_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ10_SRC19_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ10_SRC20_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ10_SRC23_PRI))

#define GIRQ10_PRI_D (0ul)


/*
 * GIRQ11
 */
/* Source[0] Reserved */
#define GIRQ11_SRC01_PRI    JTVIC_PRI1
#define GIRQ11_SRC02_PRI    JTVIC_PRI1
#define GIRQ11_SRC03_PRI    JTVIC_PRI1
#define GIRQ11_SRC04_PRI    JTVIC_PRI1
#define GIRQ11_SRC05_PRI    JTVIC_PRI1
#define GIRQ11_SRC06_PRI    JTVIC_PRI1
#define GIRQ11_SRC07_PRI    JTVIC_PRI1
#define GIRQ11_SRC08_PRI    JTVIC_PRI1
#define GIRQ11_SRC09_PRI    JTVIC_PRI1
#define GIRQ11_SRC10_PRI    JTVIC_PRI1
#define GIRQ11_SRC11_PRI    JTVIC_PRI1
#define GIRQ11_SRC12_PRI    JTVIC_PRI1
#define GIRQ11_SRC13_PRI    JTVIC_PRI1
#define GIRQ11_SRC14_PRI    JTVIC_PRI1
#define GIRQ11_SRC15_PRI    JTVIC_PRI1
#define GIRQ11_SRC16_PRI    JTVIC_PRI1
#define GIRQ11_SRC17_PRI    JTVIC_PRI1
#define GIRQ11_SRC18_PRI    JTVIC_PRI1
#define GIRQ11_SRC19_PRI    JTVIC_PRI1
#define GIRQ11_SRC20_PRI    JTVIC_PRI1
#define GIRQ11_SRC21_PRI    JTVIC_PRI1
#define GIRQ11_SRC22_PRI    JTVIC_PRI1
#define GIRQ11_SRC23_PRI    JTVIC_PRI1
#define GIRQ11_SRC24_PRI    JTVIC_PRI1
#define GIRQ11_SRC25_PRI    JTVIC_PRI1
#define GIRQ11_SRC26_PRI    JTVIC_PRI1
#define GIRQ11_SRC27_PRI    JTVIC_PRI1
#define GIRQ11_SRC28_PRI    JTVIC_PRI1
#define GIRQ11_SRC29_PRI    JTVIC_PRI1
#define GIRQ11_SRC30_PRI    JTVIC_PRI1


#define GIRQ11_PRI_A (JTVIC_PRI_VAL(1, GIRQ11_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ11_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ11_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ11_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ11_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ11_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ11_SRC07_PRI))

#define GIRQ11_PRI_B (JTVIC_PRI_VAL(0, GIRQ11_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ11_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ11_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ11_SRC11_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ11_SRC12_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ11_SRC13_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ11_SRC14_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ11_SRC15_PRI))

#define GIRQ11_PRI_C (JTVIC_PRI_VAL(0, GIRQ11_SRC16_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ11_SRC17_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ11_SRC18_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ11_SRC19_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ11_SRC20_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ11_SRC21_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ11_SRC22_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ11_SRC23_PRI))

#define GIRQ11_PRI_D (JTVIC_PRI_VAL(0, GIRQ11_SRC24_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ11_SRC25_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ11_SRC26_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ11_SRC27_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ11_SRC28_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ11_SRC29_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ11_SRC30_PRI) )


/*
 * GIRQ12
 */

#define GIRQ12_SRC00_PRI    JTVIC_PRI1
#define GIRQ12_SRC01_PRI    JTVIC_PRI1
#define GIRQ12_SRC02_PRI    JTVIC_PRI1


#define GIRQ12_PRI_A (JTVIC_PRI_VAL(0, GIRQ12_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ12_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ12_SRC02_PRI) )

#define GIRQ12_PRI_B (0ul)
#define GIRQ12_PRI_C (0ul)
#define GIRQ12_PRI_D (0ul)


/*
 * GIRQ13
 */
#define GIRQ13_SRC00_PRI    JTVIC_PRI1
#define GIRQ13_SRC01_PRI    JTVIC_PRI1
#define GIRQ13_SRC02_PRI    JTVIC_PRI1
#define GIRQ13_SRC03_PRI    JTVIC_PRI1
#define GIRQ13_SRC04_PRI    JTVIC_PRI1
#define GIRQ13_SRC05_PRI    JTVIC_PRI1
#define GIRQ13_SRC06_PRI    JTVIC_PRI1


#define GIRQ13_PRI_A (JTVIC_PRI_VAL(0, GIRQ13_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ13_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ13_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ13_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ13_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ13_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ13_SRC06_PRI) )

#define GIRQ13_PRI_B (0ul)
#define GIRQ13_PRI_C (0ul)
#define GIRQ13_PRI_D (0ul)


/*
 * GIRQ14
 */
#define GIRQ14_SRC00_PRI    JTVIC_PRI1
#define GIRQ14_SRC01_PRI    JTVIC_PRI1
#define GIRQ14_SRC02_PRI    JTVIC_PRI1
#define GIRQ14_SRC03_PRI    JTVIC_PRI1
#define GIRQ14_SRC04_PRI    JTVIC_PRI1
#define GIRQ14_SRC05_PRI    JTVIC_PRI1


#define GIRQ14_PRI_A (JTVIC_PRI_VAL(0, GIRQ14_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ14_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ14_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ14_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ14_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ14_SRC05_PRI) )

#define GIRQ14_PRI_B (0ul)
#define GIRQ14_PRI_C (0ul)
#define GIRQ14_PRI_D (0ul)


/*
 * GIRQ15
 */
#define GIRQ15_SRC00_PRI    JTVIC_PRI1
#define GIRQ15_SRC01_PRI    JTVIC_PRI1
#define GIRQ15_SRC02_PRI    JTVIC_PRI1
#define GIRQ15_SRC03_PRI    JTVIC_PRI1
#define GIRQ15_SRC04_PRI    JTVIC_PRI1
#define GIRQ15_SRC05_PRI    JTVIC_PRI1
#define GIRQ15_SRC06_PRI    JTVIC_PRI1
#define GIRQ15_SRC07_PRI    JTVIC_PRI1
#define GIRQ15_SRC08_PRI    JTVIC_PRI1
#define GIRQ15_SRC09_PRI    JTVIC_PRI1
#define GIRQ15_SRC10_PRI    JTVIC_PRI1
#define GIRQ15_SRC11_PRI    JTVIC_PRI1
#define GIRQ15_SRC12_PRI    JTVIC_PRI1
#define GIRQ15_SRC13_PRI    JTVIC_PRI1
#define GIRQ15_SRC14_PRI    JTVIC_PRI1
#define GIRQ15_SRC15_PRI    JTVIC_PRI1
#define GIRQ15_SRC16_PRI    JTVIC_PRI1
#define GIRQ15_SRC17_PRI    JTVIC_PRI1
#define GIRQ15_SRC18_PRI    JTVIC_PRI1


#define GIRQ15_PRI_A (JTVIC_PRI_VAL(0, GIRQ15_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ15_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ15_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ15_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ15_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ15_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ15_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ15_SRC07_PRI))

#define GIRQ15_PRI_B (JTVIC_PRI_VAL(0, GIRQ15_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ15_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ15_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ15_SRC11_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ15_SRC12_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ15_SRC13_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ15_SRC14_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ15_SRC15_PRI))

#define GIRQ15_PRI_C (JTVIC_PRI_VAL(0, GIRQ15_SRC16_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ15_SRC17_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ15_SRC18_PRI) )

#define GIRQ15_PRI_D (0ul)


/*
 * GIRQ16
 */
#define GIRQ16_SRC00_PRI    JTVIC_PRI1
#define GIRQ16_SRC01_PRI    JTVIC_PRI1
#define GIRQ16_SRC02_PRI    JTVIC_PRI1
#define GIRQ16_SRC03_PRI    JTVIC_PRI1
#define GIRQ16_SRC04_PRI    JTVIC_PRI1
#define GIRQ16_SRC05_PRI    JTVIC_PRI1
#define GIRQ16_SRC06_PRI    JTVIC_PRI1
#define GIRQ16_SRC07_PRI    JTVIC_PRI1
#define GIRQ16_SRC08_PRI    JTVIC_PRI1
#define GIRQ16_SRC09_PRI    JTVIC_PRI1


#define GIRQ16_PRI_A (JTVIC_PRI_VAL(0, GIRQ16_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ16_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ16_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ16_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ16_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ16_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ16_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ16_SRC07_PRI))

#define GIRQ16_PRI_B (JTVIC_PRI_VAL(0, GIRQ16_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ16_SRC09_PRI) )

#define GIRQ16_PRI_C (0ul)
#define GIRQ16_PRI_D (0ul)


/*
 * GIRQ17
 */
#define GIRQ17_SRC00_PRI    JTVIC_PRI1
#define GIRQ17_SRC01_PRI    JTVIC_PRI1
#define GIRQ17_SRC02_PRI    JTVIC_PRI1
#define GIRQ17_SRC03_PRI    JTVIC_PRI1
#define GIRQ17_SRC04_PRI    JTVIC_PRI1
#define GIRQ17_SRC05_PRI    JTVIC_PRI1
#define GIRQ17_SRC06_PRI    JTVIC_PRI1
#define GIRQ17_SRC07_PRI    JTVIC_PRI1
#define GIRQ17_SRC08_PRI    JTVIC_PRI1
#define GIRQ17_SRC09_PRI    JTVIC_PRI1
#define GIRQ17_SRC10_PRI    JTVIC_PRI1


#define GIRQ17_PRI_A (JTVIC_PRI_VAL(0, GIRQ17_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ17_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ17_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ17_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ17_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ17_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ17_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ17_SRC07_PRI))

#define GIRQ17_PRI_B (JTVIC_PRI_VAL(0, GIRQ17_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ17_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ17_SRC10_PRI) )

#define GIRQ17_PRI_C (0ul)
#define GIRQ17_PRI_D (0ul)


/*
 * GIRQ18
 */
#define GIRQ18_DISAGG   (0)
#define GIRQ18_SRC00_PRI    JTVIC_PRI1


#define GIRQ18_PRI_A (JTVIC_PRI_VAL(0, GIRQ18_SRC00_PRI) )

#define GIRQ18_PRI_B (0ul)
#define GIRQ18_PRI_C (0ul)
#define GIRQ18_PRI_D (0ul)


/*
 * GIRQ19
 */
#define GIRQ19_SRC00_PRI    JTVIC_PRI1
#define GIRQ19_SRC01_PRI    JTVIC_PRI1
#define GIRQ19_SRC02_PRI    JTVIC_PRI1
#define GIRQ19_SRC03_PRI    JTVIC_PRI1
#define GIRQ19_SRC04_PRI    JTVIC_PRI1
#define GIRQ19_SRC05_PRI    JTVIC_PRI1
#define GIRQ19_SRC06_PRI    JTVIC_PRI1
#define GIRQ19_SRC07_PRI    JTVIC_PRI1
#define GIRQ19_SRC08_PRI    JTVIC_PRI1


#define GIRQ19_PRI_A (JTVIC_PRI_VAL(0, GIRQ19_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ19_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ19_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ19_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ19_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ19_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ19_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ19_SRC07_PRI))

#define GIRQ19_PRI_B (JTVIC_PRI_VAL(0, GIRQ19_SRC08_PRI) )

#define GIRQ19_PRI_C (0ul)
#define GIRQ19_PRI_D (0ul) 


/*
 * GIRQ20
 */
#define GIRQ20_SRC00_PRI    JTVIC_PRI1
#define GIRQ20_SRC01_PRI    JTVIC_PRI1
#define GIRQ20_SRC02_PRI    JTVIC_PRI1
#define GIRQ20_SRC03_PRI    JTVIC_PRI1
#define GIRQ20_SRC04_PRI    JTVIC_PRI1
#define GIRQ20_SRC05_PRI    JTVIC_PRI1


#define GIRQ20_PRI_A (JTVIC_PRI_VAL(0, GIRQ20_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ20_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ20_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ20_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ20_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ20_SRC05_PRI) )

#define GIRQ20_PRI_B (0ul)
#define GIRQ20_PRI_C (0ul)
#define GIRQ20_PRI_D (0ul)


/* GIRQ21 is for Wake purposes. It only wakes IA logic and 
 * does not fire an interrupt to the CPU.
 * No GIRQ21 sources are defined!
 */
#define GIRQ21_DISAGG   (0)
#define GIRQ21_PRI_A (0ul)
#define GIRQ21_PRI_B (0ul)
#define GIRQ21_PRI_C (0ul)
#define GIRQ21_PRI_D (0ul)


/*
 * GIRQ22
 */
#define GIRQ22_SRC00_PRI    JTVIC_PRI1
#define GIRQ22_SRC01_PRI    JTVIC_PRI1
#define GIRQ22_SRC02_PRI    JTVIC_PRI1
#define GIRQ22_SRC03_PRI    JTVIC_PRI1
#define GIRQ22_SRC04_PRI    JTVIC_PRI1
#define GIRQ22_SRC05_PRI    JTVIC_PRI1
#define GIRQ22_SRC06_PRI    JTVIC_PRI1
#define GIRQ22_SRC07_PRI    JTVIC_PRI1
#define GIRQ22_SRC08_PRI    JTVIC_PRI1
#define GIRQ22_SRC09_PRI    JTVIC_PRI1


#define GIRQ22_PRI_A (JTVIC_PRI_VAL(0, GIRQ22_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ22_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ22_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ22_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ22_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ22_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ22_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ22_SRC07_PRI))

#define GIRQ22_PRI_B (JTVIC_PRI_VAL(0, GIRQ22_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ22_SRC09_PRI) )

#define GIRQ22_PRI_C (0ul)
#define GIRQ22_PRI_D (0ul)


/*
 * GIRQ23
 */
#define GIRQ23_SRC00_PRI    JTVIC_PRI1
#define GIRQ23_SRC01_PRI    JTVIC_PRI1
#define GIRQ23_SRC02_PRI    JTVIC_PRI1
#define GIRQ23_SRC03_PRI    JTVIC_PRI1
#define GIRQ23_SRC04_PRI    JTVIC_PRI1
#define GIRQ23_SRC05_PRI    JTVIC_PRI1
#define GIRQ23_SRC06_PRI    JTVIC_PRI1
#define GIRQ23_SRC07_PRI    JTVIC_PRI1
#define GIRQ23_SRC08_PRI    JTVIC_PRI1
#define GIRQ23_SRC09_PRI    JTVIC_PRI1
#define GIRQ23_SRC10_PRI    JTVIC_PRI1
#define GIRQ23_SRC11_PRI    JTVIC_PRI1
#define GIRQ23_SRC12_PRI    JTVIC_PRI1
#define GIRQ23_SRC13_PRI    JTVIC_PRI1
#define GIRQ23_SRC14_PRI    JTVIC_PRI1
#define GIRQ23_SRC15_PRI    JTVIC_PRI1


#define GIRQ23_PRI_A (JTVIC_PRI_VAL(0, GIRQ23_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ23_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ23_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ23_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ23_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ23_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ23_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ23_SRC07_PRI))

#define GIRQ23_PRI_B (JTVIC_PRI_VAL(0, GIRQ23_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ23_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ23_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ23_SRC11_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ23_SRC12_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ23_SRC13_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ23_SRC14_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ23_SRC15_PRI))

#define GIRQ23_PRI_C (0ul)
#define GIRQ23_PRI_D (0ul)


/*
 * GIRQ24
 */
#define GIRQ24_SRC00_PRI    JTVIC_PRI3
#define GIRQ24_SRC01_PRI    JTVIC_PRI1
#define GIRQ24_SRC02_PRI    JTVIC_PRI1


#define GIRQ24_PRI_A (JTVIC_PRI_VAL(0, GIRQ24_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ24_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ24_SRC02_PRI) )

#define GIRQ24_PRI_B (0ul)
#define GIRQ24_PRI_C (0ul)
#define GIRQ24_PRI_D (0ul)


/*
 * GIRQ25
 */
#define GIRQ25_SRC00_PRI    JTVIC_PRI1
#define GIRQ25_SRC01_PRI    JTVIC_PRI1
#define GIRQ25_SRC02_PRI    JTVIC_PRI1
#define GIRQ25_SRC03_PRI    JTVIC_PRI1
#define GIRQ25_SRC04_PRI    JTVIC_PRI1
#define GIRQ25_SRC05_PRI    JTVIC_PRI1
#define GIRQ25_SRC06_PRI    JTVIC_PRI1
#define GIRQ25_SRC07_PRI    JTVIC_PRI1
#define GIRQ25_SRC08_PRI    JTVIC_PRI1
#define GIRQ25_SRC09_PRI    JTVIC_PRI1
#define GIRQ25_SRC10_PRI    JTVIC_PRI1
#define GIRQ25_SRC11_PRI    JTVIC_PRI1
#define GIRQ25_SRC12_PRI    JTVIC_PRI1
#define GIRQ25_SRC13_PRI    JTVIC_PRI1
#define GIRQ25_SRC14_PRI    JTVIC_PRI1
#define GIRQ25_SRC15_PRI    JTVIC_PRI1
#define GIRQ25_SRC16_PRI    JTVIC_PRI1
#define GIRQ25_SRC17_PRI    JTVIC_PRI1
#define GIRQ25_SRC18_PRI    JTVIC_PRI1
#define GIRQ25_SRC19_PRI    JTVIC_PRI1
#define GIRQ25_SRC20_PRI    JTVIC_PRI1
#define GIRQ25_SRC21_PRI    JTVIC_PRI1
#define GIRQ25_SRC22_PRI    JTVIC_PRI1
#define GIRQ25_SRC23_PRI    JTVIC_PRI1
#define GIRQ25_SRC24_PRI    JTVIC_PRI1
#define GIRQ25_SRC25_PRI    JTVIC_PRI1
#define GIRQ25_SRC26_PRI    JTVIC_PRI1
#define GIRQ25_SRC27_PRI    JTVIC_PRI1


#define GIRQ25_PRI_A (JTVIC_PRI_VAL(0, GIRQ25_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ25_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ25_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ25_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ25_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ25_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ25_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ25_SRC07_PRI))

#define GIRQ25_PRI_B (JTVIC_PRI_VAL(0, GIRQ25_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ25_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ25_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ25_SRC11_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ25_SRC12_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ25_SRC13_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ25_SRC14_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ25_SRC15_PRI))

#define GIRQ25_PRI_C (JTVIC_PRI_VAL(0, GIRQ25_SRC16_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ25_SRC17_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ25_SRC18_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ25_SRC19_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ25_SRC20_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ25_SRC21_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ25_SRC22_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ25_SRC23_PRI))

#define GIRQ25_PRI_D (JTVIC_PRI_VAL(0, GIRQ25_SRC24_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ25_SRC25_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ25_SRC26_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ25_SRC27_PRI) )


/*
 * GIRQ26
 */
#define GIRQ26_SRC00_PRI    JTVIC_PRI1
#define GIRQ26_SRC01_PRI    JTVIC_PRI1
#define GIRQ26_SRC02_PRI    JTVIC_PRI1
#define GIRQ26_SRC03_PRI    JTVIC_PRI1
#define GIRQ26_SRC04_PRI    JTVIC_PRI1
#define GIRQ26_SRC05_PRI    JTVIC_PRI1
#define GIRQ26_SRC06_PRI    JTVIC_PRI1
#define GIRQ26_SRC07_PRI    JTVIC_PRI1
#define GIRQ26_SRC08_PRI    JTVIC_PRI1
#define GIRQ26_SRC09_PRI    JTVIC_PRI1
#define GIRQ26_SRC10_PRI    JTVIC_PRI1
#define GIRQ26_SRC11_PRI    JTVIC_PRI1


#define GIRQ26_PRI_A (JTVIC_PRI_VAL(0, GIRQ26_SRC00_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ26_SRC01_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ26_SRC02_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ26_SRC03_PRI) + \
                        JTVIC_PRI_VAL(4, GIRQ26_SRC04_PRI) + \
                        JTVIC_PRI_VAL(5, GIRQ26_SRC05_PRI) + \
                        JTVIC_PRI_VAL(6, GIRQ26_SRC06_PRI) + \
                        JTVIC_PRI_VAL(7, GIRQ26_SRC07_PRI))

#define GIRQ26_PRI_B (JTVIC_PRI_VAL(0, GIRQ26_SRC08_PRI) + \
                        JTVIC_PRI_VAL(1, GIRQ26_SRC09_PRI) + \
                        JTVIC_PRI_VAL(2, GIRQ26_SRC10_PRI) + \
                        JTVIC_PRI_VAL(3, GIRQ26_SRC11_PRI) )

#define GIRQ26_PRI_C (0ul)
#define GIRQ26_PRI_D (0ul)


/*
 * b[7:0] = GIRQ number (0-18) -> GIRQ(8,26)
 * b[15:8] = bit number (0-31)
 */
typedef enum IRQn
{   /* GIRQ08 */
    GPIO140_IRQn = ((0 << 8) + 0),
    GPIO141_IRQn = ((1 << 8) + 0),
    GPIO142_IRQn = ((2 << 8) + 0),
    GPIO143_IRQn = ((3 << 8) + 0),
    GPIO144_IRQn = ((4 << 8) + 0),
    GPIO145_IRQn = ((5 << 8) + 0),
    GPIO146_IRQn = ((6 << 8) + 0),
    GPIO147_IRQn = ((7 << 8) + 0),
    GPIO150_IRQn = ((8 << 8) + 0),
    GPIO151_IRQn = ((9 << 8) + 0),
    GPIO152_IRQn = ((10 << 8) + 0),
    GPIO153_IRQn = ((11 << 8) + 0),
    GPIO154_IRQn = ((12 << 8) + 0),
    GPIO155_IRQn = ((13 << 8) + 0),
    GPIO156_IRQn = ((14 << 8) + 0),
    GPIO157_IRQn = ((15 << 8) + 0),
    GPIO160_IRQn = ((16 << 8) + 0),
    GPIO161_IRQn = ((17 << 8) + 0),
    GPIO162_IRQn = ((18 << 8) + 0),
    GPIO163_IRQn = ((19 << 8) + 0),
    GPIO164_IRQn = ((20 << 8) + 0),
    GPIO165_IRQn = ((21 << 8) + 0),
    GPIO166_IRQn = ((22 << 8) + 0),
    /* GIRQ09 */
    GPIO100_IRQn = ((0 << 8) + 1),
    GPIO101_IRQn = ((1 << 8) + 1),
    GPIO102_IRQn = ((2 << 8) + 1),
    GPIO103_IRQn = ((3 << 8) + 1),
    GPIO104_IRQn = ((4 << 8) + 1),
    GPIO105_IRQn = ((5 << 8) + 1),
    GPIO106_IRQn = ((6 << 8) + 1),
    GPIO107_IRQn = ((7 << 8) + 1),
    GPIO110_IRQn = ((8 << 8) + 1),
    GPIO111_IRQn = ((9 << 8) + 1),
    GPIO112_IRQn = ((10 << 8) + 1),
    GPIO113_IRQn = ((11 << 8) + 1),
    GPIO114_IRQn = ((12 << 8) + 1),
    GPIO115_IRQn = ((13 << 8) + 1),
    GPIO116_IRQn = ((14 << 8) + 1),
    GPIO117_IRQn = ((15 << 8) + 1),
    GPIO120_IRQn = ((16 << 8) + 1),
    GPIO121_IRQn = ((17 << 8) + 1),
    GPIO122_IRQn = ((18 << 8) + 1),
    GPIO123_IRQn = ((19 << 8) + 1),
    GPIO124_IRQn = ((20 << 8) + 1),
    GPIO125_IRQn = ((21 << 8) + 1),
    GPIO126_IRQn = ((22 << 8) + 1),
    GPIO127_IRQn = ((23 << 8) + 1),
    GPIO130_IRQn = ((24 << 8) + 1),
    GPIO131_IRQn = ((25 << 8) + 1),
    GPIO132_IRQn = ((26 << 8) + 1),
    GPIO133_IRQn = ((27 << 8) + 1),
    GPIO134_IRQn = ((28 << 8) + 1),
    GPIO135_IRQn = ((29 << 8) + 1),
    GPIO136_IRQn = ((30 << 8) + 1),
    /* GIRQ10 */
    GPIO040_IRQn = ((0 << 8) + 2),
    GPIO041_IRQn = ((1 << 8) + 2),
    GPIO042_IRQn = ((2 << 8) + 2),
    GPIO043_IRQn = ((3 << 8) + 2),
    GPIO044_IRQn = ((4 << 8) + 2),
    GPIO045_IRQn = ((5 << 8) + 2),
    GPIO046_IRQn = ((6 << 8) + 2),
    GPIO047_IRQn = ((7 << 8) + 2),
    GPIO050_IRQn = ((8 << 8) + 2),
    GPIO051_IRQn = ((9 << 8) + 2),
    GPIO052_IRQn = ((10 << 8) + 2),
    GPIO053_IRQn = ((11 << 8) + 2),
    GPIO054_IRQn = ((12 << 8) + 2),
    GPIO055_IRQn = ((13 << 8) + 2),
    GPIO056_IRQn = ((14 << 8) + 2),
    GPIO057_IRQn = ((15 << 8) + 2),
    GPIO060_IRQn = ((16 << 8) + 2),
    GPIO061_IRQn = ((17 << 8) + 2),
    GPIO062_IRQn = ((18 << 8) + 2),
    GPIO063_IRQn = ((19 << 8) + 2),
    GPIO064_IRQn = ((20 << 8) + 2),
    GPIO065_IRQn = ((21 << 8) + 2),
    GPIO066_IRQn = ((22 << 8) + 2),
    GPIO067_IRQn = ((23 << 8) + 2),
    /* GIRQ11 */
    GPIO001_IRQn = ((1 << 8) + 3),
    GPIO002_IRQn = ((2 << 8) + 3),
    GPIO003_IRQn = ((3 << 8) + 3),
    GPIO004_IRQn = ((4 << 8) + 3),
    GPIO005_IRQn = ((5 << 8) + 3),
    GPIO006_IRQn = ((6 << 8) + 3),
    GPIO007_IRQn = ((7 << 8) + 3),
    GPIO010_IRQn = ((8 << 8) + 3),
    GPIO011_IRQn = ((9 << 8) + 3),
    GPIO012_IRQn = ((10 << 8) + 3),
    GPIO013_IRQn = ((11 << 8) + 3),
    GPIO014_IRQn = ((12 << 8) + 3),
    GPIO015_IRQn = ((13 << 8) + 3),
    GPIO016_IRQn = ((14 << 8) + 3),
    GPIO017_IRQn = ((15 << 8) + 3),
    GPIO020_IRQn = ((16 << 8) + 3),
    GPIO021_IRQn = ((17 << 8) + 3),
    GPIO022_IRQn = ((18 << 8) + 3),
    GPIO023_IRQn = ((19 << 8) + 3),
    GPIO024_IRQn = ((20 << 8) + 3),
    GPIO025_IRQn = ((21 << 8) + 3),
    GPIO026_IRQn = ((22 << 8) + 3),
    GPIO027_IRQn = ((23 << 8) + 3),
    GPIO030_IRQn = ((24 << 8) + 3),
    GPIO031_IRQn = ((25 << 8) + 3),
    GPIO032_IRQn = ((26 << 8) + 3),
    GPIO033_IRQn = ((27 << 8) + 3),
    GPIO034_IRQn = ((28 << 8) + 3),
    GPIO035_IRQn = ((29 << 8) + 3),
    GPIO036_IRQn = ((30 << 8) + 3),
    /* GIRQ12 */
    SMB0_IRQn = ((0 << 8) + 4),
    SMB1_IRQn = ((1 << 8) + 4),
    SMB2_IRQn = ((2 << 8) + 4),
    /* GIRQ13 */
    DMA0_IRQn = ((0 << 8) + 5),
    DMA1_IRQn = ((1 << 8) + 5),
    DMA2_IRQn = ((2 << 8) + 5),
    DMA3_IRQn = ((3 << 8) + 5),
    DMA4_IRQn = ((4 << 8) + 5),
    DMA5_IRQn = ((5 << 8) + 5),
    DMA6_IRQn = ((6 << 8) + 5),
    /* GIRQ14 */
    LPC_ERR_IRQn    = ((0 << 8) + 6),
    PFR_STS_IRQn    = ((1 << 8) + 6),
    LED0_IRQn       = ((2 << 8) + 6),
    LED1_IRQn       = ((3 << 8) + 6),
    LED2_IRQn       = ((4 << 8) + 6),
    INT32K_RDY_IRQn = ((5 << 8) + 6),
    /* GIRQ15 */
    MBOX_IRQn           = ((0 << 8) + 7),
    EMI0_IRQn           = ((2 << 8) + 7),
    KBD_OBF_IRQn        = ((4 << 8) + 7),
    KBD_IBF_IRQn        = ((5 << 8) + 7),
    P80A_IRQn           = ((6 << 8) + 7),
    P80B_IRQn           = ((7 << 8) + 7),
    ACPI_PM1_CTL_IRQn   = ((8 << 8) + 7),
    ACPI_PM1_EN_IRQn    = ((9 << 8) + 7),
    ACPI_PM1_STS_IRQn   = ((10 << 8) + 7),
    ACPI_EC0_IBF_IRQn   = ((11 << 8) + 7),
    ACPI_EC0_OBF_IRQn   = ((12 << 8) + 7),
    ACPI_EC1_IBF_IRQn   = ((13 << 8) + 7),
    ACPI_EC1_OBF_IRQn   = ((14 << 8) + 7),
    ACPI_EC2_IBF_IRQn   = ((15 << 8) + 7),
    ACPI_EC2_OBF_IRQn   = ((16 << 8) + 7),
    ACPI_EC3_IBF_IRQn   = ((17 << 8) + 7),
    ACPI_EC3_OBF_IRQn   = ((18 << 8) + 7),
    /* GIRQ16 */
    LPC_WAKE_IRQn       = ((0 << 8) + 8),
    SMB0_WAKE_IRQn      = ((1 << 8) + 8),
    SMB1_WAKE_IRQn      = ((2 << 8) + 8),
    SMB2_WAKE_IRQn      = ((3 << 8) + 8),
    PS2D0_WAKE_IRQn     = ((4 << 8) + 8),
    PS2D1A_WAKE_IRQn    = ((5 << 8) + 8),
    PS2D1B_WAKE_IRQn    = ((6 << 8) + 8),
    KSC_WAKE_IRQn       = ((7 << 8) + 8),
    ICSP_WAKE_IRQn      = ((8 << 8) + 8),
    ESPI_WAKE_IRQn      = ((9 << 8) + 8),
    /* GIRQ17 */
    ADC_SGL_IRQn        = ((0 << 8) + 9),
    ADC_RPT_IRQn        = ((1 << 8) + 9),
    PS2D0_ACT_IRQn      = ((4 << 8) + 9),
    PS2D1_ACT_IRQn      = ((5 << 8) + 9),
    KSC_IRQn            = ((6 << 8) + 9),
    UART0_IRQn          = ((7 << 8) + 9),
    PECI_HOST_IRQn      = ((8 << 8) + 9),
    TACH0_IRQn          = ((9 << 8) + 9),
    TACH1_IRQn          = ((10 << 8) + 9),
    /* GIRQ18 */
    QMSPI0_IRQn         = ((0 << 8) + 10),
    /* GIRQ19 */
    ESPI_PC_IRQn        = ((0 << 8) + 11),
    ESPI_BM1_IRQn       = ((1 << 8) + 11),
    ESPI_BM2_IRQn       = ((2 << 8) + 11),
    ESPI_LTR_IRQn       = ((3 << 8) + 11),
    ESPI_OOB_UP_IRQn    = ((4 << 8) + 11),
    ESPI_OOB_DN_IRQn    = ((5 << 8) + 11),
    ESPI_FLASH_IRQn     = ((6 << 8) + 11),
    ESPI_RESET_IRQn     = ((7 << 8) + 11),
    SUBDEC_IRQn         = ((8 << 8) + 11),
    /* GIRQ20 */
    BC0_BUSY_IRQn       = ((0 << 8) + 12),
    BC0_ERR_IRQn        = ((1 << 8) + 12),
    BC0_EV_IRQn         = ((2 << 8) + 12),
    BC1_BUSY_IRQn       = ((3 << 8) + 12),
    BC1_ERR_IRQn        = ((4 << 8) + 12),
    BC1_EV_IRQn         = ((5 << 8) + 12),
    /* GIRQ21 */
    STAP_OBF_IRQn       = ((0 << 8) + 13),
    STAP_IBF_IRQn       = ((1 << 8) + 13),
    STAP_WAKE_IRQn      = ((2 << 8) + 13),
    /* GIRQ22 */
    LPC_WAKE_ONLY_IRQn      = ((0 << 8) + 14),
    SMB0_WAKE_ONLY_IRQn     = ((1 << 8) + 14),
    SMB1_WAKE_ONLY_IRQn     = ((2 << 8) + 14),
    SMB2_WAKE_ONLY_IRQn     = ((3 << 8) + 14),
    PS2D0_WAKE_ONLY_IRQn    = ((4 << 8) + 14),
    PS2D1A_WAKE_ONLY_IRQn   = ((5 << 8) + 14),
    PS2D1B_WAKE_ONLY_IRQn   = ((6 << 8) + 14),
    KSC_WAKE_ONLY_IRQn      = ((7 << 8) + 14),
    ICSP_WAKE_ONLY_IRQn     = ((8 << 8) + 14),
    ESPI_WAKE_ONLY_IRQn     = ((9 << 8) + 14),
    /* GIRQ23 */
    TMR0_IRQn           = ((0 << 8) + 15),
    TMR1_IRQn           = ((1 << 8) + 15),
    TMR2_IRQn           = ((2 << 8) + 15),
    TMR3_IRQn           = ((3 << 8) + 15),
    RTOS_TMR_IRQn       = ((4 << 8) + 15),
    HIBTMR_IRQn         = ((5 << 8) + 15),
    WEEK_ALARM_IRQn     = ((6 << 8) + 15),
    SUB_WEEK_ALARM_IRQn = ((7 << 8) + 15),
    ONE_SEC_WEEK_IRQn   = ((8 << 8) + 15),
    SUB_SEC_WEEK_IRQn   = ((9 << 8) + 15),
    SYSPWR_PRES_IRQn    = ((10 << 8) + 15),
    VCI_OVRD_IN_IRQn    = ((11 << 8) + 15),
    VCI_IN0_IRQn        = ((12 << 8) + 15),
    VCI_IN1_IRQn        = ((13 << 8) + 15),
    /* GIRQ24 */
    M14K_COUNTER_IRQn   = ((0 << 8) + 16),
    M14K_SOFT_IRQ0_IRQn = ((1 << 8) + 16),
    M14K_SOFT_IRQ1_IRQn = ((2 << 8) + 16),
    /* GIRQ25 */
    ESPI_MSVW00_S0_IRQn = ((0 << 8) + 17),
    ESPI_MSVW00_S1_IRQn = ((1 << 8) + 17),
    ESPI_MSVW00_S2_IRQn = ((2 << 8) + 17),
    ESPI_MSVW00_S3_IRQn = ((3 << 8) + 17),
    ESPI_MSVW01_S0_IRQn = ((4 << 8) + 17),
    ESPI_MSVW01_S1_IRQn = ((5 << 8) + 17),
    ESPI_MSVW01_S2_IRQn = ((6 << 8) + 17),
    ESPI_MSVW01_S3_IRQn = ((7 << 8) + 17),
    ESPI_MSVW02_S0_IRQn = ((8 << 8) + 17),
    ESPI_MSVW02_S1_IRQn = ((9 << 8) + 17),
    ESPI_MSVW02_S2_IRQn = ((10 << 8) + 17),
    ESPI_MSVW02_S3_IRQn = ((11 << 8) + 17),
    ESPI_MSVW03_S0_IRQn = ((12 << 8) + 17),
    ESPI_MSVW03_S1_IRQn = ((13 << 8) + 17),
    ESPI_MSVW03_S2_IRQn = ((14 << 8) + 17),
    ESPI_MSVW03_S3_IRQn = ((15 << 8) + 17),
    ESPI_MSVW04_S0_IRQn = ((16 << 8) + 17),
    ESPI_MSVW04_S1_IRQn = ((17 << 8) + 17),
    ESPI_MSVW04_S2_IRQn = ((18 << 8) + 17),
    ESPI_MSVW04_S3_IRQn = ((19 << 8) + 17),
    ESPI_MSVW05_S0_IRQn = ((20 << 8) + 17),
    ESPI_MSVW05_S1_IRQn = ((21 << 8) + 17),
    ESPI_MSVW05_S2_IRQn = ((22 << 8) + 17),
    ESPI_MSVW05_S3_IRQn = ((23 << 8) + 17),
    ESPI_MSVW06_S0_IRQn = ((24 << 8) + 17),
    ESPI_MSVW06_S1_IRQn = ((25 << 8) + 17),
    ESPI_MSVW06_S2_IRQn = ((26 << 8) + 17),
    ESPI_MSVW06_S3_IRQn = ((27 << 8) + 17),
    /* GIRQ26 */
    ESPI_MSVW07_S0_IRQn = ((0 << 8) + 18),
    ESPI_MSVW07_S1_IRQn = ((1 << 8) + 18),
    ESPI_MSVW07_S2_IRQn = ((2 << 8) + 18),
    ESPI_MSVW07_S3_IRQn = ((3 << 8) + 18),
    ESPI_MSVW08_S0_IRQn = ((4 << 8) + 18),
    ESPI_MSVW08_S1_IRQn = ((5 << 8) + 18),
    ESPI_MSVW08_S2_IRQn = ((6 << 8) + 18),
    ESPI_MSVW08_S3_IRQn = ((7 << 8) + 18),
    ESPI_MSVW09_S0_IRQn = ((8 << 8) + 18),
    ESPI_MSVW09_S1_IRQn = ((9 << 8) + 18),
    ESPI_MSVW09_S2_IRQn = ((10 << 8) + 18),
    ESPI_MSVW09_S3_IRQn = ((11 << 8) + 18),
    /* End */
} IRQn_Type;

/*
 * GIRQn ISR prototypes used to export handlers.
 * NOTE: We need nomips16 on both prototype and
 * function definition. Do not add the other
 * attributes from the function definition to
 * these prototypes.
 */
void __attribute__((nomips16)) girq08_isr(void);
void __attribute__((nomips16)) girq09_isr(void);
void __attribute__((nomips16)) girq10_isr(void);
void __attribute__((nomips16)) girq11_isr(void);
void __attribute__((nomips16)) girq12_isr(void);
void __attribute__((nomips16)) girq13_isr(void);
void __attribute__((nomips16)) girq14_isr(void);
void __attribute__((nomips16)) girq15_isr(void);
void __attribute__((nomips16)) girq16_isr(void);
void __attribute__((nomips16)) girq17_isr(void);
void __attribute__((nomips16)) girq18_isr(void);
void __attribute__((nomips16)) girq19_isr(void);
void __attribute__((nomips16)) girq20_isr(void);
void __attribute__((nomips16)) girq21_isr(void);
void __attribute__((nomips16)) girq22_isr(void);
void __attribute__((nomips16)) girq23_isr(void);
void __attribute__((nomips16)) girq24_isr(void);
void __attribute__((nomips16)) girq25_isr(void);
void __attribute__((nomips16)) girq26_isr(void);


extern const JTVIC_CFG dflt_ih_table[];

#ifdef __cplusplus
}
#endif

#endif /* _MEC14XX_GIRQS_H */

/**   @}
 */
