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

/** @file girqs.c
 *MEC14xx JTVIC default configuration table
 */
/** @defgroup MEC140x ISR
 *  @{
 */

#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_girqm.h"
#include "MEC14xx/mec14xx_girqs.h"
#include "MEC14xx/mec14xx_gpio.h"
#include "MEC14xx/mec14xx_trace_func.h"


/*
 * Interrupt Service Routine prototypes for each GIRQn
*/


/*
 * Table for initializing MEC14xx JTVIC.
 * Each GIRQn handler's address must be programmed into
 * respective JTVIC register.
 */
const JTVIC_CFG dflt_ih_table[MEC14xx_NUM_JTVIC_INTS] = {
    {
    		(uint32_t)girq08_isr,
			{
					(GIRQ08_PRI_A),
					(GIRQ08_PRI_B),
					(GIRQ08_PRI_C),
					(GIRQ08_PRI_D)
			}
    },
    {
    		(uint32_t)girq09_isr,
			{
					(GIRQ09_PRI_A),
					(GIRQ09_PRI_B),
					(GIRQ09_PRI_C),
					(GIRQ09_PRI_D)
			}
    },
    {
    		(uint32_t)girq10_isr,
			{
					(GIRQ10_PRI_A),
					(GIRQ10_PRI_B),
					(GIRQ10_PRI_C),
					(GIRQ10_PRI_D)
			}
    },
    {
    		(uint32_t)girq11_isr,
    		{
    				GIRQ11_PRI_A,
					GIRQ11_PRI_B,
					GIRQ11_PRI_C,
					GIRQ11_PRI_D
    		}
    },
    {
    		(uint32_t)girq12_isr,
			{
					GIRQ12_PRI_A,
					GIRQ12_PRI_B,
					GIRQ12_PRI_C,
					GIRQ12_PRI_D
			}
    },
    {
    		(uint32_t)girq13_isr,
			{
					GIRQ13_PRI_A,
					GIRQ13_PRI_B,
					GIRQ13_PRI_C,
					GIRQ13_PRI_D
			}
    },
    {
    		(uint32_t)girq14_isr,
			{
					GIRQ14_PRI_A,
					GIRQ14_PRI_B,
					GIRQ14_PRI_C,
					GIRQ14_PRI_D
			}
    },
    {
    		(uint32_t)girq15_isr,
			{
					GIRQ15_PRI_A,
					GIRQ15_PRI_B,
					GIRQ15_PRI_C,
					GIRQ15_PRI_D
			}
    },
    {
    		(uint32_t)girq16_isr,
			{
					GIRQ16_PRI_A,
					GIRQ16_PRI_B,
					GIRQ16_PRI_C,
					GIRQ16_PRI_D
			}
    },
    {
    		(uint32_t)girq17_isr,
			{
					GIRQ17_PRI_A,
					GIRQ17_PRI_B,
					GIRQ17_PRI_C,
					GIRQ17_PRI_D
			}
    },
    {
    		(uint32_t)girq18_isr,
			{
					GIRQ18_PRI_A,
					GIRQ18_PRI_B,
					GIRQ18_PRI_C,
					GIRQ18_PRI_D
			}
    },
    {
    		(uint32_t)girq19_isr,
			{
					GIRQ19_PRI_A,
					GIRQ19_PRI_B,
					GIRQ19_PRI_C,
					GIRQ19_PRI_D
			}
    },
    {
    		(uint32_t)girq20_isr,
			{
					GIRQ20_PRI_A,
					GIRQ20_PRI_B,
					GIRQ20_PRI_C,
					GIRQ20_PRI_D
			}
    },
    {
    		(uint32_t)girq21_isr,
			{
					GIRQ21_PRI_A,
					GIRQ21_PRI_B,
					GIRQ21_PRI_C,
					GIRQ21_PRI_D
			}
    },
    {
    		(uint32_t)girq22_isr,
			{
					GIRQ22_PRI_A,
					GIRQ22_PRI_B,
					GIRQ22_PRI_C,
					GIRQ22_PRI_D
			}
    },
    {
    		(uint32_t)girq23_isr,
			{
					GIRQ23_PRI_A,
					GIRQ23_PRI_B,
					GIRQ23_PRI_C,
					GIRQ23_PRI_D
			}
    },
    {
    		(uint32_t)girq24_isr,
			{
					GIRQ24_PRI_A,
					GIRQ24_PRI_B,
					GIRQ24_PRI_C,
					GIRQ24_PRI_D
			}
    },
    {
    		(uint32_t)girq25_isr,
			{
					GIRQ25_PRI_A,
					GIRQ25_PRI_B,
					GIRQ25_PRI_C,
					GIRQ25_PRI_D
			}
    },
    {
    		(uint32_t)girq26_isr,
			{
					GIRQ26_PRI_A,
					GIRQ26_PRI_B,
					GIRQ26_PRI_C,
					GIRQ26_PRI_D
			}
    }
};


/* end girqs.c */
/**   @}
 */

