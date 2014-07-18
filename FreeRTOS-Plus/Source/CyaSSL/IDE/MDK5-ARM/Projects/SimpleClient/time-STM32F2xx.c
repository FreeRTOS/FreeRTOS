/* time-STM32F2.c
 *
 * Copyright (C) 2006-2013 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */
 
#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include "time.h"

#define PERIPH_BASE           ((uint32_t)0x40000000) 
/*-----------------------------------------------------------------------------
 *        initialize RTC 
 *----------------------------------------------------------------------------*/
#include "stm32f2xx.h"

#define assert_param(a)

#if 0
#define RTC_RSF_MASK         ((uint32_t)0xFFFFFF5F)
#define SYNCHRO_TIMEOUT      ((uint32_t) 0x00008000)
#define Bcd2ToByte(v) \
   ((((uint8_t)(v & (uint8_t)0xF0) >> (uint8_t)0x4) * 10) + (v & (uint8_t)0x0F))
#define RTC_TR_RESERVED_MASK ((uint32_t)0x007F7F7F)
#define RTC_TR_MNT           ((uint32_t)0x00007000)
#define RTC_TR_MNU           ((uint32_t)0x00000F00)

#define PWR_OFFSET           (PWR_BASE - PERIPH_BASE)
#define CR_OFFSET            (PWR_OFFSET + 0x00)
#define DBP_BitNumber        0x08
#define CR_DBP_BB     (PERIPH_BB_BASE + (CR_OFFSET * 32) + (DBP_BitNumber * 4))
#define RTC_INIT_MASK        ((uint32_t)0xFFFFFFFF)  
#define INITMODE_TIMEOUT     ((uint32_t) 0x00010000)
#endif

/*-----------------------------------------------------------------------------
 *        initialize TIM
 *----------------------------------------------------------------------------*/
#define RCC_APB1Periph_TIM2              ((uint32_t)0x00000001)

void init_time(void)
{
      uint16_t tmpcr1 = 0;

    ((uint32_t *)RCC)[0x10] |= RCC_APB1Periph_TIM2 ;

    tmpcr1 = TIM2->CR1 ;
    tmpcr1 &=   (uint16_t) (~(((uint16_t)0x0010) | ((uint16_t)0x0060) )); 
                                     /* CR1 &= ~(TIM_CR1_DIR | TIM_CR1_CMS) */
    tmpcr1 |= (uint16_t)0x0000  ;    /* CR1 |= TIM_CounterMode_Up */
    TIM2->CR1=  tmpcr1 ;

    TIM2->ARR = 0xffffffff ;         /* ARR= TIM_Period */
    TIM2->PSC = 60 ;                 /* PSC = TIM_Prescaler */
    TIM2->EGR = ((uint16_t)0x0001) ; /* EGR = TIM_PSCReloadMode_Immediate */      

    *(uint16_t *)(PERIPH_BASE+0x0) |=((uint16_t)0x0001) ; 
                                     /* TIM_Cmd(TIM2, ENABLE) ; */
}

double current_time() 
{
      return ((double)TIM2->CNT/1000000.0) ;
}

