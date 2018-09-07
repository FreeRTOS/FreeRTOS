/*
 **********************************************************************************
* © 2013 Microchip Technology Inc. and its subsidiaries.
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
 **********************************************************************************
 *  ARM_REG.h
 *      This is the header to define Cortex-M3 system control & status registers
 **********************************************************************************
 *  SMSC version control information (Perforce):
 *
 *  FILE:     $File: //depot_pcs/FWEng/projects/MEC2016/Playground/pramans/160623_FreeRTOS_Microchip_MEC170x/Demo/CORTEX_MPU_MEC1701_Keil_GCC/peripheral_library/ARM_REG.h $
 *  REVISION: $Revision: #1 $
 *  DATETIME: $DateTime: 2016/09/22 08:03:49 $
 *  AUTHOR:   $Author: pramans $
 *
 *  Revision history (latest first):
 *      #xx
 ***********************************************************************************
 */

/******************************************************************************/
/** @defgroup ARM_REG ARM_REG
 *  @{
 */

/** @file ARM_REG.h
* \brief ARM Cortex-M3 registers header file
* \author KBCEC Team
* 
* This file contains ARM Cortex-M3 system control & status registers.
******************************************************************************/   
#ifndef ARM_REG_H_
#define ARM_REG_H_

#define REG8(x)  (*((volatile unsigned char  *)(x)))
#define REG16(x) (*((volatile unsigned short *)(x)))
#define REG32(x) (*((volatile unsigned long  *)(x)))

/* NVIC Registers */
#define NVIC_INT_TYPE           REG32(0xE000E004)
#define NVIC_AUX_ACTLR          REG32(0xE000E008)
    #define WR_BUF_DISABLE      (1 << 1)
#define NVIC_ST_CTRL            REG32(0xE000E010)
    #define ST_ENABLE           (1 << 0)
    #define ST_TICKINT          (1 << 1)
    #define ST_CLKSOURCE        (1 << 2)
    #define ST_COUNTFLAG        (1 << 3)
#define NVIC_ST_RELOAD          REG32(0xE000E014)
#define NVIC_ST_CURRENT         REG32(0xE000E018)
#define NVIC_ST_CALIB           REG32(0xE000E01C)
#define NVIC_ENABLE0            REG32(0xE000E100)
#define NVIC_ENABLE1            REG32(0xE000E104)
#define NVIC_ENABLE2            REG32(0xE000E108)
#define NVIC_ENABLE3            REG32(0xE000E10C)
#define NVIC_ENABLE4            REG32(0xE000E110)
#define NVIC_ENABLE5            REG32(0xE000E114)
#define NVIC_ENABLE6            REG32(0xE000E118)
#define NVIC_ENABLE7            REG32(0xE000E11C)
#define NVIC_DISABLE0           REG32(0xE000E180)
#define NVIC_DISABLE1           REG32(0xE000E184)
#define NVIC_DISABLE2           REG32(0xE000E188)
#define NVIC_DISABLE3           REG32(0xE000E18C)
#define NVIC_DISABLE4           REG32(0xE000E190)
#define NVIC_DISABLE5           REG32(0xE000E194)
#define NVIC_DISABLE6           REG32(0xE000E198)
#define NVIC_DISABLE7           REG32(0xE000E19C)
#define NVIC_PEND0              REG32(0xE000E200)
#define NVIC_PEND1              REG32(0xE000E204)
#define NVIC_PEND2              REG32(0xE000E208)
#define NVIC_PEND3              REG32(0xE000E20C)
#define NVIC_PEND4              REG32(0xE000E210)
#define NVIC_PEND5              REG32(0xE000E214)
#define NVIC_PEND6              REG32(0xE000E218)
#define NVIC_PEND7              REG32(0xE000E21C)
#define NVIC_UNPEND0            REG32(0xE000E280)
#define NVIC_UNPEND1            REG32(0xE000E284)
#define NVIC_UNPEND2            REG32(0xE000E288)
#define NVIC_UNPEND3            REG32(0xE000E28C)
#define NVIC_UNPEND4            REG32(0xE000E290)
#define NVIC_UNPEND5            REG32(0xE000E294)
#define NVIC_UNPEND6            REG32(0xE000E298)
#define NVIC_UNPEND7            REG32(0xE000E29C)
#define NVIC_ACTIVE0            REG32(0xE000E300)
#define NVIC_ACTIVE1            REG32(0xE000E304)
#define NVIC_ACTIVE2            REG32(0xE000E308)
#define NVIC_ACTIVE3            REG32(0xE000E30C)
#define NVIC_ACTIVE4            REG32(0xE000E310)
#define NVIC_ACTIVE5            REG32(0xE000E314)
#define NVIC_ACTIVE6            REG32(0xE000E318)
#define NVIC_ACTIVE7            REG32(0xE000E31C)
#define NVIC_PRI0               REG32(0xE000E400)
#define NVIC_PRI1               REG32(0xE000E404)
#define NVIC_PRI2               REG32(0xE000E408)
#define NVIC_PRI3               REG32(0xE000E40C)
#define NVIC_PRI4               REG32(0xE000E410)
#define NVIC_PRI5               REG32(0xE000E414)
#define NVIC_PRI6               REG32(0xE000E418)
#define NVIC_PRI7               REG32(0xE000E41C)
#define NVIC_PRI8               REG32(0xE000E420)
#define NVIC_PRI9               REG32(0xE000E424)
#define NVIC_PRI10              REG32(0xE000E428)
#define NVIC_PRI11              REG32(0xE000E42C)
#define NVIC_PRI12              REG32(0xE000E430)
#define NVIC_PRI13              REG32(0xE000E434)
#define NVIC_PRI14              REG32(0xE000E438)
#define NVIC_PRI15              REG32(0xE000E43C)
#define NVIC_PRI16              REG32(0xE000E440)
#define NVIC_PRI17              REG32(0xE000E444)
#define NVIC_PRI18              REG32(0xE000E448)
#define NVIC_PRI19              REG32(0xE000E44C)
#define NVIC_PRI20              REG32(0xE000E450)
#define NVIC_PRI21              REG32(0xE000E454)
#define NVIC_PRI22              REG32(0xE000E458)
#define NVIC_PRI23              REG32(0xE000E45C)
#define NVIC_PRI24              REG32(0xE000E460)
#define NVIC_PRI25              REG32(0xE000E464)
#define NVIC_PRI26              REG32(0xE000E468)
#define NVIC_PRI27              REG32(0xE000E46C)
#define NVIC_PRI28              REG32(0xE000E470)
#define NVIC_PRI29              REG32(0xE000E474)
#define NVIC_PRI30              REG32(0xE000E478)
#define NVIC_PRI31              REG32(0xE000E47C)
#define NVIC_PRI32              REG32(0xE000E480)
#define NVIC_PRI33              REG32(0xE000E484)
#define NVIC_PRI34              REG32(0xE000E488)
#define NVIC_PRI35              REG32(0xE000E48C)
#define NVIC_PRI36              REG32(0xE000E490)
#define NVIC_PRI37              REG32(0xE000E494)
#define NVIC_PRI38              REG32(0xE000E498)
#define NVIC_PRI39              REG32(0xE000E49C)
#define NVIC_PRI40              REG32(0xE000E4A0)
#define NVIC_PRI41              REG32(0xE000E4A4)
#define NVIC_PRI42              REG32(0xE000E4A8)
#define NVIC_PRI43              REG32(0xE000E4AC)
#define NVIC_PRI44              REG32(0xE000E4B0)
#define NVIC_PRI45              REG32(0xE000E4B4)
#define NVIC_PRI46              REG32(0xE000E4B8)
#define NVIC_PRI47              REG32(0xE000E4BC)
#define NVIC_PRI48              REG32(0xE000E4C0)
#define NVIC_PRI49              REG32(0xE000E4C4)
#define NVIC_PRI50              REG32(0xE000E4C8)
#define NVIC_PRI51              REG32(0xE000E4CC)
#define NVIC_PRI52              REG32(0xE000E4D0)
#define NVIC_PRI53              REG32(0xE000E4D4)
#define NVIC_PRI54              REG32(0xE000E4D8)
#define NVIC_PRI55              REG32(0xE000E4DC)
#define NVIC_PRI56              REG32(0xE000E4E0)
#define NVIC_PRI57              REG32(0xE000E4E4)
#define NVIC_PRI58              REG32(0xE000E4E8)
#define NVIC_PRI59              REG32(0xE000E4EC)
#define NVIC_CPUID              REG32(0xE000ED00)
#define NVIC_INT_CTRL           REG32(0xE000ED04)
#define NVIC_VECT_TABLE         REG32(0xE000ED08)
#define NVIC_AP_INT_RST         REG32(0xE000ED0C)
#define NVIC_SYS_CTRL           REG32(0xE000ED10)
#define NVIC_CFG_CTRL           REG32(0xE000ED14)
#define NVIC_SYS_H_PRI1         REG32(0xE000ED18)
#define NVIC_SYS_H_PRI2         REG32(0xE000ED1C)
#define NVIC_SYS_H_PRI3         REG32(0xE000ED20)
#define NVIC_SYS_H_CTRL         REG32(0xE000ED24)
#define NVIC_FAULT_STA          REG32(0xE000ED28)
#define NVIC_HARD_F_STA         REG32(0xE000ED2C)
#define NVIC_DBG_F_STA          REG32(0xE000ED30)
#define NVIC_MM_F_ADR           REG32(0xE000ED34)
#define NVIC_BUS_F_ADR          REG32(0xE000ED38)
#define NVIC_SW_TRIG            REG32(0xE000EF00)

/* MPU Registers */
#define MPU_TYPE                REG32(0xE000ED90)
#define MPU_CTRL                REG32(0xE000ED94)
#define MPU_RG_NUM              REG32(0xE000ED98)
#define MPU_RG_ADDR             REG32(0xE000ED9C)
#define MPU_RG_AT_SZ            REG32(0xE000EDA0)


#endif /* #ifndef ARM_REG_H_ */

/**   @}
 */
