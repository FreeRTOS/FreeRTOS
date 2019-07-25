/**************************************************************************//**
 * @file     partition_ARMCM33.h
 * @brief    CMSIS-CORE Initial Setup for Secure / Non-Secure Zones for ARMCM33
 * @version  V5.0.1
 * @date     07. December 2016
 ******************************************************************************/
/*
 * Copyright (c) 2009-2016 ARM Limited. All rights reserved.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the License); you may
 * not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an AS IS BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef PARTITION_ARMCM33_H
#define PARTITION_ARMCM33_H

/*
//-------- <<< Use Configuration Wizard in Context Menu >>> -----------------
*/

/*
// <e>Initialize Security Attribution Unit (SAU) CTRL register
*/
#define SAU_INIT_CTRL          1

/*
//   <q> Enable SAU
//   <i> Value for SAU->CTRL register bit ENABLE
*/
#define SAU_INIT_CTRL_ENABLE   1

/*
//   <o> When SAU is disabled
//     <0=> All Memory is Secure
//     <1=> All Memory is Non-Secure
//   <i> Value for SAU->CTRL register bit ALLNS
//   <i> When all Memory is Non-Secure (ALLNS is 1), IDAU can override memory map configuration.
*/
#define SAU_INIT_CTRL_ALLNS  0

/*
// </e>
*/

/*
// <h>Initialize Security Attribution Unit (SAU) Address Regions
// <i>SAU configuration specifies regions to be one of:
// <i> - Secure and Non-Secure Callable
// <i> - Non-Secure
// <i>Note: All memory regions not configured by SAU are Secure
*/
#define SAU_REGIONS_MAX   8                 /* Max. number of SAU regions */

/*
//   <e>Initialize SAU Region 0
//   <i> Setup SAU Region 0 memory attributes
*/
#define SAU_INIT_REGION0    1

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START0     0x00000000      /* start address of SAU region 0 */

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END0       0x001FFFFF      /* end address of SAU region 0 */

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC0       1
/*
//   </e>
*/

/*
//   <e>Initialize SAU Region 1
//   <i> Setup SAU Region 1 memory attributes
*/
#define SAU_INIT_REGION1    1

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START1     0x00200000

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END1       0x003FFFFF

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC1       0
/*
//   </e>
*/

/*
//   <e>Initialize SAU Region 2
//   <i> Setup SAU Region 2 memory attributes
*/
#define SAU_INIT_REGION2    1

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START2     0x20200000

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END2       0x203FFFFF

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC2       0
/*
//   </e>
*/

/*
//   <e>Initialize SAU Region 3
//   <i> Setup SAU Region 3 memory attributes
*/
#define SAU_INIT_REGION3    1

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START3     0x40000000

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END3       0x40040000

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC3       0
/*
//   </e>
*/

/*
//   <e>Initialize SAU Region 4
//   <i> Setup SAU Region 4 memory attributes
*/
#define SAU_INIT_REGION4    0

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START4     0x00000000      /* start address of SAU region 4 */

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END4       0x00000000      /* end address of SAU region 4 */

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC4       0
/*
//   </e>
*/

/*
//   <e>Initialize SAU Region 5
//   <i> Setup SAU Region 5 memory attributes
*/
#define SAU_INIT_REGION5    0

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START5     0x00000000

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END5       0x00000000

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC5       0
/*
//   </e>
*/

/*
//   <e>Initialize SAU Region 6
//   <i> Setup SAU Region 6 memory attributes
*/
#define SAU_INIT_REGION6    0

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START6     0x00000000

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END6       0x00000000

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC6       0
/*
//   </e>
*/

/*
//   <e>Initialize SAU Region 7
//   <i> Setup SAU Region 7 memory attributes
*/
#define SAU_INIT_REGION7    0

/*
//     <o>Start Address <0-0xFFFFFFE0>
*/
#define SAU_INIT_START7     0x00000000

/*
//     <o>End Address <0x1F-0xFFFFFFFF>
*/
#define SAU_INIT_END7       0x00000000

/*
//     <o>Region is
//         <0=>Non-Secure
//         <1=>Secure, Non-Secure Callable
*/
#define SAU_INIT_NSC7       0
/*
//   </e>
*/

/*
// </h>
*/

/*
// <e>Setup behaviour of Sleep and Exception Handling
*/
#define SCB_CSR_AIRCR_INIT  1

/*
//   <o> Deep Sleep can be enabled by
//     <0=>Secure and Non-Secure state
//     <1=>Secure state only
//   <i> Value for SCB->CSR register bit DEEPSLEEPS
*/
#define SCB_CSR_DEEPSLEEPS_VAL  1

/*
//   <o>System reset request accessible from
//     <0=> Secure and Non-Secure state
//     <1=> Secure state only
//   <i> Value for SCB->AIRCR register bit SYSRESETREQS
*/
#define SCB_AIRCR_SYSRESETREQS_VAL  1

/*
//   <o>Priority of Non-Secure exceptions is
//     <0=> Not altered
//     <1=> Lowered to 0x80-0xFF
//   <i> Value for SCB->AIRCR register bit PRIS
*/
#define SCB_AIRCR_PRIS_VAL      1

/*
//   <o>BusFault, HardFault, and NMI target
//     <0=> Secure state
//     <1=> Non-Secure state
//   <i> Value for SCB->AIRCR register bit BFHFNMINS
*/
#define SCB_AIRCR_BFHFNMINS_VAL 0

/*
// </e>
*/

/*
// <e>Setup behaviour of Floating Point Unit
*/
#define TZ_FPU_NS_USAGE 1

/*
// <o>Floating Point Unit usage
//     <0=> Secure state only
//     <3=> Secure and Non-Secure state
//   <i> Value for SCB->NSACR register bits CP10, CP11
*/
#define SCB_NSACR_CP10_11_VAL       3

/*
// <o>Treat floating-point registers as Secure
//     <0=> Disabled
//     <1=> Enabled
//   <i> Value for FPU->FPCCR register bit TS
*/
#define FPU_FPCCR_TS_VAL            0

/*
// <o>Clear on return (CLRONRET) accessibility
//     <0=> Secure and Non-Secure state
//     <1=> Secure state only
//   <i> Value for FPU->FPCCR register bit CLRONRETS
*/
#define FPU_FPCCR_CLRONRETS_VAL     0

/*
// <o>Clear floating-point caller saved registers on exception return
//     <0=> Disabled
//     <1=> Enabled
//   <i> Value for FPU->FPCCR register bit CLRONRET
*/
#define FPU_FPCCR_CLRONRET_VAL      1

/*
// </e>
*/

/*
// <h>Setup Interrupt Target
*/

/*
//   <e>Initialize ITNS 0 (Interrupts 0..31)
*/
#define NVIC_INIT_ITNS0    1

/*
// Interrupts 0..31
//   <o.0>  Interrupt 0   <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 1   <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 2   <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 3   <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 4   <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 5   <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 6   <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 7   <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 8   <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 9   <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 10  <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 11  <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 12  <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 13  <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 14  <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 15  <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 16  <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 17  <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 18  <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 19  <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 20  <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 21  <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 22  <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 23  <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 24  <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 25  <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 26  <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 27  <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 28  <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 29  <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 30  <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 31  <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS0_VAL      0x0000122B

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 1 (Interrupts 32..63)
*/
#define NVIC_INIT_ITNS1    1

/*
// Interrupts 32..63
//   <o.0>  Interrupt 32  <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 33  <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 34  <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 35  <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 36  <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 37  <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 38  <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 39  <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 40  <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 41  <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 42  <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 43  <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 44  <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 45  <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 46  <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 47  <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 48  <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 49  <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 50  <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 51  <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 52  <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 53  <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 54  <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 55  <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 56  <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 57  <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 58  <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 59  <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 60  <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 61  <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 62  <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 63  <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS1_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 2 (Interrupts 64..95)
*/
#define NVIC_INIT_ITNS2    0

/*
// Interrupts 64..95
//   <o.0>  Interrupt 64  <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 65  <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 66  <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 67  <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 68  <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 69  <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 70  <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 71  <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 72  <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 73  <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 74  <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 75  <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 76  <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 77  <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 78  <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 79  <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 80  <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 81  <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 82  <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 83  <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 84  <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 85  <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 86  <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 87  <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 88  <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 89  <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 90  <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 91  <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 92  <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 93  <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 94  <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 95  <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS2_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 3 (Interrupts 96..127)
*/
#define NVIC_INIT_ITNS3    0

/*
// Interrupts 96..127
//   <o.0>  Interrupt 96  <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 97  <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 98  <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 99  <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 100 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 101 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 102 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 103 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 104 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 105 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 106 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 107 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 108 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 109 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 110 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 111 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 112 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 113 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 114 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 115 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 116 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 117 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 118 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 119 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 120 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 121 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 122 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 123 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 124 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 125 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 126 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 127 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS3_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 4 (Interrupts 128..159)
*/
#define NVIC_INIT_ITNS4    0

/*
// Interrupts 128..159
//   <o.0>  Interrupt 128 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 129 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 130 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 131 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 132 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 133 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 134 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 135 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 136 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 137 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 138 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 139 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 140 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 141 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 142 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 143 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 144 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 145 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 146 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 147 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 148 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 149 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 150 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 151 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 152 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 153 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 154 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 155 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 156 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 157 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 158 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 159 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS4_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 5 (Interrupts 160..191)
*/
#define NVIC_INIT_ITNS5    0

/*
// Interrupts 160..191
//   <o.0>  Interrupt 160 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 161 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 162 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 163 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 164 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 165 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 166 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 167 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 168 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 169 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 170 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 171 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 172 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 173 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 174 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 175 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 176 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 177 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 178 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 179 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 180 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 181 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 182 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 183 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 184 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 185 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 186 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 187 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 188 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 189 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 190 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 191 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS5_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 6 (Interrupts 192..223)
*/
#define NVIC_INIT_ITNS6    0

/*
// Interrupts 192..223
//   <o.0>  Interrupt 192 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 193 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 194 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 195 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 196 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 197 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 198 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 199 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 200 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 201 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 202 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 203 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 204 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 205 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 206 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 207 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 208 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 209 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 210 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 211 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 212 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 213 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 214 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 215 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 216 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 217 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 218 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 219 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 220 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 221 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 222 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 223 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS6_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 7 (Interrupts 224..255)
*/
#define NVIC_INIT_ITNS7    0

/*
// Interrupts 224..255
//   <o.0>  Interrupt 224 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 225 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 226 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 227 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 228 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 229 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 230 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 231 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 232 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 233 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 234 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 235 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 236 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 237 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 238 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 239 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 240 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 241 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 242 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 243 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 244 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 245 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 246 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 247 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 248 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 249 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 250 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 251 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 252 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 253 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 254 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 255 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS7_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 8 (Interrupts 256..287)
*/
#define NVIC_INIT_ITNS8    0

/*
// Interrupts 0..31
//   <o.0>  Interrupt 256 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 257 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 258 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 259 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 260 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 261 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 262 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 263 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 264 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 265 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 266 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 267 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 268 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 269 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 270 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 271 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 272 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 273 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 274 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 275 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 276 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 277 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 278 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 279 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 280 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 281 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 282 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 283 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 284 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 285 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 286 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 287 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS8_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 9 (Interrupts 288..319)
*/
#define NVIC_INIT_ITNS9    0

/*
// Interrupts 32..63
//   <o.0>  Interrupt 288 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 289 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 290 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 291 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 292 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 293 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 294 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 295 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 296 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 297 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 298 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 299 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 300 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 301 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 302 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 303 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 304 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 305 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 306 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 307 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 308 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 309 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 310 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 311 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 312 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 313 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 314 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 315 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 316 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 317 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 318 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 319 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS9_VAL      0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 10 (Interrupts 320..351)
*/
#define NVIC_INIT_ITNS10   0

/*
// Interrupts 64..95
//   <o.0>  Interrupt 320 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 321 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 322 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 323 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 324 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 325 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 326 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 327 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 328 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 329 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 330 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 331 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 332 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 333 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 334 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 335 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 336 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 337 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 338 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 339 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 340 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 341 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 342 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 343 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 344 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 345 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 346 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 347 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 348 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 349 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 350 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 351 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS10_VAL     0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 11 (Interrupts 352..383)
*/
#define NVIC_INIT_ITNS11   0

/*
// Interrupts 96..127
//   <o.0>  Interrupt 352 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 353 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 354 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 355 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 356 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 357 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 358 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 359 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 360 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 361 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 362 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 363 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 364 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 365 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 366 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 367 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 368 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 369 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 370 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 371 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 372 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 373 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 374 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 375 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 376 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 377 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 378 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 379 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 380 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 381 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 382 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 383 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS11_VAL     0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 12 (Interrupts 384..415)
*/
#define NVIC_INIT_ITNS12   0

/*
// Interrupts 128..159
//   <o.0>  Interrupt 384 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 385 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 386 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 387 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 388 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 389 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 390 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 391 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 392 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 393 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 394 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 395 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 396 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 397 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 398 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 399 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 400 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 401 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 402 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 403 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 404 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 405 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 406 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 407 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 408 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 409 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 410 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 411 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 412 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 413 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 414 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 415 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS12_VAL     0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 13 (Interrupts 416..447)
*/
#define NVIC_INIT_ITNS13   0

/*
// Interrupts 160..191
//   <o.0>  Interrupt 416 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 417 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 418 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 419 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 420 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 421 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 422 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 423 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 424 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 425 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 426 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 427 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 428 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 429 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 430 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 431 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 432 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 433 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 434 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 435 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 436 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 437 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 438 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 439 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 440 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 441 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 442 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 443 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 444 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 445 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 446 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 447 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS13_VAL     0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 14 (Interrupts 448..479)
*/
#define NVIC_INIT_ITNS14   0

/*
// Interrupts 192..223
//   <o.0>  Interrupt 448 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 449 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 450 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 451 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 452 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 453 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 454 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 455 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 456 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 457 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 458 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 459 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 460 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 461 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 462 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 463 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 464 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 465 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 466 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 467 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 468 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 469 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 470 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 471 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 472 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 473 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 474 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 475 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 476 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 477 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 478 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 479 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS14_VAL     0x00000000

/*
//   </e>
*/

/*
//   <e>Initialize ITNS 15 (Interrupts 480..511)
*/
#define NVIC_INIT_ITNS15   0

/*
// Interrupts 224..255
//   <o.0>  Interrupt 480 <0=> Secure state <1=> Non-Secure state
//   <o.1>  Interrupt 481 <0=> Secure state <1=> Non-Secure state
//   <o.2>  Interrupt 482 <0=> Secure state <1=> Non-Secure state
//   <o.3>  Interrupt 483 <0=> Secure state <1=> Non-Secure state
//   <o.4>  Interrupt 484 <0=> Secure state <1=> Non-Secure state
//   <o.5>  Interrupt 485 <0=> Secure state <1=> Non-Secure state
//   <o.6>  Interrupt 486 <0=> Secure state <1=> Non-Secure state
//   <o.7>  Interrupt 487 <0=> Secure state <1=> Non-Secure state
//   <o.8>  Interrupt 488 <0=> Secure state <1=> Non-Secure state
//   <o.9>  Interrupt 489 <0=> Secure state <1=> Non-Secure state
//   <o.10> Interrupt 490 <0=> Secure state <1=> Non-Secure state
//   <o.11> Interrupt 491 <0=> Secure state <1=> Non-Secure state
//   <o.12> Interrupt 492 <0=> Secure state <1=> Non-Secure state
//   <o.13> Interrupt 493 <0=> Secure state <1=> Non-Secure state
//   <o.14> Interrupt 494 <0=> Secure state <1=> Non-Secure state
//   <o.15> Interrupt 495 <0=> Secure state <1=> Non-Secure state
//   <o.16> Interrupt 496 <0=> Secure state <1=> Non-Secure state
//   <o.17> Interrupt 497 <0=> Secure state <1=> Non-Secure state
//   <o.18> Interrupt 498 <0=> Secure state <1=> Non-Secure state
//   <o.19> Interrupt 499 <0=> Secure state <1=> Non-Secure state
//   <o.20> Interrupt 500 <0=> Secure state <1=> Non-Secure state
//   <o.21> Interrupt 501 <0=> Secure state <1=> Non-Secure state
//   <o.22> Interrupt 502 <0=> Secure state <1=> Non-Secure state
//   <o.23> Interrupt 503 <0=> Secure state <1=> Non-Secure state
//   <o.24> Interrupt 504 <0=> Secure state <1=> Non-Secure state
//   <o.25> Interrupt 505 <0=> Secure state <1=> Non-Secure state
//   <o.26> Interrupt 506 <0=> Secure state <1=> Non-Secure state
//   <o.27> Interrupt 507 <0=> Secure state <1=> Non-Secure state
//   <o.28> Interrupt 508 <0=> Secure state <1=> Non-Secure state
//   <o.29> Interrupt 509 <0=> Secure state <1=> Non-Secure state
//   <o.30> Interrupt 510 <0=> Secure state <1=> Non-Secure state
//   <o.31> Interrupt 511 <0=> Secure state <1=> Non-Secure state
*/
#define NVIC_INIT_ITNS15_VAL     0x00000000

/*
//   </e>
*/

/*
// </h>
*/



/*
    max 128 SAU regions.
    SAU regions are defined in partition.h
 */

#define SAU_INIT_REGION(n) \
    SAU->RNR  =  (n                                     & SAU_RNR_REGION_Msk); \
    SAU->RBAR =  (SAU_INIT_START##n                     & SAU_RBAR_BADDR_Msk); \
    SAU->RLAR =  (SAU_INIT_END##n                       & SAU_RLAR_LADDR_Msk) | \
                ((SAU_INIT_NSC##n << SAU_RLAR_NSC_Pos)  & SAU_RLAR_NSC_Msk)   | 1U

/**
  \brief   Setup a SAU Region
  \details Writes the region information contained in SAU_Region to the
           registers SAU_RNR, SAU_RBAR, and SAU_RLAR
 */
__STATIC_INLINE void TZ_SAU_Setup (void)
{

#if defined (__SAUREGION_PRESENT) && (__SAUREGION_PRESENT == 1U)

  #if defined (SAU_INIT_REGION0) && (SAU_INIT_REGION0 == 1U)
    SAU_INIT_REGION(0);
  #endif

  #if defined (SAU_INIT_REGION1) && (SAU_INIT_REGION1 == 1U)
    SAU_INIT_REGION(1);
  #endif

  #if defined (SAU_INIT_REGION2) && (SAU_INIT_REGION2 == 1U)
    SAU_INIT_REGION(2);
  #endif

  #if defined (SAU_INIT_REGION3) && (SAU_INIT_REGION3 == 1U)
    SAU_INIT_REGION(3);
  #endif

  #if defined (SAU_INIT_REGION4) && (SAU_INIT_REGION4 == 1U)
    SAU_INIT_REGION(4);
  #endif

  #if defined (SAU_INIT_REGION5) && (SAU_INIT_REGION5 == 1U)
    SAU_INIT_REGION(5);
  #endif

  #if defined (SAU_INIT_REGION6) && (SAU_INIT_REGION6 == 1U)
    SAU_INIT_REGION(6);
  #endif

  #if defined (SAU_INIT_REGION7) && (SAU_INIT_REGION7 == 1U)
    SAU_INIT_REGION(7);
  #endif

  /* repeat this for all possible SAU regions */

#endif /* defined (__SAUREGION_PRESENT) && (__SAUREGION_PRESENT == 1U) */


  #if defined (SAU_INIT_CTRL) && (SAU_INIT_CTRL == 1U)
    SAU->CTRL = ((SAU_INIT_CTRL_ENABLE << SAU_CTRL_ENABLE_Pos) & SAU_CTRL_ENABLE_Msk) |
                ((SAU_INIT_CTRL_ALLNS  << SAU_CTRL_ALLNS_Pos)  & SAU_CTRL_ALLNS_Msk)   ;
  #endif

  #if defined (SCB_CSR_AIRCR_INIT) && (SCB_CSR_AIRCR_INIT == 1U)
    SCB->SCR   = (SCB->SCR   & ~(SCB_SCR_SLEEPDEEPS_Msk    )) |
                   ((SCB_CSR_DEEPSLEEPS_VAL     << SCB_SCR_SLEEPDEEPS_Pos)     & SCB_SCR_SLEEPDEEPS_Msk);

    SCB->AIRCR = (SCB->AIRCR & ~(SCB_AIRCR_VECTKEY_Msk   | SCB_AIRCR_SYSRESETREQS_Msk |
                                 SCB_AIRCR_BFHFNMINS_Msk | SCB_AIRCR_PRIS_Msk          ))                    |
                   ((0x05FAU                    << SCB_AIRCR_VECTKEY_Pos)      & SCB_AIRCR_VECTKEY_Msk)      |
                   ((SCB_AIRCR_SYSRESETREQS_VAL << SCB_AIRCR_SYSRESETREQS_Pos) & SCB_AIRCR_SYSRESETREQS_Msk) |
                   ((SCB_AIRCR_PRIS_VAL         << SCB_AIRCR_PRIS_Pos)         & SCB_AIRCR_PRIS_Msk)         |
                   ((SCB_AIRCR_BFHFNMINS_VAL    << SCB_AIRCR_BFHFNMINS_Pos)    & SCB_AIRCR_BFHFNMINS_Msk);
  #endif /* defined (SCB_CSR_AIRCR_INIT) && (SCB_CSR_AIRCR_INIT == 1U) */

  #if defined (__FPU_USED) && (__FPU_USED == 1U) && \
      defined (TZ_FPU_NS_USAGE) && (TZ_FPU_NS_USAGE == 1U)

    SCB->NSACR = (SCB->NSACR & ~(SCB_NSACR_CP10_Msk | SCB_NSACR_CP10_Msk)) |
                   ((SCB_NSACR_CP10_11_VAL << SCB_NSACR_CP10_Pos) & (SCB_NSACR_CP10_Msk | SCB_NSACR_CP11_Msk));

    FPU->FPCCR = (FPU->FPCCR & ~(FPU_FPCCR_TS_Msk | FPU_FPCCR_CLRONRETS_Msk | FPU_FPCCR_CLRONRET_Msk)) |
                   ((FPU_FPCCR_TS_VAL        << FPU_FPCCR_TS_Pos       ) & FPU_FPCCR_TS_Msk       ) |
                   ((FPU_FPCCR_CLRONRETS_VAL << FPU_FPCCR_CLRONRETS_Pos) & FPU_FPCCR_CLRONRETS_Msk) |
                   ((FPU_FPCCR_CLRONRET_VAL  << FPU_FPCCR_CLRONRET_Pos ) & FPU_FPCCR_CLRONRET_Msk );
  #endif

  #if defined (NVIC_INIT_ITNS0) && (NVIC_INIT_ITNS0 == 1U)
    NVIC->ITNS[0] = NVIC_INIT_ITNS0_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS1) && (NVIC_INIT_ITNS1 == 1U)
    NVIC->ITNS[1] = NVIC_INIT_ITNS1_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS2) && (NVIC_INIT_ITNS2 == 1U)
    NVIC->ITNS[2] = NVIC_INIT_ITNS2_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS3) && (NVIC_INIT_ITNS3 == 1U)
    NVIC->ITNS[3] = NVIC_INIT_ITNS3_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS4) && (NVIC_INIT_ITNS4 == 1U)
    NVIC->ITNS[4] = NVIC_INIT_ITNS4_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS5) && (NVIC_INIT_ITNS5 == 1U)
    NVIC->ITNS[5] = NVIC_INIT_ITNS5_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS6) && (NVIC_INIT_ITNS6 == 1U)
    NVIC->ITNS[6] = NVIC_INIT_ITNS6_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS7) && (NVIC_INIT_ITNS7 == 1U)
    NVIC->ITNS[7] = NVIC_INIT_ITNS7_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS8) && (NVIC_INIT_ITNS8 == 1U)
    NVIC->ITNS[8] = NVIC_INIT_ITNS8_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS9) && (NVIC_INIT_ITNS9 == 1U)
    NVIC->ITNS[9] = NVIC_INIT_ITNS9_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS10) && (NVIC_INIT_ITNS10 == 1U)
    NVIC->ITNS[10] = NVIC_INIT_ITNS10_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS11) && (NVIC_INIT_ITNS11 == 1U)
    NVIC->ITNS[11] = NVIC_INIT_ITNS11_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS12) && (NVIC_INIT_ITNS12 == 1U)
    NVIC->ITNS[12] = NVIC_INIT_ITNS12_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS13) && (NVIC_INIT_ITNS13 == 1U)
    NVIC->ITNS[13] = NVIC_INIT_ITNS13_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS14) && (NVIC_INIT_ITNS14 == 1U)
    NVIC->ITNS[14] = NVIC_INIT_ITNS14_VAL;
  #endif

  #if defined (NVIC_INIT_ITNS15) && (NVIC_INIT_ITNS15 == 1U)
    NVIC->ITNS[15] = NVIC_INIT_ITNS15_VAL;
  #endif

  /* repeat this for all possible ITNS elements */

}

#endif  /* PARTITION_ARMCM33_H */
