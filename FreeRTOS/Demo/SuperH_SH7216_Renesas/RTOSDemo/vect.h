/******************************************************************************
*   DISCLAIMER
*
*   This software is supplied by Renesas Technology Corp. and is only 
*   intended for use with Renesas products. No other uses are authorized.
*
*   This software is owned by Renesas Technology Corp. and is protected under 
*   all applicable laws, including copyright laws.
*
*   THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES 
*   REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, 
*   INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A 
*   PARTICULAR PURPOSE AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY 
*   DISCLAIMED.
*
*   TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS 
*   TECHNOLOGY CORP. NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE 
*   FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES 
*   FOR ANY REASON RELATED TO THE THIS SOFTWARE, EVEN IF RENESAS OR ITS 
*   AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
*
*   Renesas reserves the right, without notice, to make changes to this 
*   software and to discontinue the availability of this software.
*   By using this software, you agree to the additional terms and 
*   conditions found by accessing the following link: 
*   http://www.renesas.com/disclaimer
********************************************************************************
*   Copyright (C) 2009. Renesas Technology Corp., All Rights Reserved.
*""FILE COMMENT""*********** Technical reference data **************************
*   System Name : SH7216 Sample Program
*   File Name   : vect.h
*   Abstract    : Definition of Vector
*   Version     : 0.02.00
*   Device      : SH7216
*   Tool-Chain  : High-performance Embedded Workshop (Ver.4.05.01).
*               : C/C++ compiler package for the SuperH RISC engine family
*               :                             (Ver.9.03 Release00).
*   OS          : None
*   H/W Platform: R0K572167 (CPU board)
*   Description : 
********************************************************************************
*   History     : Mar.30,2009 Ver.0.02.00
*""FILE COMMENT END""**********************************************************/
#ifndef VECT_H
#define VECT_H


//;<<VECTOR DATA START (POWER ON RESET)>>
// 0 Power On Reset PC
extern void PowerON_Reset_PC(void);

//;<<VECTOR DATA END (POWER ON RESET)>>
// 1 Power On Reset SP

//;<<VECTOR DATA START (MANUAL RESET)>>
// 2 Manual Reset PC
extern void Manual_Reset_PC(void);

//;<<VECTOR DATA END (MANUAL RESET)>>
// 3 Manual Reset SP

// 4 Illegal code
#pragma interrupt INT_Illegal_code
extern void INT_Illegal_code(void);

// 5 Reserved

// 6 Illegal slot
#pragma interrupt INT_Illegal_slot
extern void INT_Illegal_slot(void);

// 7 Reserved

// 8 Reserved

// 9 CPU Address error
#pragma interrupt INT_CPU_Address
extern void INT_CPU_Address(void);

// 10 DMAC Address error
#pragma interrupt INT_DMAC_Address
extern void INT_DMAC_Address(void);

// 11 NMI
#pragma interrupt INT_NMI
extern void INT_NMI(void);

// 12 User breakpoint trap
#pragma interrupt INT_User_Break
extern void INT_User_Break(void);

// 13 Reserved

// 14 H-UDI
#pragma interrupt INT_HUDI
extern void INT_HUDI(void);

// 15 Register bank over
#pragma interrupt INT_Bank_Overflow
extern void INT_Bank_Overflow(void);

// 16 Register bank under
#pragma interrupt INT_Bank_Underflow
extern void INT_Bank_Underflow(void);

// 17 ZERO_DIV
#pragma interrupt INT_Divide_by_Zero
extern void INT_Divide_by_Zero(void);

// 18 OVER_DIV
#pragma interrupt INT_Divide_Overflow
extern void INT_Divide_Overflow(void);

// 19 Reserved

// 20 Reserved

// 21 Reserved

// 22 Reserved

// 23 Reserved

// 24 Reserved

// 25 Reserved

// 26 Reserved

// 27 Reserved

// 28 Reserved

// 29 Reserved

// 30 Reserved

// 31 Reserved

// 32 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA32
extern void INT_TRAPA32(void);

// 33 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA33
extern void INT_TRAPA33(void);

// 34 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA34
extern void INT_TRAPA34(void);

// 35 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA35
extern void INT_TRAPA35(void);

// 36 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA36
extern void INT_TRAPA36(void);

// 37 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA37
extern void INT_TRAPA37(void);

// 38 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA38
extern void INT_TRAPA38(void);

// 39 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA39
extern void INT_TRAPA39(void);

// 40 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA40
extern void INT_TRAPA40(void);

// 41 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA41
extern void INT_TRAPA41(void);

// 42 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA42
extern void INT_TRAPA42(void);

// 43 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA43
extern void INT_TRAPA43(void);

// 44 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA44
extern void INT_TRAPA44(void);

// 45 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA45
extern void INT_TRAPA45(void);

// 46 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA46
extern void INT_TRAPA46(void);

// 47 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA47
extern void INT_TRAPA47(void);

// 48 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA48
extern void INT_TRAPA48(void);

// 49 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA49
extern void INT_TRAPA49(void);

// 50 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA50
extern void INT_TRAPA50(void);

// 51 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA51
extern void INT_TRAPA51(void);

// 52 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA52
extern void INT_TRAPA52(void);

// 53 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA53
extern void INT_TRAPA53(void);

// 54 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA54
extern void INT_TRAPA54(void);

// 55 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA55
extern void INT_TRAPA55(void);

// 56 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA56
extern void INT_TRAPA56(void);

// 57 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA57
extern void INT_TRAPA57(void);

// 58 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA58
extern void INT_TRAPA58(void);

// 59 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA59
extern void INT_TRAPA59(void);

// 60 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA60
extern void INT_TRAPA60(void);

// 61 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA61
extern void INT_TRAPA61(void);

// 62 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA62
extern void INT_TRAPA62(void);

// 63 TRAPA (User Vecter)
#pragma interrupt INT_TRAPA63
extern void INT_TRAPA63(void);

// 64 Interrupt IRQ0
#pragma interrupt INT_IRQ0(resbank)
extern void INT_IRQ0(void);

// 65 Interrupt IRQ1
#pragma interrupt INT_IRQ1(resbank)
extern void INT_IRQ1(void);

// 66 Interrupt IRQ2
#pragma interrupt INT_IRQ2(resbank)
extern void INT_IRQ2(void);

// 67 Interrupt IRQ3
#pragma interrupt INT_IRQ3(resbank)
extern void INT_IRQ3(void);

// 68 Interrupt IRQ4
#pragma interrupt INT_IRQ4(resbank)
extern void INT_IRQ4(void);

// 69 Interrupt IRQ5
#pragma interrupt INT_IRQ5(resbank)
extern void INT_IRQ5(void);

// 70 Interrupt IRQ6
#pragma interrupt INT_IRQ6(resbank)
extern void INT_IRQ6(void);

// 71 Interrupt IRQ7
#pragma interrupt INT_IRQ7(resbank)
extern void INT_IRQ7(void);

// 72 Reserved

// 73 Reserved

// 74 Reserved

// 75 Reserved

// 76 Reserved

// 77 Reserved

// 78 Reserved

// 79 Reserved

// 80 Interrupt PINT0
#pragma interrupt INT_PINT0(resbank)
extern void INT_PINT0(void);

// 81 Interrupt PINT1
#pragma interrupt INT_PINT1(resbank)
extern void INT_PINT1(void);

// 82 Interrupt PINT2
#pragma interrupt INT_PINT2(resbank)
extern void INT_PINT2(void);

// 83 Interrupt PINT3
#pragma interrupt INT_PINT3(resbank)
extern void INT_PINT3(void);

// 84 Interrupt PINT4
#pragma interrupt INT_PINT4(resbank)
extern void INT_PINT4(void);

// 85 Interrupt PINT5
#pragma interrupt INT_PINT5(resbank)
extern void INT_PINT5(void);

// 86 Interrupt PINT6
#pragma interrupt INT_PINT6(resbank)
extern void INT_PINT6(void);

// 87 Interrupt PINT7
#pragma interrupt INT_PINT7(resbank)
extern void INT_PINT7(void);

// 88 Reserved

// 89 Reserved

// 90 Reserved

// 91 ROM FIFE
#pragma interrupt INT_ROM_FIFE(resbank)
extern void INT_ROM_FIFE(void);

// 92 A/D ADI0
#pragma interrupt INT_AD_ADI0(resbank)
extern void INT_AD_ADI0(void);

// 93 Reserved

// 94 Reserved

// 95 Reserved

// 96 A/D ADI1
#pragma interrupt INT_AD_ADI1(resbank)
extern void INT_AD_ADI1(void);

// 97 Reserved

// 98 Reserved

// 99 Reserved

// 100 Reserved

// 101 Reserved

// 102 Reserved

// 103 Reserved

// 104 RCANET0 ERS_0
#pragma interrupt INT_RCANET0_ERS_0
extern void INT_RCANET0_ERS_0(void);

// 105 RCANET0 OVR_0
#pragma interrupt INT_RCANET0_OVR_0
extern void INT_RCANET0_OVR_0(void);

// 106 RCANET0 RM01_0
#pragma interrupt INT_RCANET0_RM01_0
extern void INT_RCANET0_RM01_0(void);

// 107 RCANET0 SLE_0
#pragma interrupt INT_RCANET0_SLE_0
extern void INT_RCANET0_SLE_0(void);

// 108 DMAC0 DEI0
#pragma interrupt INT_DMAC0_DEI0(resbank)
extern void INT_DMAC0_DEI0(void);

// 109 DMAC0 HEI0
#pragma interrupt INT_DMAC0_HEI0(resbank)
extern void INT_DMAC0_HEI0(void);

// 110 Reserved

// 111 Reserved

// 112 DMAC1 DEI1
#pragma interrupt INT_DMAC1_DEI1(resbank)
extern void INT_DMAC1_DEI1(void);

// 113 DMAC1 HEI1
#pragma interrupt INT_DMAC1_HEI1(resbank)
extern void INT_DMAC1_HEI1(void);

// 114 Reserved

// 115 Reserved

// 116 DMAC2 DEI2
#pragma interrupt INT_DMAC2_DEI2(resbank)
extern void INT_DMAC2_DEI2(void);

// 117 DMAC2 HEI2
#pragma interrupt INT_DMAC2_HEI2(resbank)
extern void INT_DMAC2_HEI2(void);

// 118 Reserved

// 119 Reserved

// 120 DMAC3 DEI3
#pragma interrupt INT_DMAC3_DEI3(resbank)
extern void INT_DMAC3_DEI3(void);

// 121 DMAC3 HEI3
#pragma interrupt INT_DMAC3_HEI3(resbank)
extern void INT_DMAC3_HEI3(void);

// 122 Reserved

// 123 Reserved

// 124 DMAC4 DEI4
#pragma interrupt INT_DMAC4_DEI4(resbank)
extern void INT_DMAC4_DEI4(void);

// 125 DMAC4 HEI4
#pragma interrupt INT_DMAC4_HEI4(resbank)
extern void INT_DMAC4_HEI4(void);

// 126 Reserved

// 127 Reserved

// 128 DMAC5 DEI5
#pragma interrupt INT_DMAC5_DEI5(resbank)
extern void INT_DMAC5_DEI5(void);

// 129 DMAC5 HEI5
#pragma interrupt INT_DMAC5_HEI5(resbank)
extern void INT_DMAC5_HEI5(void);

// 130 Reserved

// 131 Reserved

// 132 DMAC6 DEI6
#pragma interrupt INT_DMAC6_DEI6(resbank)
extern void INT_DMAC6_DEI6(void);

// 133 DMAC6 HEI6
#pragma interrupt INT_DMAC6_HEI6(resbank)
extern void INT_DMAC6_HEI6(void);

// 134 Reserved

// 135 Reserved

// 136 DMAC7 DEI7
#pragma interrupt INT_DMAC7_DEI7(resbank)
extern void INT_DMAC7_DEI7(void);

// 137 DMAC7 HEI7
#pragma interrupt INT_DMAC7_HEI7(resbank)
extern void INT_DMAC7_HEI7(void);

// 138 Reserved

// 139 Reserved

// 140 CMT CMI0
#pragma interrupt INT_CMT_CMI0(resbank)
extern void INT_CMT_CMI0(void);

// 141 Reserved

// 142 Reserved

// 143 Reserved

// 144 CMT CMI1
#pragma interrupt INT_CMT_CMI1(resbank)
extern void INT_CMT_CMI1(void);

// 145 Reserved

// 146 Reserved

// 147 Reserved

// 148 BSC CMTI
#pragma interrupt INT_BSC_CMTI(resbank)
extern void INT_BSC_CMTI(void);

// 149 Reserved

// 150 USB EP4FULL
#pragma interrupt INT_USB_EP4FULL(resbank)
extern void INT_USB_EP4FULL(void);

// 151 USB EP5EMPTY
#pragma interrupt INT_USB_EP5EMPTY(resbank)
extern void INT_USB_EP5EMPTY(void);

// 152 WDT ITI
#pragma interrupt INT_WDT_ITI(resbank)
extern void INT_WDT_ITI(void);

// 153 E-DMAC EINT0
#pragma interrupt INT_EDMAC_EINT0(resbank)
extern void INT_EDMAC_EINT0(void);

// 154 USB EP1FULL
#pragma interrupt INT_USB_EP1FULL(resbank)
extern void INT_USB_EP1FULL(void);

// 155 USB EP2EMPTY
#pragma interrupt INT_USB_EP2EMPTY(resbank)
extern void INT_USB_EP2EMPTY(void);

// 156 MTU2 MTU0 TGI0A
#pragma interrupt INT_MTU2_MTU0_TGI0A(resbank)
extern void INT_MTU2_MTU0_TGI0A(void);

// 157 MTU2 MTU0 TGI0B
#pragma interrupt INT_MTU2_MTU0_TGI0B(resbank)
extern void INT_MTU2_MTU0_TGI0B(void);

// 158 MTU2 MTU0 TGI0C
#pragma interrupt INT_MTU2_MTU0_TGI0C(resbank)
extern void INT_MTU2_MTU0_TGI0C(void);

// 159 MTU2 MTU0 TGI0D
#pragma interrupt INT_MTU2_MTU0_TGI0D(resbank)
extern void INT_MTU2_MTU0_TGI0D(void);

// 160 MTU2 MTU0 TGI0V
#pragma interrupt INT_MTU2_MTU0_TGI0V(resbank)
extern void INT_MTU2_MTU0_TGI0V(void);

// 161 MTU2 MTU0 TGI0E
#pragma interrupt INT_MTU2_MTU0_TGI0E(resbank)
extern void INT_MTU2_MTU0_TGI0E(void);

// 162 MTU2 MTU0 TGI0F
#pragma interrupt INT_MTU2_MTU0_TGI0F(resbank)
extern void INT_MTU2_MTU0_TGI0F(void);

// 163 Reserved

// 164 MTU2 MTU1 TGI1A
#pragma interrupt INT_MTU2_MTU1_TGI1A(resbank)
extern void INT_MTU2_MTU1_TGI1A(void);

// 165 MTU2 MTU1 TGI1B
#pragma interrupt INT_MTU2_MTU1_TGI1B(resbank)
extern void INT_MTU2_MTU1_TGI1B(void);

// 166 Reserved 

// 167 Reserved

// 168 MTU2 MTU1 TGI1V
#pragma interrupt INT_MTU2_MTU1_TGI1V(resbank)
extern void INT_MTU2_MTU1_TGI1V(void);

// 169 MTU2 MTU1 TGI1U
#pragma interrupt INT_MTU2_MTU1_TGI1U(resbank)
extern void INT_MTU2_MTU1_TGI1U(void);

// 170 Reserved 

// 171 Reserved

// 172 MTU2 MTU2 TGI2A
#pragma interrupt INT_MTU2_MTU2_TGI2A(resbank)
extern void INT_MTU2_MTU2_TGI2A(void);

// 173 MTU2 MTU2 TGI2B
#pragma interrupt INT_MTU2_MTU2_TGI2B(resbank)
extern void INT_MTU2_MTU2_TGI2B(void);

// 174 Reserved 

// 175 Reserved

// 176 MTU2 MTU2 TGI2V
#pragma interrupt INT_MTU2_MTU2_TGI2V(resbank)
extern void INT_MTU2_MTU2_TGI2V(void);

// 177 MTU2 MTU2 TGI2U
#pragma interrupt INT_MTU2_MTU2_TGI2U(resbank)
extern void INT_MTU2_MTU2_TGI2U(void);

// 178 Reserved 

// 179 Reserved

// 180 MTU2 MTU3 TGI3A
#pragma interrupt INT_MTU2_MTU3_TGI3A(resbank)
extern void INT_MTU2_MTU3_TGI3A(void);

// 181 MTU2 MTU3 TGI3B
#pragma interrupt INT_MTU2_MTU3_TGI3B(resbank)
extern void INT_MTU2_MTU3_TGI3B(void);

// 182 MTU2 MTU3 TGI3C
#pragma interrupt INT_MTU2_MTU3_TGI3C(resbank)
extern void INT_MTU2_MTU3_TGI3C(void);

// 183 MTU2 MTU3 TGI3D
#pragma interrupt INT_MTU2_MTU3_TGI3D(resbank)
extern void INT_MTU2_MTU3_TGI3D(void);

// 184 MTU2 MTU3 TGI3V
#pragma interrupt INT_MTU2_MTU3_TGI3V(resbank)
extern void INT_MTU2_MTU3_TGI3V(void);

// 185 Reserved 

// 186 Reserved

// 187 Reserved 

// 188 MTU2 MTU4 TGI4A
#pragma interrupt INT_MTU2_MTU4_TGI4A(resbank)
extern void INT_MTU2_MTU4_TGI4A(void);

// 189 MTU2 MTU4 TGI4B
#pragma interrupt INT_MTU2_MTU4_TGI4B(resbank)
extern void INT_MTU2_MTU4_TGI4B(void);

// 190 MTU2 MTU4 TGI4C
#pragma interrupt INT_MTU2_MTU4_TGI4C(resbank)
extern void INT_MTU2_MTU4_TGI4C(void);

// 191 MTU2 MTU4 TGI4D
#pragma interrupt INT_MTU2_MTU4_TGI4D(resbank)
extern void INT_MTU2_MTU4_TGI4D(void);

// 192 MTU2 MTU4 TGI4V
#pragma interrupt INT_MTU2_MTU4_TGI4V(resbank)
extern void INT_MTU2_MTU4_TGI4V(void);

// 193 Reserved 

// 194 Reserved

// 195 Reserved 

// 196 MTU2 MTU5 TGI5U
#pragma interrupt INT_MTU2_MTU5_TGI5U(resbank)
extern void INT_MTU2_MTU5_TGI5U(void);

// 197 MTU2 MTU5 TGI5V
#pragma interrupt INT_MTU2_MTU5_TGI5V(resbank)
extern void INT_MTU2_MTU5_TGI5V(void);

// 198 MTU2 MTU5 TGI5W
#pragma interrupt INT_MTU2_MTU5_TGI5W(resbank)
extern void INT_MTU2_MTU5_TGI5W(void);

// 199 Reserved 

// 200 POE2 OEI1
#pragma interrupt INT_POE2_OEI1(resbank)
extern void INT_POE2_OEI1(void);

// 201 POE2 OEI2 
#pragma interrupt INT_POE2_OEI2(resbank)
extern void INT_POE2_OEI2(void);

// 202 Reserved 

// 203 Reserved

// 204 MTU2S MTU3S TGI3A 
#pragma interrupt INT_MTU2S_MTU3S_TGI3A(resbank)
extern void INT_MTU2S_MTU3S_TGI3A(void);

// 205 MTU2S MTU3S TGI3B
#pragma interrupt INT_MTU2S_MTU3S_TGI3B(resbank)
extern void INT_MTU2S_MTU3S_TGI3B(void);

// 206 MTU2S MTU3S TGI3C
#pragma interrupt INT_MTU2S_MTU3S_TGI3C(resbank)
extern void INT_MTU2S_MTU3S_TGI3C(void);

// 207 MTU2S MTU3S TGI3D 
#pragma interrupt INT_MTU2S_MTU3S_TGI3D(resbank)
extern void INT_MTU2S_MTU3S_TGI3D(void);

// 208 MTU2S MTU3S TGI3V
#pragma interrupt INT_MTU2S_MTU3S_TGI3V(resbank)
extern void INT_MTU2S_MTU3S_TGI3V(void);

// 209 Reserved 

// 210 Reserved 

// 211 Reserved

// 212 MTU2S MTU4S TGI4A 
#pragma interrupt INT_MTU2S_MTU4S_TGI4A(resbank)
extern void INT_MTU2S_MTU4S_TGI4A(void);

// 213 MTU2S MTU4S TGI4B 
#pragma interrupt INT_MTU2S_MTU4S_TGI4B(resbank)
extern void INT_MTU2S_MTU4S_TGI4B(void);

// 214 MTU2S MTU4S TGI4C
#pragma interrupt INT_MTU2S_MTU4S_TGI4C(resbank)
extern void INT_MTU2S_MTU4S_TGI4C(void); 

// 215 MTU2S MTU4S TGI4D 
#pragma interrupt INT_MTU2S_MTU4S_TGI4D(resbank)
extern void INT_MTU2S_MTU4S_TGI4D(void); 

// 216 MTU2S MTU4S TGI4V
#pragma interrupt INT_MTU2S_MTU4S_TGI4V(resbank)
extern void INT_MTU2S_MTU4S_TGI4V(void);  

// 217 Reserved 

// 218 Reserved

// 219 Reserved 

// 220 MTU2S MTU5S TGI5U
#pragma interrupt INT_MTU2S_MTU5S_TGI5U(resbank)
extern void INT_MTU2S_MTU5S_TGI5U(void);   

// 221 MTU2S MTU5S TGI5V
#pragma interrupt INT_MTU2S_MTU5S_TGI5V(resbank)
extern void INT_MTU2S_MTU5S_TGI5V(void);   

// 222 MTU2S MTU5S TGI5W 
#pragma interrupt INT_MTU2S_MTU5S_TGI5W(resbank)
extern void INT_MTU2S_MTU5S_TGI5W(void);   

// 223 Reserved

// 224 POE2 OEI3
#pragma interrupt INT_POE2_OEI3(resbank)
extern void INT_POE2_OEI3(void);

// 225 Reserved

// 226 USB USI0
#pragma interrupt INT_USB_USI0(resbank)
extern void INT_USB_USI0(void);

// 227 USB USI1
#pragma interrupt INT_USB_USI1(resbank)
extern void INT_USB_USI1(void);

// 228 IIC3 STPI
#pragma interrupt INT_IIC3_STPI(resbank)
extern void INT_IIC3_STPI(void);

// 229 IIC3 NAKI
#pragma interrupt INT_IIC3_NAKI(resbank)
extern void INT_IIC3_NAKI(void); 

// 230 IIC3 RXI
#pragma interrupt INT_IIC3_RXI(resbank)
extern void INT_IIC3_RXI(void); 

// 231 IIC3 TXI
#pragma interrupt INT_IIC3_TXI(resbank)
extern void INT_IIC3_TXI(void);

// 232 IIC3 TEI
#pragma interrupt INT_IIC3_TEI(resbank)
extern void INT_IIC3_TEI(void); 

// 233 RSPI SPERI
#pragma interrupt INT_RSPI_SPERI(resbank)
extern void INT_RSPI_SPERI(void); 

// 234 RSPI SPRXI
#pragma interrupt INT_RSPI_SPRXI(resbank)
extern void INT_RSPI_SPRXI(void); 

// 235 RSPI SPTXI
#pragma interrupt INT_RSPI_SPTXI(resbank)
extern void INT_RSPI_SPTXI(void); 

// 236 SCI SCI4 ERI4
#pragma interrupt INT_SCI_SCI4_ERI4(resbank)
extern void INT_SCI_SCI4_ERI4(void);

// 237 SCI SCI4 RXI4
#pragma interrupt INT_SCI_SCI4_RXI4(resbank)
extern void INT_SCI_SCI4_RXI4(void);

// 238 SCI SCI4 TXI4
#pragma interrupt INT_SCI_SCI4_TXI4(resbank)
extern void INT_SCI_SCI4_TXI4(void);

// 239 SCI SCI4 TEI4
#pragma interrupt INT_SCI_SCI4_TEI4(resbank)
extern void INT_SCI_SCI4_TEI4(void);

// 240 SCI SCI0 ERI0
#pragma interrupt INT_SCI_SCI0_ERI0(resbank)
extern void INT_SCI_SCI0_ERI0(void);

// 241 SCI SCI0 RXI0
#pragma interrupt INT_SCI_SCI0_RXI0(resbank)
extern void INT_SCI_SCI0_RXI0(void);

// 242 SCI SCI0 TXI0
#pragma interrupt INT_SCI_SCI0_TXI0(resbank)
extern void INT_SCI_SCI0_TXI0(void);

// 243 SCI SCI0 TEI0
#pragma interrupt INT_SCI_SCI0_TEI0(resbank)
extern void INT_SCI_SCI0_TEI0(void);

// 244 SCI SCI1 ERI1
#pragma interrupt INT_SCI_SCI1_ERI1(resbank)
extern void INT_SCI_SCI1_ERI1(void);

// 245 SCI SCI1 RXI1
#pragma interrupt INT_SCI_SCI1_RXI1(resbank)
extern void INT_SCI_SCI1_RXI1(void);

// 246 SCI SCI1 TXI1
#pragma interrupt INT_SCI_SCI1_TXI1(resbank)
extern void INT_SCI_SCI1_TXI1(void);

// 247 SCI SCI1 TEI1
#pragma interrupt INT_SCI_SCI1_TEI1(resbank)
extern void INT_SCI_SCI1_TEI1(void);

// 248 SCI SCI2 ERI2
#pragma interrupt INT_SCI_SCI2_ERI2(resbank)
extern void INT_SCI_SCI2_ERI2(void);

// 249 SCI SCI2 RXI2
#pragma interrupt INT_SCI_SCI2_RXI2(resbank)
extern void INT_SCI_SCI2_RXI2(void);

// 250 SCI SCI2 TXI2
#pragma interrupt INT_SCI_SCI2_TXI2(resbank)
extern void INT_SCI_SCI2_TXI2(void);

// 251 SCI SCI2 TEI2
#pragma interrupt INT_SCI_SCI2_TEI2(resbank)
extern void INT_SCI_SCI2_TEI2(void);

// 252 SCIF SCIF3 BRI3
#pragma interrupt INT_SCIF_SCIF3_BRI3(resbank)
extern void INT_SCIF_SCIF3_BRI3(void);

// 253 SCIF SCIF3 ERI3
#pragma interrupt INT_SCIF_SCIF3_ERI3(resbank)
extern void INT_SCIF_SCIF3_ERI3(void);

// 254 SCIF SCIF3 RXI3
#pragma interrupt INT_SCIF_SCIF3_RXI3(resbank)
extern void INT_SCIF_SCIF3_RXI3(void);

// 255 SCIF SCIF3 TXI3
#pragma interrupt INT_SCIF_SCIF3_TXI3(resbank)
extern void INT_SCIF_SCIF3_TXI3(void);

// Dummy
#pragma interrupt Dummy(resbank)
extern void Dummy(void);

#endif /* VECT_H */

/* End of File */
