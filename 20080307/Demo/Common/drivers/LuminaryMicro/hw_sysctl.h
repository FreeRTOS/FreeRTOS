//*****************************************************************************
//
// hw_sysctl.h - Macros used when accessing the system control hardware.
//
// Copyright (c) 2005-2007 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 1582 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_SYSCTL_H__
#define __HW_SYSCTL_H__

//*****************************************************************************
//
// The following define the addresses of the system control registers.
//
//*****************************************************************************
#define SYSCTL_DID0             0x400fe000  // Device identification register 0
#define SYSCTL_DID1             0x400fe004  // Device identification register 1
#define SYSCTL_DC0              0x400fe008  // Device capabilities register 0
#define SYSCTL_DC1              0x400fe010  // Device capabilities register 1
#define SYSCTL_DC2              0x400fe014  // Device capabilities register 2
#define SYSCTL_DC3              0x400fe018  // Device capabilities register 3
#define SYSCTL_DC4              0x400fe01C  // Device capabilities register 4
#define SYSCTL_PBORCTL          0x400fe030  // POR/BOR reset control register
#define SYSCTL_LDOPCTL          0x400fe034  // LDO power control register
#define SYSCTL_SRCR0            0x400fe040  // Software reset control reg 0
#define SYSCTL_SRCR1            0x400fe044  // Software reset control reg 1
#define SYSCTL_SRCR2            0x400fe048  // Software reset control reg 2
#define SYSCTL_RIS              0x400fe050  // Raw interrupt status register
#define SYSCTL_IMC              0x400fe054  // Interrupt mask/control register
#define SYSCTL_MISC             0x400fe058  // Interrupt status register
#define SYSCTL_RESC             0x400fe05c  // Reset cause register
#define SYSCTL_RCC              0x400fe060  // Run-mode clock config register
#define SYSCTL_PLLCFG           0x400fe064  // PLL configuration register
#define SYSCTL_RCC2             0x400fe070  // Run-mode clock config register 2
#define SYSCTL_RCGC0            0x400fe100  // Run-mode clock gating register 0
#define SYSCTL_RCGC1            0x400fe104  // Run-mode clock gating register 1
#define SYSCTL_RCGC2            0x400fe108  // Run-mode clock gating register 2
#define SYSCTL_SCGC0            0x400fe110  // Sleep-mode clock gating reg 0
#define SYSCTL_SCGC1            0x400fe114  // Sleep-mode clock gating reg 1
#define SYSCTL_SCGC2            0x400fe118  // Sleep-mode clock gating reg 2
#define SYSCTL_DCGC0            0x400fe120  // Deep Sleep-mode clock gate reg 0
#define SYSCTL_DCGC1            0x400fe124  // Deep Sleep-mode clock gate reg 1
#define SYSCTL_DCGC2            0x400fe128  // Deep Sleep-mode clock gate reg 2
#define SYSCTL_DSLPCLKCFG       0x400fe144  // Deep Sleep-mode clock config reg
#define SYSCTL_CLKVCLR          0x400fe150  // Clock verifcation clear register
#define SYSCTL_LDOARST          0x400fe160  // LDO reset control register
#define SYSCTL_USER0            0x400fe1e0  // NV User Register 0
#define SYSCTL_USER1            0x400fe1e4  // NV User Register 1

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DID0 register.
//
//*****************************************************************************
#define SYSCTL_DID0_VER_MASK        0x70000000  // DID0 version mask
#define SYSCTL_DID0_VER_0           0x00000000  // DID0 version 0
#define SYSCTL_DID0_VER_1           0x10000000  // DID0 version 1
#define SYSCTL_DID0_CLASS_MASK      0x00FF0000  // Device Class
#define SYSCTL_DID0_CLASS_SANDSTORM 0x00000000  // Sandstorm-class Device
#define SYSCTL_DID0_CLASS_FURY      0x00010000  // Fury-class Device
#define SYSCTL_DID0_MAJ_MASK        0x0000FF00  // Major revision mask
#define SYSCTL_DID0_MAJ_A           0x00000000  // Major revision A
#define SYSCTL_DID0_MAJ_B           0x00000100  // Major revision B
#define SYSCTL_DID0_MAJ_C           0x00000200  // Major revision C
#define SYSCTL_DID0_MIN_MASK        0x000000FF  // Minor revision mask
#define SYSCTL_DID0_MIN_0           0x00000000  // Minor revision 0
#define SYSCTL_DID0_MIN_1           0x00000001  // Minor revision 1
#define SYSCTL_DID0_MIN_2           0x00000002  // Minor revision 2
#define SYSCTL_DID0_MIN_3           0x00000003  // Minor revision 3
#define SYSCTL_DID0_MIN_4           0x00000004  // Minor revision 4
#define SYSCTL_DID0_MIN_5           0x00000005  // Minor revision 5

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DID1 register.
//
//*****************************************************************************
#define SYSCTL_DID1_VER_MASK    0xF0000000  // Register version mask
#define SYSCTL_DID1_FAM_MASK    0x0F000000  // Family mask
#define SYSCTL_DID1_FAM_S       0x00000000  // Stellaris family
#define SYSCTL_DID1_PRTNO_MASK  0x00FF0000  // Part number mask
#define SYSCTL_DID1_PRTNO_101   0x00010000  // LM3S101
#define SYSCTL_DID1_PRTNO_102   0x00020000  // LM3S102
#define SYSCTL_DID1_PRTNO_301   0x00110000  // LM3S301
#define SYSCTL_DID1_PRTNO_310   0x00120000  // LM3S310
#define SYSCTL_DID1_PRTNO_315   0x00130000  // LM3S315
#define SYSCTL_DID1_PRTNO_316   0x00140000  // LM3S316
#define SYSCTL_DID1_PRTNO_317   0x00170000  // LM3S317
#define SYSCTL_DID1_PRTNO_328   0x00150000  // LM3S328
#define SYSCTL_DID1_PRTNO_601   0x00210000  // LM3S601
#define SYSCTL_DID1_PRTNO_610   0x00220000  // LM3S610
#define SYSCTL_DID1_PRTNO_611   0x00230000  // LM3S611
#define SYSCTL_DID1_PRTNO_612   0x00240000  // LM3S612
#define SYSCTL_DID1_PRTNO_613   0x00250000  // LM3S613
#define SYSCTL_DID1_PRTNO_615   0x00260000  // LM3S615
#define SYSCTL_DID1_PRTNO_617   0x00280000  // LM3S617
#define SYSCTL_DID1_PRTNO_618   0x00290000  // LM3S618
#define SYSCTL_DID1_PRTNO_628   0x00270000  // LM3S628
#define SYSCTL_DID1_PRTNO_801   0x00310000  // LM3S801
#define SYSCTL_DID1_PRTNO_811   0x00320000  // LM3S811
#define SYSCTL_DID1_PRTNO_812   0x00330000  // LM3S812
#define SYSCTL_DID1_PRTNO_815   0x00340000  // LM3S815
#define SYSCTL_DID1_PRTNO_817   0x00360000  // LM3S817
#define SYSCTL_DID1_PRTNO_818   0x00370000  // LM3S818
#define SYSCTL_DID1_PRTNO_828   0x00350000  // LM3S828
#define SYSCTL_DID1_PRTNO_1110  0x00BF0000  // LM3S1110
#define SYSCTL_DID1_PRTNO_1133  0x00C30000  // LM3S1133
#define SYSCTL_DID1_PRTNO_1138  0x00C50000  // LM3S1138
#define SYSCTL_DID1_PRTNO_1150  0x00C10000  // LM3S1150
#define SYSCTL_DID1_PRTNO_1162  0x00C40000  // LM3S1162
#define SYSCTL_DID1_PRTNO_1165  0x00C20000  // LM3S1165
#define SYSCTL_DID1_PRTNO_1332  0x00C60000  // LM3S1332
#define SYSCTL_DID1_PRTNO_1435  0x00BC0000  // LM3S1435
#define SYSCTL_DID1_PRTNO_1439  0x00BA0000  // LM3S1439
#define SYSCTL_DID1_PRTNO_1512  0x00BB0000  // LM3S1512
#define SYSCTL_DID1_PRTNO_1538  0x00C70000  // LM3S1538
#define SYSCTL_DID1_PRTNO_1620  0x00C00000  // LM3S1620
#define SYSCTL_DID1_PRTNO_1635  0x00B30000  // LM3S1635
#define SYSCTL_DID1_PRTNO_1637  0x00BD0000  // LM3S1637
#define SYSCTL_DID1_PRTNO_1751  0x00B90000  // LM3S1751
#define SYSCTL_DID1_PRTNO_1850  0x00B40000  // LM3S1850
#define SYSCTL_DID1_PRTNO_1937  0x00B70000  // LM3S1937
#define SYSCTL_DID1_PRTNO_1958  0x00BE0000  // LM3S1958
#define SYSCTL_DID1_PRTNO_1960  0x00B50000  // LM3S1960
#define SYSCTL_DID1_PRTNO_1968  0x00B80000  // LM3S1968
#define SYSCTL_DID1_PRTNO_2110  0x00510000  // LM3S2110
#define SYSCTL_DID1_PRTNO_2139  0x00840000  // LM3S2139
#define SYSCTL_DID1_PRTNO_2410  0x00A20000  // LM3S2410
#define SYSCTL_DID1_PRTNO_2412  0x00590000  // LM3S2412
#define SYSCTL_DID1_PRTNO_2432  0x00560000  // LM3S2432
#define SYSCTL_DID1_PRTNO_2533  0x005A0000  // LM3S2533
#define SYSCTL_DID1_PRTNO_2620  0x00570000  // LM3S2620
#define SYSCTL_DID1_PRTNO_2637  0x00850000  // LM3S2637
#define SYSCTL_DID1_PRTNO_2651  0x00530000  // LM3S2651
#define SYSCTL_DID1_PRTNO_2730  0x00A40000  // LM3S2730
#define SYSCTL_DID1_PRTNO_2739  0x00520000  // LM3S2739
#define SYSCTL_DID1_PRTNO_2939  0x00540000  // LM3S2939
#define SYSCTL_DID1_PRTNO_2948  0x008F0000  // LM3S2948
#define SYSCTL_DID1_PRTNO_2950  0x00580000  // LM3S2950
#define SYSCTL_DID1_PRTNO_2965  0x00550000  // LM3S2965
#define SYSCTL_DID1_PRTNO_6100  0x00A10000  // LM3S6100
#define SYSCTL_DID1_PRTNO_6110  0x00740000  // LM3S6110
#define SYSCTL_DID1_PRTNO_6420  0x00A50000  // LM3S6420
#define SYSCTL_DID1_PRTNO_6422  0x00820000  // LM3S6422
#define SYSCTL_DID1_PRTNO_6432  0x00750000  // LM3S6432
#define SYSCTL_DID1_PRTNO_6537  0x00760000  // LM3S6537
#define SYSCTL_DID1_PRTNO_6610  0x00710000  // LM3S6610
#define SYSCTL_DID1_PRTNO_6633  0x00830000  // LM3S6633
#define SYSCTL_DID1_PRTNO_6637  0x008B0000  // LM3S6637
#define SYSCTL_DID1_PRTNO_6730  0x00A30000  // LM3S6730
#define SYSCTL_DID1_PRTNO_6753  0x00770000  // LM3S6753
#define SYSCTL_DID1_PRTNO_6938  0x00890000  // LM3S6938
#define SYSCTL_DID1_PRTNO_6950  0x00720000  // LM3S6950
#define SYSCTL_DID1_PRTNO_6952  0x00780000  // LM3S6952
#define SYSCTL_DID1_PRTNO_6965  0x00730000  // LM3S6965
#define SYSCTL_DID1_PRTNO_8530  0x00640000  // LM3S8530
#define SYSCTL_DID1_PRTNO_8538  0x008E0000  // LM3S8538
#define SYSCTL_DID1_PRTNO_8630  0x00610000  // LM3S8630
#define SYSCTL_DID1_PRTNO_8730  0x00630000  // LM3S8730
#define SYSCTL_DID1_PRTNO_8733  0x008D0000  // LM3S8733
#define SYSCTL_DID1_PRTNO_8738  0x00860000  // LM3S8738
#define SYSCTL_DID1_PRTNO_8930  0x00650000  // LM3S8930
#define SYSCTL_DID1_PRTNO_8933  0x008C0000  // LM3S8933
#define SYSCTL_DID1_PRTNO_8938  0x00880000  // LM3S8938
#define SYSCTL_DID1_PRTNO_8962  0x00A60000  // LM3S8962
#define SYSCTL_DID1_PRTNO_8970  0x00620000  // LM3S8970
#define SYSCTL_DID1_PINCNT_MASK 0x0000E000  // Pin count
#define SYSCTL_DID1_PINCNT_100  0x00004000  // 100 pin package
#define SYSCTL_DID1_TEMP_MASK   0x000000E0  // Temperature range mask
#define SYSCTL_DID1_TEMP_C      0x00000000  // Commercial temp range (0..70C)
#define SYSCTL_DID1_TEMP_I      0x00000020  // Industrial temp range (-40..85C)
#define SYSCTL_DID1_PKG_MASK    0x00000018  // Package mask
#define SYSCTL_DID1_PKG_28SOIC  0x00000000  // 28-pin SOIC
#define SYSCTL_DID1_PKG_48QFP   0x00000008  // 48-pin QFP
#define SYSCTL_DID1_ROHS        0x00000004  // Part is RoHS compliant
#define SYSCTL_DID1_QUAL_MASK   0x00000003  // Qualification status mask
#define SYSCTL_DID1_QUAL_ES     0x00000000  // Engineering sample (unqualified)
#define SYSCTL_DID1_QUAL_PP     0x00000001  // Pilot production (unqualified)
#define SYSCTL_DID1_QUAL_FQ     0x00000002  // Fully qualified
#define SYSCTL_DID1_PRTNO_SHIFT 16

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC0 register.
//
//*****************************************************************************
#define SYSCTL_DC0_SRAMSZ_MASK  0xFFFF0000  // SRAM size mask
#define SYSCTL_DC0_SRAMSZ_2KB   0x00070000  // 2 KB of SRAM
#define SYSCTL_DC0_SRAMSZ_4KB   0x000F0000  // 4 KB of SRAM
#define SYSCTL_DC0_SRAMSZ_8KB   0x001F0000  // 8 KB of SRAM
#define SYSCTL_DC0_SRAMSZ_16KB  0x003F0000  // 16 KB of SRAM
#define SYSCTL_DC0_SRAMSZ_32KB  0x007F0000  // 32 KB of SRAM
#define SYSCTL_DC0_SRAMSZ_64KB  0x00FF0000  // 64 KB of SRAM
#define SYSCTL_DC0_FLASHSZ_MASK 0x0000FFFF  // Flash size mask
#define SYSCTL_DC0_FLASHSZ_8KB  0x00000003  // 8 KB of flash
#define SYSCTL_DC0_FLASHSZ_16KB 0x00000007  // 16 KB of flash
#define SYSCTL_DC0_FLASHSZ_32KB 0x0000000F  // 32 KB of flash
#define SYSCTL_DC0_FLASHSZ_64KB 0x0000001F  // 64 KB of flash
#define SYSCTL_DC0_FLASHSZ_96KB 0x0000002F  // 96 KB of flash
#define SYSCTL_DC0_FLASHSZ_128K 0x0000003F  // 128 KB of flash
#define SYSCTL_DC0_FLASHSZ_256K 0x0000007F  // 256 KB of flash

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC1 register.
//
//*****************************************************************************
#define SYSCTL_DC1_CAN2         0x04000000  // CAN2 module present
#define SYSCTL_DC1_CAN1         0x02000000  // CAN1 module present
#define SYSCTL_DC1_CAN0         0x01000000  // CAN0 module present
#define SYSCTL_DC1_PWM          0x00100000  // PWM module present
#define SYSCTL_DC1_ADC          0x00010000  // ADC module present
#define SYSCTL_DC1_SYSDIV_MASK  0x0000F000  // Minimum system divider mask
#define SYSCTL_DC1_ADCSPD_MASK  0x00000F00  // ADC speed mask
#define SYSCTL_DC1_ADCSPD_1M    0x00000300  // 1Msps ADC
#define SYSCTL_DC1_ADCSPD_500K  0x00000200  // 500Ksps ADC
#define SYSCTL_DC1_ADCSPD_250K  0x00000100  // 250Ksps ADC
#define SYSCTL_DC1_ADCSPD_125K  0x00000000  // 125Ksps ADC
#define SYSCTL_DC1_MPU          0x00000080  // Cortex M3 MPU present
#define SYSCTL_DC1_HIB          0x00000040  // Hibernation module present
#define SYSCTL_DC1_TEMP         0x00000020  // Temperature sensor present
#define SYSCTL_DC1_PLL          0x00000010  // PLL present
#define SYSCTL_DC1_WDOG         0x00000008  // Watchdog present
#define SYSCTL_DC1_SWO          0x00000004  // Serial wire output present
#define SYSCTL_DC1_SWD          0x00000002  // Serial wire debug present
#define SYSCTL_DC1_JTAG         0x00000001  // JTAG debug present

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC2 register.
//
//*****************************************************************************
#define SYSCTL_DC2_COMP2        0x04000000  // Analog comparator 2 present
#define SYSCTL_DC2_COMP1        0x02000000  // Analog comparator 1 present
#define SYSCTL_DC2_COMP0        0x01000000  // Analog comparator 0 present
#define SYSCTL_DC2_TIMER3       0x00080000  // Timer 3 present
#define SYSCTL_DC2_TIMER2       0x00040000  // Timer 2 present
#define SYSCTL_DC2_TIMER1       0x00020000  // Timer 1 present
#define SYSCTL_DC2_TIMER0       0x00010000  // Timer 0 present
#define SYSCTL_DC2_I2C1         0x00004000  // I2C 1 present
#define SYSCTL_DC2_I2C0         0x00001000  // I2C 0 present
#ifndef DEPRECATED
#define SYSCTL_DC2_I2C          0x00001000  // I2C present
#endif
#define SYSCTL_DC2_QEI1         0x00000200  // QEI 1 present
#define SYSCTL_DC2_QEI0         0x00000100  // QEI 0 present
#ifndef DEPRECATED
#define SYSCTL_DC2_QEI          0x00000100  // QEI present
#endif
#define SYSCTL_DC2_SSI1         0x00000020  // SSI 1 present
#define SYSCTL_DC2_SSI0         0x00000010  // SSI 0 present
#ifndef DEPRECATED
#define SYSCTL_DC2_SSI          0x00000010  // SSI present
#endif
#define SYSCTL_DC2_UART2        0x00000004  // UART 2 present
#define SYSCTL_DC2_UART1        0x00000002  // UART 1 present
#define SYSCTL_DC2_UART0        0x00000001  // UART 0 present

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC3 register.
//
//*****************************************************************************
#define SYSCTL_DC3_32KHZ        0x80000000  // 32kHz pin present
#define SYSCTL_DC3_CCP5         0x20000000  // CCP5 pin present
#define SYSCTL_DC3_CCP4         0x10000000  // CCP4 pin present
#define SYSCTL_DC3_CCP3         0x08000000  // CCP3 pin present
#define SYSCTL_DC3_CCP2         0x04000000  // CCP2 pin present
#define SYSCTL_DC3_CCP1         0x02000000  // CCP1 pin present
#define SYSCTL_DC3_CCP0         0x01000000  // CCP0 pin present
#define SYSCTL_DC3_ADC7         0x00800000  // ADC7 pin present
#define SYSCTL_DC3_ADC6         0x00400000  // ADC6 pin present
#define SYSCTL_DC3_ADC5         0x00200000  // ADC5 pin present
#define SYSCTL_DC3_ADC4         0x00100000  // ADC4 pin present
#define SYSCTL_DC3_ADC3         0x00080000  // ADC3 pin present
#define SYSCTL_DC3_ADC2         0x00040000  // ADC2 pin present
#define SYSCTL_DC3_ADC1         0x00020000  // ADC1 pin present
#define SYSCTL_DC3_ADC0         0x00010000  // ADC0 pin present
#define SYSCTL_DC3_MC_FAULT0    0x00008000  // MC0 fault pin present
#define SYSCTL_DC3_C2O          0x00004000  // C2o pin present
#define SYSCTL_DC3_C2PLUS       0x00002000  // C2+ pin present
#define SYSCTL_DC3_C2MINUS      0x00001000  // C2- pin present
#define SYSCTL_DC3_C1O          0x00000800  // C1o pin present
#define SYSCTL_DC3_C1PLUS       0x00000400  // C1+ pin present
#define SYSCTL_DC3_C1MINUS      0x00000200  // C1- pin present
#define SYSCTL_DC3_C0O          0x00000100  // C0o pin present
#define SYSCTL_DC3_C0PLUS       0x00000080  // C0+ pin present
#define SYSCTL_DC3_C0MINUS      0x00000040  // C0- pin present
#define SYSCTL_DC3_PWM5         0x00000020  // PWM5 pin present
#define SYSCTL_DC3_PWM4         0x00000010  // PWM4 pin present
#define SYSCTL_DC3_PWM3         0x00000008  // PWM3 pin present
#define SYSCTL_DC3_PWM2         0x00000004  // PWM2 pin present
#define SYSCTL_DC3_PWM1         0x00000002  // PWM1 pin present
#define SYSCTL_DC3_PWM0         0x00000001  // PWM0 pin present

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC4 register.
//
//*****************************************************************************
#define SYSCTL_DC4_ETH          0x50000000  // Ethernet present
#define SYSCTL_DC4_GPIOH        0x00000080  // GPIO port H present
#define SYSCTL_DC4_GPIOG        0x00000040  // GPIO port G present
#define SYSCTL_DC4_GPIOF        0x00000020  // GPIO port F present
#define SYSCTL_DC4_GPIOE        0x00000010  // GPIO port E present
#define SYSCTL_DC4_GPIOD        0x00000008  // GPIO port D present
#define SYSCTL_DC4_GPIOC        0x00000004  // GPIO port C present
#define SYSCTL_DC4_GPIOB        0x00000002  // GPIO port B present
#define SYSCTL_DC4_GPIOA        0x00000001  // GPIO port A present

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_PBORCTL register.
//
//*****************************************************************************
#define SYSCTL_PBORCTL_BOR_MASK 0x0000FFFC  // BOR wait timer
#define SYSCTL_PBORCTL_BORIOR   0x00000002  // BOR interrupt or reset
#define SYSCTL_PBORCTL_BORWT    0x00000001  // BOR wait and check for noise
#define SYSCTL_PBORCTL_BOR_SH   2

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_LDOPCTL register.
//
//*****************************************************************************
#define SYSCTL_LDOPCTL_MASK     0x0000003F  // Voltage adjust mask
#define SYSCTL_LDOPCTL_2_25V    0x00000005  // LDO output of 2.25V
#define SYSCTL_LDOPCTL_2_30V    0x00000004  // LDO output of 2.30V
#define SYSCTL_LDOPCTL_2_35V    0x00000003  // LDO output of 2.35V
#define SYSCTL_LDOPCTL_2_40V    0x00000002  // LDO output of 2.40V
#define SYSCTL_LDOPCTL_2_45V    0x00000001  // LDO output of 2.45V
#define SYSCTL_LDOPCTL_2_50V    0x00000000  // LDO output of 2.50V
#define SYSCTL_LDOPCTL_2_55V    0x0000001F  // LDO output of 2.55V
#define SYSCTL_LDOPCTL_2_60V    0x0000001E  // LDO output of 2.60V
#define SYSCTL_LDOPCTL_2_65V    0x0000001D  // LDO output of 2.65V
#define SYSCTL_LDOPCTL_2_70V    0x0000001C  // LDO output of 2.70V
#define SYSCTL_LDOPCTL_2_75V    0x0000001B  // LDO output of 2.75V

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_SRCR0, SYSCTL_RCGC0,
// SYSCTL_SCGC0, and SYSCTL_DCGC0 registers.
//
//*****************************************************************************
#define SYSCTL_SET0_CAN2        0x04000000  // CAN2 module
#define SYSCTL_SET0_CAN1        0x02000000  // CAN1 module
#define SYSCTL_SET0_CAN0        0x01000000  // CAN0 module
#define SYSCTL_SET0_PWM         0x00100000  // PWM module
#define SYSCTL_SET0_ADC         0x00010000  // ADC module
#define SYSCTL_SET0_ADCSPD_MASK 0x00000F00  // ADC speed mask
#define SYSCTL_SET0_ADCSPD_1M   0x00000300  // 1Msps ADC
#define SYSCTL_SET0_ADCSPD_500K 0x00000200  // 500Ksps ADC
#define SYSCTL_SET0_ADCSPD_250K 0x00000100  // 250Ksps ADC
#define SYSCTL_SET0_ADCSPD_125K 0x00000000  // 125Ksps ADC
#define SYSCTL_SET0_HIB         0x00000040  // Hibernation module
#define SYSCTL_SET0_WDOG        0x00000008  // Watchdog module

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_SRCR1, SYSCTL_RCGC1,
// SYSCTL_SCGC1, and SYSCTL_DCGC1 registers.
//
//*****************************************************************************
#define SYSCTL_SET1_COMP2       0x04000000  // Analog comparator module 2
#define SYSCTL_SET1_COMP1       0x02000000  // Analog comparator module 1
#define SYSCTL_SET1_COMP0       0x01000000  // Analog comparator module 0
#define SYSCTL_SET1_TIMER3      0x00080000  // Timer module 3
#define SYSCTL_SET1_TIMER2      0x00040000  // Timer module 2
#define SYSCTL_SET1_TIMER1      0x00020000  // Timer module 1
#define SYSCTL_SET1_TIMER0      0x00010000  // Timer module 0
#define SYSCTL_SET1_I2C1        0x00004000  // I2C module 1
#define SYSCTL_SET1_I2C0        0x00001000  // I2C module 0
#ifndef DEPRECATED
#define SYSCTL_SET1_I2C         0x00001000  // I2C module
#endif
#define SYSCTL_SET1_QEI1        0x00000200  // QEI module 1
#define SYSCTL_SET1_QEI0        0x00000100  // QEI module 0
#ifndef DEPRECATED
#define SYSCTL_SET1_QEI         0x00000100  // QEI module
#endif
#define SYSCTL_SET1_SSI1        0x00000020  // SSI module 1
#define SYSCTL_SET1_SSI0        0x00000010  // SSI module 0
#ifndef DEPRECATED
#define SYSCTL_SET1_SSI         0x00000010  // SSI module
#endif
#define SYSCTL_SET1_UART2       0x00000004  // UART module 2
#define SYSCTL_SET1_UART1       0x00000002  // UART module 1
#define SYSCTL_SET1_UART0       0x00000001  // UART module 0

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_SRCR2, SYSCTL_RCGC2,
// SYSCTL_SCGC2, and SYSCTL_DCGC2 registers.
//
//*****************************************************************************
#define SYSCTL_SET2_ETH         0x50000000  // ETH module
#define SYSCTL_SET2_GPIOH       0x00000080  // GPIO H module
#define SYSCTL_SET2_GPIOG       0x00000040  // GPIO G module
#define SYSCTL_SET2_GPIOF       0x00000020  // GPIO F module
#define SYSCTL_SET2_GPIOE       0x00000010  // GPIO E module
#define SYSCTL_SET2_GPIOD       0x00000008  // GPIO D module
#define SYSCTL_SET2_GPIOC       0x00000004  // GPIO C module
#define SYSCTL_SET2_GPIOB       0x00000002  // GPIO B module
#define SYSCTL_SET2_GPIOA       0x00000001  // GIPO A module

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_RIS, SYSCTL_IMC, and
// SYSCTL_IMS registers.
//
//*****************************************************************************
#define SYSCTL_INT_PLL_LOCK     0x00000040  // PLL lock interrupt
#define SYSCTL_INT_CUR_LIMIT    0x00000020  // Current limit interrupt
#define SYSCTL_INT_IOSC_FAIL    0x00000010  // Internal oscillator failure int
#define SYSCTL_INT_MOSC_FAIL    0x00000008  // Main oscillator failure int
#define SYSCTL_INT_POR          0x00000004  // Power on reset interrupt
#define SYSCTL_INT_BOR          0x00000002  // Brown out interrupt
#define SYSCTL_INT_PLL_FAIL     0x00000001  // PLL failure interrupt

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_RESC register.
//
//*****************************************************************************
#define SYSCTL_RESC_LDO         0x00000020  // LDO power OK lost reset
#define SYSCTL_RESC_SW          0x00000010  // Software reset
#define SYSCTL_RESC_WDOG        0x00000008  // Watchdog reset
#define SYSCTL_RESC_BOR         0x00000004  // Brown-out reset
#define SYSCTL_RESC_POR         0x00000002  // Power on reset
#define SYSCTL_RESC_EXT         0x00000001  // External reset

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_RCC register.
//
//*****************************************************************************
#define SYSCTL_RCC_ACG          0x08000000  // Automatic clock gating
#define SYSCTL_RCC_SYSDIV_MASK  0x07800000  // System clock divider
#define SYSCTL_RCC_SYSDIV_2     0x00800000  // System clock /2
#define SYSCTL_RCC_SYSDIV_3     0x01000000  // System clock /3
#define SYSCTL_RCC_SYSDIV_4     0x01800000  // System clock /4
#define SYSCTL_RCC_SYSDIV_5     0x02000000  // System clock /5
#define SYSCTL_RCC_SYSDIV_6     0x02800000  // System clock /6
#define SYSCTL_RCC_SYSDIV_7     0x03000000  // System clock /7
#define SYSCTL_RCC_SYSDIV_8     0x03800000  // System clock /8
#define SYSCTL_RCC_SYSDIV_9     0x04000000  // System clock /9
#define SYSCTL_RCC_SYSDIV_10    0x04800000  // System clock /10
#define SYSCTL_RCC_SYSDIV_11    0x05000000  // System clock /11
#define SYSCTL_RCC_SYSDIV_12    0x05800000  // System clock /12
#define SYSCTL_RCC_SYSDIV_13    0x06000000  // System clock /13
#define SYSCTL_RCC_SYSDIV_14    0x06800000  // System clock /14
#define SYSCTL_RCC_SYSDIV_15    0x07000000  // System clock /15
#define SYSCTL_RCC_SYSDIV_16    0x07800000  // System clock /16
#define SYSCTL_RCC_USE_SYSDIV   0x00400000  // Use sytem clock divider
#define SYSCTL_RCC_USE_PWMDIV   0x00100000  // Use PWM clock divider
#define SYSCTL_RCC_PWMDIV_MASK  0x000E0000  // PWM clock divider
#define SYSCTL_RCC_PWMDIV_2     0x00000000  // PWM clock /2
#define SYSCTL_RCC_PWMDIV_4     0x00020000  // PWM clock /4
#define SYSCTL_RCC_PWMDIV_8     0x00040000  // PWM clock /8
#define SYSCTL_RCC_PWMDIV_16    0x00060000  // PWM clock /16
#define SYSCTL_RCC_PWMDIV_32    0x00080000  // PWM clock /32
#define SYSCTL_RCC_PWMDIV_64    0x000A0000  // PWM clock /64
#define SYSCTL_RCC_PWRDN        0x00002000  // PLL power down
#define SYSCTL_RCC_OE           0x00001000  // PLL output enable
#define SYSCTL_RCC_BYPASS       0x00000800  // PLL bypass
#define SYSCTL_RCC_PLLVER       0x00000400  // PLL verification timer enable
#define SYSCTL_RCC_XTAL_MASK    0x000003C0  // Crystal attached to main osc
#define SYSCTL_RCC_XTAL_1MHZ    0x00000000  // Using a 1MHz crystal
#define SYSCTL_RCC_XTAL_1_84MHZ 0x00000040  // Using a 1.8432MHz crystal
#define SYSCTL_RCC_XTAL_2MHZ    0x00000080  // Using a 2MHz crystal
#define SYSCTL_RCC_XTAL_2_45MHZ 0x000000C0  // Using a 2.4576MHz crystal
#define SYSCTL_RCC_XTAL_3_57MHZ 0x00000100  // Using a 3.579545MHz crystal
#define SYSCTL_RCC_XTAL_3_68MHZ 0x00000140  // Using a 3.6864MHz crystal
#define SYSCTL_RCC_XTAL_4MHZ    0x00000180  // Using a 4MHz crystal
#ifdef DEPRECATED
#define SYSCTL_RCC_XTAL_3_68MHz 0x00000140  // Using a 3.6864MHz crystal
#define SYSCTL_RCC_XTAL_4MHz    0x00000180  // Using a 4MHz crystal
#endif
#define SYSCTL_RCC_XTAL_4_09MHZ 0x000001C0  // Using a 4.096MHz crystal
#define SYSCTL_RCC_XTAL_4_91MHZ 0x00000200  // Using a 4.9152MHz crystal
#define SYSCTL_RCC_XTAL_5MHZ    0x00000240  // Using a 5MHz crystal
#define SYSCTL_RCC_XTAL_5_12MHZ 0x00000280  // Using a 5.12MHz crystal
#define SYSCTL_RCC_XTAL_6MHZ    0x000002C0  // Using a 6MHz crystal
#define SYSCTL_RCC_XTAL_6_14MHZ 0x00000300  // Using a 6.144MHz crystal
#define SYSCTL_RCC_XTAL_7_37MHZ 0x00000340  // Using a 7.3728MHz crystal
#define SYSCTL_RCC_XTAL_8MHZ    0x00000380  // Using a 8MHz crystal
#define SYSCTL_RCC_XTAL_8_19MHZ 0x000003C0  // Using a 8.192MHz crystal
#define SYSCTL_RCC_OSCSRC_MASK  0x00000030  // Oscillator input select
#define SYSCTL_RCC_OSCSRC_MAIN  0x00000000  // Use the main oscillator
#define SYSCTL_RCC_OSCSRC_INT   0x00000010  // Use the internal oscillator
#define SYSCTL_RCC_OSCSRC_INT4  0x00000020  // Use the internal oscillator / 4
#define SYSCTL_RCC_IOSCVER      0x00000008  // Int. osc. verification timer en
#define SYSCTL_RCC_MOSCVER      0x00000004  // Main osc. verification timer en
#define SYSCTL_RCC_IOSCDIS      0x00000002  // Internal oscillator disable
#define SYSCTL_RCC_MOSCDIS      0x00000001  // Main oscillator disable
#define SYSCTL_RCC_SYSDIV_SHIFT 23          // Shift to the SYSDIV field
#define SYSCTL_RCC_PWMDIV_SHIFT 17          // Shift to the PWMDIV field
#define SYSCTL_RCC_XTAL_SHIFT   6           // Shift to the XTAL field
#define SYSCTL_RCC_OSCSRC_SHIFT 4           // Shift to the OSCSRC field

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_PLLCFG register.
//
//*****************************************************************************
#define SYSCTL_PLLCFG_OD_MASK   0x0000C000  // Output divider
#define SYSCTL_PLLCFG_OD_1      0x00000000  // Output divider is 1
#define SYSCTL_PLLCFG_OD_2      0x00004000  // Output divider is 2
#define SYSCTL_PLLCFG_OD_4      0x00008000  // Output divider is 4
#define SYSCTL_PLLCFG_F_MASK    0x00003FE0  // PLL multiplier
#define SYSCTL_PLLCFG_R_MASK    0x0000001F  // Input predivider
#define SYSCTL_PLLCFG_F_SHIFT   5
#define SYSCTL_PLLCFG_R_SHIFT   0

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_RCC2 register.
//
//*****************************************************************************
#define SYSCTL_RCC2_USERCC2     0x80000000  // Use RCC2
#define SYSCTL_RCC2_SYSDIV2_MSK 0x1F800000  // System clock divider
#define SYSCTL_RCC2_SYSDIV2_2   0x00800000  // System clock /2
#define SYSCTL_RCC2_SYSDIV2_3   0x01000000  // System clock /3
#define SYSCTL_RCC2_SYSDIV2_4   0x01800000  // System clock /4
#define SYSCTL_RCC2_SYSDIV2_5   0x02000000  // System clock /5
#define SYSCTL_RCC2_SYSDIV2_6   0x02800000  // System clock /6
#define SYSCTL_RCC2_SYSDIV2_7   0x03000000  // System clock /7
#define SYSCTL_RCC2_SYSDIV2_8   0x03800000  // System clock /8
#define SYSCTL_RCC2_SYSDIV2_9   0x04000000  // System clock /9
#define SYSCTL_RCC2_SYSDIV2_10  0x04800000  // System clock /10
#define SYSCTL_RCC2_SYSDIV2_11  0x05000000  // System clock /11
#define SYSCTL_RCC2_SYSDIV2_12  0x05800000  // System clock /12
#define SYSCTL_RCC2_SYSDIV2_13  0x06000000  // System clock /13
#define SYSCTL_RCC2_SYSDIV2_14  0x06800000  // System clock /14
#define SYSCTL_RCC2_SYSDIV2_15  0x07000000  // System clock /15
#define SYSCTL_RCC2_SYSDIV2_16  0x07800000  // System clock /16
#define SYSCTL_RCC2_SYSDIV2_17  0x08000000  // System clock /17
#define SYSCTL_RCC2_SYSDIV2_18  0x08800000  // System clock /18
#define SYSCTL_RCC2_SYSDIV2_19  0x09000000  // System clock /19
#define SYSCTL_RCC2_SYSDIV2_20  0x09800000  // System clock /20
#define SYSCTL_RCC2_SYSDIV2_21  0x0A000000  // System clock /21
#define SYSCTL_RCC2_SYSDIV2_22  0x0A800000  // System clock /22
#define SYSCTL_RCC2_SYSDIV2_23  0x0B000000  // System clock /23
#define SYSCTL_RCC2_SYSDIV2_24  0x0B800000  // System clock /24
#define SYSCTL_RCC2_SYSDIV2_25  0x0C000000  // System clock /25
#define SYSCTL_RCC2_SYSDIV2_26  0x0C800000  // System clock /26
#define SYSCTL_RCC2_SYSDIV2_27  0x0D000000  // System clock /27
#define SYSCTL_RCC2_SYSDIV2_28  0x0D800000  // System clock /28
#define SYSCTL_RCC2_SYSDIV2_29  0x0E000000  // System clock /29
#define SYSCTL_RCC2_SYSDIV2_30  0x0E800000  // System clock /30
#define SYSCTL_RCC2_SYSDIV2_31  0x0F000000  // System clock /31
#define SYSCTL_RCC2_SYSDIV2_32  0x0F800000  // System clock /32
#define SYSCTL_RCC2_SYSDIV2_33  0x10000000  // System clock /33
#define SYSCTL_RCC2_SYSDIV2_34  0x10800000  // System clock /34
#define SYSCTL_RCC2_SYSDIV2_35  0x11000000  // System clock /35
#define SYSCTL_RCC2_SYSDIV2_36  0x11800000  // System clock /36
#define SYSCTL_RCC2_SYSDIV2_37  0x12000000  // System clock /37
#define SYSCTL_RCC2_SYSDIV2_38  0x12800000  // System clock /38
#define SYSCTL_RCC2_SYSDIV2_39  0x13000000  // System clock /39
#define SYSCTL_RCC2_SYSDIV2_40  0x13800000  // System clock /40
#define SYSCTL_RCC2_SYSDIV2_41  0x14000000  // System clock /41
#define SYSCTL_RCC2_SYSDIV2_42  0x14800000  // System clock /42
#define SYSCTL_RCC2_SYSDIV2_43  0x15000000  // System clock /43
#define SYSCTL_RCC2_SYSDIV2_44  0x15800000  // System clock /44
#define SYSCTL_RCC2_SYSDIV2_45  0x16000000  // System clock /45
#define SYSCTL_RCC2_SYSDIV2_46  0x16800000  // System clock /46
#define SYSCTL_RCC2_SYSDIV2_47  0x17000000  // System clock /47
#define SYSCTL_RCC2_SYSDIV2_48  0x17800000  // System clock /48
#define SYSCTL_RCC2_SYSDIV2_49  0x18000000  // System clock /49
#define SYSCTL_RCC2_SYSDIV2_50  0x18800000  // System clock /50
#define SYSCTL_RCC2_SYSDIV2_51  0x19000000  // System clock /51
#define SYSCTL_RCC2_SYSDIV2_52  0x19800000  // System clock /52
#define SYSCTL_RCC2_SYSDIV2_53  0x1A000000  // System clock /53
#define SYSCTL_RCC2_SYSDIV2_54  0x1A800000  // System clock /54
#define SYSCTL_RCC2_SYSDIV2_55  0x1B000000  // System clock /55
#define SYSCTL_RCC2_SYSDIV2_56  0x1B800000  // System clock /56
#define SYSCTL_RCC2_SYSDIV2_57  0x1C000000  // System clock /57
#define SYSCTL_RCC2_SYSDIV2_58  0x1C800000  // System clock /58
#define SYSCTL_RCC2_SYSDIV2_59  0x1D000000  // System clock /59
#define SYSCTL_RCC2_SYSDIV2_60  0x1D800000  // System clock /60
#define SYSCTL_RCC2_SYSDIV2_61  0x1E000000  // System clock /61
#define SYSCTL_RCC2_SYSDIV2_62  0x1E800000  // System clock /62
#define SYSCTL_RCC2_SYSDIV2_63  0x1F000000  // System clock /63
#define SYSCTL_RCC2_SYSDIV2_64  0x1F800000  // System clock /64
#define SYSCTL_RCC2_PWRDN2      0x00002000  // PLL power down
#define SYSCTL_RCC2_BYPASS2     0x00000800  // PLL bypass
#define SYSCTL_RCC2_OSCSRC2_MSK 0x00000070  // Oscillator input select
#define SYSCTL_RCC2_OSCSRC2_MO  0x00000000  // Use the main oscillator
#define SYSCTL_RCC2_OSCSRC2_IO  0x00000010  // Use the internal oscillator
#define SYSCTL_RCC2_OSCSRC2_IO4 0x00000020  // Use the internal oscillator / 4
#define SYSCTL_RCC2_OSCSRC2_30  0x00000030  // Use the 30 KHz internal osc.
#define SYSCTL_RCC2_OSCSRC2_32  0x00000070  // Use the 32 KHz external osc.

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DSLPCLKCFG register.
//
//*****************************************************************************
#define SYSCTL_DSLPCLKCFG_D_MSK 0x1f800000  // Deep sleep system clock override
#define SYSCTL_DSLPCLKCFG_D_2   0x00800000  // System clock /2
#define SYSCTL_DSLPCLKCFG_D_3   0x01000000  // System clock /3
#define SYSCTL_DSLPCLKCFG_D_4   0x01800000  // System clock /4
#define SYSCTL_DSLPCLKCFG_D_5   0x02000000  // System clock /5
#define SYSCTL_DSLPCLKCFG_D_6   0x02800000  // System clock /6
#define SYSCTL_DSLPCLKCFG_D_7   0x03000000  // System clock /7
#define SYSCTL_DSLPCLKCFG_D_8   0x03800000  // System clock /8
#define SYSCTL_DSLPCLKCFG_D_9   0x04000000  // System clock /9
#define SYSCTL_DSLPCLKCFG_D_10  0x04800000  // System clock /10
#define SYSCTL_DSLPCLKCFG_D_11  0x05000000  // System clock /11
#define SYSCTL_DSLPCLKCFG_D_12  0x05800000  // System clock /12
#define SYSCTL_DSLPCLKCFG_D_13  0x06000000  // System clock /13
#define SYSCTL_DSLPCLKCFG_D_14  0x06800000  // System clock /14
#define SYSCTL_DSLPCLKCFG_D_15  0x07000000  // System clock /15
#define SYSCTL_DSLPCLKCFG_D_16  0x07800000  // System clock /16
#define SYSCTL_DSLPCLKCFG_D_17  0x08000000  // System clock /17
#define SYSCTL_DSLPCLKCFG_D_18  0x08800000  // System clock /18
#define SYSCTL_DSLPCLKCFG_D_19  0x09000000  // System clock /19
#define SYSCTL_DSLPCLKCFG_D_20  0x09800000  // System clock /20
#define SYSCTL_DSLPCLKCFG_D_21  0x0A000000  // System clock /21
#define SYSCTL_DSLPCLKCFG_D_22  0x0A800000  // System clock /22
#define SYSCTL_DSLPCLKCFG_D_23  0x0B000000  // System clock /23
#define SYSCTL_DSLPCLKCFG_D_24  0x0B800000  // System clock /24
#define SYSCTL_DSLPCLKCFG_D_25  0x0C000000  // System clock /25
#define SYSCTL_DSLPCLKCFG_D_26  0x0C800000  // System clock /26
#define SYSCTL_DSLPCLKCFG_D_27  0x0D000000  // System clock /27
#define SYSCTL_DSLPCLKCFG_D_28  0x0D800000  // System clock /28
#define SYSCTL_DSLPCLKCFG_D_29  0x0E000000  // System clock /29
#define SYSCTL_DSLPCLKCFG_D_30  0x0E800000  // System clock /30
#define SYSCTL_DSLPCLKCFG_D_31  0x0F000000  // System clock /31
#define SYSCTL_DSLPCLKCFG_D_32  0x0F800000  // System clock /32
#define SYSCTL_DSLPCLKCFG_D_33  0x10000000  // System clock /33
#define SYSCTL_DSLPCLKCFG_D_34  0x10800000  // System clock /34
#define SYSCTL_DSLPCLKCFG_D_35  0x11000000  // System clock /35
#define SYSCTL_DSLPCLKCFG_D_36  0x11800000  // System clock /36
#define SYSCTL_DSLPCLKCFG_D_37  0x12000000  // System clock /37
#define SYSCTL_DSLPCLKCFG_D_38  0x12800000  // System clock /38
#define SYSCTL_DSLPCLKCFG_D_39  0x13000000  // System clock /39
#define SYSCTL_DSLPCLKCFG_D_40  0x13800000  // System clock /40
#define SYSCTL_DSLPCLKCFG_D_41  0x14000000  // System clock /41
#define SYSCTL_DSLPCLKCFG_D_42  0x14800000  // System clock /42
#define SYSCTL_DSLPCLKCFG_D_43  0x15000000  // System clock /43
#define SYSCTL_DSLPCLKCFG_D_44  0x15800000  // System clock /44
#define SYSCTL_DSLPCLKCFG_D_45  0x16000000  // System clock /45
#define SYSCTL_DSLPCLKCFG_D_46  0x16800000  // System clock /46
#define SYSCTL_DSLPCLKCFG_D_47  0x17000000  // System clock /47
#define SYSCTL_DSLPCLKCFG_D_48  0x17800000  // System clock /48
#define SYSCTL_DSLPCLKCFG_D_49  0x18000000  // System clock /49
#define SYSCTL_DSLPCLKCFG_D_50  0x18800000  // System clock /50
#define SYSCTL_DSLPCLKCFG_D_51  0x19000000  // System clock /51
#define SYSCTL_DSLPCLKCFG_D_52  0x19800000  // System clock /52
#define SYSCTL_DSLPCLKCFG_D_53  0x1A000000  // System clock /53
#define SYSCTL_DSLPCLKCFG_D_54  0x1A800000  // System clock /54
#define SYSCTL_DSLPCLKCFG_D_55  0x1B000000  // System clock /55
#define SYSCTL_DSLPCLKCFG_D_56  0x1B800000  // System clock /56
#define SYSCTL_DSLPCLKCFG_D_57  0x1C000000  // System clock /57
#define SYSCTL_DSLPCLKCFG_D_58  0x1C800000  // System clock /58
#define SYSCTL_DSLPCLKCFG_D_59  0x1D000000  // System clock /59
#define SYSCTL_DSLPCLKCFG_D_60  0x1D800000  // System clock /60
#define SYSCTL_DSLPCLKCFG_D_61  0x1E000000  // System clock /61
#define SYSCTL_DSLPCLKCFG_D_62  0x1E800000  // System clock /62
#define SYSCTL_DSLPCLKCFG_D_63  0x1F000000  // System clock /63
#define SYSCTL_DSLPCLKCFG_D_64  0x1F800000  // System clock /64
#define SYSCTL_DSLPCLKCFG_O_MSK 0x00000070  // Deep sleep oscillator override
#define SYSCTL_DSLPCLKCFG_O_IGN 0x00000000  // Do not override
#define SYSCTL_DSLPCLKCFG_O_IO  0x00000010  // Use the internal oscillator
#define SYSCTL_DSLPCLKCFG_O_30  0x00000030  // Use the 30 KHz internal osc.
#define SYSCTL_DSLPCLKCFG_O_32  0x00000070  // Use the 32 KHz external osc.

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_CLKVCLR register.
//
//*****************************************************************************
#define SYSCTL_CLKVCLR_CLR      0x00000001  // Clear clock verification fault

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_LDOARST register.
//
//*****************************************************************************
#define SYSCTL_LDOARST_ARST     0x00000001  // Allow LDO to reset device

#endif // __HW_SYSCTL_H__
