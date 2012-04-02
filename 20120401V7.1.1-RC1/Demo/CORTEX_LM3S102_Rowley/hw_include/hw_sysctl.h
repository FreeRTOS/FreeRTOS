//*****************************************************************************
//
// hw_sysctl.h - Macros used when accessing the system control hardware.
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
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
// This is part of revision 523 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __HW_SYSCTL_H__
#define __HW_SYSCTL_H__

//*****************************************************************************
//
// The following define the offsets of the system control registers.
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
#define SYSCTL_RCGC0            0x400fe100  // Run-mode clock gating register 0
#define SYSCTL_RCGC1            0x400fe104  // Run-mode clock gating register 1
#define SYSCTL_RCGC2            0x400fe108  // Run-mode clock gating register 2
#define SYSCTL_SCGC0            0x400fe110  // Sleep-mode clock gating reg 0
#define SYSCTL_SCGC1            0x400fe114  // Sleep-mode clock gating reg 1
#define SYSCTL_SCGC2            0x400fe118  // Sleep-mode clock gating reg 2
#define SYSCTL_DCGC0            0x400fe120  // Deep Sleep-mode clock gate reg 0
#define SYSCTL_DCGC1            0x400fe124  // Deep Sleep-mode clock gate reg 1
#define SYSCTL_DCGC2            0x400fe128  // Deep Sleep-mode clock gate reg 2
#define SYSCTL_CLKVCLR          0x400fe150  // Clock verifcation clear register
#define SYSCTL_LDOARST          0x400fe160  // LDO reset control register

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DID0 register.
//
//*****************************************************************************
#define SYSCTL_DID0_MAJ_MASK    0x0000FF00  // Major revision mask
#define SYSCTL_DID0_MAJ_A       0x00000000  // Major revision A
#define SYSCTL_DID0_MAJ_B       0x00000100  // Major revision B
#define SYSCTL_DID0_MIN_MASK    0x000000FF  // Minor revision mask
#define SYSCTL_DID0_MIN_0       0x00000000  // Minor revision 0
#define SYSCTL_DID0_MIN_1       0x00000001  // Minor revision 1

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
#define SYSCTL_DID1_TEMP_MASK   0x000000E0  // Temperature range mask
#define SYSCTL_DID1_TEMP_C      0x00000000  // Commercial temp range (0..70C)
#define SYSCTL_DID1_TEMP_I      0x00000020  // Industrial temp range (-40..85C)
#define SYSCTL_DID1_PKG_MASK    0x00000018  // Package mask
#define SYSCTL_DID1_PKG_28SOIC  0x00000000  // 28-pin SOIC
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
#define SYSCTL_DC0_SRAMSZ_2KB   0x00070000  // 2kB of SRAM
#define SYSCTL_DC0_FLASHSZ_MASK 0x0000FFFF  // Flash size mask
#define SYSCTL_DC0_FLASHSZ_8KB  0x00000003  // 8kB of flash

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC1 register.
//
//*****************************************************************************
#define SYSCTL_DC1_SYSDIV_MASK  0x0000F000  // Minimum system divider mask
#define SYSCTL_DC1_MPU          0x00000080  // Cortex-M3 MPU present
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
#define SYSCTL_DC2_COMP1        0x02000000  // Analog comparator 1 present
#define SYSCTL_DC2_COMP0        0x01000000  // Analog comparator 0 present
#define SYSCTL_DC2_TIMER1       0x00020000  // Timer 1 present
#define SYSCTL_DC2_TIMER0       0x00010000  // Timer 0 present
#define SYSCTL_DC2_I2C          0x00001000  // I2C present
#define SYSCTL_DC2_SSI          0x00000010  // SSI present
#define SYSCTL_DC2_UART0        0x00000001  // UART 0 present

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC3 register.
//
//*****************************************************************************
#define SYSCTL_DC3_32KHZ        0x80000000  // 32kHz pin present
#define SYSCTL_DC3_CCP1         0x02000000  // CCP1 pin present
#define SYSCTL_DC3_CCP0         0x01000000  // CCP0 pin present
#define SYSCTL_DC3_C1MINUS      0x00000200  // C1- pin present
#define SYSCTL_DC3_C0O          0x00000100  // C0o pin present
#define SYSCTL_DC3_C0PLUS       0x00000080  // C0+ pin present
#define SYSCTL_DC3_C0MINUS      0x00000040  // C0- pin present

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_DC4 register.
//
//*****************************************************************************
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
#define SYSCTL_SET0_WDOG        0x00000008  // Watchdog module

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_SRCR1, SYSCTL_RCGC1,
// SYSCTL_SCGC1, and SYSCTL_DCGC1 registers.
//
//*****************************************************************************
#define SYSCTL_SET1_COMP1       0x02000000  // Analog comparator module 1
#define SYSCTL_SET1_COMP0       0x01000000  // Analog comparator module 0
#define SYSCTL_SET1_TIMER1      0x00020000  // Timer module 1
#define SYSCTL_SET1_TIMER0      0x00010000  // Timer module 0
#define SYSCTL_SET1_I2C         0x00001000  // I2C module
#define SYSCTL_SET1_SSI         0x00000010  // SSI module
#define SYSCTL_SET1_UART0       0x00000001  // UART module 0

//*****************************************************************************
//
// The following define the bit fields in the SYSCTL_SRCR2, SYSCTL_RCGC2,
// SYSCTL_SCGC2, and SYSCTL_DCGC2 registers.
//
//*****************************************************************************
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
#define SYSCTL_INT_BOSC_FAIL    0x00000010  // Boot oscillator failure int
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
#define SYSCTL_RCC_PWRDN        0x00002000  // PLL power down
#define SYSCTL_RCC_OE           0x00001000  // PLL output enable
#define SYSCTL_RCC_BYPASS       0x00000800  // PLL bypass
#define SYSCTL_RCC_PLLVER       0x00000400  // PLL verification timer enable
#define SYSCTL_RCC_XTAL_MASK    0x000003C0  // Crystal attached to main osc
#define SYSCTL_RCC_XTAL_3_57MHZ 0x00000100  // Using a 3.579545MHz crystal
#define SYSCTL_RCC_XTAL_3_68MHz 0x00000140  // Using a 3.6864MHz crystal
#define SYSCTL_RCC_XTAL_4MHz    0x00000180  // Using a 4MHz crystal
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
#define SYSCTL_RCC_OSCSRC_BOOT  0x00000010  // Use the boot oscillator
#define SYSCTL_RCC_OSCSRC_BOOT4 0x00000020  // Use the boot oscillator / 4
#define SYSCTL_RCC_BOSCVER      0x00000008  // Boot osc. verification timer en
#define SYSCTL_RCC_MOSCVER      0x00000004  // Main osc. verification timer en
#define SYSCTL_RCC_BOSCDIS      0x00000002  // Boot oscillator disable
#define SYSCTL_RCC_MOSCDIS      0x00000001  // Main oscillator disable
#define SYSCTL_RCC_SYSDIV_SHIFT 23          // Shift to the SYSDIV field
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
