/******************************************************************************
 *   LPC17xx.h:  Header file for NXP LPC17xx Cortex-M3 Family Microprocessors
 *   The header file is the super set of all hardware definitions of the 
 *   peripherals for the LPC17xx/24xx microprocessor.
 *
 *   Copyright(C) 2006-2008, NXP Semiconductor
 *   All rights reserved.
 *
 *   History
 *
******************************************************************************/

#ifndef __LPC17xx_H
#define __LPC17xx_H

//#include "sysdefs.h"

#define SRAM_BASE_LOCAL       ((unsigned long)0x10000000)   // 32 Kb
#define SRAM_BASE_AHB         ((unsigned long)0x20000000)	// 32 Kb

/* System Control Space memory map */
#ifndef SCS_BASE
	#define SCS_BASE              ((unsigned long)0xE000E000)
#endif

#define SysTick_BASE          (SCS_BASE + 0x0010)
#define NVIC_BASE             (SCS_BASE + 0x0100)
#define CM3_PERIPH_BASE_ADDR  (SCS_BASE + 0x0D00)

typedef struct
{
  unsigned long CPUID;
  unsigned long IRQControlState;
  unsigned long ExceptionTableOffset;
  unsigned long AIRC;
  unsigned long SysCtrl;
  unsigned long ConfigCtrl;
  unsigned long SystemPriority[3];
  unsigned long SysHandlerCtrl;
  unsigned long ConfigFaultStatus;
  unsigned long HardFaultStatus;
  unsigned long DebugFaultStatus;
  unsigned long MemoryManageFaultAddr;
  unsigned long BusFaultAddr;
} CM3_t;

/* Vector Table Base Address */
#define NVIC_VectorTable_RAM          SRAM_BASE_AHB
#define NVIC_VectorTable_FLASH        ((unsigned long)0x00000000)

#define IS_NVIC_VECTORTBL(TABLE_BASE) ((TABLE_BASE == NVIC_VectorTable_RAM) || \
                                       (TABLE_BASE == NVIC_VectorTable_FLASH))
                                  
/* Pin Connect Block */
#define PINSEL_BASE_ADDR	0x4002C000
#define PINSEL0        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x00))
#define PINSEL1        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x04))
#define PINSEL2        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x08))
#define PINSEL3        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x0C))
#define PINSEL4        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x10))
#define PINSEL5        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x14))
#define PINSEL6        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x18))
#define PINSEL7        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x1C))
#define PINSEL8        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x20))
#define PINSEL9        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x24))
#define PINSEL10       (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x28))

#define PINMODE0        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x40))
#define PINMODE1        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x44))
#define PINMODE2        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x48))
#define PINMODE3        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x4C))
#define PINMODE4        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x50))
#define PINMODE5        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x54))
#define PINMODE6        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x58))
#define PINMODE7        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x5C))
#define PINMODE8        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x60))
#define PINMODE9        (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x64))

/* Open drain mode control */
#define PINMODE_OD0     (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x68))
#define PINMODE_OD1     (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x6C))
#define PINMODE_OD2     (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x70))
#define PINMODE_OD3     (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x74))
#define PINMODE_OD4     (*(volatile unsigned long *)(PINSEL_BASE_ADDR + 0x78))

#define PINSEL0_P00_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P00_TXD0      ((unsigned int) 0x00000001)
#define PINSEL0_P00_PWM1      ((unsigned int) 0x00000002)
#define PINSEL0_P00_RSVD3     ((unsigned int) 0x00000003)
#define PINSEL0_P00_MASK      ((unsigned int) 0x00000003)

#define PINSEL0_P01_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P01_RXD0      ((unsigned int) 0x00000004)
#define PINSEL0_P01_PWM3      ((unsigned int) 0x00000008)
#define PINSEL0_P01_EINT0     ((unsigned int) 0x0000000C)
#define PINSEL0_P01_MASK      ((unsigned int) 0x0000000C)

#define PINSEL0_P02_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P02_SCL0      ((unsigned int) 0x00000010)
#define PINSEL0_P02_CAP00     ((unsigned int) 0x00000020)
#define PINSEL0_P02_RSVD3     ((unsigned int) 0x00000030)
#define PINSEL0_P02_MASK      ((unsigned int) 0x00000030)

#define PINSEL0_P03_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P03_SDA0      ((unsigned int) 0x00000040)
#define PINSEL0_P03_MAT00     ((unsigned int) 0x00000080)
#define PINSEL0_P03_EINT1     ((unsigned int) 0x000000C0)
#define PINSEL0_P03_MASK      ((unsigned int) 0x000000C0)

#define PINSEL0_P04_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P04_SCK0      ((unsigned int) 0x00000100)
#define PINSEL0_P04_CAP01     ((unsigned int) 0x00000200)
#define PINSEL0_P04_RSVD3     ((unsigned int) 0x00000300)
#define PINSEL0_P04_MASK      ((unsigned int) 0x00000300)

#define PINSEL0_P05_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P05_MISO0     ((unsigned int) 0x00000400)
#define PINSEL0_P05_MAT01     ((unsigned int) 0x00000800)
#define PINSEL0_P05_AD06      ((unsigned int) 0x00000C00)
#define PINSEL0_P05_MASK      ((unsigned int) 0x00000C00)

#define PINSEL0_P06_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P06_MOSI0     ((unsigned int) 0x00001000)
#define PINSEL0_P06_CAP02     ((unsigned int) 0x00002000)
#define PINSEL0_P06_AD10      ((unsigned int) 0x00003000)
#define PINSEL0_P06_MASK      ((unsigned int) 0x00003000)

#define PINSEL0_P07_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P07_SSEL0     ((unsigned int) 0x00004000)
#define PINSEL0_P07_PWM2      ((unsigned int) 0x00008000)
#define PINSEL0_P07_EINT2     ((unsigned int) 0x0000C000)
#define PINSEL0_P07_MASK      ((unsigned int) 0x0000C000)

#define PINSEL0_P08_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P08_TXD1      ((unsigned int) 0x00010000)
#define PINSEL0_P08_PWM4      ((unsigned int) 0x00020000)
#define PINSEL0_P08_AD11      ((unsigned int) 0x00030000)
#define PINSEL0_P08_MASK      ((unsigned int) 0x00030000)

#define PINSEL0_P09_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P09_RXD1      ((unsigned int) 0x00040000)
#define PINSEL0_P09_PWM6      ((unsigned int) 0x00080000)
#define PINSEL0_P09_EINT3     ((unsigned int) 0x000C0000)
#define PINSEL0_P09_MASK      ((unsigned int) 0x000C0000)

#define PINSEL0_P010_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P010_RTS1     ((unsigned int) 0x00100000)
#define PINSEL0_P010_CAP10    ((unsigned int) 0x00200000)
#define PINSEL0_P010_AD12     ((unsigned int) 0x00300000)
#define PINSEL0_P010_MASK     ((unsigned int) 0x00300000)

#define PINSEL0_P011_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P011_CTS1     ((unsigned int) 0x00400000)
#define PINSEL0_P011_CAP11    ((unsigned int) 0x00800000)
#define PINSEL0_P011_SCL1     ((unsigned int) 0x00C00000)
#define PINSEL0_P011_MASK     ((unsigned int) 0x00C00000)

#define PINSEL0_P012_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P012_DSR1     ((unsigned int) 0x01000000)
#define PINSEL0_P012_MAT10    ((unsigned int) 0x02000000)
#define PINSEL0_P012_AD13     ((unsigned int) 0x03000000)
#define PINSEL0_P012_MASK     ((unsigned int) 0x03000000)

#define PINSEL0_P013_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P013_DTR1     ((unsigned int) 0x04000000)
#define PINSEL0_P013_MAT11    ((unsigned int) 0x08000000)
#define PINSEL0_P013_AD14     ((unsigned int) 0x0C000000)
#define PINSEL0_P013_MASK     ((unsigned int) 0x0C000000)

#define PINSEL0_P014_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P014_DCD1     ((unsigned int) 0x10000000)
#define PINSEL0_P014_EINT1    ((unsigned int) 0x20000000)
#define PINSEL0_P014_SDA1     ((unsigned int) 0x30000000)
#define PINSEL0_P014_MASK     ((unsigned int) 0x30000000)

#define PINSEL0_P015_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P015_RI1      ((unsigned int) 0x40000000)
#define PINSEL0_P015_EINT2    ((unsigned int) 0x80000000)
#define PINSEL0_P015_AD15     ((unsigned int) 0xC0000000)
#define PINSEL0_P015_MASK     ((unsigned int) 0xC0000000)

#define PINSEL1_P016_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P016_EINT0    ((unsigned int) 0x00000001)
#define PINSEL1_P016_MAT02    ((unsigned int) 0x00000002)
#define PINSEL1_P016_CAP02    ((unsigned int) 0x00000003)
#define PINSEL1_P016_MASK     ((unsigned int) 0x00000003)

#define PINSEL1_P017_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P017_CAP12    ((unsigned int) 0x00000004)
#define PINSEL1_P017_SCK1     ((unsigned int) 0x00000008)
#define PINSEL1_P017_MAT12    ((unsigned int) 0x0000000c)
#define PINSEL1_P017_MASK     ((unsigned int) 0x0000000c)

#define PINSEL1_P018_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P018_CAP13    ((unsigned int) 0x00000010)
#define PINSEL1_P018_MISO1    ((unsigned int) 0x00000020)
#define PINSEL1_P018_MAT13    ((unsigned int) 0x00000030)
#define PINSEL1_P018_MASK     ((unsigned int) 0x00000030)

#define PINSEL1_P019_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P019_MAT12    ((unsigned int) 0x00000040)
#define PINSEL1_P019_MOSI1    ((unsigned int) 0x00000080)
#define PINSEL1_P019_CAP12    ((unsigned int) 0x000000c0)

#define PINSEL1_P020_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P020_MAT13    ((unsigned int) 0x00000100)
#define PINSEL1_P020_SSEL1    ((unsigned int) 0x00000200)
#define PINSEL1_P020_EINT3    ((unsigned int) 0x00000300)
#define PINSEL1_P020_MASK     ((unsigned int) 0x00000300)

#define PINSEL1_P021_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P021_PWM5     ((unsigned int) 0x00000400)
#define PINSEL1_P021_AD16     ((unsigned int) 0x00000800)
#define PINSEL1_P021_CAP13    ((unsigned int) 0x00000c00)
#define PINSEL1_P021_MASK     ((unsigned int) 0x00000c00)

#define PINSEL1_P022_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P022_AD17     ((unsigned int) 0x00001000)
#define PINSEL1_P022_CAP00    ((unsigned int) 0x00002000)
#define PINSEL1_P022_MAT00    ((unsigned int) 0x00003000)
#define PINSEL1_P022_MASK     ((unsigned int) 0x00003000)

#define PINSEL1_P023_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P023_VBUS     ((unsigned int) 0x00004000)
#define PINSEL1_P023_RSVD2    ((unsigned int) 0x00008000)
#define PINSEL1_P023_RSVD3    ((unsigned int) 0x0000c000)
#define PINSEL1_P023_MASK     ((unsigned int) 0x0000c000)

#define PINSEL1_P024_RSVD0    ((unsigned int) 0x00000000)
#define PINSEL1_P024_RSVD1    ((unsigned int) 0x00010000)
#define PINSEL1_P024_RSVD2    ((unsigned int) 0x00020000)
#define PINSEL1_P024_RSVD3    ((unsigned int) 0x00030000)
#define PINSEL1_P024_MASK     ((unsigned int) 0x00030000)

#define PINSEL1_P025_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P025_AD04     ((unsigned int) 0x00040000)
#define PINSEL1_P025_AOUT     ((unsigned int) 0x00080000)
#define PINSEL1_P025_RSVD3    ((unsigned int) 0x000c0000)
#define PINSEL1_P025_MASK     ((unsigned int) 0x000c0000)

#define PINSEL1_P026_RSVD0    ((unsigned int) 0x00000000)
#define PINSEL1_P026_RSVD1    ((unsigned int) 0x00100000)
#define PINSEL1_P026_RSVD2    ((unsigned int) 0x00200000)
#define PINSEL1_P026_RSVD3    ((unsigned int) 0x00300000)
#define PINSEL1_P026_MASK     ((unsigned int) 0x00300000)

#define PINSEL1_P027_RSVD0    ((unsigned int) 0x00000000)
#define PINSEL1_P027_RSVD1    ((unsigned int) 0x00400000)
#define PINSEL1_P027_RSVD2    ((unsigned int) 0x00800000)
#define PINSEL1_P027_RSVD3    ((unsigned int) 0x00c00000)
#define PINSEL1_P027_MASK     ((unsigned int) 0x00c00000)

#define PINSEL1_P028_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P028_AD01     ((unsigned int) 0x01000000)
#define PINSEL1_P028_CAP02    ((unsigned int) 0x02000000)
#define PINSEL1_P028_MAT02    ((unsigned int) 0x03000000)
#define PINSEL1_P028_MASK     ((unsigned int) 0x03000000)

#define PINSEL1_P029_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P029_AD02     ((unsigned int) 0x04000000)
#define PINSEL1_P029_CAP03    ((unsigned int) 0x08000000)
#define PINSEL1_P029_MAT03    ((unsigned int) 0x0c000000)
#define PINSEL1_P029_MASK     ((unsigned int) 0x0c000000)

#define PINSEL1_P030_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P030_AD03     ((unsigned int) 0x10000000)
#define PINSEL1_P030_EINT3    ((unsigned int) 0x20000000)
#define PINSEL1_P030_CAP00    ((unsigned int) 0x30000000)
#define PINSEL1_P030_MASK     ((unsigned int) 0x30000000)

#define PINSEL1_P031_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P031_UPLED    ((unsigned int) 0x40000000)
#define PINSEL1_P031_CONNECT  ((unsigned int) 0x80000000)
#define PINSEL1_P031_RSVD3    ((unsigned int) 0xc0000000)
#define PINSEL1_P031_MASK     ((unsigned int) 0xc0000000)

#define PINSEL2_P13626_GPIO   ((unsigned int) 0x00000000) 
#define PINSEL2_P13626_DEBUG  ((unsigned int) 0x00000004) 
#define PINSEL2_P13626_MASK   ((unsigned int) 0x00000004)

#define PINSEL2_P12516_GPIO   ((unsigned int) 0x00000000) 
#define PINSEL2_P12516_TRACE  ((unsigned int) 0x00000008) 
#define PINSEL2_P12516_MASK   ((unsigned int) 0x00000008)

/* General Purpose Input/Output (GPIO) */
/* Fast I/O setup */

#define FIO_BASE_ADDR		0x50014000

#define FIO0DIR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x00)) 
#define FIO0MASK       (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x10))
#define FIO0PIN        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x14))
#define FIO0SET        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x18))
#define FIO0CLR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x1C))

#ifdef LPC1766_UM_DEFS
/* Fast GPIO Register Access */
#define FIO0SET0 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x38))
#define FIO0SET1 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x39))
#define FIO0SET2 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x3A))
#define FIO0SET3 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x3B))
#define FIO0SETL 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x38))
#define FIO0SETU 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x3A))
#endif

#define FIO1DIR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x20)) 
#define FIO1MASK       (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x30))
#define FIO1PIN        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x34))
#define FIO1SET        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x38))
#define FIO1CLR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x3C))

#ifdef LPC1766_UM_DEFS
/* Fast GPIO Register Access */
#define FIO1SET0 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x78))
#define FIO1SET1 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x79))
#define FIO1SET2 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x7A))
#define FIO1SET3 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x7B))
#define FIO1SETL 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x78))
#define FIO1SETU 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x7A))
#endif

#define FIO2DIR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x40)) 
#define FIO2MASK       (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x50))
#define FIO2PIN        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x54))
#define FIO2SET        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x58))
#define FIO2CLR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x5C))

#ifdef LPC1766_UM_DEFS
/* Fast GPIO Register Access */
#define FIO2SET0 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xB8))
#define FIO2SET1 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xB9))
#define FIO2SET2 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xBA))
#define FIO2SET3 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xBB))
#define FIO2SETL 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xB8))
#define FIO2SETU 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xBA))
#endif

#define FIO3DIR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x60)) 
#define FIO3MASK       (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x70))
#define FIO3PIN        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x74))
#define FIO3SET        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x78))
#define FIO3CLR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x7C))

#ifdef LPC1766_UM_DEFS
/* Fast GPIO Register Access */
#define FIO3SET0 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xF8))
#define FIO3SET1 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xF9))
#define FIO3SET2 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xFA))
#define FIO3SET3 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xFB))
#define FIO3SETL 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xF8))
#define FIO3SETU 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0xFA))
#endif

#define FIO4DIR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x80)) 
#define FIO4MASK       (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x90))
#define FIO4PIN        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x94))
#define FIO4SET        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x98))
#define FIO4CLR        (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x9C))

#ifdef LPC1766_UM_DEFS
/* Fast GPIO Register Access */
#define FIO4SET0 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x138))
#define FIO4SET1 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x139))
#define FIO4SET2 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x13A))
#define FIO0SET3 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x3B))
#define FIO4SET3 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x13B))
#define FIO4SETL 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x138))
#define FIO4SETU 	   (*(volatile unsigned long *)(FIO_BASE_ADDR + 0x13A))
#endif

/* General Purpose Input/Output (GPIO) */
#define GPIO_BASE_ADDR		0x40028000
#define IOPIN0         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x00))
#define IOSET0         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x04))
#define IODIR0         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x08))
#define IOCLR0         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x0C))
#define IOPIN1         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x10))
#define IOSET1         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x14))
#define IODIR1         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x18))
#define IOCLR1         (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x1C))

#define GPIO_IO_P0      ((unsigned int) 0x00000001)
#define GPIO_IO_P1      ((unsigned int) 0x00000002)
#define GPIO_IO_P2      ((unsigned int) 0x00000004)
#define GPIO_IO_P3      ((unsigned int) 0x00000008)
#define GPIO_IO_P4      ((unsigned int) 0x00000010)
#define GPIO_IO_P5      ((unsigned int) 0x00000020)
#define GPIO_IO_P6      ((unsigned int) 0x00000040)
#define GPIO_IO_P7      ((unsigned int) 0x00000080)
#define GPIO_IO_P8      ((unsigned int) 0x00000100)
#define GPIO_IO_P9      ((unsigned int) 0x00000200)
#define GPIO_IO_P10     ((unsigned int) 0x00000400)
#define GPIO_IO_P11     ((unsigned int) 0x00000800)
#define GPIO_IO_P12     ((unsigned int) 0x00001000)
#define GPIO_IO_P13     ((unsigned int) 0x00002000)
#define GPIO_IO_P14     ((unsigned int) 0x00004000)
#define GPIO_IO_P15     ((unsigned int) 0x00008000)
#define GPIO_IO_P16     ((unsigned int) 0x00010000)
#define GPIO_IO_P17     ((unsigned int) 0x00020000)
#define GPIO_IO_P18     ((unsigned int) 0x00040000)
#define GPIO_IO_P19     ((unsigned int) 0x00080000)
#define GPIO_IO_P20     ((unsigned int) 0x00100000)
#define GPIO_IO_P21     ((unsigned int) 0x00200000)
#define GPIO_IO_P22     ((unsigned int) 0x00400000)
#define GPIO_IO_P23     ((unsigned int) 0x00800000)
#define GPIO_IO_P24     ((unsigned int) 0x01000000)
#define GPIO_IO_P25     ((unsigned int) 0x02000000)
#define GPIO_IO_P26     ((unsigned int) 0x04000000)
#define GPIO_IO_P27     ((unsigned int) 0x08000000)
#define GPIO_IO_P28     ((unsigned int) 0x10000000)
#define GPIO_IO_P29     ((unsigned int) 0x20000000)
#define GPIO_IO_P30     ((unsigned int) 0x40000000)
#define GPIO_IO_P31     ((unsigned int) 0x80000000)
#define GPIO_IO_JTAG    ((unsigned int) 0x003E0000)

/* GPIO Interrupt Registers */
#define IO0_INT_EN_R    (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x90)) 
#define IO0_INT_EN_F    (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x94))
#define IO0_INT_STAT_R  (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x84))
#define IO0_INT_STAT_F  (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x88))
#define IO0_INT_CLR     (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x8C))

#define IO2_INT_EN_R    (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0xB0)) 
#define IO2_INT_EN_F    (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0xB4))
#define IO2_INT_STAT_R  (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0xA4))
#define IO2_INT_STAT_F  (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0xA8))
#define IO2_INT_CLR     (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0xAC))

#define IO_INT_STAT     (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x80))

#define PARTCFG_BASE_ADDR		0x3FFF8000
#define PARTCFG        (*(volatile unsigned long *)(PARTCFG_BASE_ADDR + 0x00)) 

/* System Control Block(SCB) modules include Memory Accelerator Module,
Phase Locked Loop, VPB divider, Power Control, External Interrupt, 
Reset, and Code Security/Debugging */
#define SCB_BASE_ADDR   0x400FC000

/* Memory Accelerator Module */

/* Phase Locked Loop (PLL0) */
#define PLL0CON        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x080))
#define PLL0CFG        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x084))
#define PLL0STAT       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x088))
#define PLL0FEED       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x08C))

/* Phase Locked Loop (PLL1) */
#define PLL1CON        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0A0))
#define PLL1CFG        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0A4))
#define PLL1STAT       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0A8))
#define PLL1FEED       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0AC))

#define PLLCON_PLLE     0x00000001
#define PLLCON_PLLC     0x00000002
#define PLLCON_MASK     0x00000003

#define PLLCFG_MUL1     0x00000000
#define PLLCFG_MUL2     0x00000001
#define PLLCFG_MUL3     0x00000002
#define PLLCFG_MUL4     0x00000003
#define PLLCFG_MUL5     0x00000004
#define PLLCFG_MUL6     0x00000005
#define PLLCFG_MUL7     0x00000006
#define PLLCFG_MUL8     0x00000007
#define PLLCFG_MUL9     0x00000008
#define PLLCFG_MUL10    0x00000009
#define PLLCFG_MUL11    0x0000000A
#define PLLCFG_MUL12    0x0000000B
#define PLLCFG_MUL13    0x0000000C
#define PLLCFG_MUL14    0x0000000D
#define PLLCFG_MUL15    0x0000000E
#define PLLCFG_MUL16    0x0000000F
#define PLLCFG_MUL17    0x00000010
#define PLLCFG_MUL18    0x00000011
#define PLLCFG_MUL19    0x00000012
#define PLLCFG_MUL20    0x00000013
#define PLLCFG_MUL21    0x00000014
#define PLLCFG_MUL22    0x00000015
#define PLLCFG_MUL23    0x00000016
#define PLLCFG_MUL24    0x00000017
#define PLLCFG_MUL25    0x00000018
#define PLLCFG_MUL26    0x00000019
#define PLLCFG_MUL27    0x0000001A
#define PLLCFG_MUL28    0x0000001B
#define PLLCFG_MUL29    0x0000001C
#define PLLCFG_MUL30    0x0000001D
#define PLLCFG_MUL31    0x0000001E
#define PLLCFG_MUL32    0x0000001F
#define PLLCFG_MUL33    0x00000020
#define PLLCFG_MUL34    0x00000021
#define PLLCFG_MUL35    0x00000022
#define PLLCFG_MUL36    0x00000023

#define PLLCFG_DIV1     0x00000000
#define PLLCFG_DIV2     0x00010000
#define PLLCFG_DIV3     0x00020000
#define PLLCFG_DIV4     0x00030000
#define PLLCFG_DIV5     0x00040000
#define PLLCFG_DIV6     0x00050000
#define PLLCFG_DIV7     0x00060000
#define PLLCFG_DIV8     0x00070000
#define PLLCFG_DIV9     0x00080000
#define PLLCFG_DIV10    0x00090000
#define PLLCFG_MASK		0x00FF7FFF

#define PLLSTAT_MSEL_MASK	0x00007FFF
#define PLLSTAT_NSEL_MASK	0x00FF0000

#define PLLSTAT_PLLE	(1 << 24)
#define PLLSTAT_PLLC	(1 << 25)
#define PLLSTAT_PLOCK	(1 << 26)

#define PLLFEED_FEED1   0x000000AA
#define PLLFEED_FEED2   0x00000055

/* Power Control */
#define PCON           (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0C0))
#define PCONP          (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0C4))

#define PCON_IDL        0x00000001
#define PCON_PD         0x00000002
#define PCON_PDBOD      0x00000004
#define PCON_BODPDM     0x00000008
#define PCON_BOGD       0x00000010
#define PCON_BORD       0x00000020
#define PCON_MASK       0x0000003F

#define PCONP_PCTIM0    0x00000002
#define PCONP_PCTIM1    0x00000004
#define PCONP_PCUART0   0x00000008
#define PCONP_PCUART1   0x00000010
#define PCONP_PCPWM1    0x00000040
#define PCONP_PCI2C0    0x00000080
#define PCONP_PCSPI     0x00000100
#define PCONP_PCRTC     0x00000200
#define PCONP_PCSSP1    0x00000400
#define PCONP_PCAD      0x00001000
#define PCONP_PCCAN1    0x00002000
#define PCONP_PCCAN2    0x00004000
#define PCONP_PCGPIO    0x00008000
#define PCONP_PCRIT     0x00010000
#define PCONP_PCMCPWM   0x00020000
#define PCONP_PCQEI     0x00040000
#define PCONP_PCI2C1    0x00080000
#define PCONP_PCSSP0    0x00200000
#define PCONP_PCTIM2    0x00400000
#define PCONP_PCTIM3    0x00800000
#define PCONP_PCUART2   0x01000000
#define PCONP_PCUART3   0x02000000
#define PCONP_PCI2C2    0x04000000
#define PCONP_PCI2S     0x08000000
#define PCONP_PCGPDMA   0x20000000
#define PCONP_PCENET    0x40000000
#define PCONP_PCUSB     0x80000000
#define PCONP_MASK      0x801817BE

// Each peripheral clock source uses 2 bits
#define PCLK_25         0x0				// divide by 4
#define PCLK_100        0x1				// divide by 1
#define PCLK_50         0x2				// divide by 2
#define PCLK_RSVD       0x3				// divide by 8*
#define PCLK_MASK       0x3

#define EXTINT_EINT0    0x00000001
#define EXTINT_EINT1    0x00000002
#define EXTINT_EINT2    0x00000004
#define EXTINT_EINT3    0x00000008
#define EXTINT_MASK     0x0000000F

#define INTWAKE_EINT0   0x00000001
#define INTWAKE_EINT1   0x00000002
#define INTWAKE_EINT2   0x00000004
#define INTWAKE_EINT3   0x00000008
#define INTWAKE_USB     0x00000020
#define INTWAKE_BOD     0x00004000
#define INTWAKE_RTC     0x00008000
#define INTWAKE_MASK    0x0000C02F

#define EXTMODE_EINT0   0x00000001
#define EXTMODE_EINT1   0x00000002
#define EXTMODE_EINT2   0x00000004
#define EXTMODE_EINT3   0x00000008
#define EXTMODE_MASK    0x0000000F

#define EXTPOLAR_EINT0  0x00000001
#define EXTPOLAR_EINT1  0x00000002
#define EXTPOLAR_EINT2  0x00000004
#define EXTPOLAR_EINT3  0x00000008
#define EXTPOLAR_MASK   0x0000000F

#define RSIR_POR        0x00000001
#define RSIR_EXTR       0x00000002
#define RSIR_WDTR       0x00000004
#define RSIR_BODR       0x00000008
#define RSIR_MASK       0x0000000F

#define SCS_GPIO0M      0x00000001
#define SCS_GPIO1M      0x00000002
#define SCS_MASK        0x00000003

/* Clock Divider */
// #define APBDIV         (*(volatile unsigned long *)(BASE_ADDR + 0x100))
#define CCLKCFG        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x104))
#define USBCLKCFG      (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x108))
#define CLKSRCSEL      (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x10C))
#define PCLKSEL0       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1A8))
#define PCLKSEL1       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1AC))
	
/* External Interrupts */
#define EXTINT         (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x140))
#define INTWAKE        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x144))
#define EXTMODE        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x148))
#define EXTPOLAR       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x14C))

/* Reset, reset source identification */
#define RSIR           (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x180))

/* RSID, code security protection */
#define CSPR           (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x184))

/* AHB configuration */
#define AHBCFG1        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x188))
#define AHBCFG2        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x18C))

/* System Controls and Status */
#define SCS            (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1A0))	

/* MPMC(EMC) registers, note: all the external memory controller(EMC) registers 
are for LPC24xx only. */
#define STATIC_MEM0_BASE		0x80000000
#define STATIC_MEM1_BASE		0x81000000
#define STATIC_MEM2_BASE		0x82000000
#define STATIC_MEM3_BASE		0x83000000

#define DYNAMIC_MEM0_BASE		0xA0000000
#define DYNAMIC_MEM1_BASE		0xB0000000
#define DYNAMIC_MEM2_BASE		0xC0000000
#define DYNAMIC_MEM3_BASE		0xD0000000

/* External Memory Controller (EMC) */
#define EMC_BASE_ADDR		0xFFE08000
#define EMC_CTRL       (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x000))
#define EMC_STAT       (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x004))
#define EMC_CONFIG     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x008))

/* Dynamic RAM access registers */
#define EMC_DYN_CTRL     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x020))
#define EMC_DYN_RFSH     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x024))
#define EMC_DYN_RD_CFG   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x028))
#define EMC_DYN_RP       (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x030))
#define EMC_DYN_RAS      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x034))
#define EMC_DYN_SREX     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x038))
#define EMC_DYN_APR      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x03C))
#define EMC_DYN_DAL      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x040))
#define EMC_DYN_WR       (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x044))
#define EMC_DYN_RC       (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x048))
#define EMC_DYN_RFC      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x04C))
#define EMC_DYN_XSR      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x050))
#define EMC_DYN_RRD      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x054))
#define EMC_DYN_MRD      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x058))

#define EMC_DYN_CFG0     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x100))
#define EMC_DYN_RASCAS0  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x104))
#define EMC_DYN_CFG1     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x120))
#define EMC_DYN_RASCAS1  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x124))
#define EMC_DYN_CFG2     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x140))
#define EMC_DYN_RASCAS2  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x144))
#define EMC_DYN_CFG3     (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x160))
#define EMC_DYN_RASCAS3  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x164))

/* static RAM access registers */
#define EMC_STA_CFG0      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x200))
#define EMC_STA_WAITWEN0  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x204))
#define EMC_STA_WAITOEN0  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x208))
#define EMC_STA_WAITRD0   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x20C))
#define EMC_STA_WAITPAGE0 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x210))
#define EMC_STA_WAITWR0   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x214))
#define EMC_STA_WAITTURN0 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x218))

#define EMC_STA_CFG1      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x220))
#define EMC_STA_WAITWEN1  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x224))
#define EMC_STA_WAITOEN1  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x228))
#define EMC_STA_WAITRD1   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x22C))
#define EMC_STA_WAITPAGE1 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x230))
#define EMC_STA_WAITWR1   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x234))
#define EMC_STA_WAITTURN1 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x238))

#define EMC_STA_CFG2      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x240))
#define EMC_STA_WAITWEN2  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x244))
#define EMC_STA_WAITOEN2  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x248))
#define EMC_STA_WAITRD2   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x24C))
#define EMC_STA_WAITPAGE2 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x250))
#define EMC_STA_WAITWR2   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x254))
#define EMC_STA_WAITTURN2 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x258))

#define EMC_STA_CFG3      (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x260))
#define EMC_STA_WAITWEN3  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x264))
#define EMC_STA_WAITOEN3  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x268))
#define EMC_STA_WAITRD3   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x26C))
#define EMC_STA_WAITPAGE3 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x270))
#define EMC_STA_WAITWR3   (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x274))
#define EMC_STA_WAITTURN3 (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x278))

#define EMC_STA_EXT_WAIT  (*(volatile unsigned long *)(EMC_BASE_ADDR + 0x880))

/* Timer 0 */
#define TMR0_BASE_ADDR		0x40004000
#define T0IR           (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x00))
#define T0TCR          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x04))
#define T0TC           (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x08))
#define T0PR           (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x0C))
#define T0PC           (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x10))
#define T0MCR          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x14))
#define T0MR0          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x18))
#define T0MR1          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x1C))
#define T0MR2          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x20))
#define T0MR3          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x24))
#define T0CCR          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x28))
#define T0CR0          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x2C))
#define T0CR1          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x30))
#define T0CR2          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x34))
#define T0CR3          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x38))
#define T0EMR          (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x3C))
#define T0CTCR         (*(volatile unsigned long *)(TMR0_BASE_ADDR + 0x70))

/* Timer 1 */
#define TMR1_BASE_ADDR		0x40008000
#define T1IR           (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x00))
#define T1TCR          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x04))
#define T1TC           (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x08))
#define T1PR           (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x0C))
#define T1PC           (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x10))
#define T1MCR          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x14))
#define T1MR0          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x18))
#define T1MR1          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x1C))
#define T1MR2          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x20))
#define T1MR3          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x24))
#define T1CCR          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x28))
#define T1CR0          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x2C))
#define T1CR1          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x30))
#define T1CR2          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x34))
#define T1CR3          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x38))
#define T1EMR          (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x3C))
#define T1CTCR         (*(volatile unsigned long *)(TMR1_BASE_ADDR + 0x70))

/* Timer 2 */
#define TMR2_BASE_ADDR		0x40090000
#define T2IR           (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x00))
#define T2TCR          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x04))
#define T2TC           (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x08))
#define T2PR           (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x0C))
#define T2PC           (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x10))
#define T2MCR          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x14))
#define T2MR0          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x18))
#define T2MR1          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x1C))
#define T2MR2          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x20))
#define T2MR3          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x24))
#define T2CCR          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x28))
#define T2CR0          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x2C))
#define T2CR1          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x30))
#define T2CR2          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x34))
#define T2CR3          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x38))
#define T2EMR          (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x3C))
#define T2CTCR         (*(volatile unsigned long *)(TMR2_BASE_ADDR + 0x70))

/* Timer 3 */
#define TMR3_BASE_ADDR		0x40094000
#define T3IR           (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x00))
#define T3TCR          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x04))
#define T3TC           (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x08))
#define T3PR           (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x0C))
#define T3PC           (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x10))
#define T3MCR          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x14))
#define T3MR0          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x18))
#define T3MR1          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x1C))
#define T3MR2          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x20))
#define T3MR3          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x24))
#define T3CCR          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x28))
#define T3CR0          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x2C))
#define T3CR1          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x30))
#define T3CR2          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x34))
#define T3CR3          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x38))
#define T3EMR          (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x3C))
#define T3CTCR         (*(volatile unsigned long *)(TMR3_BASE_ADDR + 0x70))

#define T_IR_MR0            0x00000001
#define T_IR_MR1            0x00000002
#define T_IR_MR2            0x00000004
#define T_IR_MR3            0x00000008
#define T_IR_CR0            0x00000010
#define T_IR_CR1            0x00000020
#define T_IR_CR2            0x00000040
#define T_IR_CR3            0x00000080
#define T_IR_MASK           0x000000FF

#define T_TCR_CE            0x00000001
#define T_TCR_CR            0x00000002

#define T_CTCR_MODE_PCLK    0x00000000
#define T_CTCR_MODE_CAPRISE 0x00000001
#define T_CTCR_MODE_CAPFALL 0x00000002
#define T_CTCR_MODE_CAPBOTH 0x00000003
#define T_CTCR_MODE_MASK    0x00000003
#define T_CTCR_CIS_CAPN0    0x00000000
#define T_CTCR_CIS_CAPN1    0x00000004
#define T_CTCR_CIS_CAPN2    0x00000008
#define T_CTCR_CIS_CAPN3    0x0000000C
#define T_CTCR_CIS_MASK     0x0000000C

#define T_MCR_MR0I          0x00000001
#define T_MCR_MR0R          0x00000002
#define T_MCR_MR0S          0x00000004
#define T_MCR_MR1I          0x00000008
#define T_MCR_MR1R          0x00000010
#define T_MCR_MR1S          0x00000020
#define T_MCR_MR2I          0x00000040
#define T_MCR_MR2R          0x00000080
#define T_MCR_MR2S          0x00000100
#define T_MCR_MR3I          0x00000200
#define T_MCR_MR3R          0x00000400
#define T_MCR_MR3S          0x00000800

#define T_CCR_CAP0RE        0x00000001
#define T_CCR_CAP0FE        0x00000002
#define T_CCR_CAP0I         0x00000004
#define T_CCR_CAP1RE        0x00000008
#define T_CCR_CAP1FE        0x00000010
#define T_CCR_CAP1I         0x00000020
#define T_CCR_CAP2RE        0x00000040
#define T_CCR_CAP2FE        0x00000080
#define T_CCR_CAP2I         0x00000100
#define T_CCR_CAP3RE        0x00000200
#define T_CCR_CAP3FE        0x00000400
#define T_CCR_CAP3I         0x00000800

#define T_EMR_EM0           0x00000001
#define T_EMR_EM1           0x00000002
#define T_EMR_EM2           0x00000004
#define T_EMR_EM3           0x00000008
#define T_EMR_EMC0_NONE     0x00000000
#define T_EMR_EMC0_CLEAR    0x00000010
#define T_EMR_EMC0_SET      0x00000020
#define T_EMR_EMC0_TOGGLE   0x00000030
#define T_EMR_EMC0_MASK     0x00000030
#define T_EMR_EMC1_NONE     0x00000000
#define T_EMR_EMC1_CLEAR    0x00000040
#define T_EMR_EMC1_SET      0x00000080
#define T_EMR_EMC1_TOGGLE   0x000000C0
#define T_EMR_EMC1_MASK     0x000000C0
#define T_EMR_EMC2_NONE     0x00000000
#define T_EMR_EMC2_CLEAR    0x00000100
#define T_EMR_EMC2_SET      0x00000200
#define T_EMR_EMC2_TOGGLE   0x00000300
#define T_EMR_EMC2_MASK     0x00000300
#define T_EMR_EMC3_NONE     0x00000000
#define T_EMR_EMC3_CLEAR    0x00000400
#define T_EMR_EMC3_SET      0x00000800
#define T_EMR_EMC3_TOGGLE   0x00000C00
#define T_EMR_EMC3_MASK     0x00000C00

/* Pulse Width Modulator (PWM1) */
#define PWM1_BASE_ADDR		0x40018000
#define PWM1IR          (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x00))
#define PWM1TCR         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x04))
#define PWM1TC          (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x08))
#define PWM1PR          (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x0C))
#define PWM1PC          (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x10))
#define PWM1MCR         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x14))
#define PWM1MR0         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x18))
#define PWM1MR1         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x1C))
#define PWM1MR2         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x20))
#define PWM1MR3         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x24))
#define PWM1CCR         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x28))
#define PWM1CR0         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x2C))
#define PWM1CR1         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x30))
#define PWM1CR2         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x34))
#define PWM1CR3         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x38))
#define PWM1EMR         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x3C))
#define PWM1MR4         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x40))
#define PWM1MR5         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x44))
#define PWM1MR6         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x48))
#define PWM1PCR         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x4C))
#define PWM1LER         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x50))
#define PWM1CTCR        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x70))

/* Universal Asynchronous Receiver Transmitter 0 (UART0) */
#define UART0_BASE_ADDR		0x4000C000
#define U0RBR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x00))
#define U0THR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x00))
#define U0DLL          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x00))
#define U0DLM          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x04))
#define U0IER          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x04))
#define U0IIR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x08))
#define U0FCR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x08))
#define U0LCR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x0C))
#define U0LSR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x14))
#define U0SCR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x1C))
#define U0ACR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x20))
#define U0ICR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x24))
#define U0FDR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x28))
#define U0TER          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x30))

#define UART0_RBR       U0RBR
#define UART0_THR       U0THR
#define UART0_IER       U0IER
#define UART0_IIR       U0IIR
#define UART0_FCR       U0FCR
#define UART0_LCR       U0LCR
#define UART0_LSR       U0LSR
#define UART0_SCR       U0SCR
#define UART0_ACR       U0ACR
#define UART0_FDR       U0FDR
#define UART0_TER       U0TER
#define UART0_DLL       U0DLL
#define UART0_DLM       U0DLM

/* Universal Asynchronous Receiver Transmitter 1 (UART1) */
#define UART1_BASE_ADDR		0x40010000
#define U1RBR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x00))
#define U1THR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x00))
#define U1DLL          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x00))
#define U1DLM          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x04))
#define U1IER          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x04))
#define U1IIR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x08))
#define U1FCR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x08))
#define U1LCR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x0C))
#define U1MCR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x10))
#define U1LSR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x14))
#define U1MSR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x18))
#define U1SCR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x1C))
#define U1ACR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x20))
#define U1FDR          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x28))
#define U1TER          (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x30))

#define UART1_RBR       U1RBR
#define UART1_THR       U1THR
#define UART1_IER       U1IER
#define UART1_IIR       U1IIR
#define UART1_FCR       U1FCR
#define UART1_LCR       U1LCR
#define UART1_LSR       U1LSR
#define UART1_SCR       U1SCR
#define UART1_ACR       U1ACR
#define UART1_FDR       U1FDR
#define UART1_TER       U1TER
#define UART1_DLL       U1DLL
#define UART1_DLM       U1DLM
#define UART1_MCR       U1MCR
#define UART1_MSR       U1MSR

/* Universal Asynchronous Receiver Transmitter 2 (UART2) */
#define UART2_BASE_ADDR		0x40098000
#define U2RBR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x00))
#define U2THR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x00))
#define U2DLL          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x00))
#define U2DLM          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x04))
#define U2IER          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x04))
#define U2IIR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x08))
#define U2FCR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x08))
#define U2LCR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x0C))
#define U2LSR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x14))
#define U2SCR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x1C))
#define U2ACR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x20))
#define U2ICR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x24))
#define U2FDR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x28))
#define U2TER          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x30))

/* Universal Asynchronous Receiver Transmitter 3 (UART3) */
#define UART3_BASE_ADDR		0x4009C000
#define U3RBR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x00))
#define U3THR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x00))
#define U3DLL          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x00))
#define U3DLM          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x04))
#define U3IER          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x04))
#define U3IIR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x08))
#define U3FCR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x08))
#define U3LCR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x0C))
#define U3LSR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x14))
#define U3SCR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x1C))
#define U3ACR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x20))
#define U3ICR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x24))
#define U3FDR          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x28))
#define U3TER          (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x30))

#define UART_LCR_DLAB   0x00000080
#define UART_LCR_NOPAR  0x00000000
#define UART_LCR_1STOP  0x00000000
#define UART_LCR_8BITS  0x00000003
#define UART_IER_EI     0x00000003
#define UART_FCR_EN     0x00000001
#define UART_FCR_CLR    0x00000006

/* I2C Interface 0 */
#define I2C0_BASE_ADDR		0x4001C000
#define I20CONSET      (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x00))
#define I20STAT        (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x04))
#define I20DAT         (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x08))
#define I20ADR         (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x0C))
#define I20SCLH        (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x10))
#define I20SCLL        (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x14))
#define I20CONCLR      (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x18))

/* I2C Interface 1 */
#define I2C1_BASE_ADDR		0x4005C000
#define I21CONSET      (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x00))
#define I21STAT        (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x04))
#define I21DAT         (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x08))
#define I21ADR         (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x0C))
#define I21SCLH        (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x10))
#define I21SCLL        (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x14))
#define I21CONCLR      (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x18))

/* I2C Interface 2 */
#define I2C2_BASE_ADDR		0x400A000
#define I22CONSET      (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x00))
#define I22STAT        (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x04))
#define I22DAT         (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x08))
#define I22ADR         (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x0C))
#define I22SCLH        (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x10))
#define I22SCLL        (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x14))
#define I22CONCLR      (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x18))

/* SPI0 (Serial Peripheral Interface 0) */
#define SPI0_BASE_ADDR		0x40020000
#define S0SPCR         (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x00))
#define S0SPSR         (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x04))
#define S0SPDR         (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x08))
#define S0SPCCR        (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x0C))
#define S0SPINT        (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x1C))

/* SSP0 Controller */
#define SSP0_BASE_ADDR		0x40088000
#define SSP0CR0        (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x00))
#define SSP0CR1        (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x04))
#define SSP0DR         (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x08))
#define SSP0SR         (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x0C))
#define SSP0CPSR       (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x10))
#define SSP0IMSC       (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x14))
#define SSP0RIS        (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x18))
#define SSP0MIS        (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x1C))
#define SSP0ICR        (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x20))
#define SSP0DMACR      (*(volatile unsigned long *)(SSP0_BASE_ADDR + 0x24))

/* SSP1 Controller */
#define SSP1_BASE_ADDR		0x40030000
#define SSP1CR0        (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x00))
#define SSP1CR1        (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x04))
#define SSP1DR         (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x08))
#define SSP1SR         (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x0C))
#define SSP1CPSR       (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x10))
#define SSP1IMSC       (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x14))
#define SSP1RIS        (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x18))
#define SSP1MIS        (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x1C))
#define SSP1ICR        (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x20))
#define SSP1DMACR      (*(volatile unsigned long *)(SSP1_BASE_ADDR + 0x24))

/* Real Time Clock */
#define RTC_BASE_ADDR		0x40024000
#define RTC_ILR         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x00))
#define RTC_CTC         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x04))
#define RTC_CCR         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x08))
#define RTC_CIIR        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x0C))
#define RTC_AMR         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x10))
#define RTC_CTIME0      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x14))
#define RTC_CTIME1      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x18))
#define RTC_CTIME2      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x1C))

#define RTC_SEC         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x20))
#define RTC_MIN         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x24))
#define RTC_HOUR        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x28))
#define RTC_DOM         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x2C))
#define RTC_DOW         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x30))
#define RTC_DOY         (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x34))
#define RTC_MONTH       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x38))
#define RTC_YEAR        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x3C))

#define RTC_CISS        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x40))
#define RTC_GPREG0      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x44))
#define RTC_GPREG1      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x48))
#define RTC_GPREG2      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x4C))
#define RTC_GPREG3      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x50))
#define RTC_GPREG4      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x54))
#define RTC_WAKEUPDIS   (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x58))
#define RTC_PWRCTRL     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x5C))

#define RTC_ALSEC       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x60))
#define RTC_ALMIN       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x64))
#define RTC_ALHOUR      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x68))
#define RTC_ALDOM       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x6C))
#define RTC_ALDOW       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x70))
#define RTC_ALDOY       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x74))
#define RTC_ALMON       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x78))
#define RTC_ALYEAR      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x7C))
#define RTC_PREINT      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x80))
#define RTC_PREFRAC     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x84))

#define RTC_ILR_RTCCIF  0x00000001
#define RTC_ILR_RTCALF  0x00000002
#define RTC_ILR_MASK    0x00000003

#define RTC_CCR_CLKEN   0x00000001
#define RTC_CCR_CTCRST  0x00000002
#define RTC_CCR_TEST    0x0000000c
#define RTC_CCR_CLKSRC  0x00000010

#define RTC_CIIR_IMSEC  0x00000001
#define RTC_CIIR_IMMIN  0x00000002
#define RTC_CIIR_IMHOUR 0x00000004
#define RTC_CIIR_IMDOM  0x00000008
#define RTC_CIIR_IMDOW  0x00000010
#define RTC_CIIR_IMDOY  0x00000020
#define RTC_CIIR_IMMON  0x00000040
#define RTC_CIIR_IMYEAR 0x00000080
#define RTC_CIIR_IMMASK 0x000000FF

#define RTC_AMR_AMRSEC  0x00000001
#define RTC_AMR_AMRMIN  0x00000002
#define RTC_AMR_AMRHOUR 0x00000004
#define RTC_AMR_AMRDOM  0x00000008
#define RTC_AMR_AMRDOW  0x00000010
#define RTC_AMR_AMRDOY  0x00000020
#define RTC_AMR_AMRMON  0x00000040
#define RTC_AMR_AMRYEAR 0x00000080
#define RTC_AMR_AMRMASK 0x000000FF

typedef struct __attribute__ ((packed)) 
{
  union
  {
    struct
    {
      unsigned int counter   : 14;
      unsigned int rsvd15_31 : 18;
    };

    unsigned int i;
  };
}
rtcCTC_t;

typedef struct __attribute__ ((packed)) 
{
  union
  {
    struct 
    {
      unsigned int seconds   : 6;
      unsigned int rsvd7_6   : 2;
      unsigned int minutes   : 6;
      unsigned int rsvd14_15 : 2;
      unsigned int hours     : 5;
      unsigned int rsvd21_23 : 3;
      unsigned int dow       : 3;
      unsigned int rsvd27_31 : 5;
    };

    unsigned int i;
  };
}
rtcCTIME0_t;

typedef struct __attribute__ ((packed)) 
{
  union
  {
    struct
    {
      unsigned int dom       : 5;
      unsigned int rsvd5_7   : 3;
      unsigned int month     : 4;
      unsigned int rsvd12_15 : 4;
      unsigned int year      : 12;
      unsigned int rsvd28_31 : 4;
    };

    unsigned int i;
  };
}
rtcCTIME1_t;

typedef struct __attribute__ ((packed)) 
{
  union
  {
    struct 
    {
      unsigned int doy       : 12;
      unsigned int rsvd12_31 : 20;
    };

    unsigned int i;
  };
}
rtcCTIME2_t;

/* A/D Converter 0 (AD0) */
#define AD0_BASE_ADDR		0x40034000
#define AD0CR          (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x00))
#define AD0GDR         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x04))
#define AD0INTEN       (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x0C))
#define AD0DR0         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x10))
#define AD0DR1         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x14))
#define AD0DR2         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x18))
#define AD0DR3         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x1C))
#define AD0DR4         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x20))
#define AD0DR5         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x24))
#define AD0DR6         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x28))
#define AD0DR7         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x2C))
#define AD0STAT        (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x30))

/* D/A Converter */
#define DAC_BASE_ADDR		0x4008C000
#define DACR           (*(volatile unsigned long *)(DAC_BASE_ADDR + 0x00))

/* Watchdog */
#define WDG_BASE_ADDR		0x40000000
#define WDMOD          (*(volatile unsigned long *)(WDG_BASE_ADDR + 0x00))
#define WDTC           (*(volatile unsigned long *)(WDG_BASE_ADDR + 0x04))
#define WDFEED         (*(volatile unsigned long *)(WDG_BASE_ADDR + 0x08))
#define WDTV           (*(volatile unsigned long *)(WDG_BASE_ADDR + 0x0C))
#define WDCLKSEL       (*(volatile unsigned long *)(WDG_BASE_ADDR + 0x10))

/* CAN CONTROLLERS AND ACCEPTANCE FILTER */
#define CAN_ACCEPT_BASE_ADDR		0x4003C000
#define CAN_AFMR		(*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x00))  	
#define CAN_SFF_SA 		(*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x04))  	
#define CAN_SFF_GRP_SA 	(*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x08))
#define CAN_EFF_SA 		(*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x0C))
#define CAN_EFF_GRP_SA 	(*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x10))  	
#define CAN_EOT 		(*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x14))
#define CAN_LUT_ERR_ADR (*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x18))  	
#define CAN_LUT_ERR 	(*(volatile unsigned long *)(CAN_ACCEPT_BASE_ADDR + 0x1C))

#define CAN_CENTRAL_BASE_ADDR		0xE0040000  	
#define CAN_TX_SR 	(*(volatile unsigned long *)(CAN_CENTRAL_BASE_ADDR + 0x00))  	
#define CAN_RX_SR 	(*(volatile unsigned long *)(CAN_CENTRAL_BASE_ADDR + 0x04))  	
#define CAN_MSR 	(*(volatile unsigned long *)(CAN_CENTRAL_BASE_ADDR + 0x08))

#define CAN1_BASE_ADDR		0x40044000
#define CAN1MOD 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x00))  	
#define CAN1CMR 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x04))  	
#define CAN1GSR 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x08))  	
#define CAN1ICR 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x0C))  	
#define CAN1IER 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x10))
#define CAN1BTR 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x14))  	
#define CAN1EWL 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x18))  	
#define CAN1SR 		(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x1C))  	
#define CAN1RFS 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x20))  	
#define CAN1RID 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x24))
#define CAN1RDA 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x28))  	
#define CAN1RDB 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x2C))
  	
#define CAN1TFI1 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x30))  	
#define CAN1TID1 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x34))  	
#define CAN1TDA1 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x38))
#define CAN1TDB1 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x3C))  	
#define CAN1TFI2 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x40))  	
#define CAN1TID2 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x44))  	
#define CAN1TDA2 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x48))  	
#define CAN1TDB2 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x4C))
#define CAN1TFI3 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x50))  	
#define CAN1TID3 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x54))  	
#define CAN1TDA3 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x58))  	
#define CAN1TDB3 	(*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x5C))

#define CAN2_BASE_ADDR		0x40048000
#define CAN2MOD 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x00))  	
#define CAN2CMR 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x04))  	
#define CAN2GSR 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x08))  	
#define CAN2ICR 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x0C))  	
#define CAN2IER 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x10))
#define CAN2BTR 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x14))  	
#define CAN2EWL 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x18))  	
#define CAN2SR 		(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x1C))  	
#define CAN2RFS 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x20))  	
#define CAN2RID 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x24))
#define CAN2RDA 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x28))  	
#define CAN2RDB 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x2C))
  	
#define CAN2TFI1 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x30))  	
#define CAN2TID1 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x34))  	
#define CAN2TDA1 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x38))
#define CAN2TDB1 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x3C))  	
#define CAN2TFI2 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x40))  	
#define CAN2TID2 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x44))  	
#define CAN2TDA2 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x48))  	
#define CAN2TDB2 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x4C))
#define CAN2TFI3 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x50))  	
#define CAN2TID3 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x54))  	
#define CAN2TDA3 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x58))  	
#define CAN2TDB3 	(*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x5C))

/* I2S Interface Controller (I2S) */
#define I2S_BASE_ADDR		0x400A8000
#define I2S_DAO        (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x00))
#define I2S_DAI        (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x04))
#define I2S_TX_FIFO    (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x08))
#define I2S_RX_FIFO    (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x0C))
#define I2S_STATE      (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x10))
#define I2S_DMA1       (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x14))
#define I2S_DMA2       (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x18))
#define I2S_IRQ        (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x1C))
#define I2S_TXRATE     (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x20))
#define I2S_RXRATE     (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x24))

/* General-purpose DMA Controller */
#define DMA_BASE_ADDR		0x50004000
#define GPDMA_INT_STAT         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x000))
#define GPDMA_INT_TCSTAT       (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x004))
#define GPDMA_INT_TCCLR        (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x008))
#define GPDMA_INT_ERR_STAT     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x00C))
#define GPDMA_INT_ERR_CLR      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x010))
#define GPDMA_RAW_INT_TCSTAT   (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x014))
#define GPDMA_RAW_INT_ERR_STAT (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x018))
#define GPDMA_ENABLED_CHNS     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x01C))
#define GPDMA_SOFT_BREQ        (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x020))
#define GPDMA_SOFT_SREQ        (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x024))
#define GPDMA_SOFT_LBREQ       (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x028))
#define GPDMA_SOFT_LSREQ       (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x02C))
#define GPDMA_CONFIG           (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x030))
#define GPDMA_SYNC             (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x034))

/* DMA channel 0 registers */
#define GPDMA_CH0_SRC      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x100))
#define GPDMA_CH0_DEST     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x104))
#define GPDMA_CH0_LLI      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x108))
#define GPDMA_CH0_CTRL     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x10C))
#define GPDMA_CH0_CFG      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x110))

/* DMA channel 1 registers */
#define GPDMA_CH1_SRC      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x120))
#define GPDMA_CH1_DEST     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x124))
#define GPDMA_CH1_LLI      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x128))
#define GPDMA_CH1_CTRL     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x12C))
#define GPDMA_CH1_CFG      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x130))


/* USB Controller */
#define USB_INT_BASE_ADDR	0x400FC1C0
#define USB_BASE_ADDR		0x5000C200		/* USB Base Address */

#define USB_INT_STAT    (*(volatile unsigned long *)(USB_INT_BASE_ADDR + 0x00))

/* USB Device Interrupt Registers */
#define DEV_INT_STAT    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x00))
#define DEV_INT_EN      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x04))
#define DEV_INT_CLR     (*(volatile unsigned long *)(USB_BASE_ADDR + 0x08))
#define DEV_INT_SET     (*(volatile unsigned long *)(USB_BASE_ADDR + 0x0C))
#define DEV_INT_PRIO    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2C))

/* USB Device Endpoint Interrupt Registers */
#define EP_INT_STAT     (*(volatile unsigned long *)(USB_BASE_ADDR + 0x30))
#define EP_INT_EN       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x34))
#define EP_INT_CLR      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x38))
#define EP_INT_SET      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x3C))
#define EP_INT_PRIO     (*(volatile unsigned long *)(USB_BASE_ADDR + 0x40))

/* USB Device Endpoint Realization Registers */
#define REALIZE_EP      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x44))
#define EP_INDEX        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x48))
#define MAXPACKET_SIZE  (*(volatile unsigned long *)(USB_BASE_ADDR + 0x4C))

/* USB Device Command Reagisters */
#define CMD_CODE        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x10))
#define CMD_DATA        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x14))

/* USB Device Data Transfer Registers */
#define RX_DATA         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x18))
#define TX_DATA         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x1C))
#define RX_PLENGTH      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x20))
#define TX_PLENGTH      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x24))
#define USB_CTRL        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x28))

/* USB Device DMA Registers */
#define DMA_REQ_STAT        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x50))
#define DMA_REQ_CLR         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x54))
#define DMA_REQ_SET         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x58))
#define UDCA_HEAD           (*(volatile unsigned long *)(USB_BASE_ADDR + 0x80))
#define EP_DMA_STAT         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x84))
#define EP_DMA_EN           (*(volatile unsigned long *)(USB_BASE_ADDR + 0x88))
#define EP_DMA_DIS          (*(volatile unsigned long *)(USB_BASE_ADDR + 0x8C))
#define DMA_INT_STAT        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x90))
#define DMA_INT_EN          (*(volatile unsigned long *)(USB_BASE_ADDR + 0x94))
#define EOT_INT_STAT        (*(volatile unsigned long *)(USB_BASE_ADDR + 0xA0))
#define EOT_INT_CLR         (*(volatile unsigned long *)(USB_BASE_ADDR + 0xA4))
#define EOT_INT_SET         (*(volatile unsigned long *)(USB_BASE_ADDR + 0xA8))
#define NDD_REQ_INT_STAT    (*(volatile unsigned long *)(USB_BASE_ADDR + 0xAC))
#define NDD_REQ_INT_CLR     (*(volatile unsigned long *)(USB_BASE_ADDR + 0xB0))
#define NDD_REQ_INT_SET     (*(volatile unsigned long *)(USB_BASE_ADDR + 0xB4))
#define SYS_ERR_INT_STAT    (*(volatile unsigned long *)(USB_BASE_ADDR + 0xB8))
#define SYS_ERR_INT_CLR     (*(volatile unsigned long *)(USB_BASE_ADDR + 0xBC))
#define SYS_ERR_INT_SET     (*(volatile unsigned long *)(USB_BASE_ADDR + 0xC0))

/* USB Host and OTG registers are for LPC24xx only */
/* USB Host Controller */
#define USBHC_BASE_ADDR		0x5000C000
#define HC_REVISION         (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x00))
#define HC_CONTROL          (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x04))
#define HC_CMD_STAT         (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x08))
#define HC_INT_STAT         (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x0C))
#define HC_INT_EN           (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x10))
#define HC_INT_DIS          (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x14))
#define HC_HCCA             (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x18))
#define HC_PERIOD_CUR_ED    (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x1C))
#define HC_CTRL_HEAD_ED     (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x20))
#define HC_CTRL_CUR_ED      (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x24))
#define HC_BULK_HEAD_ED     (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x28))
#define HC_BULK_CUR_ED      (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x2C))
#define HC_DONE_HEAD        (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x30))
#define HC_FM_INTERVAL      (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x34))
#define HC_FM_REMAINING     (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x38))
#define HC_FM_NUMBER        (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x3C))
#define HC_PERIOD_START     (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x40))
#define HC_LS_THRHLD        (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x44))
#define HC_RH_DESCA         (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x48))
#define HC_RH_DESCB         (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x4C))
#define HC_RH_STAT          (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x50))
#define HC_RH_PORT_STAT1    (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x54))
#define HC_RH_PORT_STAT2    (*(volatile unsigned long *)(USBHC_BASE_ADDR + 0x58))

/* USB OTG Controller */
#define USBOTG_BASE_ADDR        0x5000C100
#define OTG_INT_STAT        (*(volatile unsigned long *)(USBOTG_BASE_ADDR + 0x00))
#define OTG_INT_EN          (*(volatile unsigned long *)(USBOTG_BASE_ADDR + 0x04))
#define OTG_INT_SET         (*(volatile unsigned long *)(USBOTG_BASE_ADDR + 0x08))
#define OTG_INT_CLR         (*(volatile unsigned long *)(USBOTG_BASE_ADDR + 0x0C))
/* On LPC17xx, the name is USBPortSel */ 
#define OTG_STAT_CTRL       (*(volatile unsigned long *)(USBOTG_BASE_ADDR + 0x10))
#define OTG_TIMER           (*(volatile unsigned long *)(USBOTG_BASE_ADDR + 0x14))

#define USBOTG_I2C_BASE_ADDR	0x5000C300
#define OTG_I2C_RX          (*(volatile unsigned long *)(USBOTG_I2C_BASE_ADDR + 0x00))
#define OTG_I2C_TX          (*(volatile unsigned long *)(USBOTG_I2C_BASE_ADDR + 0x00))
#define OTG_I2C_STS         (*(volatile unsigned long *)(USBOTG_I2C_BASE_ADDR + 0x04))
#define OTG_I2C_CTL         (*(volatile unsigned long *)(USBOTG_I2C_BASE_ADDR + 0x08))
#define OTG_I2C_CLKHI       (*(volatile unsigned long *)(USBOTG_I2C_BASE_ADDR + 0x0C))
#define OTG_I2C_CLKLO       (*(volatile unsigned long *)(USBOTG_I2C_BASE_ADDR + 0x10))

/* On LPC17xx, the names are USBClkCtrl and USBClkSt */
#define USBOTG_CLK_BASE_ADDR	0x5000CFF0
#define OTG_CLK_CTRL        (*(volatile unsigned long *)(USBOTG_CLK_BASE_ADDR + 0x04))
#define OTG_CLK_STAT        (*(volatile unsigned long *)(USBOTG_CLK_BASE_ADDR + 0x08))

/* Note: below three register name convention is for LPC17xx USB device only, match
with the spec. update in USB Device Section. */ 
#define USBPortSel          (*(volatile unsigned long *)(USBOTG_BASE_ADDR + 0x10))
#define USBClkCtrl          (*(volatile unsigned long *)(USBOTG_CLK_BASE_ADDR + 0x04))
#define USBClkSt            (*(volatile unsigned long *)(USBOTG_CLK_BASE_ADDR + 0x08))

/* Ethernet MAC (32 bit data bus) -- all registers are RW unless indicated in parentheses */
#define MAC_BASE_ADDR		0x50000000
#define MAC_MAC1            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x000)) /* MAC config reg 1 */
#define MAC_MAC2            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x004)) /* MAC config reg 2 */
#define MAC_IPGT            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x008)) /* b2b InterPacketGap reg */
#define MAC_IPGR            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x00C)) /* non b2b InterPacketGap reg */
#define MAC_CLRT            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x010)) /* CoLlision window/ReTry reg */
#define MAC_MAXF            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x014)) /* MAXimum Frame reg */
#define MAC_SUPP            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x018)) /* PHY SUPPort reg */
#define MAC_TEST            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x01C)) /* TEST reg */
#define MAC_MCFG            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x020)) /* MII Mgmt ConFiG reg */
#define MAC_MCMD            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x024)) /* MII Mgmt CoMmanD reg */
#define MAC_MADR            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x028)) /* MII Mgmt ADdRess reg */
#define MAC_MWTD            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x02C)) /* MII Mgmt WriTe Data reg (WO) */
#define MAC_MRDD            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x030)) /* MII Mgmt ReaD Data reg (RO) */
#define MAC_MIND            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x034)) /* MII Mgmt INDicators reg (RO) */

#define MAC_SA0             (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x040)) /* Station Address 0 reg */
#define MAC_SA1             (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x044)) /* Station Address 1 reg */
#define MAC_SA2             (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x048)) /* Station Address 2 reg */

#define MAC_COMMAND         (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x100)) /* Command reg */
#define MAC_STATUS          (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x104)) /* Status reg (RO) */
#define MAC_RXDESCRIPTOR    (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x108)) /* Rx descriptor base address reg */
#define MAC_RXSTATUS        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x10C)) /* Rx status base address reg */
#define MAC_RXDESCRIPTORNUM (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x110)) /* Rx number of descriptors reg */
#define MAC_RXPRODUCEINDEX  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x114)) /* Rx produce index reg (RO) */
#define MAC_RXCONSUMEINDEX  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x118)) /* Rx consume index reg */
#define MAC_TXDESCRIPTOR    (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x11C)) /* Tx descriptor base address reg */
#define MAC_TXSTATUS        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x120)) /* Tx status base address reg */
#define MAC_TXDESCRIPTORNUM (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x124)) /* Tx number of descriptors reg */
#define MAC_TXPRODUCEINDEX  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x128)) /* Tx produce index reg */
#define MAC_TXCONSUMEINDEX  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x12C)) /* Tx consume index reg (RO) */

#define MAC_TSV0            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x158)) /* Tx status vector 0 reg (RO) */
#define MAC_TSV1            (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x15C)) /* Tx status vector 1 reg (RO) */
#define MAC_RSV             (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x160)) /* Rx status vector reg (RO) */

#define MAC_FLOWCONTROLCNT  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x170)) /* Flow control counter reg */
#define MAC_FLOWCONTROLSTS  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x174)) /* Flow control status reg */

#define MAC_RXFILTERCTRL    (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x200)) /* Rx filter ctrl reg */
#define MAC_RXFILTERWOLSTS  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x204)) /* Rx filter WoL status reg (RO) */
#define MAC_RXFILTERWOLCLR  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x208)) /* Rx filter WoL clear reg (WO) */

#define MAC_HASHFILTERL     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x210)) /* Hash filter LSBs reg */
#define MAC_HASHFILTERH     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x214)) /* Hash filter MSBs reg */

#define MAC_INTSTATUS       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFE0)) /* Interrupt status reg (RO) */
#define MAC_INTENABLE       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFE4)) /* Interrupt enable reg  */
#define MAC_INTCLEAR        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFE8)) /* Interrupt clear reg (WO) */
#define MAC_INTSET          (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFEC)) /* Interrupt set reg (WO) */

#define MAC_POWERDOWN       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFF4)) /* Power-down reg */
#define MAC_MODULEID        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFFC)) /* Module ID reg (RO) */


#define FLASHCFG 			(*(volatile unsigned long * ) (0x400F C000))

#endif  // __LPC17xx_H

