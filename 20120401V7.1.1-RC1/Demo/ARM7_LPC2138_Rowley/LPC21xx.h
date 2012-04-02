// Copyright (c) 2009 Rowley Associates Limited.
//
// This file may be distributed under the terms of the License Agreement
// provided with this software.
//
// THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE
// WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.

#ifndef LPC21xx_h
#define LPC21xx_h

#define FIO_BASE 0x3FFFC000

#define FIO0DIR (*(volatile unsigned long *)0x3FFFC000)
#define FIO0DIR_OFFSET 0x0

#define FIO0DIR0 (*(volatile unsigned char *)0x3FFFC000)
#define FIO0DIR0_OFFSET 0x0

#define FIO0DIR1 (*(volatile unsigned char *)0x3FFFC001)
#define FIO0DIR1_OFFSET 0x1

#define FIO0DIR2 (*(volatile unsigned char *)0x3FFFC002)
#define FIO0DIR2_OFFSET 0x2

#define FIO0DIR3 (*(volatile unsigned char *)0x3FFFC003)
#define FIO0DIR3_OFFSET 0x3

#define FIO0DIRL (*(volatile unsigned short *)0x3FFFC000)
#define FIO0DIRL_OFFSET 0x0

#define FIO0DIRH (*(volatile unsigned short *)0x3FFFC002)
#define FIO0DIRH_OFFSET 0x2

#define FIO0MASK (*(volatile unsigned long *)0x3FFFC010)
#define FIO0MASK_OFFSET 0x10

#define FIO0MASK0 (*(volatile unsigned char *)0x3FFFC010)
#define FIO0MASK0_OFFSET 0x10

#define FIO0MASK1 (*(volatile unsigned char *)0x3FFFC011)
#define FIO0MASK1_OFFSET 0x11

#define FIO0MASK2 (*(volatile unsigned char *)0x3FFFC012)
#define FIO0MASK2_OFFSET 0x12

#define FIO0MASK3 (*(volatile unsigned char *)0x3FFFC013)
#define FIO0MASK3_OFFSET 0x13

#define FIO0MASKL (*(volatile unsigned short *)0x3FFFC010)
#define FIO0MASKL_OFFSET 0x10

#define FIO0MASKH (*(volatile unsigned short *)0x3FFFC012)
#define FIO0MASKH_OFFSET 0x12

#define FIO0PIN (*(volatile unsigned long *)0x3FFFC014)
#define FIO0PIN_OFFSET 0x14

#define FIO0PIN0 (*(volatile unsigned char *)0x3FFFC014)
#define FIO0PIN0_OFFSET 0x14

#define FIO0PIN1 (*(volatile unsigned char *)0x3FFFC015)
#define FIO0PIN1_OFFSET 0x15

#define FIO0PIN2 (*(volatile unsigned char *)0x3FFFC016)
#define FIO0PIN2_OFFSET 0x16

#define FIO0PIN3 (*(volatile unsigned char *)0x3FFFC017)
#define FIO0PIN3_OFFSET 0x17

#define FIO0PINL (*(volatile unsigned short *)0x3FFFC014)
#define FIO0PINL_OFFSET 0x14

#define FIO0PINH (*(volatile unsigned short *)0x3FFFC016)
#define FIO0PINH_OFFSET 0x16

#define FIO0SET (*(volatile unsigned long *)0x3FFFC018)
#define FIO0SET_OFFSET 0x18

#define FIO0SET0 (*(volatile unsigned char *)0x3FFFC018)
#define FIO0SET0_OFFSET 0x18

#define FIO0SET1 (*(volatile unsigned char *)0x3FFFC019)
#define FIO0SET1_OFFSET 0x19

#define FIO0SET2 (*(volatile unsigned char *)0x3FFFC01A)
#define FIO0SET2_OFFSET 0x1A

#define FIO0SET3 (*(volatile unsigned char *)0x3FFFC01B)
#define FIO0SET3_OFFSET 0x1B

#define FIO0SETL (*(volatile unsigned short *)0x3FFFC018)
#define FIO0SETL_OFFSET 0x18

#define FIO0SETH (*(volatile unsigned short *)0x3FFFC01A)
#define FIO0SETH_OFFSET 0x1A

#define FIO0CLR (*(volatile unsigned long *)0x3FFFC01C)
#define FIO0CLR_OFFSET 0x1C

#define FIO0CLR0 (*(volatile unsigned char *)0x3FFFC01C)
#define FIO0CLR0_OFFSET 0x1C

#define FIO0CLR1 (*(volatile unsigned char *)0x3FFFC01D)
#define FIO0CLR1_OFFSET 0x1D

#define FIO0CLR2 (*(volatile unsigned char *)0x3FFFC01E)
#define FIO0CLR2_OFFSET 0x1E

#define FIO0CLR3 (*(volatile unsigned char *)0x3FFFC01F)
#define FIO0CLR3_OFFSET 0x1F

#define FIO0CLRL (*(volatile unsigned short *)0x3FFFC01C)
#define FIO0CLRL_OFFSET 0x1C

#define FIO0CLRH (*(volatile unsigned short *)0x3FFFC01E)
#define FIO0CLRH_OFFSET 0x1E

#define FIO1DIR (*(volatile unsigned long *)0x3FFFC020)
#define FIO1DIR_OFFSET 0x20

#define FIO1DIR0 (*(volatile unsigned char *)0x3FFFC020)
#define FIO1DIR0_OFFSET 0x20

#define FIO1DIR1 (*(volatile unsigned char *)0x3FFFC021)
#define FIO1DIR1_OFFSET 0x21

#define FIO1DIR2 (*(volatile unsigned char *)0x3FFFC022)
#define FIO1DIR2_OFFSET 0x22

#define FIO1DIR3 (*(volatile unsigned char *)0x3FFFC023)
#define FIO1DIR3_OFFSET 0x23

#define FIO1DIRL (*(volatile unsigned short *)0x3FFFC020)
#define FIO1DIRL_OFFSET 0x20

#define FIO1DIRH (*(volatile unsigned short *)0x3FFFC022)
#define FIO1DIRH_OFFSET 0x22

#define FIO1MASK (*(volatile unsigned long *)0x3FFFC030)
#define FIO1MASK_OFFSET 0x30

#define FIO1MASK0 (*(volatile unsigned char *)0x3FFFC030)
#define FIO1MASK0_OFFSET 0x30

#define FIO1MASK1 (*(volatile unsigned char *)0x3FFFC031)
#define FIO1MASK1_OFFSET 0x31

#define FIO1MASK2 (*(volatile unsigned char *)0x3FFFC032)
#define FIO1MASK2_OFFSET 0x32

#define FIO1MASK3 (*(volatile unsigned char *)0x3FFFC033)
#define FIO1MASK3_OFFSET 0x33

#define FIO1MASKL (*(volatile unsigned short *)0x3FFFC030)
#define FIO1MASKL_OFFSET 0x30

#define FIO1MASKH (*(volatile unsigned short *)0x3FFFC032)
#define FIO1MASKH_OFFSET 0x32

#define FIO1PIN (*(volatile unsigned long *)0x3FFFC034)
#define FIO1PIN_OFFSET 0x34

#define FIO1PIN0 (*(volatile unsigned char *)0x3FFFC034)
#define FIO1PIN0_OFFSET 0x34

#define FIO1PIN1 (*(volatile unsigned char *)0x3FFFC035)
#define FIO1PIN1_OFFSET 0x35

#define FIO1PIN2 (*(volatile unsigned char *)0x3FFFC036)
#define FIO1PIN2_OFFSET 0x36

#define FIO1PIN3 (*(volatile unsigned char *)0x3FFFC037)
#define FIO1PIN3_OFFSET 0x37

#define FIO1PINL (*(volatile unsigned short *)0x3FFFC034)
#define FIO1PINL_OFFSET 0x34

#define FIO1PINH (*(volatile unsigned short *)0x3FFFC036)
#define FIO1PINH_OFFSET 0x36

#define FIO1SET (*(volatile unsigned long *)0x3FFFC038)
#define FIO1SET_OFFSET 0x38

#define FIO1SET0 (*(volatile unsigned char *)0x3FFFC038)
#define FIO1SET0_OFFSET 0x38

#define FIO1SET1 (*(volatile unsigned char *)0x3FFFC039)
#define FIO1SET1_OFFSET 0x39

#define FIO1SET2 (*(volatile unsigned char *)0x3FFFC03A)
#define FIO1SET2_OFFSET 0x3A

#define FIO1SET3 (*(volatile unsigned char *)0x3FFFC03B)
#define FIO1SET3_OFFSET 0x3B

#define FIO1SETL (*(volatile unsigned short *)0x3FFFC038)
#define FIO1SETL_OFFSET 0x38

#define FIO1SETH (*(volatile unsigned short *)0x3FFFC03A)
#define FIO1SETH_OFFSET 0x3A

#define FIO1CLR (*(volatile unsigned long *)0x3FFFC03C)
#define FIO1CLR_OFFSET 0x3C

#define FIO1CLR0 (*(volatile unsigned char *)0x3FFFC03C)
#define FIO1CLR0_OFFSET 0x3C

#define FIO1CLR1 (*(volatile unsigned char *)0x3FFFC03D)
#define FIO1CLR1_OFFSET 0x3D

#define FIO1CLR2 (*(volatile unsigned char *)0x3FFFC03E)
#define FIO1CLR2_OFFSET 0x3E

#define FIO1CLR3 (*(volatile unsigned char *)0x3FFFC03F)
#define FIO1CLR3_OFFSET 0x3F

#define FIO1CLRL (*(volatile unsigned short *)0x3FFFC03C)
#define FIO1CLRL_OFFSET 0x3C

#define FIO1CLRH (*(volatile unsigned short *)0x3FFFC03E)
#define FIO1CLRH_OFFSET 0x3E

#define WDT_BASE 0xE0000000

#define WDMOD (*(volatile unsigned long *)0xE0000000)
#define WDMOD_OFFSET 0x0
#define WDMOD_WDEN_MASK 0x1
#define WDMOD_WDEN 0x1
#define WDMOD_WDEN_BIT 0
#define WDMOD_WDRESET_MASK 0x2
#define WDMOD_WDRESET 0x2
#define WDMOD_WDRESET_BIT 1
#define WDMOD_WDTOF_MASK 0x4
#define WDMOD_WDTOF 0x4
#define WDMOD_WDTOF_BIT 2
#define WDMOD_WDINT_MASK 0x8
#define WDMOD_WDINT 0x8
#define WDMOD_WDINT_BIT 3

#define WDTC (*(volatile unsigned long *)0xE0000004)
#define WDTC_OFFSET 0x4

#define WDFEED (*(volatile unsigned long *)0xE0000008)
#define WDFEED_OFFSET 0x8

#define WDTV (*(volatile unsigned long *)0xE000000C)
#define WDTV_OFFSET 0xC

#define TIMER0_BASE 0xE0004000

#define T0IR (*(volatile unsigned char *)0xE0004000)
#define T0IR_OFFSET 0x0
#define T0IR_MR0_MASK 0x1
#define T0IR_MR0 0x1
#define T0IR_MR0_BIT 0
#define T0IR_MR1_MASK 0x2
#define T0IR_MR1 0x2
#define T0IR_MR1_BIT 1
#define T0IR_MR2_MASK 0x4
#define T0IR_MR2 0x4
#define T0IR_MR2_BIT 2
#define T0IR_MR3_MASK 0x8
#define T0IR_MR3 0x8
#define T0IR_MR3_BIT 3
#define T0IR_CR0_MASK 0x10
#define T0IR_CR0 0x10
#define T0IR_CR0_BIT 4
#define T0IR_CR1_MASK 0x20
#define T0IR_CR1 0x20
#define T0IR_CR1_BIT 5
#define T0IR_CR2_MASK 0x40
#define T0IR_CR2 0x40
#define T0IR_CR2_BIT 6
#define T0IR_CR3_MASK 0x80
#define T0IR_CR3 0x80
#define T0IR_CR3_BIT 7

#define T0TCR (*(volatile unsigned char *)0xE0004004)
#define T0TCR_OFFSET 0x4
#define T0TCR_Counter_Enable_MASK 0x1
#define T0TCR_Counter_Enable 0x1
#define T0TCR_Counter_Enable_BIT 0
#define T0TCR_Counter_Reset_MASK 0x2
#define T0TCR_Counter_Reset 0x2
#define T0TCR_Counter_Reset_BIT 1

#define T0TC (*(volatile unsigned long *)0xE0004008)
#define T0TC_OFFSET 0x8

#define T0PR (*(volatile unsigned long *)0xE000400C)
#define T0PR_OFFSET 0xC

#define T0PC (*(volatile unsigned long *)0xE0004010)
#define T0PC_OFFSET 0x10

#define T0MCR (*(volatile unsigned short *)0xE0004014)
#define T0MCR_OFFSET 0x14
#define T0MCR_MR0I_MASK 0x1
#define T0MCR_MR0I 0x1
#define T0MCR_MR0I_BIT 0
#define T0MCR_MR0R_MASK 0x2
#define T0MCR_MR0R 0x2
#define T0MCR_MR0R_BIT 1
#define T0MCR_MR0S_MASK 0x4
#define T0MCR_MR0S 0x4
#define T0MCR_MR0S_BIT 2
#define T0MCR_MR1I_MASK 0x8
#define T0MCR_MR1I 0x8
#define T0MCR_MR1I_BIT 3
#define T0MCR_MR1R_MASK 0x10
#define T0MCR_MR1R 0x10
#define T0MCR_MR1R_BIT 4
#define T0MCR_MR1S_MASK 0x20
#define T0MCR_MR1S 0x20
#define T0MCR_MR1S_BIT 5
#define T0MCR_MR2I_MASK 0x40
#define T0MCR_MR2I 0x40
#define T0MCR_MR2I_BIT 6
#define T0MCR_MR2R_MASK 0x80
#define T0MCR_MR2R 0x80
#define T0MCR_MR2R_BIT 7
#define T0MCR_MR2S_MASK 0x100
#define T0MCR_MR2S 0x100
#define T0MCR_MR2S_BIT 8
#define T0MCR_MR3I_MASK 0x200
#define T0MCR_MR3I 0x200
#define T0MCR_MR3I_BIT 9
#define T0MCR_MR3R_MASK 0x400
#define T0MCR_MR3R 0x400
#define T0MCR_MR3R_BIT 10
#define T0MCR_MR3S_MASK 0x800
#define T0MCR_MR3S 0x800
#define T0MCR_MR3S_BIT 11

#define T0MR0 (*(volatile unsigned long *)0xE0004018)
#define T0MR0_OFFSET 0x18

#define T0MR1 (*(volatile unsigned long *)0xE000401C)
#define T0MR1_OFFSET 0x1C

#define T0MR2 (*(volatile unsigned long *)0xE0004020)
#define T0MR2_OFFSET 0x20

#define T0MR3 (*(volatile unsigned long *)0xE0004024)
#define T0MR3_OFFSET 0x24

#define T0CCR (*(volatile unsigned short *)0xE0004028)
#define T0CCR_OFFSET 0x28
#define T0CCR_CAP0RE_MASK 0x1
#define T0CCR_CAP0RE 0x1
#define T0CCR_CAP0RE_BIT 0
#define T0CCR_CAP0FE_MASK 0x2
#define T0CCR_CAP0FE 0x2
#define T0CCR_CAP0FE_BIT 1
#define T0CCR_CAP0I_MASK 0x4
#define T0CCR_CAP0I 0x4
#define T0CCR_CAP0I_BIT 2
#define T0CCR_CAP1RE_MASK 0x8
#define T0CCR_CAP1RE 0x8
#define T0CCR_CAP1RE_BIT 3
#define T0CCR_CAP1FE_MASK 0x10
#define T0CCR_CAP1FE 0x10
#define T0CCR_CAP1FE_BIT 4
#define T0CCR_CAP1I_MASK 0x20
#define T0CCR_CAP1I 0x20
#define T0CCR_CAP1I_BIT 5
#define T0CCR_CAP2RE_MASK 0x40
#define T0CCR_CAP2RE 0x40
#define T0CCR_CAP2RE_BIT 6
#define T0CCR_CAP2FE_MASK 0x80
#define T0CCR_CAP2FE 0x80
#define T0CCR_CAP2FE_BIT 7
#define T0CCR_CAP2I_MASK 0x100
#define T0CCR_CAP2I 0x100
#define T0CCR_CAP2I_BIT 8
#define T0CCR_CAP3RE_MASK 0x200
#define T0CCR_CAP3RE 0x200
#define T0CCR_CAP3RE_BIT 9
#define T0CCR_CAP3FE_MASK 0x400
#define T0CCR_CAP3FE 0x400
#define T0CCR_CAP3FE_BIT 10
#define T0CCR_CAP3I_MASK 0x800
#define T0CCR_CAP3I 0x800
#define T0CCR_CAP3I_BIT 11

#define T0CR0 (*(volatile unsigned long *)0xE000402C)
#define T0CR0_OFFSET 0x2C

#define T0CR1 (*(volatile unsigned long *)0xE0004030)
#define T0CR1_OFFSET 0x30

#define T0CR2 (*(volatile unsigned long *)0xE0004034)
#define T0CR2_OFFSET 0x34

#define T0CR3 (*(volatile unsigned long *)0xE0004038)
#define T0CR3_OFFSET 0x38

#define T0EMR (*(volatile unsigned short *)0xE000403C)
#define T0EMR_OFFSET 0x3C
#define T0EMR_EM0_MASK 0x1
#define T0EMR_EM0 0x1
#define T0EMR_EM0_BIT 0
#define T0EMR_EM1_MASK 0x2
#define T0EMR_EM1 0x2
#define T0EMR_EM1_BIT 1
#define T0EMR_EM2_MASK 0x4
#define T0EMR_EM2 0x4
#define T0EMR_EM2_BIT 2
#define T0EMR_EM3_MASK 0x8
#define T0EMR_EM3 0x8
#define T0EMR_EM3_BIT 3
#define T0EMR_EMC0_MASK 0x30
#define T0EMR_EMC0_BIT 4
#define T0EMR_EMC1_MASK 0xC0
#define T0EMR_EMC1_BIT 6
#define T0EMR_EMC2_MASK 0x300
#define T0EMR_EMC2_BIT 8
#define T0EMR_EMC3_MASK 0xC00
#define T0EMR_EMC3_BIT 10

#define T0CTCR (*(volatile unsigned long *)0xE0004070)
#define T0CTCR_OFFSET 0x70
#define T0CTCR_Counter_Timer_Mode_MASK 0x3
#define T0CTCR_Counter_Timer_Mode_BIT 0
#define T0CTCR_Count_Input_Select_MASK 0xC
#define T0CTCR_Count_Input_Select_BIT 2

#define TIMER1_BASE 0xE0008000

#define T1IR (*(volatile unsigned char *)0xE0008000)
#define T1IR_OFFSET 0x0
#define T1IR_MR0_MASK 0x1
#define T1IR_MR0 0x1
#define T1IR_MR0_BIT 0
#define T1IR_MR1_MASK 0x2
#define T1IR_MR1 0x2
#define T1IR_MR1_BIT 1
#define T1IR_MR2_MASK 0x4
#define T1IR_MR2 0x4
#define T1IR_MR2_BIT 2
#define T1IR_MR3_MASK 0x8
#define T1IR_MR3 0x8
#define T1IR_MR3_BIT 3
#define T1IR_CR0_MASK 0x10
#define T1IR_CR0 0x10
#define T1IR_CR0_BIT 4
#define T1IR_CR1_MASK 0x20
#define T1IR_CR1 0x20
#define T1IR_CR1_BIT 5
#define T1IR_CR2_MASK 0x40
#define T1IR_CR2 0x40
#define T1IR_CR2_BIT 6
#define T1IR_CR3_MASK 0x80
#define T1IR_CR3 0x80
#define T1IR_CR3_BIT 7

#define T1TCR (*(volatile unsigned char *)0xE0008004)
#define T1TCR_OFFSET 0x4
#define T1TCR_Counter_Enable_MASK 0x1
#define T1TCR_Counter_Enable 0x1
#define T1TCR_Counter_Enable_BIT 0
#define T1TCR_Counter_Reset_MASK 0x2
#define T1TCR_Counter_Reset 0x2
#define T1TCR_Counter_Reset_BIT 1

#define T1TC (*(volatile unsigned long *)0xE0008008)
#define T1TC_OFFSET 0x8

#define T1PR (*(volatile unsigned long *)0xE000800C)
#define T1PR_OFFSET 0xC

#define T1PC (*(volatile unsigned long *)0xE0008010)
#define T1PC_OFFSET 0x10

#define T1MCR (*(volatile unsigned short *)0xE0008014)
#define T1MCR_OFFSET 0x14
#define T1MCR_MR0I_MASK 0x1
#define T1MCR_MR0I 0x1
#define T1MCR_MR0I_BIT 0
#define T1MCR_MR0R_MASK 0x2
#define T1MCR_MR0R 0x2
#define T1MCR_MR0R_BIT 1
#define T1MCR_MR0S_MASK 0x4
#define T1MCR_MR0S 0x4
#define T1MCR_MR0S_BIT 2
#define T1MCR_MR1I_MASK 0x8
#define T1MCR_MR1I 0x8
#define T1MCR_MR1I_BIT 3
#define T1MCR_MR1R_MASK 0x10
#define T1MCR_MR1R 0x10
#define T1MCR_MR1R_BIT 4
#define T1MCR_MR1S_MASK 0x20
#define T1MCR_MR1S 0x20
#define T1MCR_MR1S_BIT 5
#define T1MCR_MR2I_MASK 0x40
#define T1MCR_MR2I 0x40
#define T1MCR_MR2I_BIT 6
#define T1MCR_MR2R_MASK 0x80
#define T1MCR_MR2R 0x80
#define T1MCR_MR2R_BIT 7
#define T1MCR_MR2S_MASK 0x100
#define T1MCR_MR2S 0x100
#define T1MCR_MR2S_BIT 8
#define T1MCR_MR3I_MASK 0x200
#define T1MCR_MR3I 0x200
#define T1MCR_MR3I_BIT 9
#define T1MCR_MR3R_MASK 0x400
#define T1MCR_MR3R 0x400
#define T1MCR_MR3R_BIT 10
#define T1MCR_MR3S_MASK 0x800
#define T1MCR_MR3S 0x800
#define T1MCR_MR3S_BIT 11

#define T1MR0 (*(volatile unsigned long *)0xE0008018)
#define T1MR0_OFFSET 0x18

#define T1MR1 (*(volatile unsigned long *)0xE000801C)
#define T1MR1_OFFSET 0x1C

#define T1MR2 (*(volatile unsigned long *)0xE0008020)
#define T1MR2_OFFSET 0x20

#define T1MR3 (*(volatile unsigned long *)0xE0008024)
#define T1MR3_OFFSET 0x24

#define T1CCR (*(volatile unsigned short *)0xE0008028)
#define T1CCR_OFFSET 0x28
#define T1CCR_CAP0RE_MASK 0x1
#define T1CCR_CAP0RE 0x1
#define T1CCR_CAP0RE_BIT 0
#define T1CCR_CAP0FE_MASK 0x2
#define T1CCR_CAP0FE 0x2
#define T1CCR_CAP0FE_BIT 1
#define T1CCR_CAP0I_MASK 0x4
#define T1CCR_CAP0I 0x4
#define T1CCR_CAP0I_BIT 2
#define T1CCR_CAP1RE_MASK 0x8
#define T1CCR_CAP1RE 0x8
#define T1CCR_CAP1RE_BIT 3
#define T1CCR_CAP1FE_MASK 0x10
#define T1CCR_CAP1FE 0x10
#define T1CCR_CAP1FE_BIT 4
#define T1CCR_CAP1I_MASK 0x20
#define T1CCR_CAP1I 0x20
#define T1CCR_CAP1I_BIT 5
#define T1CCR_CAP2RE_MASK 0x40
#define T1CCR_CAP2RE 0x40
#define T1CCR_CAP2RE_BIT 6
#define T1CCR_CAP2FE_MASK 0x80
#define T1CCR_CAP2FE 0x80
#define T1CCR_CAP2FE_BIT 7
#define T1CCR_CAP2I_MASK 0x100
#define T1CCR_CAP2I 0x100
#define T1CCR_CAP2I_BIT 8
#define T1CCR_CAP3RE_MASK 0x200
#define T1CCR_CAP3RE 0x200
#define T1CCR_CAP3RE_BIT 9
#define T1CCR_CAP3FE_MASK 0x400
#define T1CCR_CAP3FE 0x400
#define T1CCR_CAP3FE_BIT 10
#define T1CCR_CAP3I_MASK 0x800
#define T1CCR_CAP3I 0x800
#define T1CCR_CAP3I_BIT 11

#define T1CR0 (*(volatile unsigned long *)0xE000802C)
#define T1CR0_OFFSET 0x2C

#define T1CR1 (*(volatile unsigned long *)0xE0008030)
#define T1CR1_OFFSET 0x30

#define T1CR2 (*(volatile unsigned long *)0xE0008034)
#define T1CR2_OFFSET 0x34

#define T1CR3 (*(volatile unsigned long *)0xE0008038)
#define T1CR3_OFFSET 0x38

#define T1EMR (*(volatile unsigned short *)0xE000803C)
#define T1EMR_OFFSET 0x3C
#define T1EMR_EM0_MASK 0x1
#define T1EMR_EM0 0x1
#define T1EMR_EM0_BIT 0
#define T1EMR_EM1_MASK 0x2
#define T1EMR_EM1 0x2
#define T1EMR_EM1_BIT 1
#define T1EMR_EM2_MASK 0x4
#define T1EMR_EM2 0x4
#define T1EMR_EM2_BIT 2
#define T1EMR_EM3_MASK 0x8
#define T1EMR_EM3 0x8
#define T1EMR_EM3_BIT 3
#define T1EMR_EMC0_MASK 0x30
#define T1EMR_EMC0_BIT 4
#define T1EMR_EMC1_MASK 0xC0
#define T1EMR_EMC1_BIT 6
#define T1EMR_EMC2_MASK 0x300
#define T1EMR_EMC2_BIT 8
#define T1EMR_EMC3_MASK 0xC00
#define T1EMR_EMC3_BIT 10

#define T1CTCR (*(volatile unsigned long *)0xE0008070)
#define T1CTCR_OFFSET 0x70
#define T1CTCR_Counter_Timer_Mode_MASK 0x3
#define T1CTCR_Counter_Timer_Mode_BIT 0
#define T1CTCR_Count_Input_Select_MASK 0xC
#define T1CTCR_Count_Input_Select_BIT 2

#define UART0_BASE 0xE000C000

#define U0RBR (*(volatile unsigned char *)0xE000C000)
#define U0RBR_OFFSET 0x0

#define U0THR (*(volatile unsigned char *)0xE000C000)
#define U0THR_OFFSET 0x0

#define U0DLL (*(volatile unsigned char *)0xE000C000)
#define U0DLL_OFFSET 0x0

#define U0DLM (*(volatile unsigned char *)0xE000C004)
#define U0DLM_OFFSET 0x4

#define U0IER (*(volatile unsigned long *)0xE000C004)
#define U0IER_OFFSET 0x4
#define U0IER_RBR_Interrupt_Enable_MASK 0x1
#define U0IER_RBR_Interrupt_Enable 0x1
#define U0IER_RBR_Interrupt_Enable_BIT 0
#define U0IER_THRE_Interrupt_Enable_MASK 0x2
#define U0IER_THRE_Interrupt_Enable 0x2
#define U0IER_THRE_Interrupt_Enable_BIT 1
#define U0IER_Rx_Line_Status_Interrupt_Enable_MASK 0x4
#define U0IER_Rx_Line_Status_Interrupt_Enable 0x4
#define U0IER_Rx_Line_Status_Interrupt_Enable_BIT 2
#define U0IER_ABTOIntEn_MASK 0x100
#define U0IER_ABTOIntEn 0x100
#define U0IER_ABTOIntEn_BIT 8
#define U0IER_ABEOIntEn_MASK 0x200
#define U0IER_ABEOIntEn 0x200
#define U0IER_ABEOIntEn_BIT 9

#define U0IIR (*(volatile unsigned long *)0xE000C008)
#define U0IIR_OFFSET 0x8
#define U0IIR_Interrupt_Pending_MASK 0x1
#define U0IIR_Interrupt_Pending 0x1
#define U0IIR_Interrupt_Pending_BIT 0
#define U0IIR_Interrupt_Identification_MASK 0xE
#define U0IIR_Interrupt_Identification_BIT 1
#define U0IIR_FIFO_Enable_MASK 0xC0
#define U0IIR_FIFO_Enable_BIT 6
#define U0IIR_ABTOInt_MASK 0x100
#define U0IIR_ABTOInt 0x100
#define U0IIR_ABTOInt_BIT 8
#define U0IIR_ABEOInt_MASK 0x200
#define U0IIR_ABEOInt 0x200
#define U0IIR_ABEOInt_BIT 9

#define U0FCR (*(volatile unsigned char *)0xE000C008)
#define U0FCR_OFFSET 0x8
#define U0FCR_FIFO_Enable_MASK 0x1
#define U0FCR_FIFO_Enable 0x1
#define U0FCR_FIFO_Enable_BIT 0
#define U0FCR_Rx_FIFO_Reset_MASK 0x2
#define U0FCR_Rx_FIFO_Reset 0x2
#define U0FCR_Rx_FIFO_Reset_BIT 1
#define U0FCR_Tx_FIFO_Reset_MASK 0x4
#define U0FCR_Tx_FIFO_Reset 0x4
#define U0FCR_Tx_FIFO_Reset_BIT 2
#define U0FCR_Rx_Trigger_Level_Select_MASK 0xC0
#define U0FCR_Rx_Trigger_Level_Select_BIT 6

#define U0LCR (*(volatile unsigned char *)0xE000C00C)
#define U0LCR_OFFSET 0xC
#define U0LCR_Word_Length_Select_MASK 0x3
#define U0LCR_Word_Length_Select_BIT 0
#define U0LCR_Stop_Bit_Select_MASK 0x4
#define U0LCR_Stop_Bit_Select 0x4
#define U0LCR_Stop_Bit_Select_BIT 2
#define U0LCR_Parity_Enable_MASK 0x8
#define U0LCR_Parity_Enable 0x8
#define U0LCR_Parity_Enable_BIT 3
#define U0LCR_Parity_Select_MASK 0x30
#define U0LCR_Parity_Select_BIT 4
#define U0LCR_Break_Control_MASK 0x40
#define U0LCR_Break_Control 0x40
#define U0LCR_Break_Control_BIT 6
#define U0LCR_Divisor_Latch_Access_Bit_MASK 0x80
#define U0LCR_Divisor_Latch_Access_Bit 0x80
#define U0LCR_Divisor_Latch_Access_Bit_BIT 7

#define U0LSR (*(volatile unsigned char *)0xE000C014)
#define U0LSR_OFFSET 0x14
#define U0LSR_RDR_MASK 0x1
#define U0LSR_RDR 0x1
#define U0LSR_RDR_BIT 0
#define U0LSR_OE_MASK 0x2
#define U0LSR_OE 0x2
#define U0LSR_OE_BIT 1
#define U0LSR_PE_MASK 0x4
#define U0LSR_PE 0x4
#define U0LSR_PE_BIT 2
#define U0LSR_FE_MASK 0x8
#define U0LSR_FE 0x8
#define U0LSR_FE_BIT 3
#define U0LSR_BI_MASK 0x10
#define U0LSR_BI 0x10
#define U0LSR_BI_BIT 4
#define U0LSR_THRE_MASK 0x20
#define U0LSR_THRE 0x20
#define U0LSR_THRE_BIT 5
#define U0LSR_TEMT_MASK 0x40
#define U0LSR_TEMT 0x40
#define U0LSR_TEMT_BIT 6
#define U0LSR_RXFE_MASK 0x80
#define U0LSR_RXFE 0x80
#define U0LSR_RXFE_BIT 7

#define U0SCR (*(volatile unsigned char *)0xE000C01C)
#define U0SCR_OFFSET 0x1C

#define U0ACR (*(volatile unsigned long *)0xE000C020)
#define U0ACR_OFFSET 0x20
#define U0ACR_Start_MASK 0x1
#define U0ACR_Start 0x1
#define U0ACR_Start_BIT 0
#define U0ACR_Mode_MASK 0x2
#define U0ACR_Mode 0x2
#define U0ACR_Mode_BIT 1
#define U0ACR_AutoRestart_MASK 0x4
#define U0ACR_AutoRestart 0x4
#define U0ACR_AutoRestart_BIT 2
#define U0ACR_ABEOIntClr_MASK 0x100
#define U0ACR_ABEOIntClr 0x100
#define U0ACR_ABEOIntClr_BIT 8
#define U0ACR_ABTOIntClr_MASK 0x200
#define U0ACR_ABTOIntClr 0x200
#define U0ACR_ABTOIntClr_BIT 9

#define U0FDR (*(volatile unsigned long *)0xE000C028)
#define U0FDR_OFFSET 0x28
#define U0FDR_DIVADDVAL_MASK 0xF
#define U0FDR_DIVADDVAL_BIT 0
#define U0FDR_MULVAL_MASK 0xF0
#define U0FDR_MULVAL_BIT 4

#define U0TER (*(volatile unsigned char *)0xE000C030)
#define U0TER_OFFSET 0x30
#define U0TER_TXEN_MASK 0x80
#define U0TER_TXEN 0x80
#define U0TER_TXEN_BIT 7

#define UART1_BASE 0xE0010000

#define U1RBR (*(volatile unsigned char *)0xE0010000)
#define U1RBR_OFFSET 0x0

#define U1THR (*(volatile unsigned char *)0xE0010000)
#define U1THR_OFFSET 0x0

#define U1DLL (*(volatile unsigned char *)0xE0010000)
#define U1DLL_OFFSET 0x0

#define U1DLM (*(volatile unsigned char *)0xE0010004)
#define U1DLM_OFFSET 0x4

#define U1IER (*(volatile unsigned long *)0xE0010004)
#define U1IER_OFFSET 0x4
#define U1IER_RBR_Interrupt_Enable_MASK 0x1
#define U1IER_RBR_Interrupt_Enable 0x1
#define U1IER_RBR_Interrupt_Enable_BIT 0
#define U1IER_THRE_Interrupt_Enable_MASK 0x2
#define U1IER_THRE_Interrupt_Enable 0x2
#define U1IER_THRE_Interrupt_Enable_BIT 1
#define U1IER_Rx_Line_Status_Interrupt_Enable_MASK 0x4
#define U1IER_Rx_Line_Status_Interrupt_Enable 0x4
#define U1IER_Rx_Line_Status_Interrupt_Enable_BIT 2
#define U1IER_Modem_Status_Interrupt_Enable_MASK 0x8
#define U1IER_Modem_Status_Interrupt_Enable 0x8
#define U1IER_Modem_Status_Interrupt_Enable_BIT 3
#define U1IER_CTS_Interrupt_Enable_MASK 0x80
#define U1IER_CTS_Interrupt_Enable 0x80
#define U1IER_CTS_Interrupt_Enable_BIT 7
#define U1IER_ABTOIntEn_MASK 0x100
#define U1IER_ABTOIntEn 0x100
#define U1IER_ABTOIntEn_BIT 8
#define U1IER_ABEOIntEn_MASK 0x200
#define U1IER_ABEOIntEn 0x200
#define U1IER_ABEOIntEn_BIT 9

#define U1IIR (*(volatile unsigned long *)0xE0010008)
#define U1IIR_OFFSET 0x8
#define U1IIR_Interrupt_Pending_MASK 0x1
#define U1IIR_Interrupt_Pending 0x1
#define U1IIR_Interrupt_Pending_BIT 0
#define U1IIR_Interrupt_Identification_MASK 0xE
#define U1IIR_Interrupt_Identification_BIT 1
#define U1IIR_FIFO_Enable_MASK 0xC0
#define U1IIR_FIFO_Enable_BIT 6
#define U1IIR_ABEOInt_MASK 0x100
#define U1IIR_ABEOInt 0x100
#define U1IIR_ABEOInt_BIT 8
#define U1IIR_ABTOInt_MASK 0x200
#define U1IIR_ABTOInt 0x200
#define U1IIR_ABTOInt_BIT 9

#define U1FCR (*(volatile unsigned char *)0xE0010008)
#define U1FCR_OFFSET 0x8
#define U1FCR_FIFO_Enable_MASK 0x1
#define U1FCR_FIFO_Enable 0x1
#define U1FCR_FIFO_Enable_BIT 0
#define U1FCR_Rx_FIFO_Reset_MASK 0x2
#define U1FCR_Rx_FIFO_Reset 0x2
#define U1FCR_Rx_FIFO_Reset_BIT 1
#define U1FCR_Tx_FIFO_Reset_MASK 0x4
#define U1FCR_Tx_FIFO_Reset 0x4
#define U1FCR_Tx_FIFO_Reset_BIT 2
#define U1FCR_Rx_Trigger_Level_Select_MASK 0xC0
#define U1FCR_Rx_Trigger_Level_Select_BIT 6

#define U1LCR (*(volatile unsigned char *)0xE001000C)
#define U1LCR_OFFSET 0xC
#define U1LCR_Word_Length_Select_MASK 0x3
#define U1LCR_Word_Length_Select_BIT 0
#define U1LCR_Stop_Bit_Select_MASK 0x4
#define U1LCR_Stop_Bit_Select 0x4
#define U1LCR_Stop_Bit_Select_BIT 2
#define U1LCR_Parity_Enable_MASK 0x8
#define U1LCR_Parity_Enable 0x8
#define U1LCR_Parity_Enable_BIT 3
#define U1LCR_Parity_Select_MASK 0x30
#define U1LCR_Parity_Select_BIT 4
#define U1LCR_Break_Control_MASK 0x40
#define U1LCR_Break_Control 0x40
#define U1LCR_Break_Control_BIT 6
#define U1LCR_Divisor_Latch_Access_Bit_MASK 0x80
#define U1LCR_Divisor_Latch_Access_Bit 0x80
#define U1LCR_Divisor_Latch_Access_Bit_BIT 7

#define U1MCR (*(volatile unsigned char *)0xE0010010)
#define U1MCR_OFFSET 0x10
#define U1MCR_DTR_Control_MASK 0x1
#define U1MCR_DTR_Control 0x1
#define U1MCR_DTR_Control_BIT 0
#define U1MCR_RTS_Control_MASK 0x2
#define U1MCR_RTS_Control 0x2
#define U1MCR_RTS_Control_BIT 1
#define U1MCR_Loopback_Mode_Select_MASK 0x10
#define U1MCR_Loopback_Mode_Select 0x10
#define U1MCR_Loopback_Mode_Select_BIT 4
#define U1MCR_RTSen_MASK 0x40
#define U1MCR_RTSen 0x40
#define U1MCR_RTSen_BIT 6
#define U1MCR_CTSen_MASK 0x80
#define U1MCR_CTSen 0x80
#define U1MCR_CTSen_BIT 7

#define U1LSR (*(volatile unsigned char *)0xE0010014)
#define U1LSR_OFFSET 0x14
#define U1LSR_RDR_MASK 0x1
#define U1LSR_RDR 0x1
#define U1LSR_RDR_BIT 0
#define U1LSR_OE_MASK 0x2
#define U1LSR_OE 0x2
#define U1LSR_OE_BIT 1
#define U1LSR_PE_MASK 0x4
#define U1LSR_PE 0x4
#define U1LSR_PE_BIT 2
#define U1LSR_FE_MASK 0x8
#define U1LSR_FE 0x8
#define U1LSR_FE_BIT 3
#define U1LSR_BI_MASK 0x10
#define U1LSR_BI 0x10
#define U1LSR_BI_BIT 4
#define U1LSR_THRE_MASK 0x20
#define U1LSR_THRE 0x20
#define U1LSR_THRE_BIT 5
#define U1LSR_TEMT_MASK 0x40
#define U1LSR_TEMT 0x40
#define U1LSR_TEMT_BIT 6
#define U1LSR_RXFE_MASK 0x80
#define U1LSR_RXFE 0x80
#define U1LSR_RXFE_BIT 7

#define U1MSR (*(volatile unsigned char *)0xE0010018)
#define U1MSR_OFFSET 0x18
#define U1MSR_Delta_CTS_MASK 0x1
#define U1MSR_Delta_CTS 0x1
#define U1MSR_Delta_CTS_BIT 0
#define U1MSR_Delta_DSR_MASK 0x2
#define U1MSR_Delta_DSR 0x2
#define U1MSR_Delta_DSR_BIT 1
#define U1MSR_Trailing_Edge_RI_MASK 0x4
#define U1MSR_Trailing_Edge_RI 0x4
#define U1MSR_Trailing_Edge_RI_BIT 2
#define U1MSR_Delta_DCD_MASK 0x8
#define U1MSR_Delta_DCD 0x8
#define U1MSR_Delta_DCD_BIT 3
#define U1MSR_CTS_MASK 0x10
#define U1MSR_CTS 0x10
#define U1MSR_CTS_BIT 4
#define U1MSR_DSR_MASK 0x20
#define U1MSR_DSR 0x20
#define U1MSR_DSR_BIT 5
#define U1MSR_RI_MASK 0x40
#define U1MSR_RI 0x40
#define U1MSR_RI_BIT 6
#define U1MSR_DCD_MASK 0x80
#define U1MSR_DCD 0x80
#define U1MSR_DCD_BIT 7

#define U1SCR (*(volatile unsigned char *)0xE001001C)
#define U1SCR_OFFSET 0x1C

#define U1ACR (*(volatile unsigned long *)0xE0010020)
#define U1ACR_OFFSET 0x20
#define U1ACR_Start_MASK 0x1
#define U1ACR_Start 0x1
#define U1ACR_Start_BIT 0
#define U1ACR_Mode_MASK 0x2
#define U1ACR_Mode 0x2
#define U1ACR_Mode_BIT 1
#define U1ACR_AutoRestart_MASK 0x4
#define U1ACR_AutoRestart 0x4
#define U1ACR_AutoRestart_BIT 2
#define U1ACR_ABEOIntClr_MASK 0x100
#define U1ACR_ABEOIntClr 0x100
#define U1ACR_ABEOIntClr_BIT 8
#define U1ACR_ABTOIntClr_MASK 0x200
#define U1ACR_ABTOIntClr 0x200
#define U1ACR_ABTOIntClr_BIT 9

#define U1FDR (*(volatile unsigned long *)0xE0010028)
#define U1FDR_OFFSET 0x28
#define U1FDR_DIVADDVAL_MASK 0xF
#define U1FDR_DIVADDVAL_BIT 0
#define U1FDR_MULVAL_MASK 0xF0
#define U1FDR_MULVAL_BIT 4

#define U1TER (*(volatile unsigned char *)0xE0010030)
#define U1TER_OFFSET 0x30
#define U1TER_TXEN_MASK 0x80
#define U1TER_TXEN 0x80
#define U1TER_TXEN_BIT 7

#define PWM_BASE 0xE0014000

#define PWMIR (*(volatile unsigned long *)0xE0014000)
#define PWMIR_OFFSET 0x0
#define PWMIR_PWMMR0_Interrupt_MASK 0x1
#define PWMIR_PWMMR0_Interrupt 0x1
#define PWMIR_PWMMR0_Interrupt_BIT 0
#define PWMIR_PWMMR1_Interrupt_MASK 0x2
#define PWMIR_PWMMR1_Interrupt 0x2
#define PWMIR_PWMMR1_Interrupt_BIT 1
#define PWMIR_PWMMR2_Interrupt_MASK 0x4
#define PWMIR_PWMMR2_Interrupt 0x4
#define PWMIR_PWMMR2_Interrupt_BIT 2
#define PWMIR_PWMMR3_Interrupt_MASK 0x8
#define PWMIR_PWMMR3_Interrupt 0x8
#define PWMIR_PWMMR3_Interrupt_BIT 3
#define PWMIR_PWMMR4_Interrupt_MASK 0x100
#define PWMIR_PWMMR4_Interrupt 0x100
#define PWMIR_PWMMR4_Interrupt_BIT 8
#define PWMIR_PWMMR5_Interrupt_MASK 0x200
#define PWMIR_PWMMR5_Interrupt 0x200
#define PWMIR_PWMMR5_Interrupt_BIT 9
#define PWMIR_PWMMR6_Interrupt_MASK 0x400
#define PWMIR_PWMMR6_Interrupt 0x400
#define PWMIR_PWMMR6_Interrupt_BIT 10

#define PWMTCR (*(volatile unsigned long *)0xE0014004)
#define PWMTCR_OFFSET 0x4
#define PWMTCR_Counter_Enable_MASK 0x1
#define PWMTCR_Counter_Enable 0x1
#define PWMTCR_Counter_Enable_BIT 0
#define PWMTCR_Counter_Reset_MASK 0x2
#define PWMTCR_Counter_Reset 0x2
#define PWMTCR_Counter_Reset_BIT 1
#define PWMTCR_PWM_Enable_MASK 0x8
#define PWMTCR_PWM_Enable 0x8
#define PWMTCR_PWM_Enable_BIT 3

#define PWMTC (*(volatile unsigned long *)0xE0014008)
#define PWMTC_OFFSET 0x8

#define PWMPR (*(volatile unsigned long *)0xE001400C)
#define PWMPR_OFFSET 0xC

#define PWMPC (*(volatile unsigned long *)0xE0014010)
#define PWMPC_OFFSET 0x10

#define PWMMCR (*(volatile unsigned long *)0xE0014014)
#define PWMMCR_OFFSET 0x14
#define PWMMCR_PWMMR0I_MASK 0x1
#define PWMMCR_PWMMR0I 0x1
#define PWMMCR_PWMMR0I_BIT 0
#define PWMMCR_PWMMR0R_MASK 0x2
#define PWMMCR_PWMMR0R 0x2
#define PWMMCR_PWMMR0R_BIT 1
#define PWMMCR_PWMMR0S_MASK 0x4
#define PWMMCR_PWMMR0S 0x4
#define PWMMCR_PWMMR0S_BIT 2
#define PWMMCR_PWMMR1I_MASK 0x8
#define PWMMCR_PWMMR1I 0x8
#define PWMMCR_PWMMR1I_BIT 3
#define PWMMCR_PWMMR1R_MASK 0x10
#define PWMMCR_PWMMR1R 0x10
#define PWMMCR_PWMMR1R_BIT 4
#define PWMMCR_PWMMR1S_MASK 0x20
#define PWMMCR_PWMMR1S 0x20
#define PWMMCR_PWMMR1S_BIT 5
#define PWMMCR_PWMMR2I_MASK 0x40
#define PWMMCR_PWMMR2I 0x40
#define PWMMCR_PWMMR2I_BIT 6
#define PWMMCR_PWMMR2R_MASK 0x80
#define PWMMCR_PWMMR2R 0x80
#define PWMMCR_PWMMR2R_BIT 7
#define PWMMCR_PWMMR2S_MASK 0x100
#define PWMMCR_PWMMR2S 0x100
#define PWMMCR_PWMMR2S_BIT 8
#define PWMMCR_PWMMR3I_MASK 0x200
#define PWMMCR_PWMMR3I 0x200
#define PWMMCR_PWMMR3I_BIT 9
#define PWMMCR_PWMMR3R_MASK 0x400
#define PWMMCR_PWMMR3R 0x400
#define PWMMCR_PWMMR3R_BIT 10
#define PWMMCR_PWMMR3S_MASK 0x800
#define PWMMCR_PWMMR3S 0x800
#define PWMMCR_PWMMR3S_BIT 11
#define PWMMCR_PWMMR4I_MASK 0x1000
#define PWMMCR_PWMMR4I 0x1000
#define PWMMCR_PWMMR4I_BIT 12
#define PWMMCR_PWMMR4R_MASK 0x2000
#define PWMMCR_PWMMR4R 0x2000
#define PWMMCR_PWMMR4R_BIT 13
#define PWMMCR_PWMMR4S_MASK 0x4000
#define PWMMCR_PWMMR4S 0x4000
#define PWMMCR_PWMMR4S_BIT 14
#define PWMMCR_PWMMR5I_MASK 0x8000
#define PWMMCR_PWMMR5I 0x8000
#define PWMMCR_PWMMR5I_BIT 15
#define PWMMCR_PWMMR5R_MASK 0x10000
#define PWMMCR_PWMMR5R 0x10000
#define PWMMCR_PWMMR5R_BIT 16
#define PWMMCR_PWMMR5S_MASK 0x20000
#define PWMMCR_PWMMR5S 0x20000
#define PWMMCR_PWMMR5S_BIT 17
#define PWMMCR_PWMMR6I_MASK 0x40000
#define PWMMCR_PWMMR6I 0x40000
#define PWMMCR_PWMMR6I_BIT 18
#define PWMMCR_PWMMR6R_MASK 0x80000
#define PWMMCR_PWMMR6R 0x80000
#define PWMMCR_PWMMR6R_BIT 19
#define PWMMCR_PWMMR6S_MASK 0x100000
#define PWMMCR_PWMMR6S 0x100000
#define PWMMCR_PWMMR6S_BIT 20

#define PWMMR0 (*(volatile unsigned long *)0xE0014018)
#define PWMMR0_OFFSET 0x18

#define PWMMR1 (*(volatile unsigned long *)0xE001401C)
#define PWMMR1_OFFSET 0x1C

#define PWMMR2 (*(volatile unsigned long *)0xE0014020)
#define PWMMR2_OFFSET 0x20

#define PWMMR3 (*(volatile unsigned long *)0xE0014024)
#define PWMMR3_OFFSET 0x24

#define PWMMR4 (*(volatile unsigned long *)0xE0014040)
#define PWMMR4_OFFSET 0x40

#define PWMMR5 (*(volatile unsigned long *)0xE0014044)
#define PWMMR5_OFFSET 0x44

#define PWMMR6 (*(volatile unsigned long *)0xE0014048)
#define PWMMR6_OFFSET 0x48

#define PWMPCR (*(volatile unsigned long *)0xE001404C)
#define PWMPCR_OFFSET 0x4C
#define PWMPCR_PWMSEL2_MASK 0x4
#define PWMPCR_PWMSEL2 0x4
#define PWMPCR_PWMSEL2_BIT 2
#define PWMPCR_PWMSEL3_MASK 0x8
#define PWMPCR_PWMSEL3 0x8
#define PWMPCR_PWMSEL3_BIT 3
#define PWMPCR_PWMSEL4_MASK 0x10
#define PWMPCR_PWMSEL4 0x10
#define PWMPCR_PWMSEL4_BIT 4
#define PWMPCR_PWMSEL5_MASK 0x20
#define PWMPCR_PWMSEL5 0x20
#define PWMPCR_PWMSEL5_BIT 5
#define PWMPCR_PWMSEL6_MASK 0x40
#define PWMPCR_PWMSEL6 0x40
#define PWMPCR_PWMSEL6_BIT 6
#define PWMPCR_PWMENA1_MASK 0x200
#define PWMPCR_PWMENA1 0x200
#define PWMPCR_PWMENA1_BIT 9
#define PWMPCR_PWMENA2_MASK 0x400
#define PWMPCR_PWMENA2 0x400
#define PWMPCR_PWMENA2_BIT 10
#define PWMPCR_PWMENA3_MASK 0x800
#define PWMPCR_PWMENA3 0x800
#define PWMPCR_PWMENA3_BIT 11
#define PWMPCR_PWMENA4_MASK 0x1000
#define PWMPCR_PWMENA4 0x1000
#define PWMPCR_PWMENA4_BIT 12
#define PWMPCR_PWMENA5_MASK 0x2000
#define PWMPCR_PWMENA5 0x2000
#define PWMPCR_PWMENA5_BIT 13
#define PWMPCR_PWMENA6_MASK 0x4000
#define PWMPCR_PWMENA6 0x4000
#define PWMPCR_PWMENA6_BIT 14

#define PWMLER (*(volatile unsigned long *)0xE0014050)
#define PWMLER_OFFSET 0x50
#define PWMLER_Enable_PWM_Match_0_Latch_MASK 0x1
#define PWMLER_Enable_PWM_Match_0_Latch 0x1
#define PWMLER_Enable_PWM_Match_0_Latch_BIT 0
#define PWMLER_Enable_PWM_Match_1_Latch_MASK 0x2
#define PWMLER_Enable_PWM_Match_1_Latch 0x2
#define PWMLER_Enable_PWM_Match_1_Latch_BIT 1
#define PWMLER_Enable_PWM_Match_2_Latch_MASK 0x4
#define PWMLER_Enable_PWM_Match_2_Latch 0x4
#define PWMLER_Enable_PWM_Match_2_Latch_BIT 2
#define PWMLER_Enable_PWM_Match_3_Latch_MASK 0x8
#define PWMLER_Enable_PWM_Match_3_Latch 0x8
#define PWMLER_Enable_PWM_Match_3_Latch_BIT 3
#define PWMLER_Enable_PWM_Match_4_Latch_MASK 0x10
#define PWMLER_Enable_PWM_Match_4_Latch 0x10
#define PWMLER_Enable_PWM_Match_4_Latch_BIT 4
#define PWMLER_Enable_PWM_Match_5_Latch_MASK 0x20
#define PWMLER_Enable_PWM_Match_5_Latch 0x20
#define PWMLER_Enable_PWM_Match_5_Latch_BIT 5
#define PWMLER_Enable_PWM_Match_6_Latch_MASK 0x40
#define PWMLER_Enable_PWM_Match_6_Latch 0x40
#define PWMLER_Enable_PWM_Match_6_Latch_BIT 6

#define I2C_BASE 0xE001C000

#define I2CONSET (*(volatile unsigned char *)0xE001C000)
#define I2CONSET_OFFSET 0x0
#define I2CONSET_AA_MASK 0x4
#define I2CONSET_AA 0x4
#define I2CONSET_AA_BIT 2
#define I2CONSET_SI_MASK 0x8
#define I2CONSET_SI 0x8
#define I2CONSET_SI_BIT 3
#define I2CONSET_STO_MASK 0x10
#define I2CONSET_STO 0x10
#define I2CONSET_STO_BIT 4
#define I2CONSET_STA_MASK 0x20
#define I2CONSET_STA 0x20
#define I2CONSET_STA_BIT 5
#define I2CONSET_I2EN_MASK 0x40
#define I2CONSET_I2EN 0x40
#define I2CONSET_I2EN_BIT 6

#define I2STAT (*(volatile unsigned char *)0xE001C004)
#define I2STAT_OFFSET 0x4
#define I2STAT_Status_MASK 0xF8
#define I2STAT_Status_BIT 3

#define I2DAT (*(volatile unsigned char *)0xE001C008)
#define I2DAT_OFFSET 0x8

#define I2ADR (*(volatile unsigned char *)0xE001C00C)
#define I2ADR_OFFSET 0xC
#define I2ADR_GC_MASK 0x1
#define I2ADR_GC 0x1
#define I2ADR_GC_BIT 0
#define I2ADR_Address_MASK 0x7E
#define I2ADR_Address_BIT 1

#define I2SCLH (*(volatile unsigned short *)0xE001C010)
#define I2SCLH_OFFSET 0x10

#define I2SCLL (*(volatile unsigned short *)0xE001C014)
#define I2SCLL_OFFSET 0x14

#define I2CONCLR (*(volatile unsigned char *)0xE001C018)
#define I2CONCLR_OFFSET 0x18
#define I2CONCLR_AAC_MASK 0x4
#define I2CONCLR_AAC 0x4
#define I2CONCLR_AAC_BIT 2
#define I2CONCLR_SIC_MASK 0x8
#define I2CONCLR_SIC 0x8
#define I2CONCLR_SIC_BIT 3
#define I2CONCLR_STAC_MASK 0x20
#define I2CONCLR_STAC 0x20
#define I2CONCLR_STAC_BIT 5
#define I2CONCLR_I2ENC_MASK 0x40
#define I2CONCLR_I2ENC 0x40
#define I2CONCLR_I2ENC_BIT 6

#define SPI0_BASE 0xE0020000

#define S0SPCR (*(volatile unsigned short *)0xE0020000)
#define S0SPCR_OFFSET 0x0
#define S0SPCR_BitEnable_MASK 0x4
#define S0SPCR_BitEnable 0x4
#define S0SPCR_BitEnable_BIT 2
#define S0SPCR_CPHA_MASK 0x8
#define S0SPCR_CPHA 0x8
#define S0SPCR_CPHA_BIT 3
#define S0SPCR_CPOL_MASK 0x10
#define S0SPCR_CPOL 0x10
#define S0SPCR_CPOL_BIT 4
#define S0SPCR_MSTR_MASK 0x20
#define S0SPCR_MSTR 0x20
#define S0SPCR_MSTR_BIT 5
#define S0SPCR_LSBF_MASK 0x40
#define S0SPCR_LSBF 0x40
#define S0SPCR_LSBF_BIT 6
#define S0SPCR_SPIE_MASK 0x80
#define S0SPCR_SPIE 0x80
#define S0SPCR_SPIE_BIT 7
#define S0SPCR_BITS_MASK 0xF00
#define S0SPCR_BITS_BIT 8

#define S0SPSR (*(volatile unsigned char *)0xE0020004)
#define S0SPSR_OFFSET 0x4
#define S0SPSR_ABRT_MASK 0x8
#define S0SPSR_ABRT 0x8
#define S0SPSR_ABRT_BIT 3
#define S0SPSR_MODF_MASK 0x10
#define S0SPSR_MODF 0x10
#define S0SPSR_MODF_BIT 4
#define S0SPSR_ROVR_MASK 0x20
#define S0SPSR_ROVR 0x20
#define S0SPSR_ROVR_BIT 5
#define S0SPSR_WCOL_MASK 0x40
#define S0SPSR_WCOL 0x40
#define S0SPSR_WCOL_BIT 6
#define S0SPSR_SPIF_MASK 0x80
#define S0SPSR_SPIF 0x80
#define S0SPSR_SPIF_BIT 7

#define S0SPDR (*(volatile unsigned short *)0xE0020008)
#define S0SPDR_OFFSET 0x8

#define S0SPCCR (*(volatile unsigned char *)0xE002000C)
#define S0SPCCR_OFFSET 0xC

#define S0SPINT (*(volatile unsigned char *)0xE002001C)
#define S0SPINT_OFFSET 0x1C

#define RTC_BASE 0xE0024000

#define ILR (*(volatile unsigned long *)0xE0024000)
#define ILR_OFFSET 0x0
#define ILR_RTCCIF_MASK 0x1
#define ILR_RTCCIF 0x1
#define ILR_RTCCIF_BIT 0
#define ILR_RTCALF_MASK 0x2
#define ILR_RTCALF 0x2
#define ILR_RTCALF_BIT 1

#define CTC (*(volatile unsigned long *)0xE0024004)
#define CTC_OFFSET 0x4
#define CTC_Clock_Tick_Counter_MASK 0xFFFE
#define CTC_Clock_Tick_Counter_BIT 1

#define CCR (*(volatile unsigned long *)0xE0024008)
#define CCR_OFFSET 0x8
#define CCR_CLKEN_MASK 0x1
#define CCR_CLKEN 0x1
#define CCR_CLKEN_BIT 0
#define CCR_CTCRST_MASK 0x2
#define CCR_CTCRST 0x2
#define CCR_CTCRST_BIT 1
#define CCR_CTTEST_MASK 0xC
#define CCR_CTTEST_BIT 2

#define CIIR (*(volatile unsigned long *)0xE002400C)
#define CIIR_OFFSET 0xC
#define CIIR_IMSEC_MASK 0x1
#define CIIR_IMSEC 0x1
#define CIIR_IMSEC_BIT 0
#define CIIR_IMMIN_MASK 0x2
#define CIIR_IMMIN 0x2
#define CIIR_IMMIN_BIT 1
#define CIIR_IMHOUR_MASK 0x4
#define CIIR_IMHOUR 0x4
#define CIIR_IMHOUR_BIT 2
#define CIIR_IMDOM_MASK 0x8
#define CIIR_IMDOM 0x8
#define CIIR_IMDOM_BIT 3
#define CIIR_IMDOW_MASK 0x10
#define CIIR_IMDOW 0x10
#define CIIR_IMDOW_BIT 4
#define CIIR_IMDOY_MASK 0x20
#define CIIR_IMDOY 0x20
#define CIIR_IMDOY_BIT 5
#define CIIR_IMMON_MASK 0x40
#define CIIR_IMMON 0x40
#define CIIR_IMMON_BIT 6
#define CIIR_IMYEAR_MASK 0x80
#define CIIR_IMYEAR 0x80
#define CIIR_IMYEAR_BIT 7

#define AMR (*(volatile unsigned long *)0xE0024010)
#define AMR_OFFSET 0x10
#define AMR_AMRSEC_MASK 0x1
#define AMR_AMRSEC 0x1
#define AMR_AMRSEC_BIT 0
#define AMR_AMRMIN_MASK 0x2
#define AMR_AMRMIN 0x2
#define AMR_AMRMIN_BIT 1
#define AMR_AMRHOUR_MASK 0x4
#define AMR_AMRHOUR 0x4
#define AMR_AMRHOUR_BIT 2
#define AMR_AMRDOM_MASK 0x8
#define AMR_AMRDOM 0x8
#define AMR_AMRDOM_BIT 3
#define AMR_AMRDOW_MASK 0x10
#define AMR_AMRDOW 0x10
#define AMR_AMRDOW_BIT 4
#define AMR_AMRDOY_MASK 0x20
#define AMR_AMRDOY 0x20
#define AMR_AMRDOY_BIT 5
#define AMR_AMRMON_MASK 0x40
#define AMR_AMRMON 0x40
#define AMR_AMRMON_BIT 6
#define AMR_AMRYEAR_MASK 0x80
#define AMR_AMRYEAR 0x80
#define AMR_AMRYEAR_BIT 7

#define CTIME0 (*(volatile unsigned long *)0xE0024014)
#define CTIME0_OFFSET 0x14
#define CTIME0_Seconds_MASK 0x3F
#define CTIME0_Seconds_BIT 0
#define CTIME0_Minutes_MASK 0x3F00
#define CTIME0_Minutes_BIT 8
#define CTIME0_Hours_MASK 0x1F0000
#define CTIME0_Hours_BIT 16
#define CTIME0_Day_of_Week_MASK 0x7000000
#define CTIME0_Day_of_Week_BIT 24

#define CTIME1 (*(volatile unsigned long *)0xE0024018)
#define CTIME1_OFFSET 0x18
#define CTIME1_Day_of_Month_MASK 0x1F
#define CTIME1_Day_of_Month_BIT 0
#define CTIME1_Month_MASK 0xF00
#define CTIME1_Month_BIT 8
#define CTIME1_Year_MASK 0xFFF0000
#define CTIME1_Year_BIT 16

#define CTIME2 (*(volatile unsigned long *)0xE002401C)
#define CTIME2_OFFSET 0x1C
#define CTIME2_Day_of_Year_MASK 0xFFF
#define CTIME2_Day_of_Year_BIT 0

#define SEC (*(volatile unsigned long *)0xE0024020)
#define SEC_OFFSET 0x20

#define MIN (*(volatile unsigned long *)0xE0024024)
#define MIN_OFFSET 0x24

#define HOUR (*(volatile unsigned long *)0xE0024028)
#define HOUR_OFFSET 0x28

#define DOM (*(volatile unsigned long *)0xE002402C)
#define DOM_OFFSET 0x2C

#define DOW (*(volatile unsigned long *)0xE0024030)
#define DOW_OFFSET 0x30

#define DOY (*(volatile unsigned long *)0xE0024034)
#define DOY_OFFSET 0x34

#define MONTH (*(volatile unsigned long *)0xE0024038)
#define MONTH_OFFSET 0x38

#define YEAR (*(volatile unsigned long *)0xE002403C)
#define YEAR_OFFSET 0x3C

#define ALSEC (*(volatile unsigned long *)0xE0024060)
#define ALSEC_OFFSET 0x60

#define ALMIN (*(volatile unsigned long *)0xE0024064)
#define ALMIN_OFFSET 0x64

#define ALHOUR (*(volatile unsigned long *)0xE0024068)
#define ALHOUR_OFFSET 0x68

#define ALDOM (*(volatile unsigned long *)0xE002406C)
#define ALDOM_OFFSET 0x6C

#define ALDOW (*(volatile unsigned long *)0xE0024070)
#define ALDOW_OFFSET 0x70

#define ALDOY (*(volatile unsigned long *)0xE0024074)
#define ALDOY_OFFSET 0x74

#define ALMON (*(volatile unsigned long *)0xE0024078)
#define ALMON_OFFSET 0x78

#define ALYEAR (*(volatile unsigned long *)0xE002407C)
#define ALYEAR_OFFSET 0x7C

#define PREINT (*(volatile unsigned long *)0xE0024080)
#define PREINT_OFFSET 0x80

#define PREFRAC (*(volatile unsigned long *)0xE0024084)
#define PREFRAC_OFFSET 0x84

#define GPIO_BASE 0xE0028000

#define IO0PIN (*(volatile unsigned long *)0xE0028000)
#define IO0PIN_OFFSET 0x0

#define IO0SET (*(volatile unsigned long *)0xE0028004)
#define IO0SET_OFFSET 0x4

#define IO0DIR (*(volatile unsigned long *)0xE0028008)
#define IO0DIR_OFFSET 0x8

#define IO0CLR (*(volatile unsigned long *)0xE002800C)
#define IO0CLR_OFFSET 0xC

#define IO1PIN (*(volatile unsigned long *)0xE0028010)
#define IO1PIN_OFFSET 0x10

#define IO1SET (*(volatile unsigned long *)0xE0028014)
#define IO1SET_OFFSET 0x14

#define IO1DIR (*(volatile unsigned long *)0xE0028018)
#define IO1DIR_OFFSET 0x18

#define IO1CLR (*(volatile unsigned long *)0xE002801C)
#define IO1CLR_OFFSET 0x1C

#define PCB_BASE 0xE002C000

#define PINSEL0 (*(volatile unsigned long *)0xE002C000)
#define PINSEL0_OFFSET 0x0
#define PINSEL0_P0_0_MASK 0x3
#define PINSEL0_P0_0_BIT 0
#define PINSEL0_P0_1_MASK 0xC
#define PINSEL0_P0_1_BIT 2
#define PINSEL0_P0_2_MASK 0x30
#define PINSEL0_P0_2_BIT 4
#define PINSEL0_P0_3_MASK 0xC0
#define PINSEL0_P0_3_BIT 6
#define PINSEL0_P0_4_MASK 0x300
#define PINSEL0_P0_4_BIT 8
#define PINSEL0_P0_5_MASK 0xC00
#define PINSEL0_P0_5_BIT 10
#define PINSEL0_P0_6_MASK 0x3000
#define PINSEL0_P0_6_BIT 12
#define PINSEL0_P0_7_MASK 0xC000
#define PINSEL0_P0_7_BIT 14
#define PINSEL0_P0_8_MASK 0x30000
#define PINSEL0_P0_8_BIT 16
#define PINSEL0_P0_9_MASK 0xC0000
#define PINSEL0_P0_9_BIT 18
#define PINSEL0_P0_10_MASK 0x300000
#define PINSEL0_P0_10_BIT 20
#define PINSEL0_P0_11_MASK 0xC00000
#define PINSEL0_P0_11_BIT 22
#define PINSEL0_P0_12_MASK 0x3000000
#define PINSEL0_P0_12_BIT 24
#define PINSEL0_P0_13_MASK 0xC000000
#define PINSEL0_P0_13_BIT 26
#define PINSEL0_P0_14_MASK 0x30000000
#define PINSEL0_P0_14_BIT 28
#define PINSEL0_P0_15_MASK 0xC0000000
#define PINSEL0_P0_15_BIT 30

#define PINSEL1 (*(volatile unsigned long *)0xE002C004)
#define PINSEL1_OFFSET 0x4
#define PINSEL1_P0_16_MASK 0x3
#define PINSEL1_P0_16_BIT 0
#define PINSEL1_P0_17_MASK 0xC
#define PINSEL1_P0_17_BIT 2
#define PINSEL1_P0_18_MASK 0x30
#define PINSEL1_P0_18_BIT 4
#define PINSEL1_P0_19_MASK 0xC0
#define PINSEL1_P0_19_BIT 6
#define PINSEL1_P0_20_MASK 0x300
#define PINSEL1_P0_20_BIT 8
#define PINSEL1_P0_21_MASK 0xC00
#define PINSEL1_P0_21_BIT 10
#define PINSEL1_P0_22_MASK 0x3000
#define PINSEL1_P0_22_BIT 12
#define PINSEL1_P0_23_MASK 0xC000
#define PINSEL1_P0_23_BIT 14
#define PINSEL1_P0_24_MASK 0x30000
#define PINSEL1_P0_24_BIT 16
#define PINSEL1_P0_25_MASK 0xC0000
#define PINSEL1_P0_25_BIT 18
#define PINSEL1_P0_26_MASK 0x300000
#define PINSEL1_P0_26_BIT 20
#define PINSEL1_P0_27_MASK 0xC00000
#define PINSEL1_P0_27_BIT 22
#define PINSEL1_P0_28_MASK 0x3000000
#define PINSEL1_P0_28_BIT 24
#define PINSEL1_P0_29_MASK 0xC000000
#define PINSEL1_P0_29_BIT 26
#define PINSEL1_P0_30_MASK 0x30000000
#define PINSEL1_P0_30_BIT 28
#define PINSEL1_P0_31_MASK 0xC0000000
#define PINSEL1_P0_31_BIT 30

#define PINSEL2 (*(volatile unsigned long *)0xE002C014)
#define PINSEL2_OFFSET 0x14
#define PINSEL2_GPIO_DEBUG_MASK 0x4
#define PINSEL2_GPIO_DEBUG 0x4
#define PINSEL2_GPIO_DEBUG_BIT 2
#define PINSEL2_GPIO_TRACE_MASK 0x8
#define PINSEL2_GPIO_TRACE 0x8
#define PINSEL2_GPIO_TRACE_BIT 3

#define SPI1_BASE 0xE0030000

#define S1SPCR (*(volatile unsigned short *)0xE0030000)
#define S1SPCR_OFFSET 0x0
#define S1SPCR_BitEnable_MASK 0x4
#define S1SPCR_BitEnable 0x4
#define S1SPCR_BitEnable_BIT 2
#define S1SPCR_CPHA_MASK 0x8
#define S1SPCR_CPHA 0x8
#define S1SPCR_CPHA_BIT 3
#define S1SPCR_CPOL_MASK 0x10
#define S1SPCR_CPOL 0x10
#define S1SPCR_CPOL_BIT 4
#define S1SPCR_MSTR_MASK 0x20
#define S1SPCR_MSTR 0x20
#define S1SPCR_MSTR_BIT 5
#define S1SPCR_LSBF_MASK 0x40
#define S1SPCR_LSBF 0x40
#define S1SPCR_LSBF_BIT 6
#define S1SPCR_SPIE_MASK 0x80
#define S1SPCR_SPIE 0x80
#define S1SPCR_SPIE_BIT 7
#define S1SPCR_BITS_MASK 0xF00
#define S1SPCR_BITS_BIT 8

#define S1SPSR (*(volatile unsigned char *)0xE0030004)
#define S1SPSR_OFFSET 0x4
#define S1SPSR_ABRT_MASK 0x8
#define S1SPSR_ABRT 0x8
#define S1SPSR_ABRT_BIT 3
#define S1SPSR_MODF_MASK 0x10
#define S1SPSR_MODF 0x10
#define S1SPSR_MODF_BIT 4
#define S1SPSR_ROVR_MASK 0x20
#define S1SPSR_ROVR 0x20
#define S1SPSR_ROVR_BIT 5
#define S1SPSR_WCOL_MASK 0x40
#define S1SPSR_WCOL 0x40
#define S1SPSR_WCOL_BIT 6
#define S1SPSR_SPIF_MASK 0x80
#define S1SPSR_SPIF 0x80
#define S1SPSR_SPIF_BIT 7

#define S1SPDR (*(volatile unsigned short *)0xE0030008)
#define S1SPDR_OFFSET 0x8

#define S1SPCCR (*(volatile unsigned char *)0xE003000C)
#define S1SPCCR_OFFSET 0xC

#define S1SPINT (*(volatile unsigned char *)0xE003001C)
#define S1SPINT_OFFSET 0x1C

#define AD_BASE 0xE0034000

#define ADCR (*(volatile unsigned *)0xE0034000)
#define ADCR_OFFSET 0x0
#define ADCR_SEL_MASK 0xFF
#define ADCR_SEL_BIT 0
#define ADCR_CLKDIV_MASK 0xFF00
#define ADCR_CLKDIV_BIT 8
#define ADCR_BURST_MASK 0x10000
#define ADCR_BURST 0x10000
#define ADCR_BURST_BIT 16
#define ADCR_CLKS_MASK 0xE0000
#define ADCR_CLKS_BIT 17
#define ADCR_PDN_MASK 0x200000
#define ADCR_PDN 0x200000
#define ADCR_PDN_BIT 21
#define ADCR_START_MASK 0x7000000
#define ADCR_START_BIT 24
#define ADCR_EDGE_MASK 0x8000000
#define ADCR_EDGE 0x8000000
#define ADCR_EDGE_BIT 27

#define ADGDR (*(volatile unsigned *)0xE0034004)
#define ADGDR_OFFSET 0x4
#define ADGDR_RESULT_MASK 0xFFC0
#define ADGDR_RESULT_BIT 6
#define ADGDR_CHN_MASK 0x7000000
#define ADGDR_CHN_BIT 24
#define ADGDR_OVERUN_MASK 0x40000000
#define ADGDR_OVERUN 0x40000000
#define ADGDR_OVERUN_BIT 30
#define ADGDR_DONE_MASK 0x80000000
#define ADGDR_DONE 0x80000000
#define ADGDR_DONE_BIT 31

#define ADINTEN (*(volatile unsigned *)0xE003400C)
#define ADINTEN_OFFSET 0xC
#define ADINTEN_ADINTEN0_MASK 0x1
#define ADINTEN_ADINTEN0 0x1
#define ADINTEN_ADINTEN0_BIT 0
#define ADINTEN_ADINTEN1_MASK 0x2
#define ADINTEN_ADINTEN1 0x2
#define ADINTEN_ADINTEN1_BIT 1
#define ADINTEN_ADINTEN2_MASK 0x4
#define ADINTEN_ADINTEN2 0x4
#define ADINTEN_ADINTEN2_BIT 2
#define ADINTEN_ADINTEN3_MASK 0x8
#define ADINTEN_ADINTEN3 0x8
#define ADINTEN_ADINTEN3_BIT 3
#define ADINTEN_ADINTEN4_MASK 0x10
#define ADINTEN_ADINTEN4 0x10
#define ADINTEN_ADINTEN4_BIT 4
#define ADINTEN_ADINTEN5_MASK 0x20
#define ADINTEN_ADINTEN5 0x20
#define ADINTEN_ADINTEN5_BIT 5
#define ADINTEN_ADINTEN6_MASK 0x40
#define ADINTEN_ADINTEN6 0x40
#define ADINTEN_ADINTEN6_BIT 6
#define ADINTEN_ADINTEN7_MASK 0x80
#define ADINTEN_ADINTEN7 0x80
#define ADINTEN_ADINTEN7_BIT 7
#define ADINTEN_ADGINTEN_MASK 0x100
#define ADINTEN_ADGINTEN 0x100
#define ADINTEN_ADGINTEN_BIT 8

#define ADDR0 (*(volatile unsigned *)0xE0034010)
#define ADDR0_OFFSET 0x10
#define ADDR0_RESULT_MASK 0xFFC0
#define ADDR0_RESULT_BIT 6
#define ADDR0_OVERRUN_MASK 0x40000000
#define ADDR0_OVERRUN 0x40000000
#define ADDR0_OVERRUN_BIT 30
#define ADDR0_DONE_MASK 0x80000000
#define ADDR0_DONE 0x80000000
#define ADDR0_DONE_BIT 31

#define ADDR1 (*(volatile unsigned *)0xE0034014)
#define ADDR1_OFFSET 0x14
#define ADDR1_RESULT_MASK 0xFFC0
#define ADDR1_RESULT_BIT 6
#define ADDR1_OVERRUN_MASK 0x40000000
#define ADDR1_OVERRUN 0x40000000
#define ADDR1_OVERRUN_BIT 30
#define ADDR1_DONE_MASK 0x80000000
#define ADDR1_DONE 0x80000000
#define ADDR1_DONE_BIT 31

#define ADDR2 (*(volatile unsigned *)0xE0034018)
#define ADDR2_OFFSET 0x18
#define ADDR2_RESULT_MASK 0xFFC0
#define ADDR2_RESULT_BIT 6
#define ADDR2_OVERRUN_MASK 0x40000000
#define ADDR2_OVERRUN 0x40000000
#define ADDR2_OVERRUN_BIT 30
#define ADDR2_DONE_MASK 0x80000000
#define ADDR2_DONE 0x80000000
#define ADDR2_DONE_BIT 31

#define ADDR3 (*(volatile unsigned *)0xE003401C)
#define ADDR3_OFFSET 0x1C
#define ADDR3_RESULT_MASK 0xFFC0
#define ADDR3_RESULT_BIT 6
#define ADDR3_OVERRUN_MASK 0x40000000
#define ADDR3_OVERRUN 0x40000000
#define ADDR3_OVERRUN_BIT 30
#define ADDR3_DONE_MASK 0x80000000
#define ADDR3_DONE 0x80000000
#define ADDR3_DONE_BIT 31

#define ADDR4 (*(volatile unsigned *)0xE0034020)
#define ADDR4_OFFSET 0x20
#define ADDR4_RESULT_MASK 0xFFC0
#define ADDR4_RESULT_BIT 6
#define ADDR4_OVERRUN_MASK 0x40000000
#define ADDR4_OVERRUN 0x40000000
#define ADDR4_OVERRUN_BIT 30
#define ADDR4_DONE_MASK 0x80000000
#define ADDR4_DONE 0x80000000
#define ADDR4_DONE_BIT 31

#define ADDR5 (*(volatile unsigned *)0xE0034024)
#define ADDR5_OFFSET 0x24
#define ADDR5_RESULT_MASK 0xFFC0
#define ADDR5_RESULT_BIT 6
#define ADDR5_OVERRUN_MASK 0x40000000
#define ADDR5_OVERRUN 0x40000000
#define ADDR5_OVERRUN_BIT 30
#define ADDR5_DONE_MASK 0x80000000
#define ADDR5_DONE 0x80000000
#define ADDR5_DONE_BIT 31

#define ADDR6 (*(volatile unsigned *)0xE0034028)
#define ADDR6_OFFSET 0x28
#define ADDR6_RESULT_MASK 0xFFC0
#define ADDR6_RESULT_BIT 6
#define ADDR6_OVERRUN_MASK 0x40000000
#define ADDR6_OVERRUN 0x40000000
#define ADDR6_OVERRUN_BIT 30
#define ADDR6_DONE_MASK 0x80000000
#define ADDR6_DONE 0x80000000
#define ADDR6_DONE_BIT 31

#define ADDR7 (*(volatile unsigned *)0xE003402C)
#define ADDR7_OFFSET 0x2C
#define ADDR7_RESULT_MASK 0xFFC0
#define ADDR7_RESULT_BIT 6
#define ADDR7_OVERRUN_MASK 0x40000000
#define ADDR7_OVERRUN 0x40000000
#define ADDR7_OVERRUN_BIT 30
#define ADDR7_DONE_MASK 0x80000000
#define ADDR7_DONE 0x80000000
#define ADDR7_DONE_BIT 31

#define ADSTAT (*(volatile unsigned *)0xE0034030)
#define ADSTAT_OFFSET 0x30
#define ADSTAT_DONE0_MASK 0x1
#define ADSTAT_DONE0 0x1
#define ADSTAT_DONE0_BIT 0
#define ADSTAT_DONE1_MASK 0x2
#define ADSTAT_DONE1 0x2
#define ADSTAT_DONE1_BIT 1
#define ADSTAT_DONE2_MASK 0x4
#define ADSTAT_DONE2 0x4
#define ADSTAT_DONE2_BIT 2
#define ADSTAT_DONE3_MASK 0x8
#define ADSTAT_DONE3 0x8
#define ADSTAT_DONE3_BIT 3
#define ADSTAT_DONE4_MASK 0x10
#define ADSTAT_DONE4 0x10
#define ADSTAT_DONE4_BIT 4
#define ADSTAT_DONE5_MASK 0x20
#define ADSTAT_DONE5 0x20
#define ADSTAT_DONE5_BIT 5
#define ADSTAT_DONE6_MASK 0x40
#define ADSTAT_DONE6 0x40
#define ADSTAT_DONE6_BIT 6
#define ADSTAT_DONE7_MASK 0x80
#define ADSTAT_DONE7 0x80
#define ADSTAT_DONE7_BIT 7
#define ADSTAT_OVERRUN0_MASK 0x100
#define ADSTAT_OVERRUN0 0x100
#define ADSTAT_OVERRUN0_BIT 8
#define ADSTAT_OVERRUN1_MASK 0x200
#define ADSTAT_OVERRUN1 0x200
#define ADSTAT_OVERRUN1_BIT 9
#define ADSTAT_OVERRUN2_MASK 0x400
#define ADSTAT_OVERRUN2 0x400
#define ADSTAT_OVERRUN2_BIT 10
#define ADSTAT_OVERRUN3_MASK 0x800
#define ADSTAT_OVERRUN3 0x800
#define ADSTAT_OVERRUN3_BIT 11
#define ADSTAT_OVERRUN4_MASK 0x1000
#define ADSTAT_OVERRUN4 0x1000
#define ADSTAT_OVERRUN4_BIT 12
#define ADSTAT_OVERRUN5_MASK 0x2000
#define ADSTAT_OVERRUN5 0x2000
#define ADSTAT_OVERRUN5_BIT 13
#define ADSTAT_OVERRUN6_MASK 0x4000
#define ADSTAT_OVERRUN6 0x4000
#define ADSTAT_OVERRUN6_BIT 14
#define ADSTAT_OVERRUN7_MASK 0x8000
#define ADSTAT_OVERRUN7 0x8000
#define ADSTAT_OVERRUN7_BIT 15
#define ADSTAT_ADINT_MASK 0x10000
#define ADSTAT_ADINT 0x10000
#define ADSTAT_ADINT_BIT 16

#define CAN_BASE 0xE0038000

#define AFMR (*(volatile unsigned long *)0xE003C000)
#define AFMR_OFFSET 0x4000
#define AFMR_AccOff_MASK 0x1
#define AFMR_AccOff 0x1
#define AFMR_AccOff_BIT 0
#define AFMR_AccBP_MASK 0x2
#define AFMR_AccBP 0x2
#define AFMR_AccBP_BIT 1
#define AFMR_eFCAN_MASK 0x4
#define AFMR_eFCAN 0x4
#define AFMR_eFCAN_BIT 2

#define SFF_sa (*(volatile unsigned long *)0xE003C004)
#define SFF_sa_OFFSET 0x4004

#define SFF_GRP_sa (*(volatile unsigned long *)0xE003C008)
#define SFF_GRP_sa_OFFSET 0x4008

#define EFF_sa (*(volatile unsigned long *)0xE003C00C)
#define EFF_sa_OFFSET 0x400C

#define EFF_GRP_sa (*(volatile unsigned long *)0xE003C010)
#define EFF_GRP_sa_OFFSET 0x4010

#define ENDofTable (*(volatile unsigned long *)0xE003C014)
#define ENDofTable_OFFSET 0x4014

#define LUTerrAd (*(volatile unsigned long *)0xE003C018)
#define LUTerrAd_OFFSET 0x4018

#define LUTerr (*(volatile unsigned long *)0xE003C01C)
#define LUTerr_OFFSET 0x401C

#define CANTxSR (*(volatile unsigned long *)0xE0040000)
#define CANTxSR_OFFSET 0x8000
#define CANTxSR_TS1_MASK 0x1
#define CANTxSR_TS1 0x1
#define CANTxSR_TS1_BIT 0
#define CANTxSR_TS2_MASK 0x2
#define CANTxSR_TS2 0x2
#define CANTxSR_TS2_BIT 1
#define CANTxSR_TS3_MASK 0x4
#define CANTxSR_TS3 0x4
#define CANTxSR_TS3_BIT 2
#define CANTxSR_TS4_MASK 0x8
#define CANTxSR_TS4 0x8
#define CANTxSR_TS4_BIT 3
#define CANTxSR_TBS1_MASK 0x100
#define CANTxSR_TBS1 0x100
#define CANTxSR_TBS1_BIT 8
#define CANTxSR_TBS2_MASK 0x200
#define CANTxSR_TBS2 0x200
#define CANTxSR_TBS2_BIT 9
#define CANTxSR_TBS3_MASK 0x400
#define CANTxSR_TBS3 0x400
#define CANTxSR_TBS3_BIT 10
#define CANTxSR_TBS4_MASK 0x800
#define CANTxSR_TBS4 0x800
#define CANTxSR_TBS4_BIT 11
#define CANTxSR_TCS1_MASK 0x10000
#define CANTxSR_TCS1 0x10000
#define CANTxSR_TCS1_BIT 16
#define CANTxSR_TCS2_MASK 0x20000
#define CANTxSR_TCS2 0x20000
#define CANTxSR_TCS2_BIT 17
#define CANTxSR_TCS3_MASK 0x40000
#define CANTxSR_TCS3 0x40000
#define CANTxSR_TCS3_BIT 18
#define CANTxSR_TCS4_MASK 0x80000
#define CANTxSR_TCS4 0x80000
#define CANTxSR_TCS4_BIT 19

#define CANRxSR (*(volatile unsigned long *)0xE0040004)
#define CANRxSR_OFFSET 0x8004
#define CANRxSR_RS1_MASK 0x1
#define CANRxSR_RS1 0x1
#define CANRxSR_RS1_BIT 0
#define CANRxSR_RS2_MASK 0x2
#define CANRxSR_RS2 0x2
#define CANRxSR_RS2_BIT 1
#define CANRxSR_RS3_MASK 0x4
#define CANRxSR_RS3 0x4
#define CANRxSR_RS3_BIT 2
#define CANRxSR_RS4_MASK 0x8
#define CANRxSR_RS4 0x8
#define CANRxSR_RS4_BIT 3
#define CANRxSR_RB1_MASK 0x100
#define CANRxSR_RB1 0x100
#define CANRxSR_RB1_BIT 8
#define CANRxSR_RB2_MASK 0x200
#define CANRxSR_RB2 0x200
#define CANRxSR_RB2_BIT 9
#define CANRxSR_RB3_MASK 0x400
#define CANRxSR_RB3 0x400
#define CANRxSR_RB3_BIT 10
#define CANRxSR_RB4_MASK 0x800
#define CANRxSR_RB4 0x800
#define CANRxSR_RB4_BIT 11
#define CANRxSR_DOS1_MASK 0x10000
#define CANRxSR_DOS1 0x10000
#define CANRxSR_DOS1_BIT 16
#define CANRxSR_DOS2_MASK 0x20000
#define CANRxSR_DOS2 0x20000
#define CANRxSR_DOS2_BIT 17
#define CANRxSR_DOS3_MASK 0x40000
#define CANRxSR_DOS3 0x40000
#define CANRxSR_DOS3_BIT 18
#define CANRxSR_DOS4_MASK 0x80000
#define CANRxSR_DOS4 0x80000
#define CANRxSR_DOS4_BIT 19

#define CANMSR (*(volatile unsigned long *)0xE0040008)
#define CANMSR_OFFSET 0x8008
#define CANMSR_ES1_MASK 0x1
#define CANMSR_ES1 0x1
#define CANMSR_ES1_BIT 0
#define CANMSR_ES2_MASK 0x2
#define CANMSR_ES2 0x2
#define CANMSR_ES2_BIT 1
#define CANMSR_ES3_MASK 0x4
#define CANMSR_ES3 0x4
#define CANMSR_ES3_BIT 2
#define CANMSR_ES4_MASK 0x8
#define CANMSR_ES4 0x8
#define CANMSR_ES4_BIT 3
#define CANMSR_BS1_MASK 0x100
#define CANMSR_BS1 0x100
#define CANMSR_BS1_BIT 8
#define CANMSR_BS2_MASK 0x200
#define CANMSR_BS2 0x200
#define CANMSR_BS2_BIT 9
#define CANMSR_BS3_MASK 0x400
#define CANMSR_BS3 0x400
#define CANMSR_BS3_BIT 10
#define CANMSR_BS4_MASK 0x800
#define CANMSR_BS4 0x800
#define CANMSR_BS4_BIT 11

#define CAN1_BASE 0xE0044000

#define C1MOD (*(volatile unsigned long *)0xE0044000)
#define CAN1MOD C1MOD
#define C1MOD_OFFSET 0x0
#define CAN1MOD_OFFSET C1MOD_OFFSET
#define C1MOD_RM_MASK 0x1
#define CAN1MOD_RM_MASK C1MOD_RM_MASK
#define C1MOD_RM 0x1
#define CAN1MOD_RM C1MOD_RM
#define C1MOD_RM_BIT 0
#define CAN1MOD_RM_BIT C1MOD_RM_BIT
#define C1MOD_LOM_MASK 0x2
#define CAN1MOD_LOM_MASK C1MOD_LOM_MASK
#define C1MOD_LOM 0x2
#define CAN1MOD_LOM C1MOD_LOM
#define C1MOD_LOM_BIT 1
#define CAN1MOD_LOM_BIT C1MOD_LOM_BIT
#define C1MOD_STM_MASK 0x4
#define CAN1MOD_STM_MASK C1MOD_STM_MASK
#define C1MOD_STM 0x4
#define CAN1MOD_STM C1MOD_STM
#define C1MOD_STM_BIT 2
#define CAN1MOD_STM_BIT C1MOD_STM_BIT
#define C1MOD_TPM_MASK 0x8
#define CAN1MOD_TPM_MASK C1MOD_TPM_MASK
#define C1MOD_TPM 0x8
#define CAN1MOD_TPM C1MOD_TPM
#define C1MOD_TPM_BIT 3
#define CAN1MOD_TPM_BIT C1MOD_TPM_BIT
#define C1MOD_SM_MASK 0x10
#define CAN1MOD_SM_MASK C1MOD_SM_MASK
#define C1MOD_SM 0x10
#define CAN1MOD_SM C1MOD_SM
#define C1MOD_SM_BIT 4
#define CAN1MOD_SM_BIT C1MOD_SM_BIT
#define C1MOD_RPM_MASK 0x20
#define CAN1MOD_RPM_MASK C1MOD_RPM_MASK
#define C1MOD_RPM 0x20
#define CAN1MOD_RPM C1MOD_RPM
#define C1MOD_RPM_BIT 5
#define CAN1MOD_RPM_BIT C1MOD_RPM_BIT
#define C1MOD_TM_MASK 0x80
#define CAN1MOD_TM_MASK C1MOD_TM_MASK
#define C1MOD_TM 0x80
#define CAN1MOD_TM C1MOD_TM
#define C1MOD_TM_BIT 7
#define CAN1MOD_TM_BIT C1MOD_TM_BIT

#define C1CMR (*(volatile unsigned long *)0xE0044004)
#define CAN1CMR C1CMR
#define C1CMR_OFFSET 0x4
#define CAN1CMR_OFFSET C1CMR_OFFSET
#define C1CMR_TR_MASK 0x1
#define CAN1CMR_TR_MASK C1CMR_TR_MASK
#define C1CMR_TR 0x1
#define CAN1CMR_TR C1CMR_TR
#define C1CMR_TR_BIT 0
#define CAN1CMR_TR_BIT C1CMR_TR_BIT
#define C1CMR_AT_MASK 0x2
#define CAN1CMR_AT_MASK C1CMR_AT_MASK
#define C1CMR_AT 0x2
#define CAN1CMR_AT C1CMR_AT
#define C1CMR_AT_BIT 1
#define CAN1CMR_AT_BIT C1CMR_AT_BIT
#define C1CMR_RRB_MASK 0x4
#define CAN1CMR_RRB_MASK C1CMR_RRB_MASK
#define C1CMR_RRB 0x4
#define CAN1CMR_RRB C1CMR_RRB
#define C1CMR_RRB_BIT 2
#define CAN1CMR_RRB_BIT C1CMR_RRB_BIT
#define C1CMR_CDO_MASK 0x8
#define CAN1CMR_CDO_MASK C1CMR_CDO_MASK
#define C1CMR_CDO 0x8
#define CAN1CMR_CDO C1CMR_CDO
#define C1CMR_CDO_BIT 3
#define CAN1CMR_CDO_BIT C1CMR_CDO_BIT
#define C1CMR_SRR_MASK 0x10
#define CAN1CMR_SRR_MASK C1CMR_SRR_MASK
#define C1CMR_SRR 0x10
#define CAN1CMR_SRR C1CMR_SRR
#define C1CMR_SRR_BIT 4
#define CAN1CMR_SRR_BIT C1CMR_SRR_BIT
#define C1CMR_STB1_MASK 0x20
#define CAN1CMR_STB1_MASK C1CMR_STB1_MASK
#define C1CMR_STB1 0x20
#define CAN1CMR_STB1 C1CMR_STB1
#define C1CMR_STB1_BIT 5
#define CAN1CMR_STB1_BIT C1CMR_STB1_BIT
#define C1CMR_STB2_MASK 0x40
#define CAN1CMR_STB2_MASK C1CMR_STB2_MASK
#define C1CMR_STB2 0x40
#define CAN1CMR_STB2 C1CMR_STB2
#define C1CMR_STB2_BIT 6
#define CAN1CMR_STB2_BIT C1CMR_STB2_BIT
#define C1CMR_STB3_MASK 0x80
#define CAN1CMR_STB3_MASK C1CMR_STB3_MASK
#define C1CMR_STB3 0x80
#define CAN1CMR_STB3 C1CMR_STB3
#define C1CMR_STB3_BIT 7
#define CAN1CMR_STB3_BIT C1CMR_STB3_BIT

#define C1GSR (*(volatile unsigned long *)0xE0044008)
#define CAN1GSR C1GSR
#define C1GSR_OFFSET 0x8
#define CAN1GSR_OFFSET C1GSR_OFFSET
#define C1GSR_RBS_MASK 0x1
#define CAN1GSR_RBS_MASK C1GSR_RBS_MASK
#define C1GSR_RBS 0x1
#define CAN1GSR_RBS C1GSR_RBS
#define C1GSR_RBS_BIT 0
#define CAN1GSR_RBS_BIT C1GSR_RBS_BIT
#define C1GSR_DOS_MASK 0x2
#define CAN1GSR_DOS_MASK C1GSR_DOS_MASK
#define C1GSR_DOS 0x2
#define CAN1GSR_DOS C1GSR_DOS
#define C1GSR_DOS_BIT 1
#define CAN1GSR_DOS_BIT C1GSR_DOS_BIT
#define C1GSR_TBS_MASK 0x4
#define CAN1GSR_TBS_MASK C1GSR_TBS_MASK
#define C1GSR_TBS 0x4
#define CAN1GSR_TBS C1GSR_TBS
#define C1GSR_TBS_BIT 2
#define CAN1GSR_TBS_BIT C1GSR_TBS_BIT
#define C1GSR_TCS_MASK 0x8
#define CAN1GSR_TCS_MASK C1GSR_TCS_MASK
#define C1GSR_TCS 0x8
#define CAN1GSR_TCS C1GSR_TCS
#define C1GSR_TCS_BIT 3
#define CAN1GSR_TCS_BIT C1GSR_TCS_BIT
#define C1GSR_RS_MASK 0x10
#define CAN1GSR_RS_MASK C1GSR_RS_MASK
#define C1GSR_RS 0x10
#define CAN1GSR_RS C1GSR_RS
#define C1GSR_RS_BIT 4
#define CAN1GSR_RS_BIT C1GSR_RS_BIT
#define C1GSR_TS_MASK 0x20
#define CAN1GSR_TS_MASK C1GSR_TS_MASK
#define C1GSR_TS 0x20
#define CAN1GSR_TS C1GSR_TS
#define C1GSR_TS_BIT 5
#define CAN1GSR_TS_BIT C1GSR_TS_BIT
#define C1GSR_ES_MASK 0x40
#define CAN1GSR_ES_MASK C1GSR_ES_MASK
#define C1GSR_ES 0x40
#define CAN1GSR_ES C1GSR_ES
#define C1GSR_ES_BIT 6
#define CAN1GSR_ES_BIT C1GSR_ES_BIT
#define C1GSR_BS_MASK 0x80
#define CAN1GSR_BS_MASK C1GSR_BS_MASK
#define C1GSR_BS 0x80
#define CAN1GSR_BS C1GSR_BS
#define C1GSR_BS_BIT 7
#define CAN1GSR_BS_BIT C1GSR_BS_BIT
#define C1GSR_RXERR_MASK 0xFF0000
#define CAN1GSR_RXERR_MASK C1GSR_RXERR_MASK
#define C1GSR_RXERR_BIT 16
#define CAN1GSR_RXERR_BIT C1GSR_RXERR_BIT
#define C1GSR_TXERR_MASK 0xFF000000
#define CAN1GSR_TXERR_MASK C1GSR_TXERR_MASK
#define C1GSR_TXERR_BIT 24
#define CAN1GSR_TXERR_BIT C1GSR_TXERR_BIT

#define C1ICR (*(volatile unsigned long *)0xE004400C)
#define CAN1ICR C1ICR
#define C1ICR_OFFSET 0xC
#define CAN1ICR_OFFSET C1ICR_OFFSET
#define C1ICR_RI_MASK 0x1
#define CAN1ICR_RI_MASK C1ICR_RI_MASK
#define C1ICR_RI 0x1
#define CAN1ICR_RI C1ICR_RI
#define C1ICR_RI_BIT 0
#define CAN1ICR_RI_BIT C1ICR_RI_BIT
#define C1ICR_TI1_MASK 0x2
#define CAN1ICR_TI1_MASK C1ICR_TI1_MASK
#define C1ICR_TI1 0x2
#define CAN1ICR_TI1 C1ICR_TI1
#define C1ICR_TI1_BIT 1
#define CAN1ICR_TI1_BIT C1ICR_TI1_BIT
#define C1ICR_EI_MASK 0x4
#define CAN1ICR_EI_MASK C1ICR_EI_MASK
#define C1ICR_EI 0x4
#define CAN1ICR_EI C1ICR_EI
#define C1ICR_EI_BIT 2
#define CAN1ICR_EI_BIT C1ICR_EI_BIT
#define C1ICR_DOI_MASK 0x8
#define CAN1ICR_DOI_MASK C1ICR_DOI_MASK
#define C1ICR_DOI 0x8
#define CAN1ICR_DOI C1ICR_DOI
#define C1ICR_DOI_BIT 3
#define CAN1ICR_DOI_BIT C1ICR_DOI_BIT
#define C1ICR_WUI_MASK 0x10
#define CAN1ICR_WUI_MASK C1ICR_WUI_MASK
#define C1ICR_WUI 0x10
#define CAN1ICR_WUI C1ICR_WUI
#define C1ICR_WUI_BIT 4
#define CAN1ICR_WUI_BIT C1ICR_WUI_BIT
#define C1ICR_EPI_MASK 0x20
#define CAN1ICR_EPI_MASK C1ICR_EPI_MASK
#define C1ICR_EPI 0x20
#define CAN1ICR_EPI C1ICR_EPI
#define C1ICR_EPI_BIT 5
#define CAN1ICR_EPI_BIT C1ICR_EPI_BIT
#define C1ICR_ALI_MASK 0x40
#define CAN1ICR_ALI_MASK C1ICR_ALI_MASK
#define C1ICR_ALI 0x40
#define CAN1ICR_ALI C1ICR_ALI
#define C1ICR_ALI_BIT 6
#define CAN1ICR_ALI_BIT C1ICR_ALI_BIT
#define C1ICR_BEI_MASK 0x80
#define CAN1ICR_BEI_MASK C1ICR_BEI_MASK
#define C1ICR_BEI 0x80
#define CAN1ICR_BEI C1ICR_BEI
#define C1ICR_BEI_BIT 7
#define CAN1ICR_BEI_BIT C1ICR_BEI_BIT
#define C1ICR_IDI_MASK 0x100
#define CAN1ICR_IDI_MASK C1ICR_IDI_MASK
#define C1ICR_IDI 0x100
#define CAN1ICR_IDI C1ICR_IDI
#define C1ICR_IDI_BIT 8
#define CAN1ICR_IDI_BIT C1ICR_IDI_BIT
#define C1ICR_TI2_MASK 0x200
#define CAN1ICR_TI2_MASK C1ICR_TI2_MASK
#define C1ICR_TI2 0x200
#define CAN1ICR_TI2 C1ICR_TI2
#define C1ICR_TI2_BIT 9
#define CAN1ICR_TI2_BIT C1ICR_TI2_BIT
#define C1ICR_TI3_MASK 0x400
#define CAN1ICR_TI3_MASK C1ICR_TI3_MASK
#define C1ICR_TI3 0x400
#define CAN1ICR_TI3 C1ICR_TI3
#define C1ICR_TI3_BIT 10
#define CAN1ICR_TI3_BIT C1ICR_TI3_BIT
#define C1ICR_ERRBIT_MASK 0x1F0000
#define CAN1ICR_ERRBIT_MASK C1ICR_ERRBIT_MASK
#define C1ICR_ERRBIT_BIT 16
#define CAN1ICR_ERRBIT_BIT C1ICR_ERRBIT_BIT
#define C1ICR_ERRDIR_MASK 0x200000
#define CAN1ICR_ERRDIR_MASK C1ICR_ERRDIR_MASK
#define C1ICR_ERRDIR 0x200000
#define CAN1ICR_ERRDIR C1ICR_ERRDIR
#define C1ICR_ERRDIR_BIT 21
#define CAN1ICR_ERRDIR_BIT C1ICR_ERRDIR_BIT
#define C1ICR_ERRC_MASK 0xC00000
#define CAN1ICR_ERRC_MASK C1ICR_ERRC_MASK
#define C1ICR_ERRC_BIT 22
#define CAN1ICR_ERRC_BIT C1ICR_ERRC_BIT
#define C1ICR_ALCBIT_MASK 0x1F000000
#define CAN1ICR_ALCBIT_MASK C1ICR_ALCBIT_MASK
#define C1ICR_ALCBIT_BIT 24
#define CAN1ICR_ALCBIT_BIT C1ICR_ALCBIT_BIT

#define C1IER (*(volatile unsigned long *)0xE0044010)
#define CAN1IER C1IER
#define C1IER_OFFSET 0x10
#define CAN1IER_OFFSET C1IER_OFFSET
#define C1IER_RIE_MASK 0x1
#define CAN1IER_RIE_MASK C1IER_RIE_MASK
#define C1IER_RIE 0x1
#define CAN1IER_RIE C1IER_RIE
#define C1IER_RIE_BIT 0
#define CAN1IER_RIE_BIT C1IER_RIE_BIT
#define C1IER_TIE1_MASK 0x2
#define CAN1IER_TIE1_MASK C1IER_TIE1_MASK
#define C1IER_TIE1 0x2
#define CAN1IER_TIE1 C1IER_TIE1
#define C1IER_TIE1_BIT 1
#define CAN1IER_TIE1_BIT C1IER_TIE1_BIT
#define C1IER_EIE_MASK 0x4
#define CAN1IER_EIE_MASK C1IER_EIE_MASK
#define C1IER_EIE 0x4
#define CAN1IER_EIE C1IER_EIE
#define C1IER_EIE_BIT 2
#define CAN1IER_EIE_BIT C1IER_EIE_BIT
#define C1IER_DOIE_MASK 0x8
#define CAN1IER_DOIE_MASK C1IER_DOIE_MASK
#define C1IER_DOIE 0x8
#define CAN1IER_DOIE C1IER_DOIE
#define C1IER_DOIE_BIT 3
#define CAN1IER_DOIE_BIT C1IER_DOIE_BIT
#define C1IER_WUIE_MASK 0x10
#define CAN1IER_WUIE_MASK C1IER_WUIE_MASK
#define C1IER_WUIE 0x10
#define CAN1IER_WUIE C1IER_WUIE
#define C1IER_WUIE_BIT 4
#define CAN1IER_WUIE_BIT C1IER_WUIE_BIT
#define C1IER_EPIE_MASK 0x20
#define CAN1IER_EPIE_MASK C1IER_EPIE_MASK
#define C1IER_EPIE 0x20
#define CAN1IER_EPIE C1IER_EPIE
#define C1IER_EPIE_BIT 5
#define CAN1IER_EPIE_BIT C1IER_EPIE_BIT
#define C1IER_ALIE_MASK 0x40
#define CAN1IER_ALIE_MASK C1IER_ALIE_MASK
#define C1IER_ALIE 0x40
#define CAN1IER_ALIE C1IER_ALIE
#define C1IER_ALIE_BIT 6
#define CAN1IER_ALIE_BIT C1IER_ALIE_BIT
#define C1IER_BEIE_MASK 0x80
#define CAN1IER_BEIE_MASK C1IER_BEIE_MASK
#define C1IER_BEIE 0x80
#define CAN1IER_BEIE C1IER_BEIE
#define C1IER_BEIE_BIT 7
#define CAN1IER_BEIE_BIT C1IER_BEIE_BIT
#define C1IER_IDIE_MASK 0x100
#define CAN1IER_IDIE_MASK C1IER_IDIE_MASK
#define C1IER_IDIE 0x100
#define CAN1IER_IDIE C1IER_IDIE
#define C1IER_IDIE_BIT 8
#define CAN1IER_IDIE_BIT C1IER_IDIE_BIT
#define C1IER_TIE2_MASK 0x200
#define CAN1IER_TIE2_MASK C1IER_TIE2_MASK
#define C1IER_TIE2 0x200
#define CAN1IER_TIE2 C1IER_TIE2
#define C1IER_TIE2_BIT 9
#define CAN1IER_TIE2_BIT C1IER_TIE2_BIT
#define C1IER_TIE3_MASK 0x400
#define CAN1IER_TIE3_MASK C1IER_TIE3_MASK
#define C1IER_TIE3 0x400
#define CAN1IER_TIE3 C1IER_TIE3
#define C1IER_TIE3_BIT 10
#define CAN1IER_TIE3_BIT C1IER_TIE3_BIT

#define C1BTR (*(volatile unsigned long *)0xE0044014)
#define CAN1BTR C1BTR
#define C1BTR_OFFSET 0x14
#define CAN1BTR_OFFSET C1BTR_OFFSET
#define C1BTR_BRP_MASK 0x3FF
#define CAN1BTR_BRP_MASK C1BTR_BRP_MASK
#define C1BTR_BRP_BIT 0
#define CAN1BTR_BRP_BIT C1BTR_BRP_BIT
#define C1BTR_SJW_MASK 0xC000
#define CAN1BTR_SJW_MASK C1BTR_SJW_MASK
#define C1BTR_SJW_BIT 14
#define CAN1BTR_SJW_BIT C1BTR_SJW_BIT
#define C1BTR_TSEG1_MASK 0xF0000
#define CAN1BTR_TSEG1_MASK C1BTR_TSEG1_MASK
#define C1BTR_TSEG1_BIT 16
#define CAN1BTR_TSEG1_BIT C1BTR_TSEG1_BIT
#define C1BTR_TSEG2_MASK 0x700000
#define CAN1BTR_TSEG2_MASK C1BTR_TSEG2_MASK
#define C1BTR_TSEG2_BIT 20
#define CAN1BTR_TSEG2_BIT C1BTR_TSEG2_BIT
#define C1BTR_SAM_MASK 0x800000
#define CAN1BTR_SAM_MASK C1BTR_SAM_MASK
#define C1BTR_SAM 0x800000
#define CAN1BTR_SAM C1BTR_SAM
#define C1BTR_SAM_BIT 23
#define CAN1BTR_SAM_BIT C1BTR_SAM_BIT

#define C1EWL (*(volatile unsigned long *)0xE0044018)
#define CAN1EWL C1EWL
#define C1EWL_OFFSET 0x18
#define CAN1EWL_OFFSET C1EWL_OFFSET
#define C1EWL_EWL_MASK 0xFF
#define CAN1EWL_EWL_MASK C1EWL_EWL_MASK
#define C1EWL_EWL_BIT 0
#define CAN1EWL_EWL_BIT C1EWL_EWL_BIT

#define C1SR (*(volatile unsigned long *)0xE004401C)
#define CAN1SR C1SR
#define C1SR_OFFSET 0x1C
#define CAN1SR_OFFSET C1SR_OFFSET
#define C1SR_RBS_MASK 0x1
#define CAN1SR_RBS_MASK C1SR_RBS_MASK
#define C1SR_RBS 0x1
#define CAN1SR_RBS C1SR_RBS
#define C1SR_RBS_BIT 0
#define CAN1SR_RBS_BIT C1SR_RBS_BIT
#define C1SR_DOS_MASK 0x2
#define CAN1SR_DOS_MASK C1SR_DOS_MASK
#define C1SR_DOS 0x2
#define CAN1SR_DOS C1SR_DOS
#define C1SR_DOS_BIT 1
#define CAN1SR_DOS_BIT C1SR_DOS_BIT
#define C1SR_TBS1_MASK 0x4
#define CAN1SR_TBS1_MASK C1SR_TBS1_MASK
#define C1SR_TBS1 0x4
#define CAN1SR_TBS1 C1SR_TBS1
#define C1SR_TBS1_BIT 2
#define CAN1SR_TBS1_BIT C1SR_TBS1_BIT
#define C1SR_TCS1_MASK 0x8
#define CAN1SR_TCS1_MASK C1SR_TCS1_MASK
#define C1SR_TCS1 0x8
#define CAN1SR_TCS1 C1SR_TCS1
#define C1SR_TCS1_BIT 3
#define CAN1SR_TCS1_BIT C1SR_TCS1_BIT
#define C1SR_RS_MASK 0x10
#define CAN1SR_RS_MASK C1SR_RS_MASK
#define C1SR_RS 0x10
#define CAN1SR_RS C1SR_RS
#define C1SR_RS_BIT 4
#define CAN1SR_RS_BIT C1SR_RS_BIT
#define C1SR_TS1_MASK 0x20
#define CAN1SR_TS1_MASK C1SR_TS1_MASK
#define C1SR_TS1 0x20
#define CAN1SR_TS1 C1SR_TS1
#define C1SR_TS1_BIT 5
#define CAN1SR_TS1_BIT C1SR_TS1_BIT
#define C1SR_ES_MASK 0x40
#define CAN1SR_ES_MASK C1SR_ES_MASK
#define C1SR_ES 0x40
#define CAN1SR_ES C1SR_ES
#define C1SR_ES_BIT 6
#define CAN1SR_ES_BIT C1SR_ES_BIT
#define C1SR_BS_MASK 0x80
#define CAN1SR_BS_MASK C1SR_BS_MASK
#define C1SR_BS 0x80
#define CAN1SR_BS C1SR_BS
#define C1SR_BS_BIT 7
#define CAN1SR_BS_BIT C1SR_BS_BIT
#define C1SR_RBS2_MASK 0x100
#define CAN1SR_RBS2_MASK C1SR_RBS2_MASK
#define C1SR_RBS2 0x100
#define CAN1SR_RBS2 C1SR_RBS2
#define C1SR_RBS2_BIT 8
#define CAN1SR_RBS2_BIT C1SR_RBS2_BIT
#define C1SR_DOS2_MASK 0x200
#define CAN1SR_DOS2_MASK C1SR_DOS2_MASK
#define C1SR_DOS2 0x200
#define CAN1SR_DOS2 C1SR_DOS2
#define C1SR_DOS2_BIT 9
#define CAN1SR_DOS2_BIT C1SR_DOS2_BIT
#define C1SR_TBS2_MASK 0x400
#define CAN1SR_TBS2_MASK C1SR_TBS2_MASK
#define C1SR_TBS2 0x400
#define CAN1SR_TBS2 C1SR_TBS2
#define C1SR_TBS2_BIT 10
#define CAN1SR_TBS2_BIT C1SR_TBS2_BIT
#define C1SR_TCS2_MASK 0x800
#define CAN1SR_TCS2_MASK C1SR_TCS2_MASK
#define C1SR_TCS2 0x800
#define CAN1SR_TCS2 C1SR_TCS2
#define C1SR_TCS2_BIT 11
#define CAN1SR_TCS2_BIT C1SR_TCS2_BIT
#define C1SR_RS2_MASK 0x1000
#define CAN1SR_RS2_MASK C1SR_RS2_MASK
#define C1SR_RS2 0x1000
#define CAN1SR_RS2 C1SR_RS2
#define C1SR_RS2_BIT 12
#define CAN1SR_RS2_BIT C1SR_RS2_BIT
#define C1SR_TS2_MASK 0x2000
#define CAN1SR_TS2_MASK C1SR_TS2_MASK
#define C1SR_TS2 0x2000
#define CAN1SR_TS2 C1SR_TS2
#define C1SR_TS2_BIT 13
#define CAN1SR_TS2_BIT C1SR_TS2_BIT
#define C1SR_ES2_MASK 0x4000
#define CAN1SR_ES2_MASK C1SR_ES2_MASK
#define C1SR_ES2 0x4000
#define CAN1SR_ES2 C1SR_ES2
#define C1SR_ES2_BIT 14
#define CAN1SR_ES2_BIT C1SR_ES2_BIT
#define C1SR_BS2_MASK 0x8000
#define CAN1SR_BS2_MASK C1SR_BS2_MASK
#define C1SR_BS2 0x8000
#define CAN1SR_BS2 C1SR_BS2
#define C1SR_BS2_BIT 15
#define CAN1SR_BS2_BIT C1SR_BS2_BIT
#define C1SR_RBS3_MASK 0x10000
#define CAN1SR_RBS3_MASK C1SR_RBS3_MASK
#define C1SR_RBS3 0x10000
#define CAN1SR_RBS3 C1SR_RBS3
#define C1SR_RBS3_BIT 16
#define CAN1SR_RBS3_BIT C1SR_RBS3_BIT
#define C1SR_DOS3_MASK 0x20000
#define CAN1SR_DOS3_MASK C1SR_DOS3_MASK
#define C1SR_DOS3 0x20000
#define CAN1SR_DOS3 C1SR_DOS3
#define C1SR_DOS3_BIT 17
#define CAN1SR_DOS3_BIT C1SR_DOS3_BIT
#define C1SR_TBS3_MASK 0x40000
#define CAN1SR_TBS3_MASK C1SR_TBS3_MASK
#define C1SR_TBS3 0x40000
#define CAN1SR_TBS3 C1SR_TBS3
#define C1SR_TBS3_BIT 18
#define CAN1SR_TBS3_BIT C1SR_TBS3_BIT
#define C1SR_TCS3_MASK 0x80000
#define CAN1SR_TCS3_MASK C1SR_TCS3_MASK
#define C1SR_TCS3 0x80000
#define CAN1SR_TCS3 C1SR_TCS3
#define C1SR_TCS3_BIT 19
#define CAN1SR_TCS3_BIT C1SR_TCS3_BIT
#define C1SR_RS3_MASK 0x100000
#define CAN1SR_RS3_MASK C1SR_RS3_MASK
#define C1SR_RS3 0x100000
#define CAN1SR_RS3 C1SR_RS3
#define C1SR_RS3_BIT 20
#define CAN1SR_RS3_BIT C1SR_RS3_BIT
#define C1SR_TS3_MASK 0x200000
#define CAN1SR_TS3_MASK C1SR_TS3_MASK
#define C1SR_TS3 0x200000
#define CAN1SR_TS3 C1SR_TS3
#define C1SR_TS3_BIT 21
#define CAN1SR_TS3_BIT C1SR_TS3_BIT
#define C1SR_ES3_MASK 0x400000
#define CAN1SR_ES3_MASK C1SR_ES3_MASK
#define C1SR_ES3 0x400000
#define CAN1SR_ES3 C1SR_ES3
#define C1SR_ES3_BIT 22
#define CAN1SR_ES3_BIT C1SR_ES3_BIT
#define C1SR_BS3_MASK 0x800000
#define CAN1SR_BS3_MASK C1SR_BS3_MASK
#define C1SR_BS3 0x800000
#define CAN1SR_BS3 C1SR_BS3
#define C1SR_BS3_BIT 23
#define CAN1SR_BS3_BIT C1SR_BS3_BIT

#define C1RFS (*(volatile unsigned long *)0xE0044020)
#define CAN1RFS C1RFS
#define C1RFS_OFFSET 0x20
#define CAN1RFS_OFFSET C1RFS_OFFSET
#define C1RFS_ID_Index_MASK 0x3FF
#define CAN1RFS_ID_Index_MASK C1RFS_ID_Index_MASK
#define C1RFS_ID_Index_BIT 0
#define CAN1RFS_ID_Index_BIT C1RFS_ID_Index_BIT
#define C1RFS_BP_MASK 0x400
#define CAN1RFS_BP_MASK C1RFS_BP_MASK
#define C1RFS_BP 0x400
#define CAN1RFS_BP C1RFS_BP
#define C1RFS_BP_BIT 10
#define CAN1RFS_BP_BIT C1RFS_BP_BIT
#define C1RFS_DLC_MASK 0xF0000
#define CAN1RFS_DLC_MASK C1RFS_DLC_MASK
#define C1RFS_DLC_BIT 16
#define CAN1RFS_DLC_BIT C1RFS_DLC_BIT
#define C1RFS_RTR_MASK 0x40000000
#define CAN1RFS_RTR_MASK C1RFS_RTR_MASK
#define C1RFS_RTR 0x40000000
#define CAN1RFS_RTR C1RFS_RTR
#define C1RFS_RTR_BIT 30
#define CAN1RFS_RTR_BIT C1RFS_RTR_BIT
#define C1RFS_FF_MASK 0x80000000
#define CAN1RFS_FF_MASK C1RFS_FF_MASK
#define C1RFS_FF 0x80000000
#define CAN1RFS_FF C1RFS_FF
#define C1RFS_FF_BIT 31
#define CAN1RFS_FF_BIT C1RFS_FF_BIT

#define C1RID (*(volatile unsigned long *)0xE0044024)
#define CAN1RID C1RID
#define C1RID_OFFSET 0x24
#define CAN1RID_OFFSET C1RID_OFFSET
#define C1RID_ID_MASK 0x7FF
#define CAN1RID_ID_MASK C1RID_ID_MASK
#define C1RID_ID_BIT 0
#define CAN1RID_ID_BIT C1RID_ID_BIT

#define C1RDA (*(volatile unsigned long *)0xE0044028)
#define CAN1RDA C1RDA
#define C1RDA_OFFSET 0x28
#define CAN1RDA_OFFSET C1RDA_OFFSET
#define C1RDA_Data_1_MASK 0xFF
#define CAN1RDA_Data_1_MASK C1RDA_Data_1_MASK
#define C1RDA_Data_1_BIT 0
#define CAN1RDA_Data_1_BIT C1RDA_Data_1_BIT
#define C1RDA_Data_2_MASK 0xFF00
#define CAN1RDA_Data_2_MASK C1RDA_Data_2_MASK
#define C1RDA_Data_2_BIT 8
#define CAN1RDA_Data_2_BIT C1RDA_Data_2_BIT
#define C1RDA_Data_3_MASK 0xFF0000
#define CAN1RDA_Data_3_MASK C1RDA_Data_3_MASK
#define C1RDA_Data_3_BIT 16
#define CAN1RDA_Data_3_BIT C1RDA_Data_3_BIT
#define C1RDA_Data_4_MASK 0xFF000000
#define CAN1RDA_Data_4_MASK C1RDA_Data_4_MASK
#define C1RDA_Data_4_BIT 24
#define CAN1RDA_Data_4_BIT C1RDA_Data_4_BIT

#define C1RDB (*(volatile unsigned long *)0xE004402C)
#define CAN1RDB C1RDB
#define C1RDB_OFFSET 0x2C
#define CAN1RDB_OFFSET C1RDB_OFFSET
#define C1RDB_Data_5_MASK 0xFF
#define CAN1RDB_Data_5_MASK C1RDB_Data_5_MASK
#define C1RDB_Data_5_BIT 0
#define CAN1RDB_Data_5_BIT C1RDB_Data_5_BIT
#define C1RDB_Data_6_MASK 0xFF00
#define CAN1RDB_Data_6_MASK C1RDB_Data_6_MASK
#define C1RDB_Data_6_BIT 8
#define CAN1RDB_Data_6_BIT C1RDB_Data_6_BIT
#define C1RDB_Data_7_MASK 0xFF0000
#define CAN1RDB_Data_7_MASK C1RDB_Data_7_MASK
#define C1RDB_Data_7_BIT 16
#define CAN1RDB_Data_7_BIT C1RDB_Data_7_BIT
#define C1RDB_Data_8_MASK 0xFF000000
#define CAN1RDB_Data_8_MASK C1RDB_Data_8_MASK
#define C1RDB_Data_8_BIT 24
#define CAN1RDB_Data_8_BIT C1RDB_Data_8_BIT

#define C1TFI1 (*(volatile unsigned long *)0xE0044030)
#define CAN1TFI1 C1TFI1
#define C1TFI1_OFFSET 0x30
#define CAN1TFI1_OFFSET C1TFI1_OFFSET
#define C1TFI1_PRIO_MASK 0xFF
#define CAN1TFI1_PRIO_MASK C1TFI1_PRIO_MASK
#define C1TFI1_PRIO_BIT 0
#define CAN1TFI1_PRIO_BIT C1TFI1_PRIO_BIT
#define C1TFI1_DLC_MASK 0xF0000
#define CAN1TFI1_DLC_MASK C1TFI1_DLC_MASK
#define C1TFI1_DLC_BIT 16
#define CAN1TFI1_DLC_BIT C1TFI1_DLC_BIT
#define C1TFI1_RTR_MASK 0x40000000
#define CAN1TFI1_RTR_MASK C1TFI1_RTR_MASK
#define C1TFI1_RTR 0x40000000
#define CAN1TFI1_RTR C1TFI1_RTR
#define C1TFI1_RTR_BIT 30
#define CAN1TFI1_RTR_BIT C1TFI1_RTR_BIT
#define C1TFI1_FF_MASK 0x80000000
#define CAN1TFI1_FF_MASK C1TFI1_FF_MASK
#define C1TFI1_FF 0x80000000
#define CAN1TFI1_FF C1TFI1_FF
#define C1TFI1_FF_BIT 31
#define CAN1TFI1_FF_BIT C1TFI1_FF_BIT

#define C1TID1 (*(volatile unsigned long *)0xE0044034)
#define CAN1TID1 C1TID1
#define C1TID1_OFFSET 0x34
#define CAN1TID1_OFFSET C1TID1_OFFSET
#define C1TID1_ID_MASK 0x7FF
#define CAN1TID1_ID_MASK C1TID1_ID_MASK
#define C1TID1_ID_BIT 0
#define CAN1TID1_ID_BIT C1TID1_ID_BIT

#define C1TDA1 (*(volatile unsigned long *)0xE0044038)
#define CAN1TDA1 C1TDA1
#define C1TDA1_OFFSET 0x38
#define CAN1TDA1_OFFSET C1TDA1_OFFSET
#define C1TDA1_Data_1_MASK 0xFF
#define CAN1TDA1_Data_1_MASK C1TDA1_Data_1_MASK
#define C1TDA1_Data_1_BIT 0
#define CAN1TDA1_Data_1_BIT C1TDA1_Data_1_BIT
#define C1TDA1_Data_2_MASK 0xFF00
#define CAN1TDA1_Data_2_MASK C1TDA1_Data_2_MASK
#define C1TDA1_Data_2_BIT 8
#define CAN1TDA1_Data_2_BIT C1TDA1_Data_2_BIT
#define C1TDA1_Data_3_MASK 0xFF0000
#define CAN1TDA1_Data_3_MASK C1TDA1_Data_3_MASK
#define C1TDA1_Data_3_BIT 16
#define CAN1TDA1_Data_3_BIT C1TDA1_Data_3_BIT
#define C1TDA1_Data_4_MASK 0xFF000000
#define CAN1TDA1_Data_4_MASK C1TDA1_Data_4_MASK
#define C1TDA1_Data_4_BIT 24
#define CAN1TDA1_Data_4_BIT C1TDA1_Data_4_BIT

#define C1TDB1 (*(volatile unsigned long *)0xE004403C)
#define CAN1TDB1 C1TDB1
#define C1TDB1_OFFSET 0x3C
#define CAN1TDB1_OFFSET C1TDB1_OFFSET
#define C1TDB1_Data_5_MASK 0xFF
#define CAN1TDB1_Data_5_MASK C1TDB1_Data_5_MASK
#define C1TDB1_Data_5_BIT 0
#define CAN1TDB1_Data_5_BIT C1TDB1_Data_5_BIT
#define C1TDB1_Data_6_MASK 0xFF00
#define CAN1TDB1_Data_6_MASK C1TDB1_Data_6_MASK
#define C1TDB1_Data_6_BIT 8
#define CAN1TDB1_Data_6_BIT C1TDB1_Data_6_BIT
#define C1TDB1_Data_7_MASK 0xFF0000
#define CAN1TDB1_Data_7_MASK C1TDB1_Data_7_MASK
#define C1TDB1_Data_7_BIT 16
#define CAN1TDB1_Data_7_BIT C1TDB1_Data_7_BIT
#define C1TDB1_Data_8_MASK 0xFF000000
#define CAN1TDB1_Data_8_MASK C1TDB1_Data_8_MASK
#define C1TDB1_Data_8_BIT 24
#define CAN1TDB1_Data_8_BIT C1TDB1_Data_8_BIT

#define C1TFI2 (*(volatile unsigned long *)0xE0044040)
#define CAN1TFI2 C1TFI2
#define C1TFI2_OFFSET 0x40
#define CAN1TFI2_OFFSET C1TFI2_OFFSET
#define C1TFI2_PRIO_MASK 0xFF
#define CAN1TFI2_PRIO_MASK C1TFI2_PRIO_MASK
#define C1TFI2_PRIO_BIT 0
#define CAN1TFI2_PRIO_BIT C1TFI2_PRIO_BIT
#define C1TFI2_DLC_MASK 0xF0000
#define CAN1TFI2_DLC_MASK C1TFI2_DLC_MASK
#define C1TFI2_DLC_BIT 16
#define CAN1TFI2_DLC_BIT C1TFI2_DLC_BIT
#define C1TFI2_RTR_MASK 0x40000000
#define CAN1TFI2_RTR_MASK C1TFI2_RTR_MASK
#define C1TFI2_RTR 0x40000000
#define CAN1TFI2_RTR C1TFI2_RTR
#define C1TFI2_RTR_BIT 30
#define CAN1TFI2_RTR_BIT C1TFI2_RTR_BIT
#define C1TFI2_FF_MASK 0x80000000
#define CAN1TFI2_FF_MASK C1TFI2_FF_MASK
#define C1TFI2_FF 0x80000000
#define CAN1TFI2_FF C1TFI2_FF
#define C1TFI2_FF_BIT 31
#define CAN1TFI2_FF_BIT C1TFI2_FF_BIT

#define C1TID2 (*(volatile unsigned long *)0xE0044044)
#define CAN1TID2 C1TID2
#define C1TID2_OFFSET 0x44
#define CAN1TID2_OFFSET C1TID2_OFFSET
#define C1TID2_ID_MASK 0x7FF
#define CAN1TID2_ID_MASK C1TID2_ID_MASK
#define C1TID2_ID_BIT 0
#define CAN1TID2_ID_BIT C1TID2_ID_BIT

#define C1TDA2 (*(volatile unsigned long *)0xE0044048)
#define CAN1TDA2 C1TDA2
#define C1TDA2_OFFSET 0x48
#define CAN1TDA2_OFFSET C1TDA2_OFFSET
#define C1TDA2_Data_1_MASK 0xFF
#define CAN1TDA2_Data_1_MASK C1TDA2_Data_1_MASK
#define C1TDA2_Data_1_BIT 0
#define CAN1TDA2_Data_1_BIT C1TDA2_Data_1_BIT
#define C1TDA2_Data_2_MASK 0xFF00
#define CAN1TDA2_Data_2_MASK C1TDA2_Data_2_MASK
#define C1TDA2_Data_2_BIT 8
#define CAN1TDA2_Data_2_BIT C1TDA2_Data_2_BIT
#define C1TDA2_Data_3_MASK 0xFF0000
#define CAN1TDA2_Data_3_MASK C1TDA2_Data_3_MASK
#define C1TDA2_Data_3_BIT 16
#define CAN1TDA2_Data_3_BIT C1TDA2_Data_3_BIT
#define C1TDA2_Data_4_MASK 0xFF000000
#define CAN1TDA2_Data_4_MASK C1TDA2_Data_4_MASK
#define C1TDA2_Data_4_BIT 24
#define CAN1TDA2_Data_4_BIT C1TDA2_Data_4_BIT

#define C1TDB2 (*(volatile unsigned long *)0xE004404C)
#define CAN1TDB2 C1TDB2
#define C1TDB2_OFFSET 0x4C
#define CAN1TDB2_OFFSET C1TDB2_OFFSET
#define C1TDB2_Data_5_MASK 0xFF
#define CAN1TDB2_Data_5_MASK C1TDB2_Data_5_MASK
#define C1TDB2_Data_5_BIT 0
#define CAN1TDB2_Data_5_BIT C1TDB2_Data_5_BIT
#define C1TDB2_Data_6_MASK 0xFF00
#define CAN1TDB2_Data_6_MASK C1TDB2_Data_6_MASK
#define C1TDB2_Data_6_BIT 8
#define CAN1TDB2_Data_6_BIT C1TDB2_Data_6_BIT
#define C1TDB2_Data_7_MASK 0xFF0000
#define CAN1TDB2_Data_7_MASK C1TDB2_Data_7_MASK
#define C1TDB2_Data_7_BIT 16
#define CAN1TDB2_Data_7_BIT C1TDB2_Data_7_BIT
#define C1TDB2_Data_8_MASK 0xFF000000
#define CAN1TDB2_Data_8_MASK C1TDB2_Data_8_MASK
#define C1TDB2_Data_8_BIT 24
#define CAN1TDB2_Data_8_BIT C1TDB2_Data_8_BIT

#define C1TFI3 (*(volatile unsigned long *)0xE0044050)
#define CAN1TFI3 C1TFI3
#define C1TFI3_OFFSET 0x50
#define CAN1TFI3_OFFSET C1TFI3_OFFSET
#define C1TFI3_PRIO_MASK 0xFF
#define CAN1TFI3_PRIO_MASK C1TFI3_PRIO_MASK
#define C1TFI3_PRIO_BIT 0
#define CAN1TFI3_PRIO_BIT C1TFI3_PRIO_BIT
#define C1TFI3_DLC_MASK 0xF0000
#define CAN1TFI3_DLC_MASK C1TFI3_DLC_MASK
#define C1TFI3_DLC_BIT 16
#define CAN1TFI3_DLC_BIT C1TFI3_DLC_BIT
#define C1TFI3_RTR_MASK 0x40000000
#define CAN1TFI3_RTR_MASK C1TFI3_RTR_MASK
#define C1TFI3_RTR 0x40000000
#define CAN1TFI3_RTR C1TFI3_RTR
#define C1TFI3_RTR_BIT 30
#define CAN1TFI3_RTR_BIT C1TFI3_RTR_BIT
#define C1TFI3_FF_MASK 0x80000000
#define CAN1TFI3_FF_MASK C1TFI3_FF_MASK
#define C1TFI3_FF 0x80000000
#define CAN1TFI3_FF C1TFI3_FF
#define C1TFI3_FF_BIT 31
#define CAN1TFI3_FF_BIT C1TFI3_FF_BIT

#define C1TID3 (*(volatile unsigned long *)0xE0044054)
#define CAN1TID3 C1TID3
#define C1TID3_OFFSET 0x54
#define CAN1TID3_OFFSET C1TID3_OFFSET
#define C1TID3_ID_MASK 0x7FF
#define CAN1TID3_ID_MASK C1TID3_ID_MASK
#define C1TID3_ID_BIT 0
#define CAN1TID3_ID_BIT C1TID3_ID_BIT

#define C1TDA3 (*(volatile unsigned long *)0xE0044058)
#define CAN1TDA3 C1TDA3
#define C1TDA3_OFFSET 0x58
#define CAN1TDA3_OFFSET C1TDA3_OFFSET
#define C1TDA3_Data_1_MASK 0xFF
#define CAN1TDA3_Data_1_MASK C1TDA3_Data_1_MASK
#define C1TDA3_Data_1_BIT 0
#define CAN1TDA3_Data_1_BIT C1TDA3_Data_1_BIT
#define C1TDA3_Data_2_MASK 0xFF00
#define CAN1TDA3_Data_2_MASK C1TDA3_Data_2_MASK
#define C1TDA3_Data_2_BIT 8
#define CAN1TDA3_Data_2_BIT C1TDA3_Data_2_BIT
#define C1TDA3_Data_3_MASK 0xFF0000
#define CAN1TDA3_Data_3_MASK C1TDA3_Data_3_MASK
#define C1TDA3_Data_3_BIT 16
#define CAN1TDA3_Data_3_BIT C1TDA3_Data_3_BIT
#define C1TDA3_Data_4_MASK 0xFF000000
#define CAN1TDA3_Data_4_MASK C1TDA3_Data_4_MASK
#define C1TDA3_Data_4_BIT 24
#define CAN1TDA3_Data_4_BIT C1TDA3_Data_4_BIT

#define C1TDB3 (*(volatile unsigned long *)0xE004405C)
#define CAN1TDB3 C1TDB3
#define C1TDB3_OFFSET 0x5C
#define CAN1TDB3_OFFSET C1TDB3_OFFSET
#define C1TDB3_Data_5_MASK 0xFF
#define CAN1TDB3_Data_5_MASK C1TDB3_Data_5_MASK
#define C1TDB3_Data_5_BIT 0
#define CAN1TDB3_Data_5_BIT C1TDB3_Data_5_BIT
#define C1TDB3_Data_6_MASK 0xFF00
#define CAN1TDB3_Data_6_MASK C1TDB3_Data_6_MASK
#define C1TDB3_Data_6_BIT 8
#define CAN1TDB3_Data_6_BIT C1TDB3_Data_6_BIT
#define C1TDB3_Data_7_MASK 0xFF0000
#define CAN1TDB3_Data_7_MASK C1TDB3_Data_7_MASK
#define C1TDB3_Data_7_BIT 16
#define CAN1TDB3_Data_7_BIT C1TDB3_Data_7_BIT
#define C1TDB3_Data_8_MASK 0xFF000000
#define CAN1TDB3_Data_8_MASK C1TDB3_Data_8_MASK
#define C1TDB3_Data_8_BIT 24
#define CAN1TDB3_Data_8_BIT C1TDB3_Data_8_BIT

#define CAN2_BASE 0xE0048000

#define C2MOD (*(volatile unsigned long *)0xE0048000)
#define CAN2MOD C2MOD
#define C2MOD_OFFSET 0x0
#define CAN2MOD_OFFSET C2MOD_OFFSET
#define C2MOD_RM_MASK 0x1
#define CAN2MOD_RM_MASK C2MOD_RM_MASK
#define C2MOD_RM 0x1
#define CAN2MOD_RM C2MOD_RM
#define C2MOD_RM_BIT 0
#define CAN2MOD_RM_BIT C2MOD_RM_BIT
#define C2MOD_LOM_MASK 0x2
#define CAN2MOD_LOM_MASK C2MOD_LOM_MASK
#define C2MOD_LOM 0x2
#define CAN2MOD_LOM C2MOD_LOM
#define C2MOD_LOM_BIT 1
#define CAN2MOD_LOM_BIT C2MOD_LOM_BIT
#define C2MOD_STM_MASK 0x4
#define CAN2MOD_STM_MASK C2MOD_STM_MASK
#define C2MOD_STM 0x4
#define CAN2MOD_STM C2MOD_STM
#define C2MOD_STM_BIT 2
#define CAN2MOD_STM_BIT C2MOD_STM_BIT
#define C2MOD_TPM_MASK 0x8
#define CAN2MOD_TPM_MASK C2MOD_TPM_MASK
#define C2MOD_TPM 0x8
#define CAN2MOD_TPM C2MOD_TPM
#define C2MOD_TPM_BIT 3
#define CAN2MOD_TPM_BIT C2MOD_TPM_BIT
#define C2MOD_SM_MASK 0x10
#define CAN2MOD_SM_MASK C2MOD_SM_MASK
#define C2MOD_SM 0x10
#define CAN2MOD_SM C2MOD_SM
#define C2MOD_SM_BIT 4
#define CAN2MOD_SM_BIT C2MOD_SM_BIT
#define C2MOD_RPM_MASK 0x20
#define CAN2MOD_RPM_MASK C2MOD_RPM_MASK
#define C2MOD_RPM 0x20
#define CAN2MOD_RPM C2MOD_RPM
#define C2MOD_RPM_BIT 5
#define CAN2MOD_RPM_BIT C2MOD_RPM_BIT
#define C2MOD_TM_MASK 0x80
#define CAN2MOD_TM_MASK C2MOD_TM_MASK
#define C2MOD_TM 0x80
#define CAN2MOD_TM C2MOD_TM
#define C2MOD_TM_BIT 7
#define CAN2MOD_TM_BIT C2MOD_TM_BIT

#define C2CMR (*(volatile unsigned long *)0xE0048004)
#define CAN2CMR C2CMR
#define C2CMR_OFFSET 0x4
#define CAN2CMR_OFFSET C2CMR_OFFSET
#define C2CMR_TR_MASK 0x1
#define CAN2CMR_TR_MASK C2CMR_TR_MASK
#define C2CMR_TR 0x1
#define CAN2CMR_TR C2CMR_TR
#define C2CMR_TR_BIT 0
#define CAN2CMR_TR_BIT C2CMR_TR_BIT
#define C2CMR_AT_MASK 0x2
#define CAN2CMR_AT_MASK C2CMR_AT_MASK
#define C2CMR_AT 0x2
#define CAN2CMR_AT C2CMR_AT
#define C2CMR_AT_BIT 1
#define CAN2CMR_AT_BIT C2CMR_AT_BIT
#define C2CMR_RRB_MASK 0x4
#define CAN2CMR_RRB_MASK C2CMR_RRB_MASK
#define C2CMR_RRB 0x4
#define CAN2CMR_RRB C2CMR_RRB
#define C2CMR_RRB_BIT 2
#define CAN2CMR_RRB_BIT C2CMR_RRB_BIT
#define C2CMR_CDO_MASK 0x8
#define CAN2CMR_CDO_MASK C2CMR_CDO_MASK
#define C2CMR_CDO 0x8
#define CAN2CMR_CDO C2CMR_CDO
#define C2CMR_CDO_BIT 3
#define CAN2CMR_CDO_BIT C2CMR_CDO_BIT
#define C2CMR_SRR_MASK 0x10
#define CAN2CMR_SRR_MASK C2CMR_SRR_MASK
#define C2CMR_SRR 0x10
#define CAN2CMR_SRR C2CMR_SRR
#define C2CMR_SRR_BIT 4
#define CAN2CMR_SRR_BIT C2CMR_SRR_BIT
#define C2CMR_STB1_MASK 0x20
#define CAN2CMR_STB1_MASK C2CMR_STB1_MASK
#define C2CMR_STB1 0x20
#define CAN2CMR_STB1 C2CMR_STB1
#define C2CMR_STB1_BIT 5
#define CAN2CMR_STB1_BIT C2CMR_STB1_BIT
#define C2CMR_STB2_MASK 0x40
#define CAN2CMR_STB2_MASK C2CMR_STB2_MASK
#define C2CMR_STB2 0x40
#define CAN2CMR_STB2 C2CMR_STB2
#define C2CMR_STB2_BIT 6
#define CAN2CMR_STB2_BIT C2CMR_STB2_BIT
#define C2CMR_STB3_MASK 0x80
#define CAN2CMR_STB3_MASK C2CMR_STB3_MASK
#define C2CMR_STB3 0x80
#define CAN2CMR_STB3 C2CMR_STB3
#define C2CMR_STB3_BIT 7
#define CAN2CMR_STB3_BIT C2CMR_STB3_BIT

#define C2GSR (*(volatile unsigned long *)0xE0048008)
#define CAN2GSR C2GSR
#define C2GSR_OFFSET 0x8
#define CAN2GSR_OFFSET C2GSR_OFFSET
#define C2GSR_RBS_MASK 0x1
#define CAN2GSR_RBS_MASK C2GSR_RBS_MASK
#define C2GSR_RBS 0x1
#define CAN2GSR_RBS C2GSR_RBS
#define C2GSR_RBS_BIT 0
#define CAN2GSR_RBS_BIT C2GSR_RBS_BIT
#define C2GSR_DOS_MASK 0x2
#define CAN2GSR_DOS_MASK C2GSR_DOS_MASK
#define C2GSR_DOS 0x2
#define CAN2GSR_DOS C2GSR_DOS
#define C2GSR_DOS_BIT 1
#define CAN2GSR_DOS_BIT C2GSR_DOS_BIT
#define C2GSR_TBS_MASK 0x4
#define CAN2GSR_TBS_MASK C2GSR_TBS_MASK
#define C2GSR_TBS 0x4
#define CAN2GSR_TBS C2GSR_TBS
#define C2GSR_TBS_BIT 2
#define CAN2GSR_TBS_BIT C2GSR_TBS_BIT
#define C2GSR_TCS_MASK 0x8
#define CAN2GSR_TCS_MASK C2GSR_TCS_MASK
#define C2GSR_TCS 0x8
#define CAN2GSR_TCS C2GSR_TCS
#define C2GSR_TCS_BIT 3
#define CAN2GSR_TCS_BIT C2GSR_TCS_BIT
#define C2GSR_RS_MASK 0x10
#define CAN2GSR_RS_MASK C2GSR_RS_MASK
#define C2GSR_RS 0x10
#define CAN2GSR_RS C2GSR_RS
#define C2GSR_RS_BIT 4
#define CAN2GSR_RS_BIT C2GSR_RS_BIT
#define C2GSR_TS_MASK 0x20
#define CAN2GSR_TS_MASK C2GSR_TS_MASK
#define C2GSR_TS 0x20
#define CAN2GSR_TS C2GSR_TS
#define C2GSR_TS_BIT 5
#define CAN2GSR_TS_BIT C2GSR_TS_BIT
#define C2GSR_ES_MASK 0x40
#define CAN2GSR_ES_MASK C2GSR_ES_MASK
#define C2GSR_ES 0x40
#define CAN2GSR_ES C2GSR_ES
#define C2GSR_ES_BIT 6
#define CAN2GSR_ES_BIT C2GSR_ES_BIT
#define C2GSR_BS_MASK 0x80
#define CAN2GSR_BS_MASK C2GSR_BS_MASK
#define C2GSR_BS 0x80
#define CAN2GSR_BS C2GSR_BS
#define C2GSR_BS_BIT 7
#define CAN2GSR_BS_BIT C2GSR_BS_BIT
#define C2GSR_RXERR_MASK 0xFF0000
#define CAN2GSR_RXERR_MASK C2GSR_RXERR_MASK
#define C2GSR_RXERR_BIT 16
#define CAN2GSR_RXERR_BIT C2GSR_RXERR_BIT
#define C2GSR_TXERR_MASK 0xFF000000
#define CAN2GSR_TXERR_MASK C2GSR_TXERR_MASK
#define C2GSR_TXERR_BIT 24
#define CAN2GSR_TXERR_BIT C2GSR_TXERR_BIT

#define C2ICR (*(volatile unsigned long *)0xE004800C)
#define CAN2ICR C2ICR
#define C2ICR_OFFSET 0xC
#define CAN2ICR_OFFSET C2ICR_OFFSET
#define C2ICR_RI_MASK 0x1
#define CAN2ICR_RI_MASK C2ICR_RI_MASK
#define C2ICR_RI 0x1
#define CAN2ICR_RI C2ICR_RI
#define C2ICR_RI_BIT 0
#define CAN2ICR_RI_BIT C2ICR_RI_BIT
#define C2ICR_TI1_MASK 0x2
#define CAN2ICR_TI1_MASK C2ICR_TI1_MASK
#define C2ICR_TI1 0x2
#define CAN2ICR_TI1 C2ICR_TI1
#define C2ICR_TI1_BIT 1
#define CAN2ICR_TI1_BIT C2ICR_TI1_BIT
#define C2ICR_EI_MASK 0x4
#define CAN2ICR_EI_MASK C2ICR_EI_MASK
#define C2ICR_EI 0x4
#define CAN2ICR_EI C2ICR_EI
#define C2ICR_EI_BIT 2
#define CAN2ICR_EI_BIT C2ICR_EI_BIT
#define C2ICR_DOI_MASK 0x8
#define CAN2ICR_DOI_MASK C2ICR_DOI_MASK
#define C2ICR_DOI 0x8
#define CAN2ICR_DOI C2ICR_DOI
#define C2ICR_DOI_BIT 3
#define CAN2ICR_DOI_BIT C2ICR_DOI_BIT
#define C2ICR_WUI_MASK 0x10
#define CAN2ICR_WUI_MASK C2ICR_WUI_MASK
#define C2ICR_WUI 0x10
#define CAN2ICR_WUI C2ICR_WUI
#define C2ICR_WUI_BIT 4
#define CAN2ICR_WUI_BIT C2ICR_WUI_BIT
#define C2ICR_EPI_MASK 0x20
#define CAN2ICR_EPI_MASK C2ICR_EPI_MASK
#define C2ICR_EPI 0x20
#define CAN2ICR_EPI C2ICR_EPI
#define C2ICR_EPI_BIT 5
#define CAN2ICR_EPI_BIT C2ICR_EPI_BIT
#define C2ICR_ALI_MASK 0x40
#define CAN2ICR_ALI_MASK C2ICR_ALI_MASK
#define C2ICR_ALI 0x40
#define CAN2ICR_ALI C2ICR_ALI
#define C2ICR_ALI_BIT 6
#define CAN2ICR_ALI_BIT C2ICR_ALI_BIT
#define C2ICR_BEI_MASK 0x80
#define CAN2ICR_BEI_MASK C2ICR_BEI_MASK
#define C2ICR_BEI 0x80
#define CAN2ICR_BEI C2ICR_BEI
#define C2ICR_BEI_BIT 7
#define CAN2ICR_BEI_BIT C2ICR_BEI_BIT
#define C2ICR_IDI_MASK 0x100
#define CAN2ICR_IDI_MASK C2ICR_IDI_MASK
#define C2ICR_IDI 0x100
#define CAN2ICR_IDI C2ICR_IDI
#define C2ICR_IDI_BIT 8
#define CAN2ICR_IDI_BIT C2ICR_IDI_BIT
#define C2ICR_TI2_MASK 0x200
#define CAN2ICR_TI2_MASK C2ICR_TI2_MASK
#define C2ICR_TI2 0x200
#define CAN2ICR_TI2 C2ICR_TI2
#define C2ICR_TI2_BIT 9
#define CAN2ICR_TI2_BIT C2ICR_TI2_BIT
#define C2ICR_TI3_MASK 0x400
#define CAN2ICR_TI3_MASK C2ICR_TI3_MASK
#define C2ICR_TI3 0x400
#define CAN2ICR_TI3 C2ICR_TI3
#define C2ICR_TI3_BIT 10
#define CAN2ICR_TI3_BIT C2ICR_TI3_BIT
#define C2ICR_ERRBIT_MASK 0x1F0000
#define CAN2ICR_ERRBIT_MASK C2ICR_ERRBIT_MASK
#define C2ICR_ERRBIT_BIT 16
#define CAN2ICR_ERRBIT_BIT C2ICR_ERRBIT_BIT
#define C2ICR_ERRDIR_MASK 0x200000
#define CAN2ICR_ERRDIR_MASK C2ICR_ERRDIR_MASK
#define C2ICR_ERRDIR 0x200000
#define CAN2ICR_ERRDIR C2ICR_ERRDIR
#define C2ICR_ERRDIR_BIT 21
#define CAN2ICR_ERRDIR_BIT C2ICR_ERRDIR_BIT
#define C2ICR_ERRC_MASK 0xC00000
#define CAN2ICR_ERRC_MASK C2ICR_ERRC_MASK
#define C2ICR_ERRC_BIT 22
#define CAN2ICR_ERRC_BIT C2ICR_ERRC_BIT
#define C2ICR_ALCBIT_MASK 0x1F000000
#define CAN2ICR_ALCBIT_MASK C2ICR_ALCBIT_MASK
#define C2ICR_ALCBIT_BIT 24
#define CAN2ICR_ALCBIT_BIT C2ICR_ALCBIT_BIT

#define C2IER (*(volatile unsigned long *)0xE0048010)
#define CAN2IER C2IER
#define C2IER_OFFSET 0x10
#define CAN2IER_OFFSET C2IER_OFFSET
#define C2IER_RIE_MASK 0x1
#define CAN2IER_RIE_MASK C2IER_RIE_MASK
#define C2IER_RIE 0x1
#define CAN2IER_RIE C2IER_RIE
#define C2IER_RIE_BIT 0
#define CAN2IER_RIE_BIT C2IER_RIE_BIT
#define C2IER_TIE1_MASK 0x2
#define CAN2IER_TIE1_MASK C2IER_TIE1_MASK
#define C2IER_TIE1 0x2
#define CAN2IER_TIE1 C2IER_TIE1
#define C2IER_TIE1_BIT 1
#define CAN2IER_TIE1_BIT C2IER_TIE1_BIT
#define C2IER_EIE_MASK 0x4
#define CAN2IER_EIE_MASK C2IER_EIE_MASK
#define C2IER_EIE 0x4
#define CAN2IER_EIE C2IER_EIE
#define C2IER_EIE_BIT 2
#define CAN2IER_EIE_BIT C2IER_EIE_BIT
#define C2IER_DOIE_MASK 0x8
#define CAN2IER_DOIE_MASK C2IER_DOIE_MASK
#define C2IER_DOIE 0x8
#define CAN2IER_DOIE C2IER_DOIE
#define C2IER_DOIE_BIT 3
#define CAN2IER_DOIE_BIT C2IER_DOIE_BIT
#define C2IER_WUIE_MASK 0x10
#define CAN2IER_WUIE_MASK C2IER_WUIE_MASK
#define C2IER_WUIE 0x10
#define CAN2IER_WUIE C2IER_WUIE
#define C2IER_WUIE_BIT 4
#define CAN2IER_WUIE_BIT C2IER_WUIE_BIT
#define C2IER_EPIE_MASK 0x20
#define CAN2IER_EPIE_MASK C2IER_EPIE_MASK
#define C2IER_EPIE 0x20
#define CAN2IER_EPIE C2IER_EPIE
#define C2IER_EPIE_BIT 5
#define CAN2IER_EPIE_BIT C2IER_EPIE_BIT
#define C2IER_ALIE_MASK 0x40
#define CAN2IER_ALIE_MASK C2IER_ALIE_MASK
#define C2IER_ALIE 0x40
#define CAN2IER_ALIE C2IER_ALIE
#define C2IER_ALIE_BIT 6
#define CAN2IER_ALIE_BIT C2IER_ALIE_BIT
#define C2IER_BEIE_MASK 0x80
#define CAN2IER_BEIE_MASK C2IER_BEIE_MASK
#define C2IER_BEIE 0x80
#define CAN2IER_BEIE C2IER_BEIE
#define C2IER_BEIE_BIT 7
#define CAN2IER_BEIE_BIT C2IER_BEIE_BIT
#define C2IER_IDIE_MASK 0x100
#define CAN2IER_IDIE_MASK C2IER_IDIE_MASK
#define C2IER_IDIE 0x100
#define CAN2IER_IDIE C2IER_IDIE
#define C2IER_IDIE_BIT 8
#define CAN2IER_IDIE_BIT C2IER_IDIE_BIT
#define C2IER_TIE2_MASK 0x200
#define CAN2IER_TIE2_MASK C2IER_TIE2_MASK
#define C2IER_TIE2 0x200
#define CAN2IER_TIE2 C2IER_TIE2
#define C2IER_TIE2_BIT 9
#define CAN2IER_TIE2_BIT C2IER_TIE2_BIT
#define C2IER_TIE3_MASK 0x400
#define CAN2IER_TIE3_MASK C2IER_TIE3_MASK
#define C2IER_TIE3 0x400
#define CAN2IER_TIE3 C2IER_TIE3
#define C2IER_TIE3_BIT 10
#define CAN2IER_TIE3_BIT C2IER_TIE3_BIT

#define C2BTR (*(volatile unsigned long *)0xE0048014)
#define CAN2BTR C2BTR
#define C2BTR_OFFSET 0x14
#define CAN2BTR_OFFSET C2BTR_OFFSET
#define C2BTR_BRP_MASK 0x3FF
#define CAN2BTR_BRP_MASK C2BTR_BRP_MASK
#define C2BTR_BRP_BIT 0
#define CAN2BTR_BRP_BIT C2BTR_BRP_BIT
#define C2BTR_SJW_MASK 0xC000
#define CAN2BTR_SJW_MASK C2BTR_SJW_MASK
#define C2BTR_SJW_BIT 14
#define CAN2BTR_SJW_BIT C2BTR_SJW_BIT
#define C2BTR_TSEG1_MASK 0xF0000
#define CAN2BTR_TSEG1_MASK C2BTR_TSEG1_MASK
#define C2BTR_TSEG1_BIT 16
#define CAN2BTR_TSEG1_BIT C2BTR_TSEG1_BIT
#define C2BTR_TSEG2_MASK 0x700000
#define CAN2BTR_TSEG2_MASK C2BTR_TSEG2_MASK
#define C2BTR_TSEG2_BIT 20
#define CAN2BTR_TSEG2_BIT C2BTR_TSEG2_BIT
#define C2BTR_SAM_MASK 0x800000
#define CAN2BTR_SAM_MASK C2BTR_SAM_MASK
#define C2BTR_SAM 0x800000
#define CAN2BTR_SAM C2BTR_SAM
#define C2BTR_SAM_BIT 23
#define CAN2BTR_SAM_BIT C2BTR_SAM_BIT

#define C2EWL (*(volatile unsigned long *)0xE0048018)
#define CAN2EWL C2EWL
#define C2EWL_OFFSET 0x18
#define CAN2EWL_OFFSET C2EWL_OFFSET
#define C2EWL_EWL_MASK 0xFF
#define CAN2EWL_EWL_MASK C2EWL_EWL_MASK
#define C2EWL_EWL_BIT 0
#define CAN2EWL_EWL_BIT C2EWL_EWL_BIT

#define C2SR (*(volatile unsigned long *)0xE004801C)
#define CAN2SR C2SR
#define C2SR_OFFSET 0x1C
#define CAN2SR_OFFSET C2SR_OFFSET
#define C2SR_RBS_MASK 0x1
#define CAN2SR_RBS_MASK C2SR_RBS_MASK
#define C2SR_RBS 0x1
#define CAN2SR_RBS C2SR_RBS
#define C2SR_RBS_BIT 0
#define CAN2SR_RBS_BIT C2SR_RBS_BIT
#define C2SR_DOS_MASK 0x2
#define CAN2SR_DOS_MASK C2SR_DOS_MASK
#define C2SR_DOS 0x2
#define CAN2SR_DOS C2SR_DOS
#define C2SR_DOS_BIT 1
#define CAN2SR_DOS_BIT C2SR_DOS_BIT
#define C2SR_TBS1_MASK 0x4
#define CAN2SR_TBS1_MASK C2SR_TBS1_MASK
#define C2SR_TBS1 0x4
#define CAN2SR_TBS1 C2SR_TBS1
#define C2SR_TBS1_BIT 2
#define CAN2SR_TBS1_BIT C2SR_TBS1_BIT
#define C2SR_TCS1_MASK 0x8
#define CAN2SR_TCS1_MASK C2SR_TCS1_MASK
#define C2SR_TCS1 0x8
#define CAN2SR_TCS1 C2SR_TCS1
#define C2SR_TCS1_BIT 3
#define CAN2SR_TCS1_BIT C2SR_TCS1_BIT
#define C2SR_RS_MASK 0x10
#define CAN2SR_RS_MASK C2SR_RS_MASK
#define C2SR_RS 0x10
#define CAN2SR_RS C2SR_RS
#define C2SR_RS_BIT 4
#define CAN2SR_RS_BIT C2SR_RS_BIT
#define C2SR_TS1_MASK 0x20
#define CAN2SR_TS1_MASK C2SR_TS1_MASK
#define C2SR_TS1 0x20
#define CAN2SR_TS1 C2SR_TS1
#define C2SR_TS1_BIT 5
#define CAN2SR_TS1_BIT C2SR_TS1_BIT
#define C2SR_ES_MASK 0x40
#define CAN2SR_ES_MASK C2SR_ES_MASK
#define C2SR_ES 0x40
#define CAN2SR_ES C2SR_ES
#define C2SR_ES_BIT 6
#define CAN2SR_ES_BIT C2SR_ES_BIT
#define C2SR_BS_MASK 0x80
#define CAN2SR_BS_MASK C2SR_BS_MASK
#define C2SR_BS 0x80
#define CAN2SR_BS C2SR_BS
#define C2SR_BS_BIT 7
#define CAN2SR_BS_BIT C2SR_BS_BIT
#define C2SR_RBS2_MASK 0x100
#define CAN2SR_RBS2_MASK C2SR_RBS2_MASK
#define C2SR_RBS2 0x100
#define CAN2SR_RBS2 C2SR_RBS2
#define C2SR_RBS2_BIT 8
#define CAN2SR_RBS2_BIT C2SR_RBS2_BIT
#define C2SR_DOS2_MASK 0x200
#define CAN2SR_DOS2_MASK C2SR_DOS2_MASK
#define C2SR_DOS2 0x200
#define CAN2SR_DOS2 C2SR_DOS2
#define C2SR_DOS2_BIT 9
#define CAN2SR_DOS2_BIT C2SR_DOS2_BIT
#define C2SR_TBS2_MASK 0x400
#define CAN2SR_TBS2_MASK C2SR_TBS2_MASK
#define C2SR_TBS2 0x400
#define CAN2SR_TBS2 C2SR_TBS2
#define C2SR_TBS2_BIT 10
#define CAN2SR_TBS2_BIT C2SR_TBS2_BIT
#define C2SR_TCS2_MASK 0x800
#define CAN2SR_TCS2_MASK C2SR_TCS2_MASK
#define C2SR_TCS2 0x800
#define CAN2SR_TCS2 C2SR_TCS2
#define C2SR_TCS2_BIT 11
#define CAN2SR_TCS2_BIT C2SR_TCS2_BIT
#define C2SR_RS2_MASK 0x1000
#define CAN2SR_RS2_MASK C2SR_RS2_MASK
#define C2SR_RS2 0x1000
#define CAN2SR_RS2 C2SR_RS2
#define C2SR_RS2_BIT 12
#define CAN2SR_RS2_BIT C2SR_RS2_BIT
#define C2SR_TS2_MASK 0x2000
#define CAN2SR_TS2_MASK C2SR_TS2_MASK
#define C2SR_TS2 0x2000
#define CAN2SR_TS2 C2SR_TS2
#define C2SR_TS2_BIT 13
#define CAN2SR_TS2_BIT C2SR_TS2_BIT
#define C2SR_ES2_MASK 0x4000
#define CAN2SR_ES2_MASK C2SR_ES2_MASK
#define C2SR_ES2 0x4000
#define CAN2SR_ES2 C2SR_ES2
#define C2SR_ES2_BIT 14
#define CAN2SR_ES2_BIT C2SR_ES2_BIT
#define C2SR_BS2_MASK 0x8000
#define CAN2SR_BS2_MASK C2SR_BS2_MASK
#define C2SR_BS2 0x8000
#define CAN2SR_BS2 C2SR_BS2
#define C2SR_BS2_BIT 15
#define CAN2SR_BS2_BIT C2SR_BS2_BIT
#define C2SR_RBS3_MASK 0x10000
#define CAN2SR_RBS3_MASK C2SR_RBS3_MASK
#define C2SR_RBS3 0x10000
#define CAN2SR_RBS3 C2SR_RBS3
#define C2SR_RBS3_BIT 16
#define CAN2SR_RBS3_BIT C2SR_RBS3_BIT
#define C2SR_DOS3_MASK 0x20000
#define CAN2SR_DOS3_MASK C2SR_DOS3_MASK
#define C2SR_DOS3 0x20000
#define CAN2SR_DOS3 C2SR_DOS3
#define C2SR_DOS3_BIT 17
#define CAN2SR_DOS3_BIT C2SR_DOS3_BIT
#define C2SR_TBS3_MASK 0x40000
#define CAN2SR_TBS3_MASK C2SR_TBS3_MASK
#define C2SR_TBS3 0x40000
#define CAN2SR_TBS3 C2SR_TBS3
#define C2SR_TBS3_BIT 18
#define CAN2SR_TBS3_BIT C2SR_TBS3_BIT
#define C2SR_TCS3_MASK 0x80000
#define CAN2SR_TCS3_MASK C2SR_TCS3_MASK
#define C2SR_TCS3 0x80000
#define CAN2SR_TCS3 C2SR_TCS3
#define C2SR_TCS3_BIT 19
#define CAN2SR_TCS3_BIT C2SR_TCS3_BIT
#define C2SR_RS3_MASK 0x100000
#define CAN2SR_RS3_MASK C2SR_RS3_MASK
#define C2SR_RS3 0x100000
#define CAN2SR_RS3 C2SR_RS3
#define C2SR_RS3_BIT 20
#define CAN2SR_RS3_BIT C2SR_RS3_BIT
#define C2SR_TS3_MASK 0x200000
#define CAN2SR_TS3_MASK C2SR_TS3_MASK
#define C2SR_TS3 0x200000
#define CAN2SR_TS3 C2SR_TS3
#define C2SR_TS3_BIT 21
#define CAN2SR_TS3_BIT C2SR_TS3_BIT
#define C2SR_ES3_MASK 0x400000
#define CAN2SR_ES3_MASK C2SR_ES3_MASK
#define C2SR_ES3 0x400000
#define CAN2SR_ES3 C2SR_ES3
#define C2SR_ES3_BIT 22
#define CAN2SR_ES3_BIT C2SR_ES3_BIT
#define C2SR_BS3_MASK 0x800000
#define CAN2SR_BS3_MASK C2SR_BS3_MASK
#define C2SR_BS3 0x800000
#define CAN2SR_BS3 C2SR_BS3
#define C2SR_BS3_BIT 23
#define CAN2SR_BS3_BIT C2SR_BS3_BIT

#define C2RFS (*(volatile unsigned long *)0xE0048020)
#define CAN2RFS C2RFS
#define C2RFS_OFFSET 0x20
#define CAN2RFS_OFFSET C2RFS_OFFSET
#define C2RFS_ID_Index_MASK 0x3FF
#define CAN2RFS_ID_Index_MASK C2RFS_ID_Index_MASK
#define C2RFS_ID_Index_BIT 0
#define CAN2RFS_ID_Index_BIT C2RFS_ID_Index_BIT
#define C2RFS_BP_MASK 0x400
#define CAN2RFS_BP_MASK C2RFS_BP_MASK
#define C2RFS_BP 0x400
#define CAN2RFS_BP C2RFS_BP
#define C2RFS_BP_BIT 10
#define CAN2RFS_BP_BIT C2RFS_BP_BIT
#define C2RFS_DLC_MASK 0xF0000
#define CAN2RFS_DLC_MASK C2RFS_DLC_MASK
#define C2RFS_DLC_BIT 16
#define CAN2RFS_DLC_BIT C2RFS_DLC_BIT
#define C2RFS_RTR_MASK 0x40000000
#define CAN2RFS_RTR_MASK C2RFS_RTR_MASK
#define C2RFS_RTR 0x40000000
#define CAN2RFS_RTR C2RFS_RTR
#define C2RFS_RTR_BIT 30
#define CAN2RFS_RTR_BIT C2RFS_RTR_BIT
#define C2RFS_FF_MASK 0x80000000
#define CAN2RFS_FF_MASK C2RFS_FF_MASK
#define C2RFS_FF 0x80000000
#define CAN2RFS_FF C2RFS_FF
#define C2RFS_FF_BIT 31
#define CAN2RFS_FF_BIT C2RFS_FF_BIT

#define C2RID (*(volatile unsigned long *)0xE0048024)
#define CAN2RID C2RID
#define C2RID_OFFSET 0x24
#define CAN2RID_OFFSET C2RID_OFFSET
#define C2RID_ID_MASK 0x7FF
#define CAN2RID_ID_MASK C2RID_ID_MASK
#define C2RID_ID_BIT 0
#define CAN2RID_ID_BIT C2RID_ID_BIT

#define C2RDA (*(volatile unsigned long *)0xE0048028)
#define CAN2RDA C2RDA
#define C2RDA_OFFSET 0x28
#define CAN2RDA_OFFSET C2RDA_OFFSET
#define C2RDA_Data_1_MASK 0xFF
#define CAN2RDA_Data_1_MASK C2RDA_Data_1_MASK
#define C2RDA_Data_1_BIT 0
#define CAN2RDA_Data_1_BIT C2RDA_Data_1_BIT
#define C2RDA_Data_2_MASK 0xFF00
#define CAN2RDA_Data_2_MASK C2RDA_Data_2_MASK
#define C2RDA_Data_2_BIT 8
#define CAN2RDA_Data_2_BIT C2RDA_Data_2_BIT
#define C2RDA_Data_3_MASK 0xFF0000
#define CAN2RDA_Data_3_MASK C2RDA_Data_3_MASK
#define C2RDA_Data_3_BIT 16
#define CAN2RDA_Data_3_BIT C2RDA_Data_3_BIT
#define C2RDA_Data_4_MASK 0xFF000000
#define CAN2RDA_Data_4_MASK C2RDA_Data_4_MASK
#define C2RDA_Data_4_BIT 24
#define CAN2RDA_Data_4_BIT C2RDA_Data_4_BIT

#define C2RDB (*(volatile unsigned long *)0xE004802C)
#define CAN2RDB C2RDB
#define C2RDB_OFFSET 0x2C
#define CAN2RDB_OFFSET C2RDB_OFFSET
#define C2RDB_Data_5_MASK 0xFF
#define CAN2RDB_Data_5_MASK C2RDB_Data_5_MASK
#define C2RDB_Data_5_BIT 0
#define CAN2RDB_Data_5_BIT C2RDB_Data_5_BIT
#define C2RDB_Data_6_MASK 0xFF00
#define CAN2RDB_Data_6_MASK C2RDB_Data_6_MASK
#define C2RDB_Data_6_BIT 8
#define CAN2RDB_Data_6_BIT C2RDB_Data_6_BIT
#define C2RDB_Data_7_MASK 0xFF0000
#define CAN2RDB_Data_7_MASK C2RDB_Data_7_MASK
#define C2RDB_Data_7_BIT 16
#define CAN2RDB_Data_7_BIT C2RDB_Data_7_BIT
#define C2RDB_Data_8_MASK 0xFF000000
#define CAN2RDB_Data_8_MASK C2RDB_Data_8_MASK
#define C2RDB_Data_8_BIT 24
#define CAN2RDB_Data_8_BIT C2RDB_Data_8_BIT

#define C2TFI1 (*(volatile unsigned long *)0xE0048030)
#define CAN2TFI1 C2TFI1
#define C2TFI1_OFFSET 0x30
#define CAN2TFI1_OFFSET C2TFI1_OFFSET
#define C2TFI1_PRIO_MASK 0xFF
#define CAN2TFI1_PRIO_MASK C2TFI1_PRIO_MASK
#define C2TFI1_PRIO_BIT 0
#define CAN2TFI1_PRIO_BIT C2TFI1_PRIO_BIT
#define C2TFI1_DLC_MASK 0xF0000
#define CAN2TFI1_DLC_MASK C2TFI1_DLC_MASK
#define C2TFI1_DLC_BIT 16
#define CAN2TFI1_DLC_BIT C2TFI1_DLC_BIT
#define C2TFI1_RTR_MASK 0x40000000
#define CAN2TFI1_RTR_MASK C2TFI1_RTR_MASK
#define C2TFI1_RTR 0x40000000
#define CAN2TFI1_RTR C2TFI1_RTR
#define C2TFI1_RTR_BIT 30
#define CAN2TFI1_RTR_BIT C2TFI1_RTR_BIT
#define C2TFI1_FF_MASK 0x80000000
#define CAN2TFI1_FF_MASK C2TFI1_FF_MASK
#define C2TFI1_FF 0x80000000
#define CAN2TFI1_FF C2TFI1_FF
#define C2TFI1_FF_BIT 31
#define CAN2TFI1_FF_BIT C2TFI1_FF_BIT

#define C2TID1 (*(volatile unsigned long *)0xE0048034)
#define CAN2TID1 C2TID1
#define C2TID1_OFFSET 0x34
#define CAN2TID1_OFFSET C2TID1_OFFSET
#define C2TID1_ID_MASK 0x7FF
#define CAN2TID1_ID_MASK C2TID1_ID_MASK
#define C2TID1_ID_BIT 0
#define CAN2TID1_ID_BIT C2TID1_ID_BIT

#define C2TDA1 (*(volatile unsigned long *)0xE0048038)
#define CAN2TDA1 C2TDA1
#define C2TDA1_OFFSET 0x38
#define CAN2TDA1_OFFSET C2TDA1_OFFSET
#define C2TDA1_Data_1_MASK 0xFF
#define CAN2TDA1_Data_1_MASK C2TDA1_Data_1_MASK
#define C2TDA1_Data_1_BIT 0
#define CAN2TDA1_Data_1_BIT C2TDA1_Data_1_BIT
#define C2TDA1_Data_2_MASK 0xFF00
#define CAN2TDA1_Data_2_MASK C2TDA1_Data_2_MASK
#define C2TDA1_Data_2_BIT 8
#define CAN2TDA1_Data_2_BIT C2TDA1_Data_2_BIT
#define C2TDA1_Data_3_MASK 0xFF0000
#define CAN2TDA1_Data_3_MASK C2TDA1_Data_3_MASK
#define C2TDA1_Data_3_BIT 16
#define CAN2TDA1_Data_3_BIT C2TDA1_Data_3_BIT
#define C2TDA1_Data_4_MASK 0xFF000000
#define CAN2TDA1_Data_4_MASK C2TDA1_Data_4_MASK
#define C2TDA1_Data_4_BIT 24
#define CAN2TDA1_Data_4_BIT C2TDA1_Data_4_BIT

#define C2TDB1 (*(volatile unsigned long *)0xE004803C)
#define CAN2TDB1 C2TDB1
#define C2TDB1_OFFSET 0x3C
#define CAN2TDB1_OFFSET C2TDB1_OFFSET
#define C2TDB1_Data_5_MASK 0xFF
#define CAN2TDB1_Data_5_MASK C2TDB1_Data_5_MASK
#define C2TDB1_Data_5_BIT 0
#define CAN2TDB1_Data_5_BIT C2TDB1_Data_5_BIT
#define C2TDB1_Data_6_MASK 0xFF00
#define CAN2TDB1_Data_6_MASK C2TDB1_Data_6_MASK
#define C2TDB1_Data_6_BIT 8
#define CAN2TDB1_Data_6_BIT C2TDB1_Data_6_BIT
#define C2TDB1_Data_7_MASK 0xFF0000
#define CAN2TDB1_Data_7_MASK C2TDB1_Data_7_MASK
#define C2TDB1_Data_7_BIT 16
#define CAN2TDB1_Data_7_BIT C2TDB1_Data_7_BIT
#define C2TDB1_Data_8_MASK 0xFF000000
#define CAN2TDB1_Data_8_MASK C2TDB1_Data_8_MASK
#define C2TDB1_Data_8_BIT 24
#define CAN2TDB1_Data_8_BIT C2TDB1_Data_8_BIT

#define C2TFI2 (*(volatile unsigned long *)0xE0048040)
#define CAN2TFI2 C2TFI2
#define C2TFI2_OFFSET 0x40
#define CAN2TFI2_OFFSET C2TFI2_OFFSET
#define C2TFI2_PRIO_MASK 0xFF
#define CAN2TFI2_PRIO_MASK C2TFI2_PRIO_MASK
#define C2TFI2_PRIO_BIT 0
#define CAN2TFI2_PRIO_BIT C2TFI2_PRIO_BIT
#define C2TFI2_DLC_MASK 0xF0000
#define CAN2TFI2_DLC_MASK C2TFI2_DLC_MASK
#define C2TFI2_DLC_BIT 16
#define CAN2TFI2_DLC_BIT C2TFI2_DLC_BIT
#define C2TFI2_RTR_MASK 0x40000000
#define CAN2TFI2_RTR_MASK C2TFI2_RTR_MASK
#define C2TFI2_RTR 0x40000000
#define CAN2TFI2_RTR C2TFI2_RTR
#define C2TFI2_RTR_BIT 30
#define CAN2TFI2_RTR_BIT C2TFI2_RTR_BIT
#define C2TFI2_FF_MASK 0x80000000
#define CAN2TFI2_FF_MASK C2TFI2_FF_MASK
#define C2TFI2_FF 0x80000000
#define CAN2TFI2_FF C2TFI2_FF
#define C2TFI2_FF_BIT 31
#define CAN2TFI2_FF_BIT C2TFI2_FF_BIT

#define C2TID2 (*(volatile unsigned long *)0xE0048044)
#define CAN2TID2 C2TID2
#define C2TID2_OFFSET 0x44
#define CAN2TID2_OFFSET C2TID2_OFFSET
#define C2TID2_ID_MASK 0x7FF
#define CAN2TID2_ID_MASK C2TID2_ID_MASK
#define C2TID2_ID_BIT 0
#define CAN2TID2_ID_BIT C2TID2_ID_BIT

#define C2TDA2 (*(volatile unsigned long *)0xE0048048)
#define CAN2TDA2 C2TDA2
#define C2TDA2_OFFSET 0x48
#define CAN2TDA2_OFFSET C2TDA2_OFFSET
#define C2TDA2_Data_1_MASK 0xFF
#define CAN2TDA2_Data_1_MASK C2TDA2_Data_1_MASK
#define C2TDA2_Data_1_BIT 0
#define CAN2TDA2_Data_1_BIT C2TDA2_Data_1_BIT
#define C2TDA2_Data_2_MASK 0xFF00
#define CAN2TDA2_Data_2_MASK C2TDA2_Data_2_MASK
#define C2TDA2_Data_2_BIT 8
#define CAN2TDA2_Data_2_BIT C2TDA2_Data_2_BIT
#define C2TDA2_Data_3_MASK 0xFF0000
#define CAN2TDA2_Data_3_MASK C2TDA2_Data_3_MASK
#define C2TDA2_Data_3_BIT 16
#define CAN2TDA2_Data_3_BIT C2TDA2_Data_3_BIT
#define C2TDA2_Data_4_MASK 0xFF000000
#define CAN2TDA2_Data_4_MASK C2TDA2_Data_4_MASK
#define C2TDA2_Data_4_BIT 24
#define CAN2TDA2_Data_4_BIT C2TDA2_Data_4_BIT

#define C2TDB2 (*(volatile unsigned long *)0xE004804C)
#define CAN2TDB2 C2TDB2
#define C2TDB2_OFFSET 0x4C
#define CAN2TDB2_OFFSET C2TDB2_OFFSET
#define C2TDB2_Data_5_MASK 0xFF
#define CAN2TDB2_Data_5_MASK C2TDB2_Data_5_MASK
#define C2TDB2_Data_5_BIT 0
#define CAN2TDB2_Data_5_BIT C2TDB2_Data_5_BIT
#define C2TDB2_Data_6_MASK 0xFF00
#define CAN2TDB2_Data_6_MASK C2TDB2_Data_6_MASK
#define C2TDB2_Data_6_BIT 8
#define CAN2TDB2_Data_6_BIT C2TDB2_Data_6_BIT
#define C2TDB2_Data_7_MASK 0xFF0000
#define CAN2TDB2_Data_7_MASK C2TDB2_Data_7_MASK
#define C2TDB2_Data_7_BIT 16
#define CAN2TDB2_Data_7_BIT C2TDB2_Data_7_BIT
#define C2TDB2_Data_8_MASK 0xFF000000
#define CAN2TDB2_Data_8_MASK C2TDB2_Data_8_MASK
#define C2TDB2_Data_8_BIT 24
#define CAN2TDB2_Data_8_BIT C2TDB2_Data_8_BIT

#define C2TFI3 (*(volatile unsigned long *)0xE0048050)
#define CAN2TFI3 C2TFI3
#define C2TFI3_OFFSET 0x50
#define CAN2TFI3_OFFSET C2TFI3_OFFSET
#define C2TFI3_PRIO_MASK 0xFF
#define CAN2TFI3_PRIO_MASK C2TFI3_PRIO_MASK
#define C2TFI3_PRIO_BIT 0
#define CAN2TFI3_PRIO_BIT C2TFI3_PRIO_BIT
#define C2TFI3_DLC_MASK 0xF0000
#define CAN2TFI3_DLC_MASK C2TFI3_DLC_MASK
#define C2TFI3_DLC_BIT 16
#define CAN2TFI3_DLC_BIT C2TFI3_DLC_BIT
#define C2TFI3_RTR_MASK 0x40000000
#define CAN2TFI3_RTR_MASK C2TFI3_RTR_MASK
#define C2TFI3_RTR 0x40000000
#define CAN2TFI3_RTR C2TFI3_RTR
#define C2TFI3_RTR_BIT 30
#define CAN2TFI3_RTR_BIT C2TFI3_RTR_BIT
#define C2TFI3_FF_MASK 0x80000000
#define CAN2TFI3_FF_MASK C2TFI3_FF_MASK
#define C2TFI3_FF 0x80000000
#define CAN2TFI3_FF C2TFI3_FF
#define C2TFI3_FF_BIT 31
#define CAN2TFI3_FF_BIT C2TFI3_FF_BIT

#define C2TID3 (*(volatile unsigned long *)0xE0048054)
#define CAN2TID3 C2TID3
#define C2TID3_OFFSET 0x54
#define CAN2TID3_OFFSET C2TID3_OFFSET
#define C2TID3_ID_MASK 0x7FF
#define CAN2TID3_ID_MASK C2TID3_ID_MASK
#define C2TID3_ID_BIT 0
#define CAN2TID3_ID_BIT C2TID3_ID_BIT

#define C2TDA3 (*(volatile unsigned long *)0xE0048058)
#define CAN2TDA3 C2TDA3
#define C2TDA3_OFFSET 0x58
#define CAN2TDA3_OFFSET C2TDA3_OFFSET
#define C2TDA3_Data_1_MASK 0xFF
#define CAN2TDA3_Data_1_MASK C2TDA3_Data_1_MASK
#define C2TDA3_Data_1_BIT 0
#define CAN2TDA3_Data_1_BIT C2TDA3_Data_1_BIT
#define C2TDA3_Data_2_MASK 0xFF00
#define CAN2TDA3_Data_2_MASK C2TDA3_Data_2_MASK
#define C2TDA3_Data_2_BIT 8
#define CAN2TDA3_Data_2_BIT C2TDA3_Data_2_BIT
#define C2TDA3_Data_3_MASK 0xFF0000
#define CAN2TDA3_Data_3_MASK C2TDA3_Data_3_MASK
#define C2TDA3_Data_3_BIT 16
#define CAN2TDA3_Data_3_BIT C2TDA3_Data_3_BIT
#define C2TDA3_Data_4_MASK 0xFF000000
#define CAN2TDA3_Data_4_MASK C2TDA3_Data_4_MASK
#define C2TDA3_Data_4_BIT 24
#define CAN2TDA3_Data_4_BIT C2TDA3_Data_4_BIT

#define C2TDB3 (*(volatile unsigned long *)0xE004805C)
#define CAN2TDB3 C2TDB3
#define C2TDB3_OFFSET 0x5C
#define CAN2TDB3_OFFSET C2TDB3_OFFSET
#define C2TDB3_Data_5_MASK 0xFF
#define CAN2TDB3_Data_5_MASK C2TDB3_Data_5_MASK
#define C2TDB3_Data_5_BIT 0
#define CAN2TDB3_Data_5_BIT C2TDB3_Data_5_BIT
#define C2TDB3_Data_6_MASK 0xFF00
#define CAN2TDB3_Data_6_MASK C2TDB3_Data_6_MASK
#define C2TDB3_Data_6_BIT 8
#define CAN2TDB3_Data_6_BIT C2TDB3_Data_6_BIT
#define C2TDB3_Data_7_MASK 0xFF0000
#define CAN2TDB3_Data_7_MASK C2TDB3_Data_7_MASK
#define C2TDB3_Data_7_BIT 16
#define CAN2TDB3_Data_7_BIT C2TDB3_Data_7_BIT
#define C2TDB3_Data_8_MASK 0xFF000000
#define CAN2TDB3_Data_8_MASK C2TDB3_Data_8_MASK
#define C2TDB3_Data_8_BIT 24
#define CAN2TDB3_Data_8_BIT C2TDB3_Data_8_BIT

#define CAN3_BASE 0xE004C000

#define C3MOD (*(volatile unsigned long *)0xE004C000)
#define CAN3MOD C3MOD
#define C3MOD_OFFSET 0x0
#define CAN3MOD_OFFSET C3MOD_OFFSET
#define C3MOD_RM_MASK 0x1
#define CAN3MOD_RM_MASK C3MOD_RM_MASK
#define C3MOD_RM 0x1
#define CAN3MOD_RM C3MOD_RM
#define C3MOD_RM_BIT 0
#define CAN3MOD_RM_BIT C3MOD_RM_BIT
#define C3MOD_LOM_MASK 0x2
#define CAN3MOD_LOM_MASK C3MOD_LOM_MASK
#define C3MOD_LOM 0x2
#define CAN3MOD_LOM C3MOD_LOM
#define C3MOD_LOM_BIT 1
#define CAN3MOD_LOM_BIT C3MOD_LOM_BIT
#define C3MOD_STM_MASK 0x4
#define CAN3MOD_STM_MASK C3MOD_STM_MASK
#define C3MOD_STM 0x4
#define CAN3MOD_STM C3MOD_STM
#define C3MOD_STM_BIT 2
#define CAN3MOD_STM_BIT C3MOD_STM_BIT
#define C3MOD_TPM_MASK 0x8
#define CAN3MOD_TPM_MASK C3MOD_TPM_MASK
#define C3MOD_TPM 0x8
#define CAN3MOD_TPM C3MOD_TPM
#define C3MOD_TPM_BIT 3
#define CAN3MOD_TPM_BIT C3MOD_TPM_BIT
#define C3MOD_SM_MASK 0x10
#define CAN3MOD_SM_MASK C3MOD_SM_MASK
#define C3MOD_SM 0x10
#define CAN3MOD_SM C3MOD_SM
#define C3MOD_SM_BIT 4
#define CAN3MOD_SM_BIT C3MOD_SM_BIT
#define C3MOD_RPM_MASK 0x20
#define CAN3MOD_RPM_MASK C3MOD_RPM_MASK
#define C3MOD_RPM 0x20
#define CAN3MOD_RPM C3MOD_RPM
#define C3MOD_RPM_BIT 5
#define CAN3MOD_RPM_BIT C3MOD_RPM_BIT
#define C3MOD_TM_MASK 0x80
#define CAN3MOD_TM_MASK C3MOD_TM_MASK
#define C3MOD_TM 0x80
#define CAN3MOD_TM C3MOD_TM
#define C3MOD_TM_BIT 7
#define CAN3MOD_TM_BIT C3MOD_TM_BIT

#define C3CMR (*(volatile unsigned long *)0xE004C004)
#define CAN3CMR C3CMR
#define C3CMR_OFFSET 0x4
#define CAN3CMR_OFFSET C3CMR_OFFSET
#define C3CMR_TR_MASK 0x1
#define CAN3CMR_TR_MASK C3CMR_TR_MASK
#define C3CMR_TR 0x1
#define CAN3CMR_TR C3CMR_TR
#define C3CMR_TR_BIT 0
#define CAN3CMR_TR_BIT C3CMR_TR_BIT
#define C3CMR_AT_MASK 0x2
#define CAN3CMR_AT_MASK C3CMR_AT_MASK
#define C3CMR_AT 0x2
#define CAN3CMR_AT C3CMR_AT
#define C3CMR_AT_BIT 1
#define CAN3CMR_AT_BIT C3CMR_AT_BIT
#define C3CMR_RRB_MASK 0x4
#define CAN3CMR_RRB_MASK C3CMR_RRB_MASK
#define C3CMR_RRB 0x4
#define CAN3CMR_RRB C3CMR_RRB
#define C3CMR_RRB_BIT 2
#define CAN3CMR_RRB_BIT C3CMR_RRB_BIT
#define C3CMR_CDO_MASK 0x8
#define CAN3CMR_CDO_MASK C3CMR_CDO_MASK
#define C3CMR_CDO 0x8
#define CAN3CMR_CDO C3CMR_CDO
#define C3CMR_CDO_BIT 3
#define CAN3CMR_CDO_BIT C3CMR_CDO_BIT
#define C3CMR_SRR_MASK 0x10
#define CAN3CMR_SRR_MASK C3CMR_SRR_MASK
#define C3CMR_SRR 0x10
#define CAN3CMR_SRR C3CMR_SRR
#define C3CMR_SRR_BIT 4
#define CAN3CMR_SRR_BIT C3CMR_SRR_BIT
#define C3CMR_STB1_MASK 0x20
#define CAN3CMR_STB1_MASK C3CMR_STB1_MASK
#define C3CMR_STB1 0x20
#define CAN3CMR_STB1 C3CMR_STB1
#define C3CMR_STB1_BIT 5
#define CAN3CMR_STB1_BIT C3CMR_STB1_BIT
#define C3CMR_STB2_MASK 0x40
#define CAN3CMR_STB2_MASK C3CMR_STB2_MASK
#define C3CMR_STB2 0x40
#define CAN3CMR_STB2 C3CMR_STB2
#define C3CMR_STB2_BIT 6
#define CAN3CMR_STB2_BIT C3CMR_STB2_BIT
#define C3CMR_STB3_MASK 0x80
#define CAN3CMR_STB3_MASK C3CMR_STB3_MASK
#define C3CMR_STB3 0x80
#define CAN3CMR_STB3 C3CMR_STB3
#define C3CMR_STB3_BIT 7
#define CAN3CMR_STB3_BIT C3CMR_STB3_BIT

#define C3GSR (*(volatile unsigned long *)0xE004C008)
#define CAN3GSR C3GSR
#define C3GSR_OFFSET 0x8
#define CAN3GSR_OFFSET C3GSR_OFFSET
#define C3GSR_RBS_MASK 0x1
#define CAN3GSR_RBS_MASK C3GSR_RBS_MASK
#define C3GSR_RBS 0x1
#define CAN3GSR_RBS C3GSR_RBS
#define C3GSR_RBS_BIT 0
#define CAN3GSR_RBS_BIT C3GSR_RBS_BIT
#define C3GSR_DOS_MASK 0x2
#define CAN3GSR_DOS_MASK C3GSR_DOS_MASK
#define C3GSR_DOS 0x2
#define CAN3GSR_DOS C3GSR_DOS
#define C3GSR_DOS_BIT 1
#define CAN3GSR_DOS_BIT C3GSR_DOS_BIT
#define C3GSR_TBS_MASK 0x4
#define CAN3GSR_TBS_MASK C3GSR_TBS_MASK
#define C3GSR_TBS 0x4
#define CAN3GSR_TBS C3GSR_TBS
#define C3GSR_TBS_BIT 2
#define CAN3GSR_TBS_BIT C3GSR_TBS_BIT
#define C3GSR_TCS_MASK 0x8
#define CAN3GSR_TCS_MASK C3GSR_TCS_MASK
#define C3GSR_TCS 0x8
#define CAN3GSR_TCS C3GSR_TCS
#define C3GSR_TCS_BIT 3
#define CAN3GSR_TCS_BIT C3GSR_TCS_BIT
#define C3GSR_RS_MASK 0x10
#define CAN3GSR_RS_MASK C3GSR_RS_MASK
#define C3GSR_RS 0x10
#define CAN3GSR_RS C3GSR_RS
#define C3GSR_RS_BIT 4
#define CAN3GSR_RS_BIT C3GSR_RS_BIT
#define C3GSR_TS_MASK 0x20
#define CAN3GSR_TS_MASK C3GSR_TS_MASK
#define C3GSR_TS 0x20
#define CAN3GSR_TS C3GSR_TS
#define C3GSR_TS_BIT 5
#define CAN3GSR_TS_BIT C3GSR_TS_BIT
#define C3GSR_ES_MASK 0x40
#define CAN3GSR_ES_MASK C3GSR_ES_MASK
#define C3GSR_ES 0x40
#define CAN3GSR_ES C3GSR_ES
#define C3GSR_ES_BIT 6
#define CAN3GSR_ES_BIT C3GSR_ES_BIT
#define C3GSR_BS_MASK 0x80
#define CAN3GSR_BS_MASK C3GSR_BS_MASK
#define C3GSR_BS 0x80
#define CAN3GSR_BS C3GSR_BS
#define C3GSR_BS_BIT 7
#define CAN3GSR_BS_BIT C3GSR_BS_BIT
#define C3GSR_RXERR_MASK 0xFF0000
#define CAN3GSR_RXERR_MASK C3GSR_RXERR_MASK
#define C3GSR_RXERR_BIT 16
#define CAN3GSR_RXERR_BIT C3GSR_RXERR_BIT
#define C3GSR_TXERR_MASK 0xFF000000
#define CAN3GSR_TXERR_MASK C3GSR_TXERR_MASK
#define C3GSR_TXERR_BIT 24
#define CAN3GSR_TXERR_BIT C3GSR_TXERR_BIT

#define C3ICR (*(volatile unsigned long *)0xE004C00C)
#define CAN3ICR C3ICR
#define C3ICR_OFFSET 0xC
#define CAN3ICR_OFFSET C3ICR_OFFSET
#define C3ICR_RI_MASK 0x1
#define CAN3ICR_RI_MASK C3ICR_RI_MASK
#define C3ICR_RI 0x1
#define CAN3ICR_RI C3ICR_RI
#define C3ICR_RI_BIT 0
#define CAN3ICR_RI_BIT C3ICR_RI_BIT
#define C3ICR_TI1_MASK 0x2
#define CAN3ICR_TI1_MASK C3ICR_TI1_MASK
#define C3ICR_TI1 0x2
#define CAN3ICR_TI1 C3ICR_TI1
#define C3ICR_TI1_BIT 1
#define CAN3ICR_TI1_BIT C3ICR_TI1_BIT
#define C3ICR_EI_MASK 0x4
#define CAN3ICR_EI_MASK C3ICR_EI_MASK
#define C3ICR_EI 0x4
#define CAN3ICR_EI C3ICR_EI
#define C3ICR_EI_BIT 2
#define CAN3ICR_EI_BIT C3ICR_EI_BIT
#define C3ICR_DOI_MASK 0x8
#define CAN3ICR_DOI_MASK C3ICR_DOI_MASK
#define C3ICR_DOI 0x8
#define CAN3ICR_DOI C3ICR_DOI
#define C3ICR_DOI_BIT 3
#define CAN3ICR_DOI_BIT C3ICR_DOI_BIT
#define C3ICR_WUI_MASK 0x10
#define CAN3ICR_WUI_MASK C3ICR_WUI_MASK
#define C3ICR_WUI 0x10
#define CAN3ICR_WUI C3ICR_WUI
#define C3ICR_WUI_BIT 4
#define CAN3ICR_WUI_BIT C3ICR_WUI_BIT
#define C3ICR_EPI_MASK 0x20
#define CAN3ICR_EPI_MASK C3ICR_EPI_MASK
#define C3ICR_EPI 0x20
#define CAN3ICR_EPI C3ICR_EPI
#define C3ICR_EPI_BIT 5
#define CAN3ICR_EPI_BIT C3ICR_EPI_BIT
#define C3ICR_ALI_MASK 0x40
#define CAN3ICR_ALI_MASK C3ICR_ALI_MASK
#define C3ICR_ALI 0x40
#define CAN3ICR_ALI C3ICR_ALI
#define C3ICR_ALI_BIT 6
#define CAN3ICR_ALI_BIT C3ICR_ALI_BIT
#define C3ICR_BEI_MASK 0x80
#define CAN3ICR_BEI_MASK C3ICR_BEI_MASK
#define C3ICR_BEI 0x80
#define CAN3ICR_BEI C3ICR_BEI
#define C3ICR_BEI_BIT 7
#define CAN3ICR_BEI_BIT C3ICR_BEI_BIT
#define C3ICR_IDI_MASK 0x100
#define CAN3ICR_IDI_MASK C3ICR_IDI_MASK
#define C3ICR_IDI 0x100
#define CAN3ICR_IDI C3ICR_IDI
#define C3ICR_IDI_BIT 8
#define CAN3ICR_IDI_BIT C3ICR_IDI_BIT
#define C3ICR_TI2_MASK 0x200
#define CAN3ICR_TI2_MASK C3ICR_TI2_MASK
#define C3ICR_TI2 0x200
#define CAN3ICR_TI2 C3ICR_TI2
#define C3ICR_TI2_BIT 9
#define CAN3ICR_TI2_BIT C3ICR_TI2_BIT
#define C3ICR_TI3_MASK 0x400
#define CAN3ICR_TI3_MASK C3ICR_TI3_MASK
#define C3ICR_TI3 0x400
#define CAN3ICR_TI3 C3ICR_TI3
#define C3ICR_TI3_BIT 10
#define CAN3ICR_TI3_BIT C3ICR_TI3_BIT
#define C3ICR_ERRBIT_MASK 0x1F0000
#define CAN3ICR_ERRBIT_MASK C3ICR_ERRBIT_MASK
#define C3ICR_ERRBIT_BIT 16
#define CAN3ICR_ERRBIT_BIT C3ICR_ERRBIT_BIT
#define C3ICR_ERRDIR_MASK 0x200000
#define CAN3ICR_ERRDIR_MASK C3ICR_ERRDIR_MASK
#define C3ICR_ERRDIR 0x200000
#define CAN3ICR_ERRDIR C3ICR_ERRDIR
#define C3ICR_ERRDIR_BIT 21
#define CAN3ICR_ERRDIR_BIT C3ICR_ERRDIR_BIT
#define C3ICR_ERRC_MASK 0xC00000
#define CAN3ICR_ERRC_MASK C3ICR_ERRC_MASK
#define C3ICR_ERRC_BIT 22
#define CAN3ICR_ERRC_BIT C3ICR_ERRC_BIT
#define C3ICR_ALCBIT_MASK 0x1F000000
#define CAN3ICR_ALCBIT_MASK C3ICR_ALCBIT_MASK
#define C3ICR_ALCBIT_BIT 24
#define CAN3ICR_ALCBIT_BIT C3ICR_ALCBIT_BIT

#define C3IER (*(volatile unsigned long *)0xE004C010)
#define CAN3IER C3IER
#define C3IER_OFFSET 0x10
#define CAN3IER_OFFSET C3IER_OFFSET
#define C3IER_RIE_MASK 0x1
#define CAN3IER_RIE_MASK C3IER_RIE_MASK
#define C3IER_RIE 0x1
#define CAN3IER_RIE C3IER_RIE
#define C3IER_RIE_BIT 0
#define CAN3IER_RIE_BIT C3IER_RIE_BIT
#define C3IER_TIE1_MASK 0x2
#define CAN3IER_TIE1_MASK C3IER_TIE1_MASK
#define C3IER_TIE1 0x2
#define CAN3IER_TIE1 C3IER_TIE1
#define C3IER_TIE1_BIT 1
#define CAN3IER_TIE1_BIT C3IER_TIE1_BIT
#define C3IER_EIE_MASK 0x4
#define CAN3IER_EIE_MASK C3IER_EIE_MASK
#define C3IER_EIE 0x4
#define CAN3IER_EIE C3IER_EIE
#define C3IER_EIE_BIT 2
#define CAN3IER_EIE_BIT C3IER_EIE_BIT
#define C3IER_DOIE_MASK 0x8
#define CAN3IER_DOIE_MASK C3IER_DOIE_MASK
#define C3IER_DOIE 0x8
#define CAN3IER_DOIE C3IER_DOIE
#define C3IER_DOIE_BIT 3
#define CAN3IER_DOIE_BIT C3IER_DOIE_BIT
#define C3IER_WUIE_MASK 0x10
#define CAN3IER_WUIE_MASK C3IER_WUIE_MASK
#define C3IER_WUIE 0x10
#define CAN3IER_WUIE C3IER_WUIE
#define C3IER_WUIE_BIT 4
#define CAN3IER_WUIE_BIT C3IER_WUIE_BIT
#define C3IER_EPIE_MASK 0x20
#define CAN3IER_EPIE_MASK C3IER_EPIE_MASK
#define C3IER_EPIE 0x20
#define CAN3IER_EPIE C3IER_EPIE
#define C3IER_EPIE_BIT 5
#define CAN3IER_EPIE_BIT C3IER_EPIE_BIT
#define C3IER_ALIE_MASK 0x40
#define CAN3IER_ALIE_MASK C3IER_ALIE_MASK
#define C3IER_ALIE 0x40
#define CAN3IER_ALIE C3IER_ALIE
#define C3IER_ALIE_BIT 6
#define CAN3IER_ALIE_BIT C3IER_ALIE_BIT
#define C3IER_BEIE_MASK 0x80
#define CAN3IER_BEIE_MASK C3IER_BEIE_MASK
#define C3IER_BEIE 0x80
#define CAN3IER_BEIE C3IER_BEIE
#define C3IER_BEIE_BIT 7
#define CAN3IER_BEIE_BIT C3IER_BEIE_BIT
#define C3IER_IDIE_MASK 0x100
#define CAN3IER_IDIE_MASK C3IER_IDIE_MASK
#define C3IER_IDIE 0x100
#define CAN3IER_IDIE C3IER_IDIE
#define C3IER_IDIE_BIT 8
#define CAN3IER_IDIE_BIT C3IER_IDIE_BIT
#define C3IER_TIE2_MASK 0x200
#define CAN3IER_TIE2_MASK C3IER_TIE2_MASK
#define C3IER_TIE2 0x200
#define CAN3IER_TIE2 C3IER_TIE2
#define C3IER_TIE2_BIT 9
#define CAN3IER_TIE2_BIT C3IER_TIE2_BIT
#define C3IER_TIE3_MASK 0x400
#define CAN3IER_TIE3_MASK C3IER_TIE3_MASK
#define C3IER_TIE3 0x400
#define CAN3IER_TIE3 C3IER_TIE3
#define C3IER_TIE3_BIT 10
#define CAN3IER_TIE3_BIT C3IER_TIE3_BIT

#define C3BTR (*(volatile unsigned long *)0xE004C014)
#define CAN3BTR C3BTR
#define C3BTR_OFFSET 0x14
#define CAN3BTR_OFFSET C3BTR_OFFSET
#define C3BTR_BRP_MASK 0x3FF
#define CAN3BTR_BRP_MASK C3BTR_BRP_MASK
#define C3BTR_BRP_BIT 0
#define CAN3BTR_BRP_BIT C3BTR_BRP_BIT
#define C3BTR_SJW_MASK 0xC000
#define CAN3BTR_SJW_MASK C3BTR_SJW_MASK
#define C3BTR_SJW_BIT 14
#define CAN3BTR_SJW_BIT C3BTR_SJW_BIT
#define C3BTR_TSEG1_MASK 0xF0000
#define CAN3BTR_TSEG1_MASK C3BTR_TSEG1_MASK
#define C3BTR_TSEG1_BIT 16
#define CAN3BTR_TSEG1_BIT C3BTR_TSEG1_BIT
#define C3BTR_TSEG2_MASK 0x700000
#define CAN3BTR_TSEG2_MASK C3BTR_TSEG2_MASK
#define C3BTR_TSEG2_BIT 20
#define CAN3BTR_TSEG2_BIT C3BTR_TSEG2_BIT
#define C3BTR_SAM_MASK 0x800000
#define CAN3BTR_SAM_MASK C3BTR_SAM_MASK
#define C3BTR_SAM 0x800000
#define CAN3BTR_SAM C3BTR_SAM
#define C3BTR_SAM_BIT 23
#define CAN3BTR_SAM_BIT C3BTR_SAM_BIT

#define C3EWL (*(volatile unsigned long *)0xE004C018)
#define CAN3EWL C3EWL
#define C3EWL_OFFSET 0x18
#define CAN3EWL_OFFSET C3EWL_OFFSET
#define C3EWL_EWL_MASK 0xFF
#define CAN3EWL_EWL_MASK C3EWL_EWL_MASK
#define C3EWL_EWL_BIT 0
#define CAN3EWL_EWL_BIT C3EWL_EWL_BIT

#define C3SR (*(volatile unsigned long *)0xE004C01C)
#define CAN3SR C3SR
#define C3SR_OFFSET 0x1C
#define CAN3SR_OFFSET C3SR_OFFSET
#define C3SR_RBS_MASK 0x1
#define CAN3SR_RBS_MASK C3SR_RBS_MASK
#define C3SR_RBS 0x1
#define CAN3SR_RBS C3SR_RBS
#define C3SR_RBS_BIT 0
#define CAN3SR_RBS_BIT C3SR_RBS_BIT
#define C3SR_DOS_MASK 0x2
#define CAN3SR_DOS_MASK C3SR_DOS_MASK
#define C3SR_DOS 0x2
#define CAN3SR_DOS C3SR_DOS
#define C3SR_DOS_BIT 1
#define CAN3SR_DOS_BIT C3SR_DOS_BIT
#define C3SR_TBS1_MASK 0x4
#define CAN3SR_TBS1_MASK C3SR_TBS1_MASK
#define C3SR_TBS1 0x4
#define CAN3SR_TBS1 C3SR_TBS1
#define C3SR_TBS1_BIT 2
#define CAN3SR_TBS1_BIT C3SR_TBS1_BIT
#define C3SR_TCS1_MASK 0x8
#define CAN3SR_TCS1_MASK C3SR_TCS1_MASK
#define C3SR_TCS1 0x8
#define CAN3SR_TCS1 C3SR_TCS1
#define C3SR_TCS1_BIT 3
#define CAN3SR_TCS1_BIT C3SR_TCS1_BIT
#define C3SR_RS_MASK 0x10
#define CAN3SR_RS_MASK C3SR_RS_MASK
#define C3SR_RS 0x10
#define CAN3SR_RS C3SR_RS
#define C3SR_RS_BIT 4
#define CAN3SR_RS_BIT C3SR_RS_BIT
#define C3SR_TS1_MASK 0x20
#define CAN3SR_TS1_MASK C3SR_TS1_MASK
#define C3SR_TS1 0x20
#define CAN3SR_TS1 C3SR_TS1
#define C3SR_TS1_BIT 5
#define CAN3SR_TS1_BIT C3SR_TS1_BIT
#define C3SR_ES_MASK 0x40
#define CAN3SR_ES_MASK C3SR_ES_MASK
#define C3SR_ES 0x40
#define CAN3SR_ES C3SR_ES
#define C3SR_ES_BIT 6
#define CAN3SR_ES_BIT C3SR_ES_BIT
#define C3SR_BS_MASK 0x80
#define CAN3SR_BS_MASK C3SR_BS_MASK
#define C3SR_BS 0x80
#define CAN3SR_BS C3SR_BS
#define C3SR_BS_BIT 7
#define CAN3SR_BS_BIT C3SR_BS_BIT
#define C3SR_RBS2_MASK 0x100
#define CAN3SR_RBS2_MASK C3SR_RBS2_MASK
#define C3SR_RBS2 0x100
#define CAN3SR_RBS2 C3SR_RBS2
#define C3SR_RBS2_BIT 8
#define CAN3SR_RBS2_BIT C3SR_RBS2_BIT
#define C3SR_DOS2_MASK 0x200
#define CAN3SR_DOS2_MASK C3SR_DOS2_MASK
#define C3SR_DOS2 0x200
#define CAN3SR_DOS2 C3SR_DOS2
#define C3SR_DOS2_BIT 9
#define CAN3SR_DOS2_BIT C3SR_DOS2_BIT
#define C3SR_TBS2_MASK 0x400
#define CAN3SR_TBS2_MASK C3SR_TBS2_MASK
#define C3SR_TBS2 0x400
#define CAN3SR_TBS2 C3SR_TBS2
#define C3SR_TBS2_BIT 10
#define CAN3SR_TBS2_BIT C3SR_TBS2_BIT
#define C3SR_TCS2_MASK 0x800
#define CAN3SR_TCS2_MASK C3SR_TCS2_MASK
#define C3SR_TCS2 0x800
#define CAN3SR_TCS2 C3SR_TCS2
#define C3SR_TCS2_BIT 11
#define CAN3SR_TCS2_BIT C3SR_TCS2_BIT
#define C3SR_RS2_MASK 0x1000
#define CAN3SR_RS2_MASK C3SR_RS2_MASK
#define C3SR_RS2 0x1000
#define CAN3SR_RS2 C3SR_RS2
#define C3SR_RS2_BIT 12
#define CAN3SR_RS2_BIT C3SR_RS2_BIT
#define C3SR_TS2_MASK 0x2000
#define CAN3SR_TS2_MASK C3SR_TS2_MASK
#define C3SR_TS2 0x2000
#define CAN3SR_TS2 C3SR_TS2
#define C3SR_TS2_BIT 13
#define CAN3SR_TS2_BIT C3SR_TS2_BIT
#define C3SR_ES2_MASK 0x4000
#define CAN3SR_ES2_MASK C3SR_ES2_MASK
#define C3SR_ES2 0x4000
#define CAN3SR_ES2 C3SR_ES2
#define C3SR_ES2_BIT 14
#define CAN3SR_ES2_BIT C3SR_ES2_BIT
#define C3SR_BS2_MASK 0x8000
#define CAN3SR_BS2_MASK C3SR_BS2_MASK
#define C3SR_BS2 0x8000
#define CAN3SR_BS2 C3SR_BS2
#define C3SR_BS2_BIT 15
#define CAN3SR_BS2_BIT C3SR_BS2_BIT
#define C3SR_RBS3_MASK 0x10000
#define CAN3SR_RBS3_MASK C3SR_RBS3_MASK
#define C3SR_RBS3 0x10000
#define CAN3SR_RBS3 C3SR_RBS3
#define C3SR_RBS3_BIT 16
#define CAN3SR_RBS3_BIT C3SR_RBS3_BIT
#define C3SR_DOS3_MASK 0x20000
#define CAN3SR_DOS3_MASK C3SR_DOS3_MASK
#define C3SR_DOS3 0x20000
#define CAN3SR_DOS3 C3SR_DOS3
#define C3SR_DOS3_BIT 17
#define CAN3SR_DOS3_BIT C3SR_DOS3_BIT
#define C3SR_TBS3_MASK 0x40000
#define CAN3SR_TBS3_MASK C3SR_TBS3_MASK
#define C3SR_TBS3 0x40000
#define CAN3SR_TBS3 C3SR_TBS3
#define C3SR_TBS3_BIT 18
#define CAN3SR_TBS3_BIT C3SR_TBS3_BIT
#define C3SR_TCS3_MASK 0x80000
#define CAN3SR_TCS3_MASK C3SR_TCS3_MASK
#define C3SR_TCS3 0x80000
#define CAN3SR_TCS3 C3SR_TCS3
#define C3SR_TCS3_BIT 19
#define CAN3SR_TCS3_BIT C3SR_TCS3_BIT
#define C3SR_RS3_MASK 0x100000
#define CAN3SR_RS3_MASK C3SR_RS3_MASK
#define C3SR_RS3 0x100000
#define CAN3SR_RS3 C3SR_RS3
#define C3SR_RS3_BIT 20
#define CAN3SR_RS3_BIT C3SR_RS3_BIT
#define C3SR_TS3_MASK 0x200000
#define CAN3SR_TS3_MASK C3SR_TS3_MASK
#define C3SR_TS3 0x200000
#define CAN3SR_TS3 C3SR_TS3
#define C3SR_TS3_BIT 21
#define CAN3SR_TS3_BIT C3SR_TS3_BIT
#define C3SR_ES3_MASK 0x400000
#define CAN3SR_ES3_MASK C3SR_ES3_MASK
#define C3SR_ES3 0x400000
#define CAN3SR_ES3 C3SR_ES3
#define C3SR_ES3_BIT 22
#define CAN3SR_ES3_BIT C3SR_ES3_BIT
#define C3SR_BS3_MASK 0x800000
#define CAN3SR_BS3_MASK C3SR_BS3_MASK
#define C3SR_BS3 0x800000
#define CAN3SR_BS3 C3SR_BS3
#define C3SR_BS3_BIT 23
#define CAN3SR_BS3_BIT C3SR_BS3_BIT

#define C3RFS (*(volatile unsigned long *)0xE004C020)
#define CAN3RFS C3RFS
#define C3RFS_OFFSET 0x20
#define CAN3RFS_OFFSET C3RFS_OFFSET
#define C3RFS_ID_Index_MASK 0x3FF
#define CAN3RFS_ID_Index_MASK C3RFS_ID_Index_MASK
#define C3RFS_ID_Index_BIT 0
#define CAN3RFS_ID_Index_BIT C3RFS_ID_Index_BIT
#define C3RFS_BP_MASK 0x400
#define CAN3RFS_BP_MASK C3RFS_BP_MASK
#define C3RFS_BP 0x400
#define CAN3RFS_BP C3RFS_BP
#define C3RFS_BP_BIT 10
#define CAN3RFS_BP_BIT C3RFS_BP_BIT
#define C3RFS_DLC_MASK 0xF0000
#define CAN3RFS_DLC_MASK C3RFS_DLC_MASK
#define C3RFS_DLC_BIT 16
#define CAN3RFS_DLC_BIT C3RFS_DLC_BIT
#define C3RFS_RTR_MASK 0x40000000
#define CAN3RFS_RTR_MASK C3RFS_RTR_MASK
#define C3RFS_RTR 0x40000000
#define CAN3RFS_RTR C3RFS_RTR
#define C3RFS_RTR_BIT 30
#define CAN3RFS_RTR_BIT C3RFS_RTR_BIT
#define C3RFS_FF_MASK 0x80000000
#define CAN3RFS_FF_MASK C3RFS_FF_MASK
#define C3RFS_FF 0x80000000
#define CAN3RFS_FF C3RFS_FF
#define C3RFS_FF_BIT 31
#define CAN3RFS_FF_BIT C3RFS_FF_BIT

#define C3RID (*(volatile unsigned long *)0xE004C024)
#define CAN3RID C3RID
#define C3RID_OFFSET 0x24
#define CAN3RID_OFFSET C3RID_OFFSET
#define C3RID_ID_MASK 0x7FF
#define CAN3RID_ID_MASK C3RID_ID_MASK
#define C3RID_ID_BIT 0
#define CAN3RID_ID_BIT C3RID_ID_BIT

#define C3RDA (*(volatile unsigned long *)0xE004C028)
#define CAN3RDA C3RDA
#define C3RDA_OFFSET 0x28
#define CAN3RDA_OFFSET C3RDA_OFFSET
#define C3RDA_Data_1_MASK 0xFF
#define CAN3RDA_Data_1_MASK C3RDA_Data_1_MASK
#define C3RDA_Data_1_BIT 0
#define CAN3RDA_Data_1_BIT C3RDA_Data_1_BIT
#define C3RDA_Data_2_MASK 0xFF00
#define CAN3RDA_Data_2_MASK C3RDA_Data_2_MASK
#define C3RDA_Data_2_BIT 8
#define CAN3RDA_Data_2_BIT C3RDA_Data_2_BIT
#define C3RDA_Data_3_MASK 0xFF0000
#define CAN3RDA_Data_3_MASK C3RDA_Data_3_MASK
#define C3RDA_Data_3_BIT 16
#define CAN3RDA_Data_3_BIT C3RDA_Data_3_BIT
#define C3RDA_Data_4_MASK 0xFF000000
#define CAN3RDA_Data_4_MASK C3RDA_Data_4_MASK
#define C3RDA_Data_4_BIT 24
#define CAN3RDA_Data_4_BIT C3RDA_Data_4_BIT

#define C3RDB (*(volatile unsigned long *)0xE004C02C)
#define CAN3RDB C3RDB
#define C3RDB_OFFSET 0x2C
#define CAN3RDB_OFFSET C3RDB_OFFSET
#define C3RDB_Data_5_MASK 0xFF
#define CAN3RDB_Data_5_MASK C3RDB_Data_5_MASK
#define C3RDB_Data_5_BIT 0
#define CAN3RDB_Data_5_BIT C3RDB_Data_5_BIT
#define C3RDB_Data_6_MASK 0xFF00
#define CAN3RDB_Data_6_MASK C3RDB_Data_6_MASK
#define C3RDB_Data_6_BIT 8
#define CAN3RDB_Data_6_BIT C3RDB_Data_6_BIT
#define C3RDB_Data_7_MASK 0xFF0000
#define CAN3RDB_Data_7_MASK C3RDB_Data_7_MASK
#define C3RDB_Data_7_BIT 16
#define CAN3RDB_Data_7_BIT C3RDB_Data_7_BIT
#define C3RDB_Data_8_MASK 0xFF000000
#define CAN3RDB_Data_8_MASK C3RDB_Data_8_MASK
#define C3RDB_Data_8_BIT 24
#define CAN3RDB_Data_8_BIT C3RDB_Data_8_BIT

#define C3TFI1 (*(volatile unsigned long *)0xE004C030)
#define CAN3TFI1 C3TFI1
#define C3TFI1_OFFSET 0x30
#define CAN3TFI1_OFFSET C3TFI1_OFFSET
#define C3TFI1_PRIO_MASK 0xFF
#define CAN3TFI1_PRIO_MASK C3TFI1_PRIO_MASK
#define C3TFI1_PRIO_BIT 0
#define CAN3TFI1_PRIO_BIT C3TFI1_PRIO_BIT
#define C3TFI1_DLC_MASK 0xF0000
#define CAN3TFI1_DLC_MASK C3TFI1_DLC_MASK
#define C3TFI1_DLC_BIT 16
#define CAN3TFI1_DLC_BIT C3TFI1_DLC_BIT
#define C3TFI1_RTR_MASK 0x40000000
#define CAN3TFI1_RTR_MASK C3TFI1_RTR_MASK
#define C3TFI1_RTR 0x40000000
#define CAN3TFI1_RTR C3TFI1_RTR
#define C3TFI1_RTR_BIT 30
#define CAN3TFI1_RTR_BIT C3TFI1_RTR_BIT
#define C3TFI1_FF_MASK 0x80000000
#define CAN3TFI1_FF_MASK C3TFI1_FF_MASK
#define C3TFI1_FF 0x80000000
#define CAN3TFI1_FF C3TFI1_FF
#define C3TFI1_FF_BIT 31
#define CAN3TFI1_FF_BIT C3TFI1_FF_BIT

#define C3TID1 (*(volatile unsigned long *)0xE004C034)
#define CAN3TID1 C3TID1
#define C3TID1_OFFSET 0x34
#define CAN3TID1_OFFSET C3TID1_OFFSET
#define C3TID1_ID_MASK 0x7FF
#define CAN3TID1_ID_MASK C3TID1_ID_MASK
#define C3TID1_ID_BIT 0
#define CAN3TID1_ID_BIT C3TID1_ID_BIT

#define C3TDA1 (*(volatile unsigned long *)0xE004C038)
#define CAN3TDA1 C3TDA1
#define C3TDA1_OFFSET 0x38
#define CAN3TDA1_OFFSET C3TDA1_OFFSET
#define C3TDA1_Data_1_MASK 0xFF
#define CAN3TDA1_Data_1_MASK C3TDA1_Data_1_MASK
#define C3TDA1_Data_1_BIT 0
#define CAN3TDA1_Data_1_BIT C3TDA1_Data_1_BIT
#define C3TDA1_Data_2_MASK 0xFF00
#define CAN3TDA1_Data_2_MASK C3TDA1_Data_2_MASK
#define C3TDA1_Data_2_BIT 8
#define CAN3TDA1_Data_2_BIT C3TDA1_Data_2_BIT
#define C3TDA1_Data_3_MASK 0xFF0000
#define CAN3TDA1_Data_3_MASK C3TDA1_Data_3_MASK
#define C3TDA1_Data_3_BIT 16
#define CAN3TDA1_Data_3_BIT C3TDA1_Data_3_BIT
#define C3TDA1_Data_4_MASK 0xFF000000
#define CAN3TDA1_Data_4_MASK C3TDA1_Data_4_MASK
#define C3TDA1_Data_4_BIT 24
#define CAN3TDA1_Data_4_BIT C3TDA1_Data_4_BIT

#define C3TDB1 (*(volatile unsigned long *)0xE004C03C)
#define CAN3TDB1 C3TDB1
#define C3TDB1_OFFSET 0x3C
#define CAN3TDB1_OFFSET C3TDB1_OFFSET
#define C3TDB1_Data_5_MASK 0xFF
#define CAN3TDB1_Data_5_MASK C3TDB1_Data_5_MASK
#define C3TDB1_Data_5_BIT 0
#define CAN3TDB1_Data_5_BIT C3TDB1_Data_5_BIT
#define C3TDB1_Data_6_MASK 0xFF00
#define CAN3TDB1_Data_6_MASK C3TDB1_Data_6_MASK
#define C3TDB1_Data_6_BIT 8
#define CAN3TDB1_Data_6_BIT C3TDB1_Data_6_BIT
#define C3TDB1_Data_7_MASK 0xFF0000
#define CAN3TDB1_Data_7_MASK C3TDB1_Data_7_MASK
#define C3TDB1_Data_7_BIT 16
#define CAN3TDB1_Data_7_BIT C3TDB1_Data_7_BIT
#define C3TDB1_Data_8_MASK 0xFF000000
#define CAN3TDB1_Data_8_MASK C3TDB1_Data_8_MASK
#define C3TDB1_Data_8_BIT 24
#define CAN3TDB1_Data_8_BIT C3TDB1_Data_8_BIT

#define C3TFI2 (*(volatile unsigned long *)0xE004C040)
#define CAN3TFI2 C3TFI2
#define C3TFI2_OFFSET 0x40
#define CAN3TFI2_OFFSET C3TFI2_OFFSET
#define C3TFI2_PRIO_MASK 0xFF
#define CAN3TFI2_PRIO_MASK C3TFI2_PRIO_MASK
#define C3TFI2_PRIO_BIT 0
#define CAN3TFI2_PRIO_BIT C3TFI2_PRIO_BIT
#define C3TFI2_DLC_MASK 0xF0000
#define CAN3TFI2_DLC_MASK C3TFI2_DLC_MASK
#define C3TFI2_DLC_BIT 16
#define CAN3TFI2_DLC_BIT C3TFI2_DLC_BIT
#define C3TFI2_RTR_MASK 0x40000000
#define CAN3TFI2_RTR_MASK C3TFI2_RTR_MASK
#define C3TFI2_RTR 0x40000000
#define CAN3TFI2_RTR C3TFI2_RTR
#define C3TFI2_RTR_BIT 30
#define CAN3TFI2_RTR_BIT C3TFI2_RTR_BIT
#define C3TFI2_FF_MASK 0x80000000
#define CAN3TFI2_FF_MASK C3TFI2_FF_MASK
#define C3TFI2_FF 0x80000000
#define CAN3TFI2_FF C3TFI2_FF
#define C3TFI2_FF_BIT 31
#define CAN3TFI2_FF_BIT C3TFI2_FF_BIT

#define C3TID2 (*(volatile unsigned long *)0xE004C044)
#define CAN3TID2 C3TID2
#define C3TID2_OFFSET 0x44
#define CAN3TID2_OFFSET C3TID2_OFFSET
#define C3TID2_ID_MASK 0x7FF
#define CAN3TID2_ID_MASK C3TID2_ID_MASK
#define C3TID2_ID_BIT 0
#define CAN3TID2_ID_BIT C3TID2_ID_BIT

#define C3TDA2 (*(volatile unsigned long *)0xE004C048)
#define CAN3TDA2 C3TDA2
#define C3TDA2_OFFSET 0x48
#define CAN3TDA2_OFFSET C3TDA2_OFFSET
#define C3TDA2_Data_1_MASK 0xFF
#define CAN3TDA2_Data_1_MASK C3TDA2_Data_1_MASK
#define C3TDA2_Data_1_BIT 0
#define CAN3TDA2_Data_1_BIT C3TDA2_Data_1_BIT
#define C3TDA2_Data_2_MASK 0xFF00
#define CAN3TDA2_Data_2_MASK C3TDA2_Data_2_MASK
#define C3TDA2_Data_2_BIT 8
#define CAN3TDA2_Data_2_BIT C3TDA2_Data_2_BIT
#define C3TDA2_Data_3_MASK 0xFF0000
#define CAN3TDA2_Data_3_MASK C3TDA2_Data_3_MASK
#define C3TDA2_Data_3_BIT 16
#define CAN3TDA2_Data_3_BIT C3TDA2_Data_3_BIT
#define C3TDA2_Data_4_MASK 0xFF000000
#define CAN3TDA2_Data_4_MASK C3TDA2_Data_4_MASK
#define C3TDA2_Data_4_BIT 24
#define CAN3TDA2_Data_4_BIT C3TDA2_Data_4_BIT

#define C3TDB2 (*(volatile unsigned long *)0xE004C04C)
#define CAN3TDB2 C3TDB2
#define C3TDB2_OFFSET 0x4C
#define CAN3TDB2_OFFSET C3TDB2_OFFSET
#define C3TDB2_Data_5_MASK 0xFF
#define CAN3TDB2_Data_5_MASK C3TDB2_Data_5_MASK
#define C3TDB2_Data_5_BIT 0
#define CAN3TDB2_Data_5_BIT C3TDB2_Data_5_BIT
#define C3TDB2_Data_6_MASK 0xFF00
#define CAN3TDB2_Data_6_MASK C3TDB2_Data_6_MASK
#define C3TDB2_Data_6_BIT 8
#define CAN3TDB2_Data_6_BIT C3TDB2_Data_6_BIT
#define C3TDB2_Data_7_MASK 0xFF0000
#define CAN3TDB2_Data_7_MASK C3TDB2_Data_7_MASK
#define C3TDB2_Data_7_BIT 16
#define CAN3TDB2_Data_7_BIT C3TDB2_Data_7_BIT
#define C3TDB2_Data_8_MASK 0xFF000000
#define CAN3TDB2_Data_8_MASK C3TDB2_Data_8_MASK
#define C3TDB2_Data_8_BIT 24
#define CAN3TDB2_Data_8_BIT C3TDB2_Data_8_BIT

#define C3TFI3 (*(volatile unsigned long *)0xE004C050)
#define CAN3TFI3 C3TFI3
#define C3TFI3_OFFSET 0x50
#define CAN3TFI3_OFFSET C3TFI3_OFFSET
#define C3TFI3_PRIO_MASK 0xFF
#define CAN3TFI3_PRIO_MASK C3TFI3_PRIO_MASK
#define C3TFI3_PRIO_BIT 0
#define CAN3TFI3_PRIO_BIT C3TFI3_PRIO_BIT
#define C3TFI3_DLC_MASK 0xF0000
#define CAN3TFI3_DLC_MASK C3TFI3_DLC_MASK
#define C3TFI3_DLC_BIT 16
#define CAN3TFI3_DLC_BIT C3TFI3_DLC_BIT
#define C3TFI3_RTR_MASK 0x40000000
#define CAN3TFI3_RTR_MASK C3TFI3_RTR_MASK
#define C3TFI3_RTR 0x40000000
#define CAN3TFI3_RTR C3TFI3_RTR
#define C3TFI3_RTR_BIT 30
#define CAN3TFI3_RTR_BIT C3TFI3_RTR_BIT
#define C3TFI3_FF_MASK 0x80000000
#define CAN3TFI3_FF_MASK C3TFI3_FF_MASK
#define C3TFI3_FF 0x80000000
#define CAN3TFI3_FF C3TFI3_FF
#define C3TFI3_FF_BIT 31
#define CAN3TFI3_FF_BIT C3TFI3_FF_BIT

#define C3TID3 (*(volatile unsigned long *)0xE004C054)
#define CAN3TID3 C3TID3
#define C3TID3_OFFSET 0x54
#define CAN3TID3_OFFSET C3TID3_OFFSET
#define C3TID3_ID_MASK 0x7FF
#define CAN3TID3_ID_MASK C3TID3_ID_MASK
#define C3TID3_ID_BIT 0
#define CAN3TID3_ID_BIT C3TID3_ID_BIT

#define C3TDA3 (*(volatile unsigned long *)0xE004C058)
#define CAN3TDA3 C3TDA3
#define C3TDA3_OFFSET 0x58
#define CAN3TDA3_OFFSET C3TDA3_OFFSET
#define C3TDA3_Data_1_MASK 0xFF
#define CAN3TDA3_Data_1_MASK C3TDA3_Data_1_MASK
#define C3TDA3_Data_1_BIT 0
#define CAN3TDA3_Data_1_BIT C3TDA3_Data_1_BIT
#define C3TDA3_Data_2_MASK 0xFF00
#define CAN3TDA3_Data_2_MASK C3TDA3_Data_2_MASK
#define C3TDA3_Data_2_BIT 8
#define CAN3TDA3_Data_2_BIT C3TDA3_Data_2_BIT
#define C3TDA3_Data_3_MASK 0xFF0000
#define CAN3TDA3_Data_3_MASK C3TDA3_Data_3_MASK
#define C3TDA3_Data_3_BIT 16
#define CAN3TDA3_Data_3_BIT C3TDA3_Data_3_BIT
#define C3TDA3_Data_4_MASK 0xFF000000
#define CAN3TDA3_Data_4_MASK C3TDA3_Data_4_MASK
#define C3TDA3_Data_4_BIT 24
#define CAN3TDA3_Data_4_BIT C3TDA3_Data_4_BIT

#define C3TDB3 (*(volatile unsigned long *)0xE004C05C)
#define CAN3TDB3 C3TDB3
#define C3TDB3_OFFSET 0x5C
#define CAN3TDB3_OFFSET C3TDB3_OFFSET
#define C3TDB3_Data_5_MASK 0xFF
#define CAN3TDB3_Data_5_MASK C3TDB3_Data_5_MASK
#define C3TDB3_Data_5_BIT 0
#define CAN3TDB3_Data_5_BIT C3TDB3_Data_5_BIT
#define C3TDB3_Data_6_MASK 0xFF00
#define CAN3TDB3_Data_6_MASK C3TDB3_Data_6_MASK
#define C3TDB3_Data_6_BIT 8
#define CAN3TDB3_Data_6_BIT C3TDB3_Data_6_BIT
#define C3TDB3_Data_7_MASK 0xFF0000
#define CAN3TDB3_Data_7_MASK C3TDB3_Data_7_MASK
#define C3TDB3_Data_7_BIT 16
#define CAN3TDB3_Data_7_BIT C3TDB3_Data_7_BIT
#define C3TDB3_Data_8_MASK 0xFF000000
#define CAN3TDB3_Data_8_MASK C3TDB3_Data_8_MASK
#define C3TDB3_Data_8_BIT 24
#define CAN3TDB3_Data_8_BIT C3TDB3_Data_8_BIT

#define CAN4_BASE 0xE0050000

#define C4MOD (*(volatile unsigned long *)0xE0050000)
#define CAN4MOD C4MOD
#define C4MOD_OFFSET 0x0
#define CAN4MOD_OFFSET C4MOD_OFFSET
#define C4MOD_RM_MASK 0x1
#define CAN4MOD_RM_MASK C4MOD_RM_MASK
#define C4MOD_RM 0x1
#define CAN4MOD_RM C4MOD_RM
#define C4MOD_RM_BIT 0
#define CAN4MOD_RM_BIT C4MOD_RM_BIT
#define C4MOD_LOM_MASK 0x2
#define CAN4MOD_LOM_MASK C4MOD_LOM_MASK
#define C4MOD_LOM 0x2
#define CAN4MOD_LOM C4MOD_LOM
#define C4MOD_LOM_BIT 1
#define CAN4MOD_LOM_BIT C4MOD_LOM_BIT
#define C4MOD_STM_MASK 0x4
#define CAN4MOD_STM_MASK C4MOD_STM_MASK
#define C4MOD_STM 0x4
#define CAN4MOD_STM C4MOD_STM
#define C4MOD_STM_BIT 2
#define CAN4MOD_STM_BIT C4MOD_STM_BIT
#define C4MOD_TPM_MASK 0x8
#define CAN4MOD_TPM_MASK C4MOD_TPM_MASK
#define C4MOD_TPM 0x8
#define CAN4MOD_TPM C4MOD_TPM
#define C4MOD_TPM_BIT 3
#define CAN4MOD_TPM_BIT C4MOD_TPM_BIT
#define C4MOD_SM_MASK 0x10
#define CAN4MOD_SM_MASK C4MOD_SM_MASK
#define C4MOD_SM 0x10
#define CAN4MOD_SM C4MOD_SM
#define C4MOD_SM_BIT 4
#define CAN4MOD_SM_BIT C4MOD_SM_BIT
#define C4MOD_RPM_MASK 0x20
#define CAN4MOD_RPM_MASK C4MOD_RPM_MASK
#define C4MOD_RPM 0x20
#define CAN4MOD_RPM C4MOD_RPM
#define C4MOD_RPM_BIT 5
#define CAN4MOD_RPM_BIT C4MOD_RPM_BIT
#define C4MOD_TM_MASK 0x80
#define CAN4MOD_TM_MASK C4MOD_TM_MASK
#define C4MOD_TM 0x80
#define CAN4MOD_TM C4MOD_TM
#define C4MOD_TM_BIT 7
#define CAN4MOD_TM_BIT C4MOD_TM_BIT

#define C4CMR (*(volatile unsigned long *)0xE0050004)
#define CAN4CMR C4CMR
#define C4CMR_OFFSET 0x4
#define CAN4CMR_OFFSET C4CMR_OFFSET
#define C4CMR_TR_MASK 0x1
#define CAN4CMR_TR_MASK C4CMR_TR_MASK
#define C4CMR_TR 0x1
#define CAN4CMR_TR C4CMR_TR
#define C4CMR_TR_BIT 0
#define CAN4CMR_TR_BIT C4CMR_TR_BIT
#define C4CMR_AT_MASK 0x2
#define CAN4CMR_AT_MASK C4CMR_AT_MASK
#define C4CMR_AT 0x2
#define CAN4CMR_AT C4CMR_AT
#define C4CMR_AT_BIT 1
#define CAN4CMR_AT_BIT C4CMR_AT_BIT
#define C4CMR_RRB_MASK 0x4
#define CAN4CMR_RRB_MASK C4CMR_RRB_MASK
#define C4CMR_RRB 0x4
#define CAN4CMR_RRB C4CMR_RRB
#define C4CMR_RRB_BIT 2
#define CAN4CMR_RRB_BIT C4CMR_RRB_BIT
#define C4CMR_CDO_MASK 0x8
#define CAN4CMR_CDO_MASK C4CMR_CDO_MASK
#define C4CMR_CDO 0x8
#define CAN4CMR_CDO C4CMR_CDO
#define C4CMR_CDO_BIT 3
#define CAN4CMR_CDO_BIT C4CMR_CDO_BIT
#define C4CMR_SRR_MASK 0x10
#define CAN4CMR_SRR_MASK C4CMR_SRR_MASK
#define C4CMR_SRR 0x10
#define CAN4CMR_SRR C4CMR_SRR
#define C4CMR_SRR_BIT 4
#define CAN4CMR_SRR_BIT C4CMR_SRR_BIT
#define C4CMR_STB1_MASK 0x20
#define CAN4CMR_STB1_MASK C4CMR_STB1_MASK
#define C4CMR_STB1 0x20
#define CAN4CMR_STB1 C4CMR_STB1
#define C4CMR_STB1_BIT 5
#define CAN4CMR_STB1_BIT C4CMR_STB1_BIT
#define C4CMR_STB2_MASK 0x40
#define CAN4CMR_STB2_MASK C4CMR_STB2_MASK
#define C4CMR_STB2 0x40
#define CAN4CMR_STB2 C4CMR_STB2
#define C4CMR_STB2_BIT 6
#define CAN4CMR_STB2_BIT C4CMR_STB2_BIT
#define C4CMR_STB3_MASK 0x80
#define CAN4CMR_STB3_MASK C4CMR_STB3_MASK
#define C4CMR_STB3 0x80
#define CAN4CMR_STB3 C4CMR_STB3
#define C4CMR_STB3_BIT 7
#define CAN4CMR_STB3_BIT C4CMR_STB3_BIT

#define C4GSR (*(volatile unsigned long *)0xE0050008)
#define CAN4GSR C4GSR
#define C4GSR_OFFSET 0x8
#define CAN4GSR_OFFSET C4GSR_OFFSET
#define C4GSR_RBS_MASK 0x1
#define CAN4GSR_RBS_MASK C4GSR_RBS_MASK
#define C4GSR_RBS 0x1
#define CAN4GSR_RBS C4GSR_RBS
#define C4GSR_RBS_BIT 0
#define CAN4GSR_RBS_BIT C4GSR_RBS_BIT
#define C4GSR_DOS_MASK 0x2
#define CAN4GSR_DOS_MASK C4GSR_DOS_MASK
#define C4GSR_DOS 0x2
#define CAN4GSR_DOS C4GSR_DOS
#define C4GSR_DOS_BIT 1
#define CAN4GSR_DOS_BIT C4GSR_DOS_BIT
#define C4GSR_TBS_MASK 0x4
#define CAN4GSR_TBS_MASK C4GSR_TBS_MASK
#define C4GSR_TBS 0x4
#define CAN4GSR_TBS C4GSR_TBS
#define C4GSR_TBS_BIT 2
#define CAN4GSR_TBS_BIT C4GSR_TBS_BIT
#define C4GSR_TCS_MASK 0x8
#define CAN4GSR_TCS_MASK C4GSR_TCS_MASK
#define C4GSR_TCS 0x8
#define CAN4GSR_TCS C4GSR_TCS
#define C4GSR_TCS_BIT 3
#define CAN4GSR_TCS_BIT C4GSR_TCS_BIT
#define C4GSR_RS_MASK 0x10
#define CAN4GSR_RS_MASK C4GSR_RS_MASK
#define C4GSR_RS 0x10
#define CAN4GSR_RS C4GSR_RS
#define C4GSR_RS_BIT 4
#define CAN4GSR_RS_BIT C4GSR_RS_BIT
#define C4GSR_TS_MASK 0x20
#define CAN4GSR_TS_MASK C4GSR_TS_MASK
#define C4GSR_TS 0x20
#define CAN4GSR_TS C4GSR_TS
#define C4GSR_TS_BIT 5
#define CAN4GSR_TS_BIT C4GSR_TS_BIT
#define C4GSR_ES_MASK 0x40
#define CAN4GSR_ES_MASK C4GSR_ES_MASK
#define C4GSR_ES 0x40
#define CAN4GSR_ES C4GSR_ES
#define C4GSR_ES_BIT 6
#define CAN4GSR_ES_BIT C4GSR_ES_BIT
#define C4GSR_BS_MASK 0x80
#define CAN4GSR_BS_MASK C4GSR_BS_MASK
#define C4GSR_BS 0x80
#define CAN4GSR_BS C4GSR_BS
#define C4GSR_BS_BIT 7
#define CAN4GSR_BS_BIT C4GSR_BS_BIT
#define C4GSR_RXERR_MASK 0xFF0000
#define CAN4GSR_RXERR_MASK C4GSR_RXERR_MASK
#define C4GSR_RXERR_BIT 16
#define CAN4GSR_RXERR_BIT C4GSR_RXERR_BIT
#define C4GSR_TXERR_MASK 0xFF000000
#define CAN4GSR_TXERR_MASK C4GSR_TXERR_MASK
#define C4GSR_TXERR_BIT 24
#define CAN4GSR_TXERR_BIT C4GSR_TXERR_BIT

#define C4ICR (*(volatile unsigned long *)0xE005000C)
#define CAN4ICR C4ICR
#define C4ICR_OFFSET 0xC
#define CAN4ICR_OFFSET C4ICR_OFFSET
#define C4ICR_RI_MASK 0x1
#define CAN4ICR_RI_MASK C4ICR_RI_MASK
#define C4ICR_RI 0x1
#define CAN4ICR_RI C4ICR_RI
#define C4ICR_RI_BIT 0
#define CAN4ICR_RI_BIT C4ICR_RI_BIT
#define C4ICR_TI1_MASK 0x2
#define CAN4ICR_TI1_MASK C4ICR_TI1_MASK
#define C4ICR_TI1 0x2
#define CAN4ICR_TI1 C4ICR_TI1
#define C4ICR_TI1_BIT 1
#define CAN4ICR_TI1_BIT C4ICR_TI1_BIT
#define C4ICR_EI_MASK 0x4
#define CAN4ICR_EI_MASK C4ICR_EI_MASK
#define C4ICR_EI 0x4
#define CAN4ICR_EI C4ICR_EI
#define C4ICR_EI_BIT 2
#define CAN4ICR_EI_BIT C4ICR_EI_BIT
#define C4ICR_DOI_MASK 0x8
#define CAN4ICR_DOI_MASK C4ICR_DOI_MASK
#define C4ICR_DOI 0x8
#define CAN4ICR_DOI C4ICR_DOI
#define C4ICR_DOI_BIT 3
#define CAN4ICR_DOI_BIT C4ICR_DOI_BIT
#define C4ICR_WUI_MASK 0x10
#define CAN4ICR_WUI_MASK C4ICR_WUI_MASK
#define C4ICR_WUI 0x10
#define CAN4ICR_WUI C4ICR_WUI
#define C4ICR_WUI_BIT 4
#define CAN4ICR_WUI_BIT C4ICR_WUI_BIT
#define C4ICR_EPI_MASK 0x20
#define CAN4ICR_EPI_MASK C4ICR_EPI_MASK
#define C4ICR_EPI 0x20
#define CAN4ICR_EPI C4ICR_EPI
#define C4ICR_EPI_BIT 5
#define CAN4ICR_EPI_BIT C4ICR_EPI_BIT
#define C4ICR_ALI_MASK 0x40
#define CAN4ICR_ALI_MASK C4ICR_ALI_MASK
#define C4ICR_ALI 0x40
#define CAN4ICR_ALI C4ICR_ALI
#define C4ICR_ALI_BIT 6
#define CAN4ICR_ALI_BIT C4ICR_ALI_BIT
#define C4ICR_BEI_MASK 0x80
#define CAN4ICR_BEI_MASK C4ICR_BEI_MASK
#define C4ICR_BEI 0x80
#define CAN4ICR_BEI C4ICR_BEI
#define C4ICR_BEI_BIT 7
#define CAN4ICR_BEI_BIT C4ICR_BEI_BIT
#define C4ICR_IDI_MASK 0x100
#define CAN4ICR_IDI_MASK C4ICR_IDI_MASK
#define C4ICR_IDI 0x100
#define CAN4ICR_IDI C4ICR_IDI
#define C4ICR_IDI_BIT 8
#define CAN4ICR_IDI_BIT C4ICR_IDI_BIT
#define C4ICR_TI2_MASK 0x200
#define CAN4ICR_TI2_MASK C4ICR_TI2_MASK
#define C4ICR_TI2 0x200
#define CAN4ICR_TI2 C4ICR_TI2
#define C4ICR_TI2_BIT 9
#define CAN4ICR_TI2_BIT C4ICR_TI2_BIT
#define C4ICR_TI3_MASK 0x400
#define CAN4ICR_TI3_MASK C4ICR_TI3_MASK
#define C4ICR_TI3 0x400
#define CAN4ICR_TI3 C4ICR_TI3
#define C4ICR_TI3_BIT 10
#define CAN4ICR_TI3_BIT C4ICR_TI3_BIT
#define C4ICR_ERRBIT_MASK 0x1F0000
#define CAN4ICR_ERRBIT_MASK C4ICR_ERRBIT_MASK
#define C4ICR_ERRBIT_BIT 16
#define CAN4ICR_ERRBIT_BIT C4ICR_ERRBIT_BIT
#define C4ICR_ERRDIR_MASK 0x200000
#define CAN4ICR_ERRDIR_MASK C4ICR_ERRDIR_MASK
#define C4ICR_ERRDIR 0x200000
#define CAN4ICR_ERRDIR C4ICR_ERRDIR
#define C4ICR_ERRDIR_BIT 21
#define CAN4ICR_ERRDIR_BIT C4ICR_ERRDIR_BIT
#define C4ICR_ERRC_MASK 0xC00000
#define CAN4ICR_ERRC_MASK C4ICR_ERRC_MASK
#define C4ICR_ERRC_BIT 22
#define CAN4ICR_ERRC_BIT C4ICR_ERRC_BIT
#define C4ICR_ALCBIT_MASK 0x1F000000
#define CAN4ICR_ALCBIT_MASK C4ICR_ALCBIT_MASK
#define C4ICR_ALCBIT_BIT 24
#define CAN4ICR_ALCBIT_BIT C4ICR_ALCBIT_BIT

#define C4IER (*(volatile unsigned long *)0xE0050010)
#define CAN4IER C4IER
#define C4IER_OFFSET 0x10
#define CAN4IER_OFFSET C4IER_OFFSET
#define C4IER_RIE_MASK 0x1
#define CAN4IER_RIE_MASK C4IER_RIE_MASK
#define C4IER_RIE 0x1
#define CAN4IER_RIE C4IER_RIE
#define C4IER_RIE_BIT 0
#define CAN4IER_RIE_BIT C4IER_RIE_BIT
#define C4IER_TIE1_MASK 0x2
#define CAN4IER_TIE1_MASK C4IER_TIE1_MASK
#define C4IER_TIE1 0x2
#define CAN4IER_TIE1 C4IER_TIE1
#define C4IER_TIE1_BIT 1
#define CAN4IER_TIE1_BIT C4IER_TIE1_BIT
#define C4IER_EIE_MASK 0x4
#define CAN4IER_EIE_MASK C4IER_EIE_MASK
#define C4IER_EIE 0x4
#define CAN4IER_EIE C4IER_EIE
#define C4IER_EIE_BIT 2
#define CAN4IER_EIE_BIT C4IER_EIE_BIT
#define C4IER_DOIE_MASK 0x8
#define CAN4IER_DOIE_MASK C4IER_DOIE_MASK
#define C4IER_DOIE 0x8
#define CAN4IER_DOIE C4IER_DOIE
#define C4IER_DOIE_BIT 3
#define CAN4IER_DOIE_BIT C4IER_DOIE_BIT
#define C4IER_WUIE_MASK 0x10
#define CAN4IER_WUIE_MASK C4IER_WUIE_MASK
#define C4IER_WUIE 0x10
#define CAN4IER_WUIE C4IER_WUIE
#define C4IER_WUIE_BIT 4
#define CAN4IER_WUIE_BIT C4IER_WUIE_BIT
#define C4IER_EPIE_MASK 0x20
#define CAN4IER_EPIE_MASK C4IER_EPIE_MASK
#define C4IER_EPIE 0x20
#define CAN4IER_EPIE C4IER_EPIE
#define C4IER_EPIE_BIT 5
#define CAN4IER_EPIE_BIT C4IER_EPIE_BIT
#define C4IER_ALIE_MASK 0x40
#define CAN4IER_ALIE_MASK C4IER_ALIE_MASK
#define C4IER_ALIE 0x40
#define CAN4IER_ALIE C4IER_ALIE
#define C4IER_ALIE_BIT 6
#define CAN4IER_ALIE_BIT C4IER_ALIE_BIT
#define C4IER_BEIE_MASK 0x80
#define CAN4IER_BEIE_MASK C4IER_BEIE_MASK
#define C4IER_BEIE 0x80
#define CAN4IER_BEIE C4IER_BEIE
#define C4IER_BEIE_BIT 7
#define CAN4IER_BEIE_BIT C4IER_BEIE_BIT
#define C4IER_IDIE_MASK 0x100
#define CAN4IER_IDIE_MASK C4IER_IDIE_MASK
#define C4IER_IDIE 0x100
#define CAN4IER_IDIE C4IER_IDIE
#define C4IER_IDIE_BIT 8
#define CAN4IER_IDIE_BIT C4IER_IDIE_BIT
#define C4IER_TIE2_MASK 0x200
#define CAN4IER_TIE2_MASK C4IER_TIE2_MASK
#define C4IER_TIE2 0x200
#define CAN4IER_TIE2 C4IER_TIE2
#define C4IER_TIE2_BIT 9
#define CAN4IER_TIE2_BIT C4IER_TIE2_BIT
#define C4IER_TIE3_MASK 0x400
#define CAN4IER_TIE3_MASK C4IER_TIE3_MASK
#define C4IER_TIE3 0x400
#define CAN4IER_TIE3 C4IER_TIE3
#define C4IER_TIE3_BIT 10
#define CAN4IER_TIE3_BIT C4IER_TIE3_BIT

#define C4BTR (*(volatile unsigned long *)0xE0050014)
#define CAN4BTR C4BTR
#define C4BTR_OFFSET 0x14
#define CAN4BTR_OFFSET C4BTR_OFFSET
#define C4BTR_BRP_MASK 0x3FF
#define CAN4BTR_BRP_MASK C4BTR_BRP_MASK
#define C4BTR_BRP_BIT 0
#define CAN4BTR_BRP_BIT C4BTR_BRP_BIT
#define C4BTR_SJW_MASK 0xC000
#define CAN4BTR_SJW_MASK C4BTR_SJW_MASK
#define C4BTR_SJW_BIT 14
#define CAN4BTR_SJW_BIT C4BTR_SJW_BIT
#define C4BTR_TSEG1_MASK 0xF0000
#define CAN4BTR_TSEG1_MASK C4BTR_TSEG1_MASK
#define C4BTR_TSEG1_BIT 16
#define CAN4BTR_TSEG1_BIT C4BTR_TSEG1_BIT
#define C4BTR_TSEG2_MASK 0x700000
#define CAN4BTR_TSEG2_MASK C4BTR_TSEG2_MASK
#define C4BTR_TSEG2_BIT 20
#define CAN4BTR_TSEG2_BIT C4BTR_TSEG2_BIT
#define C4BTR_SAM_MASK 0x800000
#define CAN4BTR_SAM_MASK C4BTR_SAM_MASK
#define C4BTR_SAM 0x800000
#define CAN4BTR_SAM C4BTR_SAM
#define C4BTR_SAM_BIT 23
#define CAN4BTR_SAM_BIT C4BTR_SAM_BIT

#define C4EWL (*(volatile unsigned long *)0xE0050018)
#define CAN4EWL C4EWL
#define C4EWL_OFFSET 0x18
#define CAN4EWL_OFFSET C4EWL_OFFSET
#define C4EWL_EWL_MASK 0xFF
#define CAN4EWL_EWL_MASK C4EWL_EWL_MASK
#define C4EWL_EWL_BIT 0
#define CAN4EWL_EWL_BIT C4EWL_EWL_BIT

#define C4SR (*(volatile unsigned long *)0xE005001C)
#define CAN4SR C4SR
#define C4SR_OFFSET 0x1C
#define CAN4SR_OFFSET C4SR_OFFSET
#define C4SR_RBS_MASK 0x1
#define CAN4SR_RBS_MASK C4SR_RBS_MASK
#define C4SR_RBS 0x1
#define CAN4SR_RBS C4SR_RBS
#define C4SR_RBS_BIT 0
#define CAN4SR_RBS_BIT C4SR_RBS_BIT
#define C4SR_DOS_MASK 0x2
#define CAN4SR_DOS_MASK C4SR_DOS_MASK
#define C4SR_DOS 0x2
#define CAN4SR_DOS C4SR_DOS
#define C4SR_DOS_BIT 1
#define CAN4SR_DOS_BIT C4SR_DOS_BIT
#define C4SR_TBS1_MASK 0x4
#define CAN4SR_TBS1_MASK C4SR_TBS1_MASK
#define C4SR_TBS1 0x4
#define CAN4SR_TBS1 C4SR_TBS1
#define C4SR_TBS1_BIT 2
#define CAN4SR_TBS1_BIT C4SR_TBS1_BIT
#define C4SR_TCS1_MASK 0x8
#define CAN4SR_TCS1_MASK C4SR_TCS1_MASK
#define C4SR_TCS1 0x8
#define CAN4SR_TCS1 C4SR_TCS1
#define C4SR_TCS1_BIT 3
#define CAN4SR_TCS1_BIT C4SR_TCS1_BIT
#define C4SR_RS_MASK 0x10
#define CAN4SR_RS_MASK C4SR_RS_MASK
#define C4SR_RS 0x10
#define CAN4SR_RS C4SR_RS
#define C4SR_RS_BIT 4
#define CAN4SR_RS_BIT C4SR_RS_BIT
#define C4SR_TS1_MASK 0x20
#define CAN4SR_TS1_MASK C4SR_TS1_MASK
#define C4SR_TS1 0x20
#define CAN4SR_TS1 C4SR_TS1
#define C4SR_TS1_BIT 5
#define CAN4SR_TS1_BIT C4SR_TS1_BIT
#define C4SR_ES_MASK 0x40
#define CAN4SR_ES_MASK C4SR_ES_MASK
#define C4SR_ES 0x40
#define CAN4SR_ES C4SR_ES
#define C4SR_ES_BIT 6
#define CAN4SR_ES_BIT C4SR_ES_BIT
#define C4SR_BS_MASK 0x80
#define CAN4SR_BS_MASK C4SR_BS_MASK
#define C4SR_BS 0x80
#define CAN4SR_BS C4SR_BS
#define C4SR_BS_BIT 7
#define CAN4SR_BS_BIT C4SR_BS_BIT
#define C4SR_RBS2_MASK 0x100
#define CAN4SR_RBS2_MASK C4SR_RBS2_MASK
#define C4SR_RBS2 0x100
#define CAN4SR_RBS2 C4SR_RBS2
#define C4SR_RBS2_BIT 8
#define CAN4SR_RBS2_BIT C4SR_RBS2_BIT
#define C4SR_DOS2_MASK 0x200
#define CAN4SR_DOS2_MASK C4SR_DOS2_MASK
#define C4SR_DOS2 0x200
#define CAN4SR_DOS2 C4SR_DOS2
#define C4SR_DOS2_BIT 9
#define CAN4SR_DOS2_BIT C4SR_DOS2_BIT
#define C4SR_TBS2_MASK 0x400
#define CAN4SR_TBS2_MASK C4SR_TBS2_MASK
#define C4SR_TBS2 0x400
#define CAN4SR_TBS2 C4SR_TBS2
#define C4SR_TBS2_BIT 10
#define CAN4SR_TBS2_BIT C4SR_TBS2_BIT
#define C4SR_TCS2_MASK 0x800
#define CAN4SR_TCS2_MASK C4SR_TCS2_MASK
#define C4SR_TCS2 0x800
#define CAN4SR_TCS2 C4SR_TCS2
#define C4SR_TCS2_BIT 11
#define CAN4SR_TCS2_BIT C4SR_TCS2_BIT
#define C4SR_RS2_MASK 0x1000
#define CAN4SR_RS2_MASK C4SR_RS2_MASK
#define C4SR_RS2 0x1000
#define CAN4SR_RS2 C4SR_RS2
#define C4SR_RS2_BIT 12
#define CAN4SR_RS2_BIT C4SR_RS2_BIT
#define C4SR_TS2_MASK 0x2000
#define CAN4SR_TS2_MASK C4SR_TS2_MASK
#define C4SR_TS2 0x2000
#define CAN4SR_TS2 C4SR_TS2
#define C4SR_TS2_BIT 13
#define CAN4SR_TS2_BIT C4SR_TS2_BIT
#define C4SR_ES2_MASK 0x4000
#define CAN4SR_ES2_MASK C4SR_ES2_MASK
#define C4SR_ES2 0x4000
#define CAN4SR_ES2 C4SR_ES2
#define C4SR_ES2_BIT 14
#define CAN4SR_ES2_BIT C4SR_ES2_BIT
#define C4SR_BS2_MASK 0x8000
#define CAN4SR_BS2_MASK C4SR_BS2_MASK
#define C4SR_BS2 0x8000
#define CAN4SR_BS2 C4SR_BS2
#define C4SR_BS2_BIT 15
#define CAN4SR_BS2_BIT C4SR_BS2_BIT
#define C4SR_RBS3_MASK 0x10000
#define CAN4SR_RBS3_MASK C4SR_RBS3_MASK
#define C4SR_RBS3 0x10000
#define CAN4SR_RBS3 C4SR_RBS3
#define C4SR_RBS3_BIT 16
#define CAN4SR_RBS3_BIT C4SR_RBS3_BIT
#define C4SR_DOS3_MASK 0x20000
#define CAN4SR_DOS3_MASK C4SR_DOS3_MASK
#define C4SR_DOS3 0x20000
#define CAN4SR_DOS3 C4SR_DOS3
#define C4SR_DOS3_BIT 17
#define CAN4SR_DOS3_BIT C4SR_DOS3_BIT
#define C4SR_TBS3_MASK 0x40000
#define CAN4SR_TBS3_MASK C4SR_TBS3_MASK
#define C4SR_TBS3 0x40000
#define CAN4SR_TBS3 C4SR_TBS3
#define C4SR_TBS3_BIT 18
#define CAN4SR_TBS3_BIT C4SR_TBS3_BIT
#define C4SR_TCS3_MASK 0x80000
#define CAN4SR_TCS3_MASK C4SR_TCS3_MASK
#define C4SR_TCS3 0x80000
#define CAN4SR_TCS3 C4SR_TCS3
#define C4SR_TCS3_BIT 19
#define CAN4SR_TCS3_BIT C4SR_TCS3_BIT
#define C4SR_RS3_MASK 0x100000
#define CAN4SR_RS3_MASK C4SR_RS3_MASK
#define C4SR_RS3 0x100000
#define CAN4SR_RS3 C4SR_RS3
#define C4SR_RS3_BIT 20
#define CAN4SR_RS3_BIT C4SR_RS3_BIT
#define C4SR_TS3_MASK 0x200000
#define CAN4SR_TS3_MASK C4SR_TS3_MASK
#define C4SR_TS3 0x200000
#define CAN4SR_TS3 C4SR_TS3
#define C4SR_TS3_BIT 21
#define CAN4SR_TS3_BIT C4SR_TS3_BIT
#define C4SR_ES3_MASK 0x400000
#define CAN4SR_ES3_MASK C4SR_ES3_MASK
#define C4SR_ES3 0x400000
#define CAN4SR_ES3 C4SR_ES3
#define C4SR_ES3_BIT 22
#define CAN4SR_ES3_BIT C4SR_ES3_BIT
#define C4SR_BS3_MASK 0x800000
#define CAN4SR_BS3_MASK C4SR_BS3_MASK
#define C4SR_BS3 0x800000
#define CAN4SR_BS3 C4SR_BS3
#define C4SR_BS3_BIT 23
#define CAN4SR_BS3_BIT C4SR_BS3_BIT

#define C4RFS (*(volatile unsigned long *)0xE0050020)
#define CAN4RFS C4RFS
#define C4RFS_OFFSET 0x20
#define CAN4RFS_OFFSET C4RFS_OFFSET
#define C4RFS_ID_Index_MASK 0x3FF
#define CAN4RFS_ID_Index_MASK C4RFS_ID_Index_MASK
#define C4RFS_ID_Index_BIT 0
#define CAN4RFS_ID_Index_BIT C4RFS_ID_Index_BIT
#define C4RFS_BP_MASK 0x400
#define CAN4RFS_BP_MASK C4RFS_BP_MASK
#define C4RFS_BP 0x400
#define CAN4RFS_BP C4RFS_BP
#define C4RFS_BP_BIT 10
#define CAN4RFS_BP_BIT C4RFS_BP_BIT
#define C4RFS_DLC_MASK 0xF0000
#define CAN4RFS_DLC_MASK C4RFS_DLC_MASK
#define C4RFS_DLC_BIT 16
#define CAN4RFS_DLC_BIT C4RFS_DLC_BIT
#define C4RFS_RTR_MASK 0x40000000
#define CAN4RFS_RTR_MASK C4RFS_RTR_MASK
#define C4RFS_RTR 0x40000000
#define CAN4RFS_RTR C4RFS_RTR
#define C4RFS_RTR_BIT 30
#define CAN4RFS_RTR_BIT C4RFS_RTR_BIT
#define C4RFS_FF_MASK 0x80000000
#define CAN4RFS_FF_MASK C4RFS_FF_MASK
#define C4RFS_FF 0x80000000
#define CAN4RFS_FF C4RFS_FF
#define C4RFS_FF_BIT 31
#define CAN4RFS_FF_BIT C4RFS_FF_BIT

#define C4RID (*(volatile unsigned long *)0xE0050024)
#define CAN4RID C4RID
#define C4RID_OFFSET 0x24
#define CAN4RID_OFFSET C4RID_OFFSET
#define C4RID_ID_MASK 0x7FF
#define CAN4RID_ID_MASK C4RID_ID_MASK
#define C4RID_ID_BIT 0
#define CAN4RID_ID_BIT C4RID_ID_BIT

#define C4RDA (*(volatile unsigned long *)0xE0050028)
#define CAN4RDA C4RDA
#define C4RDA_OFFSET 0x28
#define CAN4RDA_OFFSET C4RDA_OFFSET
#define C4RDA_Data_1_MASK 0xFF
#define CAN4RDA_Data_1_MASK C4RDA_Data_1_MASK
#define C4RDA_Data_1_BIT 0
#define CAN4RDA_Data_1_BIT C4RDA_Data_1_BIT
#define C4RDA_Data_2_MASK 0xFF00
#define CAN4RDA_Data_2_MASK C4RDA_Data_2_MASK
#define C4RDA_Data_2_BIT 8
#define CAN4RDA_Data_2_BIT C4RDA_Data_2_BIT
#define C4RDA_Data_3_MASK 0xFF0000
#define CAN4RDA_Data_3_MASK C4RDA_Data_3_MASK
#define C4RDA_Data_3_BIT 16
#define CAN4RDA_Data_3_BIT C4RDA_Data_3_BIT
#define C4RDA_Data_4_MASK 0xFF000000
#define CAN4RDA_Data_4_MASK C4RDA_Data_4_MASK
#define C4RDA_Data_4_BIT 24
#define CAN4RDA_Data_4_BIT C4RDA_Data_4_BIT

#define C4RDB (*(volatile unsigned long *)0xE005002C)
#define CAN4RDB C4RDB
#define C4RDB_OFFSET 0x2C
#define CAN4RDB_OFFSET C4RDB_OFFSET
#define C4RDB_Data_5_MASK 0xFF
#define CAN4RDB_Data_5_MASK C4RDB_Data_5_MASK
#define C4RDB_Data_5_BIT 0
#define CAN4RDB_Data_5_BIT C4RDB_Data_5_BIT
#define C4RDB_Data_6_MASK 0xFF00
#define CAN4RDB_Data_6_MASK C4RDB_Data_6_MASK
#define C4RDB_Data_6_BIT 8
#define CAN4RDB_Data_6_BIT C4RDB_Data_6_BIT
#define C4RDB_Data_7_MASK 0xFF0000
#define CAN4RDB_Data_7_MASK C4RDB_Data_7_MASK
#define C4RDB_Data_7_BIT 16
#define CAN4RDB_Data_7_BIT C4RDB_Data_7_BIT
#define C4RDB_Data_8_MASK 0xFF000000
#define CAN4RDB_Data_8_MASK C4RDB_Data_8_MASK
#define C4RDB_Data_8_BIT 24
#define CAN4RDB_Data_8_BIT C4RDB_Data_8_BIT

#define C4TFI1 (*(volatile unsigned long *)0xE0050030)
#define CAN4TFI1 C4TFI1
#define C4TFI1_OFFSET 0x30
#define CAN4TFI1_OFFSET C4TFI1_OFFSET
#define C4TFI1_PRIO_MASK 0xFF
#define CAN4TFI1_PRIO_MASK C4TFI1_PRIO_MASK
#define C4TFI1_PRIO_BIT 0
#define CAN4TFI1_PRIO_BIT C4TFI1_PRIO_BIT
#define C4TFI1_DLC_MASK 0xF0000
#define CAN4TFI1_DLC_MASK C4TFI1_DLC_MASK
#define C4TFI1_DLC_BIT 16
#define CAN4TFI1_DLC_BIT C4TFI1_DLC_BIT
#define C4TFI1_RTR_MASK 0x40000000
#define CAN4TFI1_RTR_MASK C4TFI1_RTR_MASK
#define C4TFI1_RTR 0x40000000
#define CAN4TFI1_RTR C4TFI1_RTR
#define C4TFI1_RTR_BIT 30
#define CAN4TFI1_RTR_BIT C4TFI1_RTR_BIT
#define C4TFI1_FF_MASK 0x80000000
#define CAN4TFI1_FF_MASK C4TFI1_FF_MASK
#define C4TFI1_FF 0x80000000
#define CAN4TFI1_FF C4TFI1_FF
#define C4TFI1_FF_BIT 31
#define CAN4TFI1_FF_BIT C4TFI1_FF_BIT

#define C4TID1 (*(volatile unsigned long *)0xE0050034)
#define CAN4TID1 C4TID1
#define C4TID1_OFFSET 0x34
#define CAN4TID1_OFFSET C4TID1_OFFSET
#define C4TID1_ID_MASK 0x7FF
#define CAN4TID1_ID_MASK C4TID1_ID_MASK
#define C4TID1_ID_BIT 0
#define CAN4TID1_ID_BIT C4TID1_ID_BIT

#define C4TDA1 (*(volatile unsigned long *)0xE0050038)
#define CAN4TDA1 C4TDA1
#define C4TDA1_OFFSET 0x38
#define CAN4TDA1_OFFSET C4TDA1_OFFSET
#define C4TDA1_Data_1_MASK 0xFF
#define CAN4TDA1_Data_1_MASK C4TDA1_Data_1_MASK
#define C4TDA1_Data_1_BIT 0
#define CAN4TDA1_Data_1_BIT C4TDA1_Data_1_BIT
#define C4TDA1_Data_2_MASK 0xFF00
#define CAN4TDA1_Data_2_MASK C4TDA1_Data_2_MASK
#define C4TDA1_Data_2_BIT 8
#define CAN4TDA1_Data_2_BIT C4TDA1_Data_2_BIT
#define C4TDA1_Data_3_MASK 0xFF0000
#define CAN4TDA1_Data_3_MASK C4TDA1_Data_3_MASK
#define C4TDA1_Data_3_BIT 16
#define CAN4TDA1_Data_3_BIT C4TDA1_Data_3_BIT
#define C4TDA1_Data_4_MASK 0xFF000000
#define CAN4TDA1_Data_4_MASK C4TDA1_Data_4_MASK
#define C4TDA1_Data_4_BIT 24
#define CAN4TDA1_Data_4_BIT C4TDA1_Data_4_BIT

#define C4TDB1 (*(volatile unsigned long *)0xE005003C)
#define CAN4TDB1 C4TDB1
#define C4TDB1_OFFSET 0x3C
#define CAN4TDB1_OFFSET C4TDB1_OFFSET
#define C4TDB1_Data_5_MASK 0xFF
#define CAN4TDB1_Data_5_MASK C4TDB1_Data_5_MASK
#define C4TDB1_Data_5_BIT 0
#define CAN4TDB1_Data_5_BIT C4TDB1_Data_5_BIT
#define C4TDB1_Data_6_MASK 0xFF00
#define CAN4TDB1_Data_6_MASK C4TDB1_Data_6_MASK
#define C4TDB1_Data_6_BIT 8
#define CAN4TDB1_Data_6_BIT C4TDB1_Data_6_BIT
#define C4TDB1_Data_7_MASK 0xFF0000
#define CAN4TDB1_Data_7_MASK C4TDB1_Data_7_MASK
#define C4TDB1_Data_7_BIT 16
#define CAN4TDB1_Data_7_BIT C4TDB1_Data_7_BIT
#define C4TDB1_Data_8_MASK 0xFF000000
#define CAN4TDB1_Data_8_MASK C4TDB1_Data_8_MASK
#define C4TDB1_Data_8_BIT 24
#define CAN4TDB1_Data_8_BIT C4TDB1_Data_8_BIT

#define C4TFI2 (*(volatile unsigned long *)0xE0050040)
#define CAN4TFI2 C4TFI2
#define C4TFI2_OFFSET 0x40
#define CAN4TFI2_OFFSET C4TFI2_OFFSET
#define C4TFI2_PRIO_MASK 0xFF
#define CAN4TFI2_PRIO_MASK C4TFI2_PRIO_MASK
#define C4TFI2_PRIO_BIT 0
#define CAN4TFI2_PRIO_BIT C4TFI2_PRIO_BIT
#define C4TFI2_DLC_MASK 0xF0000
#define CAN4TFI2_DLC_MASK C4TFI2_DLC_MASK
#define C4TFI2_DLC_BIT 16
#define CAN4TFI2_DLC_BIT C4TFI2_DLC_BIT
#define C4TFI2_RTR_MASK 0x40000000
#define CAN4TFI2_RTR_MASK C4TFI2_RTR_MASK
#define C4TFI2_RTR 0x40000000
#define CAN4TFI2_RTR C4TFI2_RTR
#define C4TFI2_RTR_BIT 30
#define CAN4TFI2_RTR_BIT C4TFI2_RTR_BIT
#define C4TFI2_FF_MASK 0x80000000
#define CAN4TFI2_FF_MASK C4TFI2_FF_MASK
#define C4TFI2_FF 0x80000000
#define CAN4TFI2_FF C4TFI2_FF
#define C4TFI2_FF_BIT 31
#define CAN4TFI2_FF_BIT C4TFI2_FF_BIT

#define C4TID2 (*(volatile unsigned long *)0xE0050044)
#define CAN4TID2 C4TID2
#define C4TID2_OFFSET 0x44
#define CAN4TID2_OFFSET C4TID2_OFFSET
#define C4TID2_ID_MASK 0x7FF
#define CAN4TID2_ID_MASK C4TID2_ID_MASK
#define C4TID2_ID_BIT 0
#define CAN4TID2_ID_BIT C4TID2_ID_BIT

#define C4TDA2 (*(volatile unsigned long *)0xE0050048)
#define CAN4TDA2 C4TDA2
#define C4TDA2_OFFSET 0x48
#define CAN4TDA2_OFFSET C4TDA2_OFFSET
#define C4TDA2_Data_1_MASK 0xFF
#define CAN4TDA2_Data_1_MASK C4TDA2_Data_1_MASK
#define C4TDA2_Data_1_BIT 0
#define CAN4TDA2_Data_1_BIT C4TDA2_Data_1_BIT
#define C4TDA2_Data_2_MASK 0xFF00
#define CAN4TDA2_Data_2_MASK C4TDA2_Data_2_MASK
#define C4TDA2_Data_2_BIT 8
#define CAN4TDA2_Data_2_BIT C4TDA2_Data_2_BIT
#define C4TDA2_Data_3_MASK 0xFF0000
#define CAN4TDA2_Data_3_MASK C4TDA2_Data_3_MASK
#define C4TDA2_Data_3_BIT 16
#define CAN4TDA2_Data_3_BIT C4TDA2_Data_3_BIT
#define C4TDA2_Data_4_MASK 0xFF000000
#define CAN4TDA2_Data_4_MASK C4TDA2_Data_4_MASK
#define C4TDA2_Data_4_BIT 24
#define CAN4TDA2_Data_4_BIT C4TDA2_Data_4_BIT

#define C4TDB2 (*(volatile unsigned long *)0xE005004C)
#define CAN4TDB2 C4TDB2
#define C4TDB2_OFFSET 0x4C
#define CAN4TDB2_OFFSET C4TDB2_OFFSET
#define C4TDB2_Data_5_MASK 0xFF
#define CAN4TDB2_Data_5_MASK C4TDB2_Data_5_MASK
#define C4TDB2_Data_5_BIT 0
#define CAN4TDB2_Data_5_BIT C4TDB2_Data_5_BIT
#define C4TDB2_Data_6_MASK 0xFF00
#define CAN4TDB2_Data_6_MASK C4TDB2_Data_6_MASK
#define C4TDB2_Data_6_BIT 8
#define CAN4TDB2_Data_6_BIT C4TDB2_Data_6_BIT
#define C4TDB2_Data_7_MASK 0xFF0000
#define CAN4TDB2_Data_7_MASK C4TDB2_Data_7_MASK
#define C4TDB2_Data_7_BIT 16
#define CAN4TDB2_Data_7_BIT C4TDB2_Data_7_BIT
#define C4TDB2_Data_8_MASK 0xFF000000
#define CAN4TDB2_Data_8_MASK C4TDB2_Data_8_MASK
#define C4TDB2_Data_8_BIT 24
#define CAN4TDB2_Data_8_BIT C4TDB2_Data_8_BIT

#define C4TFI3 (*(volatile unsigned long *)0xE0050050)
#define CAN4TFI3 C4TFI3
#define C4TFI3_OFFSET 0x50
#define CAN4TFI3_OFFSET C4TFI3_OFFSET
#define C4TFI3_PRIO_MASK 0xFF
#define CAN4TFI3_PRIO_MASK C4TFI3_PRIO_MASK
#define C4TFI3_PRIO_BIT 0
#define CAN4TFI3_PRIO_BIT C4TFI3_PRIO_BIT
#define C4TFI3_DLC_MASK 0xF0000
#define CAN4TFI3_DLC_MASK C4TFI3_DLC_MASK
#define C4TFI3_DLC_BIT 16
#define CAN4TFI3_DLC_BIT C4TFI3_DLC_BIT
#define C4TFI3_RTR_MASK 0x40000000
#define CAN4TFI3_RTR_MASK C4TFI3_RTR_MASK
#define C4TFI3_RTR 0x40000000
#define CAN4TFI3_RTR C4TFI3_RTR
#define C4TFI3_RTR_BIT 30
#define CAN4TFI3_RTR_BIT C4TFI3_RTR_BIT
#define C4TFI3_FF_MASK 0x80000000
#define CAN4TFI3_FF_MASK C4TFI3_FF_MASK
#define C4TFI3_FF 0x80000000
#define CAN4TFI3_FF C4TFI3_FF
#define C4TFI3_FF_BIT 31
#define CAN4TFI3_FF_BIT C4TFI3_FF_BIT

#define C4TID3 (*(volatile unsigned long *)0xE0050054)
#define CAN4TID3 C4TID3
#define C4TID3_OFFSET 0x54
#define CAN4TID3_OFFSET C4TID3_OFFSET
#define C4TID3_ID_MASK 0x7FF
#define CAN4TID3_ID_MASK C4TID3_ID_MASK
#define C4TID3_ID_BIT 0
#define CAN4TID3_ID_BIT C4TID3_ID_BIT

#define C4TDA3 (*(volatile unsigned long *)0xE0050058)
#define CAN4TDA3 C4TDA3
#define C4TDA3_OFFSET 0x58
#define CAN4TDA3_OFFSET C4TDA3_OFFSET
#define C4TDA3_Data_1_MASK 0xFF
#define CAN4TDA3_Data_1_MASK C4TDA3_Data_1_MASK
#define C4TDA3_Data_1_BIT 0
#define CAN4TDA3_Data_1_BIT C4TDA3_Data_1_BIT
#define C4TDA3_Data_2_MASK 0xFF00
#define CAN4TDA3_Data_2_MASK C4TDA3_Data_2_MASK
#define C4TDA3_Data_2_BIT 8
#define CAN4TDA3_Data_2_BIT C4TDA3_Data_2_BIT
#define C4TDA3_Data_3_MASK 0xFF0000
#define CAN4TDA3_Data_3_MASK C4TDA3_Data_3_MASK
#define C4TDA3_Data_3_BIT 16
#define CAN4TDA3_Data_3_BIT C4TDA3_Data_3_BIT
#define C4TDA3_Data_4_MASK 0xFF000000
#define CAN4TDA3_Data_4_MASK C4TDA3_Data_4_MASK
#define C4TDA3_Data_4_BIT 24
#define CAN4TDA3_Data_4_BIT C4TDA3_Data_4_BIT

#define C4TDB3 (*(volatile unsigned long *)0xE005005C)
#define CAN4TDB3 C4TDB3
#define C4TDB3_OFFSET 0x5C
#define CAN4TDB3_OFFSET C4TDB3_OFFSET
#define C4TDB3_Data_5_MASK 0xFF
#define CAN4TDB3_Data_5_MASK C4TDB3_Data_5_MASK
#define C4TDB3_Data_5_BIT 0
#define CAN4TDB3_Data_5_BIT C4TDB3_Data_5_BIT
#define C4TDB3_Data_6_MASK 0xFF00
#define CAN4TDB3_Data_6_MASK C4TDB3_Data_6_MASK
#define C4TDB3_Data_6_BIT 8
#define CAN4TDB3_Data_6_BIT C4TDB3_Data_6_BIT
#define C4TDB3_Data_7_MASK 0xFF0000
#define CAN4TDB3_Data_7_MASK C4TDB3_Data_7_MASK
#define C4TDB3_Data_7_BIT 16
#define CAN4TDB3_Data_7_BIT C4TDB3_Data_7_BIT
#define C4TDB3_Data_8_MASK 0xFF000000
#define CAN4TDB3_Data_8_MASK C4TDB3_Data_8_MASK
#define C4TDB3_Data_8_BIT 24
#define CAN4TDB3_Data_8_BIT C4TDB3_Data_8_BIT

#define SSP_BASE 0xE005C000

#define SSPCR0 (*(volatile unsigned long *)0xE005C000)
#define SSPCR0_OFFSET 0x0
#define SSPCR0_SCR_MASK 0xFF00
#define SSPCR0_SCR_BIT 8
#define SSPCR0_CPHA_MASK 0x80
#define SSPCR0_CPHA 0x80
#define SSPCR0_CPHA_BIT 7
#define SSPCR0_CPOL_MASK 0x40
#define SSPCR0_CPOL 0x40
#define SSPCR0_CPOL_BIT 6
#define SSPCR0_FRF_MASK 0x30
#define SSPCR0_FRF_BIT 4
#define SSPCR0_DSS_MASK 0xF
#define SSPCR0_DSS_BIT 0

#define SSPCR1 (*(volatile unsigned long *)0xE005C004)
#define SSPCR1_OFFSET 0x4
#define SSPCR1_SOD_MASK 0x8
#define SSPCR1_SOD 0x8
#define SSPCR1_SOD_BIT 3
#define SSPCR1_MS_MASK 0x4
#define SSPCR1_MS 0x4
#define SSPCR1_MS_BIT 2
#define SSPCR1_SSE_MASK 0x2
#define SSPCR1_SSE 0x2
#define SSPCR1_SSE_BIT 1
#define SSPCR1_LBE_MASK 0x1
#define SSPCR1_LBE 0x1
#define SSPCR1_LBE_BIT 0

#define SSPDR (*(volatile unsigned long *)0xE005C008)
#define SSPDR_OFFSET 0x8

#define SSPSR (*(volatile unsigned long *)0xE005C00C)
#define SSPSR_OFFSET 0xC
#define SSPSR_BSY_MASK 0x10
#define SSPSR_BSY 0x10
#define SSPSR_BSY_BIT 4
#define SSPSR_RFF_MASK 0x8
#define SSPSR_RFF 0x8
#define SSPSR_RFF_BIT 3
#define SSPSR_RNE_MASK 0x4
#define SSPSR_RNE 0x4
#define SSPSR_RNE_BIT 2
#define SSPSR_TNF_MASK 0x2
#define SSPSR_TNF 0x2
#define SSPSR_TNF_BIT 1
#define SSPSR_TFE_MASK 0x1
#define SSPSR_TFE 0x1
#define SSPSR_TFE_BIT 0

#define SSPCPSR (*(volatile unsigned long *)0xE005C010)
#define SSPCPSR_OFFSET 0x10
#define SSPCPSR_CPSDVSR_MASK 0xFF
#define SSPCPSR_CPSDVSR_BIT 0

#define SSPIMSC (*(volatile unsigned long *)0xE005C014)
#define SSPIMSC_OFFSET 0x14
#define SSPIMSC_TXIM_MASK 0x8
#define SSPIMSC_TXIM 0x8
#define SSPIMSC_TXIM_BIT 3
#define SSPIMSC_RXIM_MASK 0x4
#define SSPIMSC_RXIM 0x4
#define SSPIMSC_RXIM_BIT 2
#define SSPIMSC_RTIM_MASK 0x2
#define SSPIMSC_RTIM 0x2
#define SSPIMSC_RTIM_BIT 1
#define SSPIMSC_RORIM_MASK 0x1
#define SSPIMSC_RORIM 0x1
#define SSPIMSC_RORIM_BIT 0

#define SSPRIS (*(volatile unsigned long *)0xE005C018)
#define SSPRIS_OFFSET 0x18
#define SSPRIS_TXRIS_MASK 0x8
#define SSPRIS_TXRIS 0x8
#define SSPRIS_TXRIS_BIT 3
#define SSPRIS_RXRIS_MASK 0x4
#define SSPRIS_RXRIS 0x4
#define SSPRIS_RXRIS_BIT 2
#define SSPRIS_RTRIS_MASK 0x2
#define SSPRIS_RTRIS 0x2
#define SSPRIS_RTRIS_BIT 1
#define SSPRIS_RORRIS_MASK 0x1
#define SSPRIS_RORRIS 0x1
#define SSPRIS_RORRIS_BIT 0

#define SSPMIS (*(volatile unsigned long *)0xE005C01C)
#define SSPMIS_OFFSET 0x1C
#define SSPMIS_TXMIS_MASK 0x8
#define SSPMIS_TXMIS 0x8
#define SSPMIS_TXMIS_BIT 3
#define SSPMIS_RXMIS_MASK 0x4
#define SSPMIS_RXMIS 0x4
#define SSPMIS_RXMIS_BIT 2
#define SSPMIS_RTMIS_MASK 0x2
#define SSPMIS_RTMIS 0x2
#define SSPMIS_RTMIS_BIT 1
#define SSPMIS_RORMIS_MASK 0x1
#define SSPMIS_RORMIS 0x1
#define SSPMIS_RORMIS_BIT 0

#define SSPICR (*(volatile unsigned long *)0xE005C020)
#define SSPICR_OFFSET 0x20
#define SSPICR_RTIC_MASK 0x2
#define SSPICR_RTIC 0x2
#define SSPICR_RTIC_BIT 1
#define SSPICR_RORIC_MASK 0x1
#define SSPICR_RORIC 0x1
#define SSPICR_RORIC_BIT 0

#define SCB_BASE 0xE01FC000

#define MAMCR (*(volatile unsigned char *)0xE01FC000)
#define MAMCR_OFFSET 0x0
#define MAMCR_MAM_mode_control_MASK 0x3
#define MAMCR_MAM_mode_control_BIT 0

#define MAMTIM (*(volatile unsigned char *)0xE01FC004)
#define MAMTIM_OFFSET 0x4
#define MAMTIM_MAM_fetch_cycle_timing_MASK 0x7
#define MAMTIM_MAM_fetch_cycle_timing_BIT 0

#define MEMMAP (*(volatile unsigned char *)0xE01FC040)
#define MEMMAP_OFFSET 0x40
#define MEMMAP_MAP_MASK 0x3
#define MEMMAP_MAP_BIT 0

#define PLLCON (*(volatile unsigned char *)0xE01FC080)
#define PLLCON_OFFSET 0x80
#define PLLCON_PLLE_MASK 0x1
#define PLLCON_PLLE 0x1
#define PLLCON_PLLE_BIT 0
#define PLLCON_PLLC_MASK 0x2
#define PLLCON_PLLC 0x2
#define PLLCON_PLLC_BIT 1

#define PLLCFG (*(volatile unsigned char *)0xE01FC084)
#define PLLCFG_OFFSET 0x84
#define PLLCFG_MSEL_MASK 0x1F
#define PLLCFG_MSEL_BIT 0
#define PLLCFG_PSEL_MASK 0x60
#define PLLCFG_PSEL_BIT 5

#define PLLSTAT (*(volatile unsigned short *)0xE01FC088)
#define PLLSTAT_OFFSET 0x88
#define PLLSTAT_MSEL_MASK 0x1F
#define PLLSTAT_MSEL_BIT 0
#define PLLSTAT_PSEL_MASK 0x60
#define PLLSTAT_PSEL_BIT 5
#define PLLSTAT_PLLE_MASK 0x100
#define PLLSTAT_PLLE 0x100
#define PLLSTAT_PLLE_BIT 8
#define PLLSTAT_PLLC_MASK 0x200
#define PLLSTAT_PLLC 0x200
#define PLLSTAT_PLLC_BIT 9
#define PLLSTAT_PLOCK_MASK 0x400
#define PLLSTAT_PLOCK 0x400
#define PLLSTAT_PLOCK_BIT 10

#define PLLFEED (*(volatile unsigned char *)0xE01FC08C)
#define PLLFEED_OFFSET 0x8C

#define PCON (*(volatile unsigned char *)0xE01FC0C0)
#define PCON_OFFSET 0xC0
#define PCON_IDL_MASK 0x1
#define PCON_IDL 0x1
#define PCON_IDL_BIT 0
#define PCON_PD_MASK 0x2
#define PCON_PD 0x2
#define PCON_PD_BIT 1

#define PCONP (*(volatile unsigned long *)0xE01FC0C4)
#define PCONP_OFFSET 0xC4
#define PCONP_PCTIM0_MASK 0x2
#define PCONP_PCTIM0 0x2
#define PCONP_PCTIM0_BIT 1
#define PCONP_PCTIM1_MASK 0x4
#define PCONP_PCTIM1 0x4
#define PCONP_PCTIM1_BIT 2
#define PCONP_PCUART0_MASK 0x8
#define PCONP_PCUART0 0x8
#define PCONP_PCUART0_BIT 3
#define PCONP_PCUART1_MASK 0x10
#define PCONP_PCUART1 0x10
#define PCONP_PCUART1_BIT 4
#define PCONP_PCPWM0_MASK 0x20
#define PCONP_PCPWM0 0x20
#define PCONP_PCPWM0_BIT 5
#define PCONP_PCI2C_MASK 0x80
#define PCONP_PCI2C 0x80
#define PCONP_PCI2C_BIT 7
#define PCONP_PCSPI0_MASK 0x100
#define PCONP_PCSPI0 0x100
#define PCONP_PCSPI0_BIT 8
#define PCONP_PCRTC_MASK 0x200
#define PCONP_PCRTC 0x200
#define PCONP_PCRTC_BIT 9
#define PCONP_PCSPI1_MASK 0x400
#define PCONP_PCSPI1 0x400
#define PCONP_PCSPI1_BIT 10
#define PCONP_PCAD_MASK 0x1000
#define PCONP_PCAD 0x1000
#define PCONP_PCAD_BIT 12
#define PCONP_PCAN1_MASK 0x2000
#define PCONP_PCAN1 0x2000
#define PCONP_PCAN1_BIT 13
#define PCONP_PCAN2_MASK 0x4000
#define PCONP_PCAN2 0x4000
#define PCONP_PCAN2_BIT 14
#define PCONP_PCAN3_MASK 0x8000
#define PCONP_PCAN3 0x8000
#define PCONP_PCAN3_BIT 15
#define PCONP_PCAN4_MASK 0x10000
#define PCONP_PCAN4 0x10000
#define PCONP_PCAN4_BIT 16

#define VPBDIV (*(volatile unsigned char *)0xE01FC100)
#define VPBDIV_OFFSET 0x100
#define VPBDIV_VPBDIV_MASK 0x3
#define VPBDIV_VPBDIV_BIT 0

#define EXTINT (*(volatile unsigned char *)0xE01FC140)
#define EXTINT_OFFSET 0x140
#define EXTINT_EINT0_MASK 0x1
#define EXTINT_EINT0 0x1
#define EXTINT_EINT0_BIT 0
#define EXTINT_EINT1_MASK 0x2
#define EXTINT_EINT1 0x2
#define EXTINT_EINT1_BIT 1
#define EXTINT_EINT2_MASK 0x4
#define EXTINT_EINT2 0x4
#define EXTINT_EINT2_BIT 2
#define EXTINT_EINT3_MASK 0x8
#define EXTINT_EINT3 0x8
#define EXTINT_EINT3_BIT 3

#define EXTWAKE (*(volatile unsigned char *)0xE01FC144)
#define EXTWAKE_OFFSET 0x144
#define EXTWAKE_EXTWAKE0_MASK 0x1
#define EXTWAKE_EXTWAKE0 0x1
#define EXTWAKE_EXTWAKE0_BIT 0
#define EXTWAKE_EXTWAKE1_MASK 0x2
#define EXTWAKE_EXTWAKE1 0x2
#define EXTWAKE_EXTWAKE1_BIT 1
#define EXTWAKE_EXTWAKE2_MASK 0x4
#define EXTWAKE_EXTWAKE2 0x4
#define EXTWAKE_EXTWAKE2_BIT 2
#define EXTWAKE_EXTWAKE3_MASK 0x8
#define EXTWAKE_EXTWAKE3 0x8
#define EXTWAKE_EXTWAKE3_BIT 3

#define EXTMODE (*(volatile unsigned char *)0xE01FC148)
#define EXTMODE_OFFSET 0x148
#define EXTMODE_EXTMODE0_MASK 0x1
#define EXTMODE_EXTMODE0 0x1
#define EXTMODE_EXTMODE0_BIT 0
#define EXTMODE_EXTMODE1_MASK 0x2
#define EXTMODE_EXTMODE1 0x2
#define EXTMODE_EXTMODE1_BIT 1
#define EXTMODE_EXTMODE2_MASK 0x4
#define EXTMODE_EXTMODE2 0x4
#define EXTMODE_EXTMODE2_BIT 2
#define EXTMODE_EXTMODE3_MASK 0x8
#define EXTMODE_EXTMODE3 0x8
#define EXTMODE_EXTMODE3_BIT 3

#define EXTPOLAR (*(volatile unsigned char *)0xE01FC14C)
#define EXTPOLAR_OFFSET 0x14C
#define EXTPOLAR_EXTPOLAR0_MASK 0x1
#define EXTPOLAR_EXTPOLAR0 0x1
#define EXTPOLAR_EXTPOLAR0_BIT 0
#define EXTPOLAR_EXTPOLAR1_MASK 0x2
#define EXTPOLAR_EXTPOLAR1 0x2
#define EXTPOLAR_EXTPOLAR1_BIT 1
#define EXTPOLAR_EXTPOLAR2_MASK 0x4
#define EXTPOLAR_EXTPOLAR2 0x4
#define EXTPOLAR_EXTPOLAR2_BIT 2
#define EXTPOLAR_EXTPOLAR3_MASK 0x8
#define EXTPOLAR_EXTPOLAR3 0x8
#define EXTPOLAR_EXTPOLAR3_BIT 3

#define VIC_BASE 0xFFFFF000

#define VICIRQStatus (*(volatile unsigned long *)0xFFFFF000)
#define VICIRQStatus_OFFSET 0x0

#define VICFIQStatus (*(volatile unsigned long *)0xFFFFF004)
#define VICFIQStatus_OFFSET 0x4

#define VICRawIntr (*(volatile unsigned long *)0xFFFFF008)
#define VICRawIntr_OFFSET 0x8

#define VICIntSelect (*(volatile unsigned long *)0xFFFFF00C)
#define VICIntSelect_OFFSET 0xC

#define VICIntEnable (*(volatile unsigned long *)0xFFFFF010)
#define VICIntEnable_OFFSET 0x10

#define VICIntEnClr (*(volatile unsigned long *)0xFFFFF014)
#define VICIntEnClr_OFFSET 0x14

#define VICSoftInt (*(volatile unsigned long *)0xFFFFF018)
#define VICSoftInt_OFFSET 0x18

#define VICSoftIntClear (*(volatile unsigned long *)0xFFFFF01C)
#define VICSoftIntClear_OFFSET 0x1C

#define VICProtection (*(volatile unsigned long *)0xFFFFF020)
#define VICProtection_OFFSET 0x20

#define VICVectAddr (*(volatile unsigned long *)0xFFFFF030)
#define VICVectAddr_OFFSET 0x30

#define VICDefVectAddr (*(volatile unsigned long *)0xFFFFF034)
#define VICDefVectAddr_OFFSET 0x34

#define VICVectAddr0 (*(volatile unsigned long *)0xFFFFF100)
#define VICVectAddr0_OFFSET 0x100

#define VICVectAddr1 (*(volatile unsigned long *)0xFFFFF104)
#define VICVectAddr1_OFFSET 0x104

#define VICVectAddr2 (*(volatile unsigned long *)0xFFFFF108)
#define VICVectAddr2_OFFSET 0x108

#define VICVectAddr3 (*(volatile unsigned long *)0xFFFFF10C)
#define VICVectAddr3_OFFSET 0x10C

#define VICVectAddr4 (*(volatile unsigned long *)0xFFFFF110)
#define VICVectAddr4_OFFSET 0x110

#define VICVectAddr5 (*(volatile unsigned long *)0xFFFFF114)
#define VICVectAddr5_OFFSET 0x114

#define VICVectAddr6 (*(volatile unsigned long *)0xFFFFF118)
#define VICVectAddr6_OFFSET 0x118

#define VICVectAddr7 (*(volatile unsigned long *)0xFFFFF11C)
#define VICVectAddr7_OFFSET 0x11C

#define VICVectAddr8 (*(volatile unsigned long *)0xFFFFF120)
#define VICVectAddr8_OFFSET 0x120

#define VICVectAddr9 (*(volatile unsigned long *)0xFFFFF124)
#define VICVectAddr9_OFFSET 0x124

#define VICVectAddr10 (*(volatile unsigned long *)0xFFFFF128)
#define VICVectAddr10_OFFSET 0x128

#define VICVectAddr11 (*(volatile unsigned long *)0xFFFFF12C)
#define VICVectAddr11_OFFSET 0x12C

#define VICVectAddr12 (*(volatile unsigned long *)0xFFFFF130)
#define VICVectAddr12_OFFSET 0x130

#define VICVectAddr13 (*(volatile unsigned long *)0xFFFFF134)
#define VICVectAddr13_OFFSET 0x134

#define VICVectAddr14 (*(volatile unsigned long *)0xFFFFF138)
#define VICVectAddr14_OFFSET 0x138

#define VICVectAddr15 (*(volatile unsigned long *)0xFFFFF13C)
#define VICVectAddr15_OFFSET 0x13C

#define VICVectCntl0 (*(volatile unsigned long *)0xFFFFF200)
#define VICVectCntl0_OFFSET 0x200

#define VICVectCntl1 (*(volatile unsigned long *)0xFFFFF204)
#define VICVectCntl1_OFFSET 0x204

#define VICVectCntl2 (*(volatile unsigned long *)0xFFFFF208)
#define VICVectCntl2_OFFSET 0x208

#define VICVectCntl3 (*(volatile unsigned long *)0xFFFFF20C)
#define VICVectCntl3_OFFSET 0x20C

#define VICVectCntl4 (*(volatile unsigned long *)0xFFFFF210)
#define VICVectCntl4_OFFSET 0x210

#define VICVectCntl5 (*(volatile unsigned long *)0xFFFFF214)
#define VICVectCntl5_OFFSET 0x214

#define VICVectCntl6 (*(volatile unsigned long *)0xFFFFF218)
#define VICVectCntl6_OFFSET 0x218

#define VICVectCntl7 (*(volatile unsigned long *)0xFFFFF21C)
#define VICVectCntl7_OFFSET 0x21C

#define VICVectCntl8 (*(volatile unsigned long *)0xFFFFF220)
#define VICVectCntl8_OFFSET 0x220

#define VICVectCntl9 (*(volatile unsigned long *)0xFFFFF224)
#define VICVectCntl9_OFFSET 0x224

#define VICVectCntl10 (*(volatile unsigned long *)0xFFFFF228)
#define VICVectCntl10_OFFSET 0x228

#define VICVectCntl11 (*(volatile unsigned long *)0xFFFFF22C)
#define VICVectCntl11_OFFSET 0x22C

#define VICVectCntl12 (*(volatile unsigned long *)0xFFFFF230)
#define VICVectCntl12_OFFSET 0x230

#define VICVectCntl13 (*(volatile unsigned long *)0xFFFFF234)
#define VICVectCntl13_OFFSET 0x234

#define VICVectCntl14 (*(volatile unsigned long *)0xFFFFF238)
#define VICVectCntl14_OFFSET 0x238

#define VICVectCntl15 (*(volatile unsigned long *)0xFFFFF23C)
#define VICVectCntl15_OFFSET 0x23C


#endif
