#ifndef __LPC17xx_H
#define __LPC17xx_H

#include "CortexM3.h"


/* System Control Block (SCB) includes:
   Flash Accelerator Module, Clocking and Power Control, External Interrupts,
   Reset, System Control and Status
*/
#define SCB_BASE_ADDR   0x400FC000

/* Flash Accelerator Module */
#define FLASHCTRL      (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x000))
#define FLASHTIM       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x004))

/* Phase Locked Loop (Main PLL0) */
#define PLL0CON        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x080))
#define PLL0CFG        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x084))
#define PLL0STAT       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x088))
#define PLL0FEED       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x08C))

/* Phase Locked Loop (USB PLL1) */
#define PLL1CON        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0A0))
#define PLL1CFG        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0A4))
#define PLL1STAT       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0A8))
#define PLL1FEED       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0AC))

/* Power Control */
#define PCON           (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0C0))
#define PCONP          (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x0C4))

/* Clock Selection and Dividers */
#define CCLKCFG        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x104))
#define USBCLKCFG      (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x108))
#define CLKSRCSEL      (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x10C))
#define IRCTRIM        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1A4))
#define PCLKSEL0       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1A8))
#define PCLKSEL1       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1AC))
    
/* External Interrupts */
#define EXTINT         (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x140))
#define EXTMODE        (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x148))
#define EXTPOLAR       (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x14C))

/* Reset */
#define RSIR           (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x180))

/* System Controls and Status */
#define SCS            (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1A0)) 


/* Pin Connect Block */
#define PINCON_BASE_ADDR 0x4002C000
#define PINSEL0        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x00))
#define PINSEL1        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x04))
#define PINSEL2        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x08))
#define PINSEL3        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x0C))
#define PINSEL4        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x10))
#define PINSEL5        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x14))
#define PINSEL6        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x18))
#define PINSEL7        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x1C))
#define PINSEL8        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x20))
#define PINSEL9        (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x24))
#define PINSEL10       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x28))

#define PINMODE0       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x40))
#define PINMODE1       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x44))
#define PINMODE2       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x48))
#define PINMODE3       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x4C))
#define PINMODE4       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x50))
#define PINMODE5       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x54))
#define PINMODE6       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x58))
#define PINMODE7       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x5C))
#define PINMODE8       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x60))
#define PINMODE9       (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x64))
#define PINMODE_OD0    (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x68))
#define PINMODE_OD1    (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x6C))
#define PINMODE_OD2    (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x70))
#define PINMODE_OD3    (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x74))
#define PINMODE_OD4    (*(volatile unsigned long *)(PINCON_BASE_ADDR + 0x78))


/* General Purpose Input/Output (GPIO) - Fast GPIO */
// #define GPIO_BASE_ADDR  0x50014000	/* For the first silicon v0.00 */
#define GPIO_BASE_ADDR  0x2009C000		/* For silicon v0.01 or newer */
#define FIO0DIR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x00)) 
#define FIO0MASK       (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x10))
#define FIO0PIN        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x14))
#define FIO0SET        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x18))
#define FIO0CLR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x1C))

#define FIO1DIR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x20)) 
#define FIO1MASK       (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x30))
#define FIO1PIN        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x34))
#define FIO1SET        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x38))
#define FIO1CLR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x3C))

#define FIO2DIR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x40)) 
#define FIO2MASK       (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x50))
#define FIO2PIN        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x54))
#define FIO2SET        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x58))
#define FIO2CLR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x5C))

#define FIO3DIR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x60)) 
#define FIO3MASK       (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x70))
#define FIO3PIN        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x74))
#define FIO3SET        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x78))
#define FIO3CLR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x7C))

#define FIO4DIR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x80)) 
#define FIO4MASK       (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x90))
#define FIO4PIN        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x94))
#define FIO4SET        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x98))
#define FIO4CLR        (*(volatile unsigned long *)(GPIO_BASE_ADDR + 0x9C))

/* FIOs can be accessed through WORD, HALF-WORD or BYTE. */
#define FIO0DIR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x00)) 
#define FIO1DIR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x20)) 
#define FIO2DIR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x40)) 
#define FIO3DIR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x60)) 
#define FIO4DIR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x80)) 

#define FIO0DIR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x01)) 
#define FIO1DIR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x21)) 
#define FIO2DIR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x41)) 
#define FIO3DIR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x61)) 
#define FIO4DIR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x81)) 

#define FIO0DIR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x02)) 
#define FIO1DIR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x22)) 
#define FIO2DIR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x42)) 
#define FIO3DIR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x62)) 
#define FIO4DIR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x82)) 

#define FIO0DIR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x03)) 
#define FIO1DIR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x23)) 
#define FIO2DIR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x43)) 
#define FIO3DIR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x63)) 
#define FIO4DIR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x83)) 

#define FIO0DIRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x00)) 
#define FIO1DIRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x20)) 
#define FIO2DIRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x40)) 
#define FIO3DIRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x60)) 
#define FIO4DIRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x80)) 

#define FIO0DIRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x02)) 
#define FIO1DIRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x22)) 
#define FIO2DIRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x42)) 
#define FIO3DIRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x62)) 
#define FIO4DIRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x82)) 

#define FIO0MASK0      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x10)) 
#define FIO1MASK0      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x30)) 
#define FIO2MASK0      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x40)) 
#define FIO3MASK0      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x50)) 
#define FIO4MASK0      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x90)) 

#define FIO0MASK1      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x11)) 
#define FIO1MASK1      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x31)) 
#define FIO2MASK1      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x41)) 
#define FIO3MASK1      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x51)) 
#define FIO4MASK1      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x91)) 

#define FIO0MASK2      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x12)) 
#define FIO1MASK2      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x32)) 
#define FIO2MASK2      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x42)) 
#define FIO3MASK2      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x52)) 
#define FIO4MASK2      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x92)) 

#define FIO0MASK3      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x13)) 
#define FIO1MASK3      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x33)) 
#define FIO2MASK3      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x43)) 
#define FIO3MASK3      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x53)) 
#define FIO4MASK3      (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x93)) 

#define FIO0MASKL      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x10)) 
#define FIO1MASKL      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x30)) 
#define FIO2MASKL      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x40)) 
#define FIO3MASKL      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x50)) 
#define FIO4MASKL      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x90)) 

#define FIO0MASKU      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x12)) 
#define FIO1MASKU      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x32)) 
#define FIO2MASKU      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x42)) 
#define FIO3MASKU      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x52)) 
#define FIO4MASKU      (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x92)) 

#define FIO0PIN0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x14)) 
#define FIO1PIN0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x34)) 
#define FIO2PIN0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x44)) 
#define FIO3PIN0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x54)) 
#define FIO4PIN0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x94)) 

#define FIO0PIN1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x15)) 
#define FIO1PIN1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x35)) 
#define FIO2PIN1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x45)) 
#define FIO3PIN1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x55)) 
#define FIO4PIN1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x95)) 

#define FIO0PIN2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x16)) 
#define FIO1PIN2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x36)) 
#define FIO2PIN2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x46)) 
#define FIO3PIN2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x56)) 
#define FIO4PIN2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x96)) 

#define FIO0PIN3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x17)) 
#define FIO1PIN3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x37)) 
#define FIO2PIN3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x47)) 
#define FIO3PIN3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x57)) 
#define FIO4PIN3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x97)) 

#define FIO0PINL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x14)) 
#define FIO1PINL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x34)) 
#define FIO2PINL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x44)) 
#define FIO3PINL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x54)) 
#define FIO4PINL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x94)) 

#define FIO0PINU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x16)) 
#define FIO1PINU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x36)) 
#define FIO2PINU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x46)) 
#define FIO3PINU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x56)) 
#define FIO4PINU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x96)) 

#define FIO0SET0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x18)) 
#define FIO1SET0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x38)) 
#define FIO2SET0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x48)) 
#define FIO3SET0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x58)) 
#define FIO4SET0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x98)) 

#define FIO0SET1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x19)) 
#define FIO1SET1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x39)) 
#define FIO2SET1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x49)) 
#define FIO3SET1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x59)) 
#define FIO4SET1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x99)) 

#define FIO0SET2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x1A)) 
#define FIO1SET2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x3A)) 
#define FIO2SET2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x4A)) 
#define FIO3SET2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x5A)) 
#define FIO4SET2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x9A)) 

#define FIO0SET3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x1B)) 
#define FIO1SET3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x3B)) 
#define FIO2SET3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x4B)) 
#define FIO3SET3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x5B)) 
#define FIO4SET3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x9B)) 

#define FIO0SETL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x18)) 
#define FIO1SETL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x38)) 
#define FIO2SETL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x48)) 
#define FIO3SETL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x58)) 
#define FIO4SETL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x98)) 

#define FIO0SETU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x1A)) 
#define FIO1SETU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x3A)) 
#define FIO2SETU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x4A)) 
#define FIO3SETU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x5A)) 
#define FIO4SETU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x9A)) 

#define FIO0CLR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x1C)) 
#define FIO1CLR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x3C)) 
#define FIO2CLR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x4C)) 
#define FIO3CLR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x5C)) 
#define FIO4CLR0       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x9C)) 

#define FIO0CLR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x1D)) 
#define FIO1CLR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x3D)) 
#define FIO2CLR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x4D)) 
#define FIO3CLR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x5D)) 
#define FIO4CLR1       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x9D)) 

#define FIO0CLR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x1E)) 
#define FIO1CLR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x3E)) 
#define FIO2CLR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x4E)) 
#define FIO3CLR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x5E)) 
#define FIO4CLR2       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x9E)) 

#define FIO0CLR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x1F)) 
#define FIO1CLR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x3F)) 
#define FIO2CLR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x4F)) 
#define FIO3CLR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x5F)) 
#define FIO4CLR3       (*(volatile unsigned char  *)(GPIO_BASE_ADDR + 0x9F)) 

#define FIO0CLRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x1C)) 
#define FIO1CLRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x3C)) 
#define FIO2CLRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x4C)) 
#define FIO3CLRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x5C)) 
#define FIO4CLRL       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x9C)) 

#define FIO0CLRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x1E)) 
#define FIO1CLRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x3E)) 
#define FIO2CLRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x4E)) 
#define FIO3CLRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x5E)) 
#define FIO4CLRU       (*(volatile unsigned short *)(GPIO_BASE_ADDR + 0x9E)) 

/* GPIO Interrupt Registers */
#define GPIO_INT_BASE_ADDR 0x40028000
#define IO0IntEnR      (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0x90)) 
#define IO0IntEnF      (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0x94))
#define IO0IntStatR    (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0x84))
#define IO0IntStatF    (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0x88))
#define IO0IntClr      (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0x8C))

#define IO2IntEnR      (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0xB0)) 
#define IO2IntEnF      (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0xB4))
#define IO2IntStatR    (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0xA4))
#define IO2IntStatF    (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0xA8))
#define IO2IntClr      (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0xAC))

#define IOIntStatus    (*(volatile unsigned long *)(GPIO_INT_BASE_ADDR + 0x80))


/* Timer 0 */
#define TMR0_BASE_ADDR 0x40004000
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
#define TMR1_BASE_ADDR 0x40008000
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
#define TMR2_BASE_ADDR 0x40090000
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
#define TMR3_BASE_ADDR 0x40094000
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


/* Pulse Width Modulator (PWM) */
#define PWM1_BASE_ADDR 0x40018000
#define PWM1IR         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x00))
#define PWM1TCR        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x04))
#define PWM1TC         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x08))
#define PWM1PR         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x0C))
#define PWM1PC         (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x10))
#define PWM1MCR        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x14))
#define PWM1MR0        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x18))
#define PWM1MR1        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x1C))
#define PWM1MR2        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x20))
#define PWM1MR3        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x24))
#define PWM1CCR        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x28))
#define PWM1CR0        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x2C))
#define PWM1CR1        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x30))
#define PWM1CR2        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x34))
#define PWM1CR3        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x38))
#define PWM1MR4        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x40))
#define PWM1MR5        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x44))
#define PWM1MR6        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x48))
#define PWM1PCR        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x4C))
#define PWM1LER        (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x50))
#define PWM1CTCR       (*(volatile unsigned long *)(PWM1_BASE_ADDR + 0x70))


/* Universal Asynchronous Receiver Transmitter 0 (UART0) */
#define UART0_BASE_ADDR 0x4000C000
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
#define U0FDR          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x28))
#define U0TER          (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x30))
#define U0RS485CTRL    (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x4C))
#define U0ADRMATCH     (*(volatile unsigned long *)(UART0_BASE_ADDR + 0x50))

/* Universal Asynchronous Receiver Transmitter 1 (UART1) */
#define UART1_BASE_ADDR 0x40010000
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
#define U1RS485CTRL    (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x4C))
#define U1ADRMATCH     (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x50))
#define U1RS485DLY     (*(volatile unsigned long *)(UART1_BASE_ADDR + 0x54))

/* Universal Asynchronous Receiver Transmitter 2 (UART2) */
#define UART2_BASE_ADDR 0x40098000
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
#define U2FDR          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x28))
#define U2TER          (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x30))
#define U2RS485CTRL    (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x4C))
#define U2ADRMATCH     (*(volatile unsigned long *)(UART2_BASE_ADDR + 0x50))

/* Universal Asynchronous Receiver Transmitter 3 (UART3) */
#define UART3_BASE_ADDR 0x4009C000
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
#define U3RS485CTRL    (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x4C))
#define U3ADRMATCH     (*(volatile unsigned long *)(UART3_BASE_ADDR + 0x50))


/* SPI0 (Serial Peripheral Interface 0) */
#define SPI0_BASE_ADDR 0x40020000
#define S0SPCR         (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x00))
#define S0SPSR         (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x04))
#define S0SPDR         (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x08))
#define S0SPCCR        (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x0C))
#define S0SPINT        (*(volatile unsigned long *)(SPI0_BASE_ADDR + 0x1C))

/* SSP0 Controller */
#define SSP0_BASE_ADDR 0x40088000
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
#define SSP1_BASE_ADDR 0x40030000
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


/* I2C Interface 0 */
#define I2C0_BASE_ADDR 0x4001C000
#define I2C0CONSET     (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x00))
#define I2C0STAT       (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x04))
#define I2C0DAT        (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x08))
#define I2C0ADR0       (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x0C))
#define I2C0SCLH       (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x10))
#define I2C0SCLL       (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x14))
#define I2C0CONCLR     (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x18))
#define I2C0MMCLR      (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x1C))
#define I2C0ADR1       (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x20))
#define I2C0ADR2       (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x24))
#define I2C0ADR3       (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x28))
#define I2C0DATBUFFER  (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x2C))
#define I2C0MASK0      (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x30))
#define I2C0MASK1      (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x34))
#define I2C0MASK2      (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x38))
#define I2C0MASK3      (*(volatile unsigned long *)(I2C0_BASE_ADDR + 0x3C))

/* I2C Interface 1 */
#define I2C1_BASE_ADDR 0x4005C000
#define I2C1CONSET     (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x00))
#define I2C1STAT       (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x04))
#define I2C1DAT        (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x08))
#define I2C1ADR0       (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x0C))
#define I2C1SCLH       (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x10))
#define I2C1SCLL       (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x14))
#define I2C1CONCLR     (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x18))
#define I2C1MMCLR      (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x1C))
#define I2C1ADR1       (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x20))
#define I2C1ADR2       (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x24))
#define I2C1ADR3       (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x28))
#define I2C1DATBUFFER  (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x2C))
#define I2C1MASK0      (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x30))
#define I2C1MASK1      (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x34))
#define I2C1MASK2      (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x38))
#define I2C1MASK3      (*(volatile unsigned long *)(I2C1_BASE_ADDR + 0x3C))

/* I2C Interface 2 */
#define I2C2_BASE_ADDR 0x400A0000
#define I2C2CONSET     (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x00))
#define I2C2STAT       (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x04))
#define I2C2DAT        (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x08))
#define I2C2ADR0       (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x0C))
#define I2C2SCLH       (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x10))
#define I2C2SCLL       (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x14))
#define I2C2CONCLR     (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x18))
#define I2C2MMCLR      (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x1C))
#define I2C2ADR1       (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x20))
#define I2C2ADR2       (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x24))
#define I2C2ADR3       (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x28))
#define I2C2DATBUFFER  (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x2C))
#define I2C2MASK0      (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x30))
#define I2C2MASK1      (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x34))
#define I2C2MASK2      (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x38))
#define I2C2MASK3      (*(volatile unsigned long *)(I2C2_BASE_ADDR + 0x3C))


/* I2S Interface Controller (I2S) */
#define I2S_BASE_ADDR  0x400A8000
#define I2SDAO         (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x00))
#define I2SDAI         (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x04))
#define I2STXFIFO      (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x08))
#define I2SRXFIFO      (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x0C))
#define I2SSTATE       (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x10))
#define I2SDMA1        (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x14))
#define I2SDMA2        (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x18))
#define I2SIRQ         (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x1C))
#define I2STXRATE      (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x20))
#define I2SRXRATE      (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x24))
#define I2STXBITRATE   (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x28))
#define I2SRXBITRATE   (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x2C))
#define I2STXMODE      (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x30))
#define I2SRXMODE      (*(volatile unsigned long *)(I2S_BASE_ADDR + 0x34))


/* Repetitive Interrupt Timer (RIT) */
#define RIT_BASE_ADDR  0x400B4000
#define RICOMPVAL      (*(volatile unsigned long *)(RIT_BASE_ADDR + 0x00))
#define RIMASK         (*(volatile unsigned long *)(RIT_BASE_ADDR + 0x04))
#define RICTRL         (*(volatile unsigned long *)(RIT_BASE_ADDR + 0x08))
#define RICOUNTER      (*(volatile unsigned long *)(RIT_BASE_ADDR + 0x0C))


/* Real Time Clock (RTC) */
#define RTC_BASE_ADDR  0x40024000
#define RTC_ILR        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x00))
#define RTC_CCR        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x08))
#define RTC_CIIR       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x0C))
#define RTC_AMR        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x10))
#define RTC_CTIME0     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x14))
#define RTC_CTIME1     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x18))
#define RTC_CTIME2     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x1C))
#define RTC_SEC        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x20))
#define RTC_MIN        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x24))
#define RTC_HOUR       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x28))
#define RTC_DOM        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x2C))
#define RTC_DOW        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x30))
#define RTC_DOY        (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x34))
#define RTC_MONTH      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x38))
#define RTC_YEAR       (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x3C))
#define RTC_CALIBRATION (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x40))
#define RTC_GPREG0     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x44))
#define RTC_GPREG1     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x48))
#define RTC_GPREG2     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x4C))
#define RTC_GPREG3     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x50))
#define RTC_GPREG4     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x54))
#define RTC_WAKEUPDIS  (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x58))
#define RTC_PWRCTRL    (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x5c))
#define RTC_ALSEC      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x60))
#define RTC_ALMIN      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x64))
#define RTC_ALHOUR     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x68))
#define RTC_ALDOM      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x6C))
#define RTC_ALDOW      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x70))
#define RTC_ALDOY      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x74))
#define RTC_ALMON      (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x78))
#define RTC_ALYEAR     (*(volatile unsigned long *)(RTC_BASE_ADDR + 0x7C))


/* Watchdog Timer (WDT) */
#define WDT_BASE_ADDR  0x40000000
#define WDMOD          (*(volatile unsigned long *)(WDT_BASE_ADDR + 0x00))
#define WDTC           (*(volatile unsigned long *)(WDT_BASE_ADDR + 0x04))
#define WDFEED         (*(volatile unsigned long *)(WDT_BASE_ADDR + 0x08))
#define WDTV           (*(volatile unsigned long *)(WDT_BASE_ADDR + 0x0C))
#define WDCLKSEL       (*(volatile unsigned long *)(WDT_BASE_ADDR + 0x10))


/* A/D Converter 0 (ADC0) */
#define AD0_BASE_ADDR  0x40034000
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
#define ADTRIM         (*(volatile unsigned long *)(AD0_BASE_ADDR + 0x34))


/* D/A Converter (DAC) */
#define DAC_BASE_ADDR  0x4008C000
#define DACR           (*(volatile unsigned long *)(DAC_BASE_ADDR + 0x00))
#define DACCTRL        (*(volatile unsigned long *)(DAC_BASE_ADDR + 0x04))
#define DACCNTVAL      (*(volatile unsigned long *)(DAC_BASE_ADDR + 0x08))


/* Motor Control PWM */
#define MCPWM_BASE_ADDR 0x400B8000
#define MCCON          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x00))
#define MCCON_SET      (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x04))
#define MCCON_CLR      (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x08))
#define MCCAPCON       (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x0C))
#define MCCAPCON_SET   (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x10))
#define MCCAPCON_CLR   (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x14))
#define MCTIM0         (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x18))
#define MCTIM1         (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x1C))
#define MCTIM2         (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x20))
#define MCPER0         (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x24))
#define MCPER1         (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x28))
#define MCPER2         (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x2C))
#define MCPW0          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x30))
#define MCPW1          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x34))
#define MCPW2          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x38))
#define MCDEADTIME     (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x3C))
#define MCCCP          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x40))
#define MCCR0          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x44))
#define MCCR1          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x48))
#define MCCR2          (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x4C))
#define MCINTEN        (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x50))
#define MCINTEN_SET    (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x54))
#define MCINTEN_CLR    (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x58))
#define MCCNTCON       (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x5C))
#define MCCNTCON_SET   (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x60))
#define MCCNTCON_CLR   (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x64))
#define MCINTFLAG      (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x68))
#define MCINTFLAG_SET  (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x6C))
#define MCINTFLAG_CLR  (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x70))
#define MCCAP_CLR      (*(volatile unsigned long *)(MCPWM_BASE_ADDR + 0x74))


/* Quadrature Encoder Interface (QEI) */
#define QEI_BASE_ADDR  0x400BC000

/* QEI Control Registers */
#define QEICON         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x000))
#define QEISTAT        (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x004))
#define QEICONF        (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x008))

/* QEI Position, Index, and Timer Registers */
#define QEIPOS         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x00C))
#define QEIMAXPSOS     (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x010))
#define CMPOS0         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x014))
#define CMPOS1         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x018))
#define CMPOS2         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x01C))
#define INXCNT         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x020))
#define INXCMP         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x024))
#define QEILOAD        (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x028))
#define QEITIME        (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x02C))
#define QEIVEL         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x030))
#define QEICAP         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x034))
#define VELCOMP        (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x038))
#define FILTER         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0x03C))

/* QEI Interrupt registers */
#define QEIIES         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0xFDC))
#define QEIIEC         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0xFD8))
#define QEIINTSTAT     (*(volatile unsigned long *)(QEI_BASE_ADDR + 0xFE0))
#define QEIIE          (*(volatile unsigned long *)(QEI_BASE_ADDR + 0xFE4))
#define QEICLR         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0xFE8))
#define QEISET         (*(volatile unsigned long *)(QEI_BASE_ADDR + 0xFEC))


/* CAN Controllers and Acceptance Filter */

/* CAN Acceptance Filter */
#define CAN_AF_BASE_ADDR 0x4003C000
#define AFMR           (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x00))      
#define SFF_sa         (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x04))      
#define SFF_GRP_sa     (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x08))
#define EFF_sa         (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x0C))
#define EFF_GRP_sa     (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x10))      
#define ENDofTable     (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x14))
#define LUTerrAd       (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x18))      
#define LUTerr         (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x1C))
#define FCANIE         (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x20))
#define FCANIC0        (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x24))
#define FCANIC1        (*(volatile unsigned long *)(CAN_AF_BASE_ADDR + 0x28))

/* CAN Centralized Registers */
#define CAN_BASE_ADDR  0x40040000      
#define CANTxSR        (*(volatile unsigned long *)(CAN_BASE_ADDR + 0x00))     
#define CANRxSR        (*(volatile unsigned long *)(CAN_BASE_ADDR + 0x04))     
#define CANMSR         (*(volatile unsigned long *)(CAN_BASE_ADDR + 0x08))

/* CAN1 Controller */
#define CAN1_BASE_ADDR 0x40044000
#define CAN1MOD        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x00))    
#define CAN1CMR        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x04))    
#define CAN1GSR        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x08))    
#define CAN1ICR        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x0C))    
#define CAN1IER        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x10))
#define CAN1BTR        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x14))    
#define CAN1EWL        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x18))    
#define CAN1SR         (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x1C))    
#define CAN1RFS        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x20))    
#define CAN1RID        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x24))
#define CAN1RDA        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x28))    
#define CAN1RDB        (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x2C))   
#define CAN1TFI1       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x30))    
#define CAN1TID1       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x34))    
#define CAN1TDA1       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x38))
#define CAN1TDB1       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x3C))    
#define CAN1TFI2       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x40))    
#define CAN1TID2       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x44))    
#define CAN1TDA2       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x48))    
#define CAN1TDB2       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x4C))
#define CAN1TFI3       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x50))    
#define CAN1TID3       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x54))    
#define CAN1TDA3       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x58))    
#define CAN1TDB3       (*(volatile unsigned long *)(CAN1_BASE_ADDR + 0x5C))

/* CAN2 Controller */
#define CAN2_BASE_ADDR 0x40048000
#define CAN2MOD        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x00))    
#define CAN2CMR        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x04))    
#define CAN2GSR        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x08))    
#define CAN2ICR        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x0C))    
#define CAN2IER        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x10))
#define CAN2BTR        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x14))    
#define CAN2EWL        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x18))    
#define CAN2SR         (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x1C))    
#define CAN2RFS        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x20))    
#define CAN2RID        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x24))
#define CAN2RDA        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x28))    
#define CAN2RDB        (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x2C))   
#define CAN2TFI1       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x30))    
#define CAN2TID1       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x34))    
#define CAN2TDA1       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x38))
#define CAN2TDB1       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x3C))    
#define CAN2TFI2       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x40))    
#define CAN2TID2       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x44))    
#define CAN2TDA2       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x48))    
#define CAN2TDB2       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x4C))
#define CAN2TFI3       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x50))    
#define CAN2TID3       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x54))    
#define CAN2TDA3       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x58))    
#define CAN2TDB3       (*(volatile unsigned long *)(CAN2_BASE_ADDR + 0x5C))


/* General Purpose DMA Controller (GPDMA) */
#define DMA_BASE_ADDR     0x50004000
#define DMACIntStat       (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x000))
#define DMACIntTCStat     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x004))
#define DMACIntTCClear    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x008))
#define DMACIntErrStat    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x00C))
#define DMACIntErrClr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x010))
#define DMACRawIntTCStat  (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x014))
#define DMACRawIntErrStat (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x018))
#define DMACEnbldChns     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x01C))
#define DMACSoftBReq      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x020))
#define DMACSoftSReq      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x024))
#define DMACSoftLBReq     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x028))
#define DMACSoftLSReq     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x02C))
#define DMACConfig        (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x030))
#define DMACSync          (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x034))

/* DMA Channel 0 Registers */
#define DMACC0SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x100))
#define DMACC0DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x104))
#define DMACC0LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x108))
#define DMACC0Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x10C))
#define DMACC0Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x110))

/* DMA Channel 1 Registers */
#define DMACC1SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x120))
#define DMACC1DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x124))
#define DMACC1LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x128))
#define DMACC1Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x12C))
#define DMACC1Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x130))

/* DMA Channel 2 Registers */
#define DMACC2SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x140))
#define DMACC2DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x144))
#define DMACC2LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x148))
#define DMACC2Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x14C))
#define DMACC2Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x150))

/* DMA Channel 3 Registers */
#define DMACC3SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x160))
#define DMACC3DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x164))
#define DMACC3LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x168))
#define DMACC3Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x16C))
#define DMACC3Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x170))

/* DMA Channel 4 Registers */
#define DMACC4SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x180))
#define DMACC4DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x184))
#define DMACC4LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x188))
#define DMACC4Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x18C))
#define DMACC4Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x190))

/* DMA Channel 5 Registers */
#define DMACC5SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1A0))
#define DMACC5DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1A4))
#define DMACC5LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1A8))
#define DMACC5Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1AC))
#define DMACC5Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1B0))

/* DMA Channel 6 Registers */
#define DMACC6SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1C0))
#define DMACC6DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1C4))
#define DMACC6LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1C8))
#define DMACC6Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1CC))
#define DMACC6Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1D0))

/* DMA Channel 7 Registers */
#define DMACC7SrcAddr     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1E0))
#define DMACC7DestAddr    (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1E4))
#define DMACC7LLI         (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1E8))
#define DMACC7Control     (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1EC))
#define DMACC7Config      (*(volatile unsigned long *)(DMA_BASE_ADDR + 0x1F0))


/* USB Controller */
#define USB_BASE_ADDR     0x5000C000

#define USBIntSt          (*(volatile unsigned long *)(SCB_BASE_ADDR + 0x1C0))


/* USB Device Controller */

/* USB Device Clock Control Registers */
#define USBClkCtrl        (*(volatile unsigned long *)(USB_BASE_ADDR + 0xFF4))
#define USBClkSt          (*(volatile unsigned long *)(USB_BASE_ADDR + 0xFF8))

/* USB Device Interrupt Registers */
#define USBDevIntSt       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x200))
#define USBDevIntEn       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x204))
#define USBDevIntClr      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x208))
#define USBDevIntSet      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x20C))
#define USBDevIntPri      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x22C))

/* USB Device Endpoint Interrupt Registers */
#define USBEpIntSt        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x230))
#define USBEpIntEn        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x234))
#define USBEpIntClr       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x238))
#define USBEpIntSet       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x23C))
#define USBEpIntPri       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x240))

/* USB Device Endpoint Realization Registers */
#define USBReEp           (*(volatile unsigned long *)(USB_BASE_ADDR + 0x244))
#define USBEpInd          (*(volatile unsigned long *)(USB_BASE_ADDR + 0x248))
#define USBMaxPSize       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x24C))

/* USB Device SIE Command Reagisters */
#define USBCmdCode        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x210))
#define USBCmdData        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x214))

/* USB Device Data Transfer Registers */
#define USBRxData         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x218))
#define USBTxData         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x21C))
#define USBRxPLen         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x220))
#define USBTxPLen         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x224))
#define USBCtrl           (*(volatile unsigned long *)(USB_BASE_ADDR + 0x228))

/* USB Device DMA Registers */
#define USBDMARSt         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x250))
#define USBDMARClr        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x254))
#define USBDMARSet        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x258))
#define USBUDCAH          (*(volatile unsigned long *)(USB_BASE_ADDR + 0x280))
#define USBEpDMASt        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x284))
#define USBEpDMAEn        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x288))
#define USBEpDMADis       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x28C))
#define USBDMAIntSt       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x290))
#define USBDMAIntEn       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x294))
#define USBEoTIntSt       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2A0))
#define USBEoTIntClr      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2A4))
#define USBEoTIntSet      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2A8))
#define USBNDDRIntSt      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2AC))
#define USBNDDRIntClr     (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2B0))
#define USBNDDRIntSet     (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2B4))
#define USBSysErrIntSt    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2B8))
#define USBSysErrIntClr   (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2BC))
#define USBSysErrIntSet   (*(volatile unsigned long *)(USB_BASE_ADDR + 0x2C0))


/* USB Host Controller */
#define HcRevision         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x000))
#define HcControl          (*(volatile unsigned long *)(USB_BASE_ADDR + 0x004))
#define HcCommandStatus    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x008))
#define HcInterruptStatus  (*(volatile unsigned long *)(USB_BASE_ADDR + 0x00C))
#define HcInterruptEnable  (*(volatile unsigned long *)(USB_BASE_ADDR + 0x010))
#define HcInterruptDisable (*(volatile unsigned long *)(USB_BASE_ADDR + 0x014))
#define HcHCCA             (*(volatile unsigned long *)(USB_BASE_ADDR + 0x018))
#define HcPeriodCurrentED  (*(volatile unsigned long *)(USB_BASE_ADDR + 0x01C))
#define HcControlHeadED    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x020))
#define HcControlCurrentED (*(volatile unsigned long *)(USB_BASE_ADDR + 0x024))
#define HcBulkHeadED       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x028))
#define HcBulkCurrentED    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x02C))
#define HcDoneHead         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x030))
#define HcFmInterval       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x034))
#define HcFmRemaining      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x038))
#define HcFmNumber         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x03C))
#define HcPeriodStart      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x040))
#define HcLSThreshold      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x044))
#define HcRhDescriptorA    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x048))
#define HcRhDescriptorB    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x04C))
#define HcRhStatus         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x050))
#define HcRhPortStatus1    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x054))
#define HcRhPortStatus2    (*(volatile unsigned long *)(USB_BASE_ADDR + 0x058))


/* USB OTG Controller */

/* USB OTG Registers */
#define OTGIntSt       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x100))
#define OTGIntEn       (*(volatile unsigned long *)(USB_BASE_ADDR + 0x104))
#define OTGIntSet      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x108))
#define OTGIntClr      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x10C))
#define OTGIntCtrl     (*(volatile unsigned long *)(USB_BASE_ADDR + 0x110))
#define OTGTmr         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x114))

/* USB OTG I2C Registers */
#define I2C_RX         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x300))
#define I2C_TX         (*(volatile unsigned long *)(USB_BASE_ADDR + 0x300))
#define I2C_STS        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x304))
#define I2C_CTL        (*(volatile unsigned long *)(USB_BASE_ADDR + 0x308))
#define I2C_CLKHI      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x30C))
#define I2C_CLKLO      (*(volatile unsigned long *)(USB_BASE_ADDR + 0x310))

/* USB OTG Clock Control Registers */
#define OTGClkCtrl     (*(volatile unsigned long *)(USB_BASE_ADDR + 0xFF4))
#define OTGClkSt       (*(volatile unsigned long *)(USB_BASE_ADDR + 0xFF8))


/* Ethernet MAC */
#define MAC_BASE_ADDR      0x50000000

/* MAC Registers */
#define ETH_MAC1       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x000))
#define ETH_MAC2       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x004))
#define ETH_IPGT       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x008))
#define ETH_IPGR       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x00C))
#define ETH_CLRT       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x010))
#define ETH_MAXF       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x014))
#define ETH_PHYSUPP    (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x018))
#define ETH_TEST       (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x01C))
#define ETH_MIICFG     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x020))
#define ETH_MIICMD     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x024))
#define ETH_MIIADR     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x028))
#define ETH_MIIWTD     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x02C))
#define ETH_MIIRDD     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x030))
#define ETH_MIIIND     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x034))
#define ETH_SA0        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x040))
#define ETH_SA1        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x044))
#define ETH_SA2        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x048))

/* MAC Control Registers */
#define ETH_COMMAND          (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x100))
#define ETH_STATUS           (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x104))
#define ETH_RXDESC           (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x108))
#define ETH_RXSTAT           (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x10C))
#define ETH_RXDESCRNO        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x110))
#define ETH_RXPRODIX         (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x114))
#define ETH_RXCONSIX         (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x118))
#define ETH_TXDESC           (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x11C))
#define ETH_TXSTAT           (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x120))
#define ETH_TXDESCRNO        (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x124))
#define ETH_TXPRODIX         (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x128))
#define ETH_TXCONSIX         (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x12C))
#define ETH_TSV0             (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x158))
#define ETH_TSV1             (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x15C))
#define ETH_RSV              (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x160))
#define ETH_FLOWCNTCOUNT     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x170))
#define ETH_FLOWCNTSTAT      (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x174))

/* MAX Rx Filter Registers */
#define ETH_RXFILTERCTL      (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x200))
#define ETH_RXFILTERWOLSTAT  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x204))
#define ETH_RXFILTERWOLCLR   (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x208))
#define ETH_HASHFILTERL      (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x210))
#define ETH_HASHFILTERH      (*(volatile unsigned long *)(MAC_BASE_ADDR + 0x214))

/* MAC Module Control Registers */
#define ETH_INSTSTAT   (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFE0))
#define ETH_INTENABLE  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFE4))
#define ETH_INTCLEAR   (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFE8))
#define ETH_INTSET     (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFEC))
#define ETH_POWERDOWN  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFF4))

#define MAC_Module_ID  (*(volatile unsigned long *)(MAC_BASE_ADDR + 0xFFC))

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

#define NVIC_IRQ_WDT         0u         // IRQ0,  exception number 16
#define NVIC_IRQ_TIMER0      1u         // IRQ1,  exception number 17
#define NVIC_IRQ_TIMER1      2u         // IRQ2,  exception number 18
#define NVIC_IRQ_TIMER2      3u         // IRQ3,  exception number 19
#define NVIC_IRQ_TIMER3      4u         // IRQ4,  exception number 20
#define NVIC_IRQ_UART0       5u         // IRQ5,  exception number 21
#define NVIC_IRQ_UART1       6u         // IRQ6,  exception number 22
#define NVIC_IRQ_UART2       7u         // IRQ7,  exception number 23
#define NVIC_IRQ_UART3       8u         // IRQ8,  exception number 24
#define NVIC_IRQ_PWM1        9u         // IRQ9,  exception number 25
#define NVIC_IRQ_I2C0        10u        // IRQ10, exception number 26
#define NVIC_IRQ_I2C1        11u        // IRQ11, exception number 27
#define NVIC_IRQ_I2C2        12u        // IRQ12, exception number 28
#define NVIC_IRQ_SPI         13u        // IRQ13, exception number 29
#define NVIC_IRQ_SSP0        14u        // IRQ14, exception number 30
#define NVIC_IRQ_SSP1        15u        // IRQ15, exception number 31
#define NVIC_IRQ_PLL0        16u        // IRQ16, exception number 32
#define NVIC_IRQ_RTC         17u        // IRQ17, exception number 33
#define NVIC_IRQ_EINT0       18u        // IRQ18, exception number 34
#define NVIC_IRQ_EINT1       19u        // IRQ19, exception number 35
#define NVIC_IRQ_EINT2       20u        // IRQ20, exception number 36
#define NVIC_IRQ_EINT3       21u        // IRQ21, exception number 37
#define NVIC_IRQ_ADC         22u        // IRQ22, exception number 38
#define NVIC_IRQ_BOD         23u        // IRQ23, exception number 39
#define NVIC_IRQ_USB         24u        // IRQ24, exception number 40
#define NVIC_IRQ_CAN         25u        // IRQ25, exception number 41
#define NVIC_IRQ_GPDMA       26u        // IRQ26, exception number 42
#define NVIC_IRQ_I2S         27u        // IRQ27, exception number 43
#define NVIC_IRQ_ETHERNET    28u        // IRQ28, exception number 44
#define NVIC_IRQ_RIT         29u        // IRQ29, exception number 45
#define NVIC_IRQ_MCPWM       30u        // IRQ30, exception number 46
#define NVIC_IRQ_QE          31u        // IRQ31, exception number 47
#define NVIC_IRQ_PLL1        32u        // IRQ32, exception number 48
#define NVIC_IRQ_USB_ACT     33u        // IRQ33, exception number 49
#define NVIC_IRQ_CAN_ACT     34u        // IRQ34, exception number 50

typedef enum IRQn
{
/******  Cortex-M3 Processor Exceptions Numbers ***************************************************/
  NonMaskableInt_IRQn           = -14,      /*!< 2 Non Maskable Interrupt                         */
  MemoryManagement_IRQn         = -12,      /*!< 4 Cortex-M3 Memory Management Interrupt          */
  BusFault_IRQn                 = -11,      /*!< 5 Cortex-M3 Bus Fault Interrupt                  */
  UsageFault_IRQn               = -10,      /*!< 6 Cortex-M3 Usage Fault Interrupt                */
  SVCall_IRQn                   = -5,       /*!< 11 Cortex-M3 SV Call Interrupt                   */
  DebugMonitor_IRQn             = -4,       /*!< 12 Cortex-M3 Debug Monitor Interrupt             */
  PendSV_IRQn                   = -2,       /*!< 14 Cortex-M3 Pend SV Interrupt                   */
  SysTick_IRQn                  = -1,       /*!< 15 Cortex-M3 System Tick Interrupt               */

/******  LPC17xx Specific Interrupt Numbers *******************************************************/
  WDT_IRQn                      = 0,        /*!< Watchdog Timer Interrupt                         */
  TIMER0_IRQn                   = 1,        /*!< Timer0 Interrupt                                 */
  TIMER1_IRQn                   = 2,        /*!< Timer1 Interrupt                                 */
  TIMER2_IRQn                   = 3,        /*!< Timer2 Interrupt                                 */
  TIMER3_IRQn                   = 4,        /*!< Timer3 Interrupt                                 */
  UART0_IRQn                    = 5,        /*!< UART0 Interrupt                                  */
  UART1_IRQn                    = 6,        /*!< UART1 Interrupt                                  */
  UART2_IRQn                    = 7,        /*!< UART2 Interrupt                                  */
  UART3_IRQn                    = 8,        /*!< UART3 Interrupt                                  */
  PWM1_IRQn                     = 9,        /*!< PWM1 Interrupt                                   */
  I2C0_IRQn                     = 10,       /*!< I2C0 Interrupt                                   */
  I2C1_IRQn                     = 11,       /*!< I2C1 Interrupt                                   */
  I2C2_IRQn                     = 12,       /*!< I2C2 Interrupt                                   */
  SPI_IRQn                      = 13,       /*!< SPI Interrupt                                    */
  SSP0_IRQn                     = 14,       /*!< SSP0 Interrupt                                   */
  SSP1_IRQn                     = 15,       /*!< SSP1 Interrupt                                   */
  PLL0_IRQn                     = 16,       /*!< PLL0 Lock (Main PLL) Interrupt                   */
  RTC_IRQn                      = 17,       /*!< Real Time Clock Interrupt                        */
  EINT0_IRQn                    = 18,       /*!< External Interrupt 0 Interrupt                   */
  EINT1_IRQn                    = 19,       /*!< External Interrupt 1 Interrupt                   */
  EINT2_IRQn                    = 20,       /*!< External Interrupt 2 Interrupt                   */
  EINT3_IRQn                    = 21,       /*!< External Interrupt 3 Interrupt                   */
  ADC_IRQn                      = 22,       /*!< A/D Converter Interrupt                          */
  BOD_IRQn                      = 23,       /*!< Brown-Out Detect Interrupt                       */
  USB_IRQn                      = 24,       /*!< USB Interrupt                                    */
  CAN_IRQn                      = 25,       /*!< CAN Interrupt                                    */
  DMA_IRQn                      = 26,       /*!< General Purpose DMA Interrupt                    */
  I2S_IRQn                      = 27,       /*!< I2S Interrupt                                    */
  ENET_IRQn                     = 28,       /*!< Ethernet Interrupt                               */
  RIT_IRQn                      = 29,       /*!< Repetitive Interrupt Timer Interrupt             */
  MCPWM_IRQn                    = 30,       /*!< Motor Control PWM Interrupt                      */
  QEI_IRQn                      = 31,       /*!< Quadrature Encoder Interface Interrupt           */
  PLL1_IRQn                     = 32,       /*!< PLL1 Lock (USB PLL) Interrupt                    */
} IRQn_Type;

#endif  // __LPC17xx_H
