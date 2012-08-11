#ifndef lpc210x_h
#define lpc210x_h
/*******************************************************************************
lpc210x.h - Register defs for Philips LPC210X: LPC2104, LPC2105 and LPC2106

           
THE SOFTWARE IS DELIVERED "AS IS" WITHOUT WARRANTY OR CONDITION OF ANY KIND, 
EITHER EXPRESS, IMPLIED OR STATUTORY. THIS INCLUDES WITHOUT LIMITATION ANY 
WARRANTY OR CONDITION WITH RESPECT TO MERCHANTABILITY OR FITNESS FOR ANY 
PARTICULAR PURPOSE, OR AGAINST THE INFRINGEMENTS OF INTELLECTUAL PROPERTY RIGHTS 
OF OTHERS.
           
This file may be freely used for commercial and non-commercial applications, 
including being redistributed with any tools.

If you find a problem with the file, please report it so that it can be fixed.

Created by Sten Larsson (sten_larsson at yahoo com)

Edited by Richard Barry.
*******************************************************************************/

#define REG8  (volatile unsigned char*)
#define REG16 (volatile unsigned short*)
#define REG32 (volatile unsigned int*)


/*##############################################################################
## MISC
##############################################################################*/

        /* Constants for data to put in IRQ/FIQ Exception Vectors */
#define VECTDATA_IRQ  0xE51FFFF0  /* LDR PC,[PC,#-0xFF0] */
#define VECTDATA_FIQ  /* __TODO */


/*##############################################################################
## VECTORED INTERRUPT CONTROLLER
##############################################################################*/

#define VICIRQStatus    (*(REG32 (0xFFFFF000)))
#define VICFIQStatus    (*(REG32 (0xFFFFF004)))
#define VICRawIntr      (*(REG32 (0xFFFFF008)))
#define VICIntSelect    (*(REG32 (0xFFFFF00C)))
#define VICIntEnable    (*(REG32 (0xFFFFF010)))
#define VICIntEnClear   (*(REG32 (0xFFFFF014)))
#define VICSoftInt      (*(REG32 (0xFFFFF018)))
#define VICSoftIntClear (*(REG32 (0xFFFFF01C)))
#define VICProtection   (*(REG32 (0xFFFFF020)))
#define VICVectAddr     (*(REG32 (0xFFFFF030)))
#define VICDefVectAddr  (*(REG32 (0xFFFFF034)))

#define VICVectAddr0    (*(REG32 (0xFFFFF100)))
#define VICVectAddr1    (*(REG32 (0xFFFFF104)))
#define VICVectAddr2    (*(REG32 (0xFFFFF108)))
#define VICVectAddr3    (*(REG32 (0xFFFFF10C)))
#define VICVectAddr4    (*(REG32 (0xFFFFF110)))
#define VICVectAddr5    (*(REG32 (0xFFFFF114)))
#define VICVectAddr6    (*(REG32 (0xFFFFF118)))
#define VICVectAddr7    (*(REG32 (0xFFFFF11C)))
#define VICVectAddr8    (*(REG32 (0xFFFFF120)))
#define VICVectAddr9    (*(REG32 (0xFFFFF124)))
#define VICVectAddr10   (*(REG32 (0xFFFFF128)))
#define VICVectAddr11   (*(REG32 (0xFFFFF12C)))
#define VICVectAddr12   (*(REG32 (0xFFFFF130)))
#define VICVectAddr13   (*(REG32 (0xFFFFF134)))
#define VICVectAddr14   (*(REG32 (0xFFFFF138)))
#define VICVectAddr15   (*(REG32 (0xFFFFF13C)))

#define VICVectCntl0    (*(REG32 (0xFFFFF200)))
#define VICVectCntl1    (*(REG32 (0xFFFFF204)))
#define VICVectCntl2    (*(REG32 (0xFFFFF208)))
#define VICVectCntl3    (*(REG32 (0xFFFFF20C)))
#define VICVectCntl4    (*(REG32 (0xFFFFF210)))
#define VICVectCntl5    (*(REG32 (0xFFFFF214)))
#define VICVectCntl6    (*(REG32 (0xFFFFF218)))
#define VICVectCntl7    (*(REG32 (0xFFFFF21C)))
#define VICVectCntl8    (*(REG32 (0xFFFFF220)))
#define VICVectCntl9    (*(REG32 (0xFFFFF224)))
#define VICVectCntl10   (*(REG32 (0xFFFFF228)))
#define VICVectCntl11   (*(REG32 (0xFFFFF22C)))
#define VICVectCntl12   (*(REG32 (0xFFFFF230)))
#define VICVectCntl13   (*(REG32 (0xFFFFF234)))
#define VICVectCntl14   (*(REG32 (0xFFFFF238)))
#define VICVectCntl15   (*(REG32 (0xFFFFF23C)))

#define VICITCR         (*(REG32 (0xFFFFF300)))
#define VICITIP1        (*(REG32 (0xFFFFF304)))
#define VICITIP2        (*(REG32 (0xFFFFF308)))
#define VICITOP1        (*(REG32 (0xFFFFF30C)))
#define VICITOP2        (*(REG32 (0xFFFFF310)))
#define VICPeriphID0    (*(REG32 (0xFFFFFFE0)))
#define VICPeriphID1    (*(REG32 (0xFFFFFFE4)))
#define VICPeriphID2    (*(REG32 (0xFFFFFFE8)))
#define VICPeriphID3    (*(REG32 (0xFFFFFFEC)))

#define VICIntEnClr     VICIntEnClear
#define VICSoftIntClr   VICSoftIntClear


/*##############################################################################
## PCB - Pin Connect Block
##############################################################################*/

#define PCB_PINSEL0     (*(REG32 (0xE002C000)))
#define PCB_PINSEL1     (*(REG32 (0xE002C004)))


/*##############################################################################
## GPIO - General Purpose I/O
##############################################################################*/

#define GPIO_IOPIN      (*(REG32 (0xE0028000))) /* ALTERNATE NAME GPIO = GPIO0 */
#define GPIO_IOSET      (*(REG32 (0xE0028004)))
#define GPIO_IODIR      (*(REG32 (0xE0028008)))
#define GPIO_IOCLR      (*(REG32 (0xE002800C)))

#define GPIO0_IOPIN     (*(REG32 (0xE0028000))) /* ALTERNATE NAME GPIO = GPIO0 */
#define GPIO0_IOSET     (*(REG32 (0xE0028004)))
#define GPIO0_IODIR     (*(REG32 (0xE0028008)))
#define GPIO0_IOCLR     (*(REG32 (0xE002800C)))


/*##############################################################################
## UART0 / UART1
##############################################################################*/

/* ---- UART 0 --------------------------------------------- */
#define UART0_RBR       (*(REG32 (0xE000C000)))
#define UART0_THR       (*(REG32 (0xE000C000)))
#define UART0_IER       (*(REG32 (0xE000C004)))
#define UART0_IIR       (*(REG32 (0xE000C008)))
#define UART0_FCR       (*(REG32 (0xE000C008)))
#define UART0_LCR       (*(REG32 (0xE000C00C)))
#define UART0_LSR       (*(REG32 (0xE000C014)))
#define UART0_SCR       (*(REG32 (0xE000C01C)))
#define UART0_DLL       (*(REG32 (0xE000C000)))
#define UART0_DLM       (*(REG32 (0xE000C004)))

/* ---- UART 1 --------------------------------------------- */
#define UART1_RBR       (*(REG32 (0xE0010000)))
#define UART1_THR       (*(REG32 (0xE0010000)))
#define UART1_IER       (*(REG32 (0xE0010004)))
#define UART1_IIR       (*(REG32 (0xE0010008)))
#define UART1_FCR       (*(REG32 (0xE0010008)))
#define UART1_LCR       (*(REG32 (0xE001000C)))
#define UART1_LSR       (*(REG32 (0xE0010014)))
#define UART1_SCR       (*(REG32 (0xE001001C)))
#define UART1_DLL       (*(REG32 (0xE0010000)))
#define UART1_DLM       (*(REG32 (0xE0010004)))
#define UART1_MCR       (*(REG32 (0xE0010010)))
#define UART1_MSR       (*(REG32 (0xE0010018)))


/*##############################################################################
## I2C
##############################################################################*/

#define I2C_I2CONSET    (*(REG32 (0xE001C000)))
#define I2C_I2STAT      (*(REG32 (0xE001C004)))
#define I2C_I2DAT       (*(REG32 (0xE001C008)))
#define I2C_I2ADR       (*(REG32 (0xE001C00C)))
#define I2C_I2SCLH      (*(REG32 (0xE001C010)))
#define I2C_I2SCLL      (*(REG32 (0xE001C014)))
#define I2C_I2CONCLR    (*(REG32 (0xE001C018)))


/*##############################################################################
## SPI - Serial Peripheral Interface
##############################################################################*/

#define SPI_SPCR        (*(REG32 (0xE0020000)))
#define SPI_SPSR        (*(REG32 (0xE0020004)))
#define SPI_SPDR        (*(REG32 (0xE0020008)))
#define SPI_SPCCR       (*(REG32 (0xE002000C)))
#define SPI_SPTCR       (*(REG32 (0xE0020010)))
#define SPI_SPTSR       (*(REG32 (0xE0020014)))
#define SPI_SPTOR       (*(REG32 (0xE0020018)))
#define SPI_SPINT       (*(REG32 (0xE002001C)))


/*##############################################################################
## Timer 0 and Timer 1
##############################################################################*/

/* ---- Timer 0 -------------------------------------------- */
#define T0_IR           (*(REG32 (0xE0004000)))
#define T0_TCR          (*(REG32 (0xE0004004)))
#define T0_TC           (*(REG32 (0xE0004008)))
#define T0_PR           (*(REG32 (0xE000400C)))
#define T0_PC           (*(REG32 (0xE0004010)))
#define T0_MCR          (*(REG32 (0xE0004014)))
#define T0_MR0          (*(REG32 (0xE0004018)))
#define T0_MR1          (*(REG32 (0xE000401C)))
#define T0_MR2          (*(REG32 (0xE0004020)))
#define T0_MR3          (*(REG32 (0xE0004024)))
#define T0_CCR          (*(REG32 (0xE0004028)))
#define T0_CR0          (*(REG32 (0xE000402C)))
#define T0_CR1          (*(REG32 (0xE0004030)))
#define T0_CR2          (*(REG32 (0xE0004034)))
#define T0_CR3          (*(REG32 (0xE0004038)))
#define T0_EMR          (*(REG32 (0xE000403C)))

/* ---- Timer 1 -------------------------------------------- */
#define T1_IR           (*(REG32 (0xE0008000)))
#define T1_TCR          (*(REG32 (0xE0008004)))
#define T1_TC           (*(REG32 (0xE0008008)))
#define T1_PR           (*(REG32 (0xE000800C)))
#define T1_PC           (*(REG32 (0xE0008010)))
#define T1_MCR          (*(REG32 (0xE0008014)))
#define T1_MR0          (*(REG32 (0xE0008018)))
#define T1_MR1          (*(REG32 (0xE000801C)))
#define T1_MR2          (*(REG32 (0xE0008020)))
#define T1_MR3          (*(REG32 (0xE0008024)))
#define T1_CCR          (*(REG32 (0xE0008028)))
#define T1_CR0          (*(REG32 (0xE000802C)))
#define T1_CR1          (*(REG32 (0xE0008030)))
#define T1_CR2          (*(REG32 (0xE0008034)))
#define T1_CR3          (*(REG32 (0xE0008038)))
#define T1_EMR          (*(REG32 (0xE000803C)))


/*##############################################################################
## PWM
##############################################################################*/

#define PWM_IR          (*(REG32 (0xE0014000)))
#define PWM_TCR         (*(REG32 (0xE0014004)))
#define PWM_TC          (*(REG32 (0xE0014008)))
#define PWM_PR          (*(REG32 (0xE001400C)))
#define PWM_PC          (*(REG32 (0xE0014010)))
#define PWM_MCR         (*(REG32 (0xE0014014)))
#define PWM_MR0         (*(REG32 (0xE0014018)))
#define PWM_MR1         (*(REG32 (0xE001401C)))
#define PWM_MR2         (*(REG32 (0xE0014020)))
#define PWM_MR3         (*(REG32 (0xE0014024)))
#define PWM_MR4         (*(REG32 (0xE0014040)))
#define PWM_MR5         (*(REG32 (0xE0014044)))
#define PWM_MR6         (*(REG32 (0xE0014048)))
#define PWM_EMR         (*(REG32 (0xE001403C)))
#define PWM_PCR         (*(REG32 (0xE001404C)))
#define PWM_LER         (*(REG32 (0xE0014050)))
#define PWM_CCR         (*(REG32 (0xE0014028)))
#define PWM_CR0         (*(REG32 (0xE001402C)))
#define PWM_CR1         (*(REG32 (0xE0014030)))
#define PWM_CR2         (*(REG32 (0xE0014034)))
#define PWM_CR3         (*(REG32 (0xE0014038)))

/*##############################################################################
## RTC
##############################################################################*/

/* ---- RTC: Miscellaneous Register Group ------------------ */
#define RTC_ILR         (*(REG32 (0xE0024000)))
#define RTC_CTC         (*(REG32 (0xE0024004)))
#define RTC_CCR         (*(REG32 (0xE0024008)))  
#define RTC_CIIR        (*(REG32 (0xE002400C)))
#define RTC_AMR         (*(REG32 (0xE0024010)))
#define RTC_CTIME0      (*(REG32 (0xE0024014)))
#define RTC_CTIME1      (*(REG32 (0xE0024018)))
#define RTC_CTIME2      (*(REG32 (0xE002401C)))

/* ---- RTC: Timer Control Group --------------------------- */
#define RTC_SEC         (*(REG32 (0xE0024020)))
#define RTC_MIN         (*(REG32 (0xE0024024)))
#define RTC_HOUR        (*(REG32 (0xE0024028)))
#define RTC_DOM         (*(REG32 (0xE002402C)))
#define RTC_DOW         (*(REG32 (0xE0024030)))
#define RTC_DOY         (*(REG32 (0xE0024034)))
#define RTC_MONTH       (*(REG32 (0xE0024038)))
#define RTC_YEAR        (*(REG32 (0xE002403C)))

/* ---- RTC: Alarm Control Group --------------------------- */
#define RTC_ALSEC       (*(REG32 (0xE0024060)))
#define RTC_ALMIN       (*(REG32 (0xE0024064)))
#define RTC_ALHOUR      (*(REG32 (0xE0024068)))
#define RTC_ALDOM       (*(REG32 (0xE002406C)))
#define RTC_ALDOW       (*(REG32 (0xE0024070)))
#define RTC_ALDOY       (*(REG32 (0xE0024074)))
#define RTC_ALMON       (*(REG32 (0xE0024078)))
#define RTC_ALYEAR      (*(REG32 (0xE002407C)))

/* ---- RTC: Reference Clock Divider Group ----------------- */
#define RTC_PREINT      (*(REG32 (0xE0024080)))
#define RTC_PREFRAC     (*(REG32 (0xE0024084)))


/*##############################################################################
## WD - Watchdog
##############################################################################*/

#define WD_WDMOD        (*(REG32 (0xE0000000)))
#define WD_WDTC         (*(REG32 (0xE0000004)))
#define WD_WDFEED       (*(REG32 (0xE0000008)))
#define WD_WDTV         (*(REG32 (0xE000000C)))


/*##############################################################################
## System Control Block
##############################################################################*/

#define SCB_EXTINT      (*(REG32 (0xE01FC140)))
#define SCB_EXTWAKE     (*(REG32 (0xE01FC144)))
#define SCB_MEMMAP      (*(REG32 (0xE01FC040)))
#define SCB_PLLCON      (*(REG32 (0xE01FC080)))
#define SCB_PLLCFG      (*(REG32 (0xE01FC084)))
#define SCB_PLLSTAT     (*(REG32 (0xE01FC088)))
#define SCB_PLLFEED     (*(REG32 (0xE01FC08C)))
#define SCB_PCON        (*(REG32 (0xE01FC0C0)))
#define SCB_PCONP       (*(REG32 (0xE01FC0C4)))
#define SCB_VPBDIV      (*(REG32 (0xE01FC100)))

/*##############################################################################
## Memory Accelerator Module (MAM)
##############################################################################*/

#define MAM_TIM			(*(REG32 (0xE01FC004)))
#define MAM_CR			(*(REG32 (0xE01FC000)))

#endif /* lpc210x_h */

