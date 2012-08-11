//*---------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*---------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*-----------------------------------------------------------------------------
//* File Name           : pio.h
//* Object              : Parallel I/O Definition File
//* Translator          : ARM Software Development Toolkit V2.11a
//*
//* 1.0 20/10/97 JCZ    : Creation
//* 2.0 21/10/98 JCZ    : Clean up
//*---------------------------------------------------------------------------

#ifndef pio_h
#define pio_h

/*---------------------------------------------*/
/* Parallel I/O Interface Structure Definition */
/*---------------------------------------------*/

typedef struct
{
    at91_reg        PIO_PER ;           /* PIO Enable Register */
    at91_reg        PIO_PDR ;           /* PIO Disable Register */
    at91_reg        PIO_PSR ;           /* PIO Status Register */
    at91_reg        Reserved0 ;
    at91_reg        PIO_OER ;           /* Output Enable Register */
    at91_reg        PIO_ODR ;           /* Output Disable Register */
    at91_reg        PIO_OSR ;           /* Output Status Register */
    at91_reg        Reserved1 ;
    at91_reg        PIO_IFER ;          /* Input Filter Enable Register */
    at91_reg        PIO_IFDR ;          /* Input Filter Disable Register */
    at91_reg        PIO_IFSR ;          /* Input Filter Status Register */
    at91_reg        Reserved2 ;
    at91_reg        PIO_SODR ;          /* Set Output Data Register */
    at91_reg        PIO_CODR ;          /* Clear Output Data Register */
    at91_reg        PIO_ODSR ;          /* Output Data Status Register */
    at91_reg        PIO_PDSR ;          /* Pin Data Status Register */
    at91_reg        PIO_IER ;           /* Interrupt Enable Register */
    at91_reg        PIO_IDR ;           /* Interrupt Disable Register */
    at91_reg        PIO_IMR ;           /* Interrupt Mask Register */
    at91_reg        PIO_ISR ;           /* Interrupt Status Register */
} StructPIO ;

/*-----------------------------*/
/* PIO Handler type definition */
/*-----------------------------*/

//typedef void (*TypePIOHandler) ( StructPIO *pio_pt, u_int pio_mask ) ;

/*--------------------------------*/
/* Device Dependancies Definition */
/*--------------------------------*/

/* Number of PIO Controller */
#define NB_PIO_CTRL     1
/* Base Address */
#define PIO_BASE        ((StructPIO *) 0xFFFF0000 )
/* Number of PIO Lines */
#define NB_PIO          32

/* Parallel I/O Bits Definition */
#define P0              (1<<0)
#define P1              (1<<1)
#define P2              (1<<2)
#define P3              (1<<3)
#define P4              (1<<4)
#define P5              (1<<5)
#define P6              (1<<6)
#define P7              (1<<7)
#define P8              (1<<8)
#define P9              (1<<9)
#define P10             (1<<10)
#define P11             (1<<11)
#define P12             (1<<12)
#define P13             (1<<13)
#define P14             (1<<14)
#define P15             (1<<15)
#define P16             (1<<16)
#define P17             (1<<17)
#define P18             (1<<18)
#define P19             (1<<19)
#define P20             (1<<20)
#define P21             (1<<21)
#define P22             (1<<22)
#define P23             (1<<23)
#define P24             (1<<24)
#define P25             (1<<25)
#define P26             (1<<26)
#define P27             (1<<27)
#define P28             (1<<28)
#define P29             (1<<29)
#define P30             (1<<30)
#define P31             (1<<31)

/* PIO Multiplexing Definition */

/* There is only one PIO Controller */
#define PIO_CTRL        0

#define PIO_TC0         PIO_CTRL
#define TCLK0           P0
#define TIOA0           P1
#define TIOB0           P2
#define PIN_TC0         (TIOA0|TIOB0|TCLK0)

#define PIO_TC1         PIO_CTRL
#define TCLK1           P3
#define TIOA1           P4
#define TIOB1           P5
#define PIN_TC1         (TIOA1|TIOB1|TCLK1)

#define PIO_TC2         PIO_CTRL
#define TCLK2           P6
#define TIOA2           P7
#define TIOB2           P8
#define PIN_TC2         (TIOA2|TIOB2|TCLK2)

#define PIO_EXT_IRQ     PIO_CTRL
#define PIN_IRQ0        P9
#define PIN_IRQ1        P10
#define PIN_IRQ2        P11
#define PIN_FIQ         P12

#define PIO_USART0      PIO_CTRL
#define SCK0            P13
#define TXD0            P14
#define RXD0            P15
#define PIN_USART0      (SCK0|TXD0|RXD0)

#define PIO_USART1      PIO_CTRL
#define SCK1            P20
#define TXD1            P21
#define RXD1            P22
#define PIN_USART1      (SCK1|TXD1|RXD1)

#define MCKO            P25
#define CS2             P26
#define CS3             P27
#define CS4             P31
#define CS5             P30
#define CS6             P29
#define CS7             P28

#endif /* pio_h */
