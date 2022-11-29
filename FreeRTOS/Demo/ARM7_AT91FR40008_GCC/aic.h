//*----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*----------------------------------------------------------------------------
//* File Name           : aic.h
//* Object              : Advanced Interrupt Controller Definition File.
//*
//* 1.0 01/04/00 JCZ    : Creation
//*----------------------------------------------------------------------------

#ifndef aic_h
#define aic_h

//#include    "periph/stdc/std_c.h"

/*-----------------------------------------*/
/* AIC User Interface Structure Definition */
/*-----------------------------------------*/

typedef struct
{
    at91_reg        AIC_SMR[32] ;       /* Source Mode Register */
    at91_reg        AIC_SVR[32] ;       /* Source Vector Register */
    at91_reg        AIC_IVR ;           /* IRQ Vector Register */
    at91_reg        AIC_FVR ;           /* FIQ Vector Register */
    at91_reg        AIC_ISR ;           /* Interrupt Status Register */
    at91_reg        AIC_IPR ;           /* Interrupt Pending Register */
    at91_reg        AIC_IMR ;           /* Interrupt Mask Register */
    at91_reg        AIC_CISR ;          /* Core Interrupt Status Register */
    at91_reg        reserved0 ;
    at91_reg        reserved1 ;
    at91_reg        AIC_IECR ;          /* Interrupt Enable Command Register */
    at91_reg        AIC_IDCR ;          /* Interrupt Disable Command Register */
    at91_reg        AIC_ICCR ;          /* Interrupt Clear Command Register */
    at91_reg        AIC_ISCR ;          /* Interrupt Set Command Register */
    at91_reg        AIC_EOICR ;         /* End of Interrupt Command Register */
    at91_reg        AIC_SPU ;           /* Spurious Vector Register */
} StructAIC ;

/*--------------------------------------------*/
/* AIC_SMR[]: Interrupt Source Mode Registers */
/*--------------------------------------------*/

#define AIC_PRIOR                       0x07    /* Priority */

#define AIC_SRCTYPE                     0x60    /* Source Type Definition */

/* Internal Interrupts */
#define AIC_SRCTYPE_INT_LEVEL_SENSITIVE 0x00    /* Level Sensitive */
#define AIC_SRCTYPE_INT_EDGE_TRIGGERED  0x20    /* Edge Triggered */

/* External Interrupts */
#define AIC_SRCTYPE_EXT_LOW_LEVEL       0x00    /* Low Level */
#define AIC_SRCTYPE_EXT_NEGATIVE_EDGE   0x20    /* Negative Edge */
#define AIC_SRCTYPE_EXT_HIGH_LEVEL      0x40    /* High Level */
#define AIC_SRCTYPE_EXT_POSITIVE_EDGE   0x60    /* Positive Edge */

/*------------------------------------*/
/* AIC_ISR: Interrupt Status Register */
/*------------------------------------*/

#define AIC_IRQID                       0x1F    /* Current source interrupt */

/*------------------------------------------*/
/* AIC_CISR: Interrupt Core Status Register */
/*------------------------------------------*/

#define AIC_NFIQ                        0x01    /* Core FIQ Status */
#define AIC_NIRQ                        0x02    /* Core IRQ Status */

/*-------------------------------*/
/* Advanced Interrupt Controller */
/*-------------------------------*/
#define AIC_BASE                        ((StructAIC *)0xFFFFF000)

#endif /* aic_h */
