//*----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*-----------------------------------------------------------------------------
//* File Name           : tc.h
//* Object              : Timer Counter Header File
//*
//* 1.0 01/04/00 JCZ    : Creation
//* 1.0 01/09/00 JPP    : modification TC_BEEVT, TC_BEEVT_SET_OUTPUT,
//*                       TC_BEEVT_CLEAR_OUTPUT, TC_BEEVT_TOGGLE_OUTPUT
//*-----------------------------------------------------------------------------

#ifndef tc_h
#define tc_h

//#include    "periph/stdc/std_c.h"
//#include    "periph/pio/lib_pio.h"

/*-------------------------------------------*/
/* Timer User Interface Structure Definition */
/*-------------------------------------------*/

typedef struct
{
    at91_reg        TC_CCR ;        /* Control Register */
    at91_reg        TC_CMR ;        /* Mode Register */
    at91_reg        Reserved0 ;
    at91_reg        Reserved1 ;
    at91_reg        TC_CV ;         /* Counter value */
    at91_reg        TC_RA ;         /* Register A */
    at91_reg        TC_RB ;         /* Register B */
    at91_reg        TC_RC ;         /* Register C */
    at91_reg        TC_SR ;         /* Status Register */
    at91_reg        TC_IER ;        /* Interrupt Enable Register */
    at91_reg        TC_IDR ;        /* Interrupt Disable Register */
    at91_reg        TC_IMR ;        /* Interrupt Mask Register */
    at91_reg        Reserved2 ;
    at91_reg        Reserved3 ;
    at91_reg        Reserved4 ;
    at91_reg        Reserved5 ;
} StructTC ;

#define NB_TC_CHANNEL       3

typedef struct
{
    StructTC        TC[NB_TC_CHANNEL] ;
    at91_reg        TC_BCR ;        /* Block Control Register */
    at91_reg        TC_BMR ;        /* Block Mode Register  */
} StructTCBlock ;

/*--------------------------------------------------------*/
/* TC_CCR: Timer Counter Control Register Bits Definition */
/*--------------------------------------------------------*/
#define TC_CLKEN            0x1
#define TC_CLKDIS           0x2
#define TC_SWTRG            0x4

/*---------------------------------------------------------------*/
/* TC_CMR: Timer Counter Channel Mode Register Bits Definition   */
/*---------------------------------------------------------------*/

/*-----------------*/
/* Clock Selection */
/*-----------------*/
#define TC_CLKS                  0x7
#define TC_CLKS_MCK2             0x0
#define TC_CLKS_MCK8             0x1
#define TC_CLKS_MCK32            0x2
#define TC_CLKS_MCK128           0x3
#define TC_CLKS_MCK1024          0x4

#define TC_CLKS_SLCK             0x4

#define TC_CLKS_XC0              0x5
#define TC_CLKS_XC1              0x6
#define TC_CLKS_XC2              0x7


/*-----------------*/
/* Clock Inversion */
/*-----------------*/
#define TC_CLKI             0x8

/*------------------------*/
/* Burst Signal Selection */
/*------------------------*/
#define TC_BURST            0x30
#define TC_BURST_NONE       0x0
#define TC_BUSRT_XC0        0x10
#define TC_BURST_XC1        0x20
#define TC_BURST_XC2        0x30

/*------------------------------------------------------*/
/* Capture Mode : Counter Clock Stopped with RB Loading */
/*------------------------------------------------------*/
#define TC_LDBSTOP          0x40

/*-------------------------------------------------------*/
/* Waveform Mode : Counter Clock Stopped with RC Compare */
/*-------------------------------------------------------*/
#define TC_CPCSTOP          0x40

/*-------------------------------------------------------*/
/* Capture Mode : Counter Clock Disabled with RB Loading */
/*--------------------------------------------------------*/
#define TC_LDBDIS           0x80

/*--------------------------------------------------------*/
/* Waveform Mode : Counter Clock Disabled with RC Compare */
/*--------------------------------------------------------*/
#define TC_CPCDIS           0x80

/*------------------------------------------------*/
/* Capture Mode : External Trigger Edge Selection */
/*------------------------------------------------*/
#define TC_ETRGEDG                  0x300
#define TC_ETRGEDG_EDGE_NONE        0x0
#define TC_ETRGEDG_RISING_EDGE      0x100
#define TC_ETRGEDG_FALLING_EDGE     0x200
#define TC_ETRGEDG_BOTH_EDGE        0x300

/*-----------------------------------------------*/
/* Waveform Mode : External Event Edge Selection */
/*-----------------------------------------------*/
#define TC_EEVTEDG                  0x300
#define TC_EEVTEDG_EDGE_NONE        0x0
#define TC_EEVTEDG_RISING_EDGE      0x100
#define TC_EEVTEDG_FALLING_EDGE     0x200
#define TC_EEVTEDG_BOTH_EDGE        0x300

/*--------------------------------------------------------*/
/* Capture Mode : TIOA or TIOB External Trigger Selection */
/*--------------------------------------------------------*/
#define TC_ABETRG                   0x400
#define TC_ABETRG_TIOB              0x0
#define TC_ABETRG_TIOA              0x400

/*------------------------------------------*/
/* Waveform Mode : External Event Selection */
/*------------------------------------------*/
#define TC_EEVT                     0xC00
#define TC_EEVT_TIOB                0x0
#define TC_EEVT_XC0                 0x400
#define TC_EEVT_XC1                 0x800
#define TC_EEVT_XC2                 0xC00

/*--------------------------------------------------*/
/* Waveform Mode : Enable Trigger on External Event */
/*--------------------------------------------------*/
#define TC_ENETRG                   0x1000

/*----------------------------------*/
/* RC Compare Enable Trigger Enable */
/*----------------------------------*/
#define TC_CPCTRG                   0x4000

/*----------------*/
/* Mode Selection */
/*----------------*/
#define TC_WAVE                     0x8000
#define TC_CAPT                     0x0

/*-------------------------------------*/
/* Capture Mode : RA Loading Selection */
/*-------------------------------------*/
#define TC_LDRA                     0x30000
#define TC_LDRA_EDGE_NONE           0x0
#define TC_LDRA_RISING_EDGE         0x10000
#define TC_LDRA_FALLING_EDGE        0x20000
#define TC_LDRA_BOTH_EDGE           0x30000

/*-------------------------------------------*/
/* Waveform Mode : RA Compare Effect on TIOA */
/*-------------------------------------------*/
#define TC_ACPA                     0x30000
#define TC_ACPA_OUTPUT_NONE         0x0
#define TC_ACPA_SET_OUTPUT          0x10000
#define TC_ACPA_CLEAR_OUTPUT        0x20000
#define TC_ACPA_TOGGLE_OUTPUT       0x30000

/*-------------------------------------*/
/* Capture Mode : RB Loading Selection */
/*-------------------------------------*/
#define TC_LDRB                     0xC0000
#define TC_LDRB_EDGE_NONE           0x0
#define TC_LDRB_RISING_EDGE         0x40000
#define TC_LDRB_FALLING_EDGE        0x80000
#define TC_LDRB_BOTH_EDGE           0xC0000

/*-------------------------------------------*/
/* Waveform Mode : RC Compare Effect on TIOA */
/*-------------------------------------------*/
#define TC_ACPC                     0xC0000
#define TC_ACPC_OUTPUT_NONE         0x0
#define TC_ACPC_SET_OUTPUT          0x40000
#define TC_ACPC_CLEAR_OUTPUT        0x80000
#define TC_ACPC_TOGGLE_OUTPUT       0xC0000

/*-----------------------------------------------*/
/* Waveform Mode : External Event Effect on TIOA */
/*-----------------------------------------------*/
#define TC_AEEVT                    0x300000
#define TC_AEEVT_OUTPUT_NONE        0x0
#define TC_AEEVT_SET_OUTPUT         0x100000
#define TC_AEEVT_CLEAR_OUTPUT       0x200000
#define TC_AEEVT_TOGGLE_OUTPUT      0x300000

/*-------------------------------------------------*/
/* Waveform Mode : Software Trigger Effect on TIOA */
/*-------------------------------------------------*/
#define TC_ASWTRG                   0xC00000
#define TC_ASWTRG_OUTPUT_NONE       0x0
#define TC_ASWTRG_SET_OUTPUT        0x400000
#define TC_ASWTRG_CLEAR_OUTPUT      0x800000
#define TC_ASWTRG_TOGGLE_OUTPUT     0xC00000

/*-------------------------------------------*/
/* Waveform Mode : RB Compare Effect on TIOB */
/*-------------------------------------------*/
#define TC_BCPB                     0x1000000
#define TC_BCPB_OUTPUT_NONE         0x0
#define TC_BCPB_SET_OUTPUT          0x1000000
#define TC_BCPB_CLEAR_OUTPUT        0x2000000
#define TC_BCPB_TOGGLE_OUTPUT       0x3000000

/*-------------------------------------------*/
/* Waveform Mode : RC Compare Effect on TIOB */
/*-------------------------------------------*/
#define TC_BCPC                     0xC000000
#define TC_BCPC_OUTPUT_NONE         0x0
#define TC_BCPC_SET_OUTPUT          0x4000000
#define TC_BCPC_CLEAR_OUTPUT        0x8000000
#define TC_BCPC_TOGGLE_OUTPUT       0xC000000

/*-----------------------------------------------*/
/* Waveform Mode : External Event Effect on TIOB */
/*-----------------------------------------------*/
#define TC_BEEVT                    0x30000000      //* bit 29-28
#define TC_BEEVT_OUTPUT_NONE        0x0
#define TC_BEEVT_SET_OUTPUT         0x10000000      //* bit 29-28  01
#define TC_BEEVT_CLEAR_OUTPUT       0x20000000      //* bit 29-28  10
#define TC_BEEVT_TOGGLE_OUTPUT      0x30000000      //* bit 29-28  11

/*- -----------------------------------------------*/
/* Waveform Mode : Software Trigger Effect on TIOB */
/*-------------------------------------------------*/
#define TC_BSWTRG                   0xC0000000
#define TC_BSWTRG_OUTPUT_NONE       0x0
#define TC_BSWTRG_SET_OUTPUT        0x40000000
#define TC_BSWTRG_CLEAR_OUTPUT      0x80000000
#define TC_BSWTRG_TOGGLE_OUTPUT     0xC0000000

/*------------------------------------------------------*/
/* TC_SR: Timer Counter Status Register Bits Definition */
/*------------------------------------------------------*/
#define TC_COVFS            0x1         /* Counter Overflow Status */
#define TC_LOVRS            0x2         /* Load Overrun Status */
#define TC_CPAS             0x4         /* RA Compare Status */
#define TC_CPBS             0x8         /* RB Compare Status */
#define TC_CPCS             0x10        /* RC Compare Status */
#define TC_LDRAS            0x20        /* RA Loading Status */
#define TC_LDRBS            0x40        /* RB Loading Status */
#define TC_ETRGS            0x80        /* External Trigger Status */
#define TC_CLKSTA           0x10000     /* Clock Status */
#define TC_MTIOA            0x20000     /* TIOA Mirror */
#define TC_MTIOB            0x40000     /* TIOB Status */

/*--------------------------------------------------------------*/
/* TC_BCR: Timer Counter Block Control Register Bits Definition */
/*--------------------------------------------------------------*/
#define TC_SYNC             0x1         /* Synchronisation Trigger */

/*------------------------------------------------------------*/
/*  TC_BMR: Timer Counter Block Mode Register Bits Definition */
/*------------------------------------------------------------*/
#define TC_TC0XC0S          0x3        /* External Clock Signal 0 Selection */
#define TC_TCLK0XC0         0x0
#define TC_NONEXC0          0x1
#define TC_TIOA1XC0         0x2
#define TC_TIOA2XC0         0x3

#define TC_TC1XC1S          0xC        /* External Clock Signal 1 Selection */
#define TC_TCLK1XC1         0x0
#define TC_NONEXC1          0x4
#define TC_TIOA0XC1         0x8
#define TC_TIOA2XC1         0xC

#define TC_TC2XC2S          0x30       /* External Clock Signal 2 Selection */
#define TC_TCLK2XC2         0x0
#define TC_NONEXC2          0x10
#define TC_TIOA0XC2         0x20
#define TC_TIOA1XC2         0x30

#endif /* tc_h */

