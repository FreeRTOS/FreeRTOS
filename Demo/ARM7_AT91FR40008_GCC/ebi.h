//*-----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*-----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*-----------------------------------------------------------------------------
//* File Name           : ebi.h
//* Object              : External Bus Interface Definition File
//* Translator          : ARM Software Development Toolkit V2.11a
//*
//* 1.0 03/11/97 JCZ    : Creation
//* 2.0 21/10/98 JCZ    : Clean up
//*-----------------------------------------------------------------------------

#ifndef ebi_h
#define ebi_h

/*----------------------------------------*/
/* Memory Controller Interface Definition */
/*----------------------------------------*/

typedef struct
{
    at91_reg        EBI_CSR[8] ;        /* Chip Select Register */
    at91_reg        EBI_RCR ;           /* Remap Control Register */
    at91_reg        EBI_MCR ;           /* Memory Control Register */
} StructEBI ;

/*-----------------------*/
/* Chip Select Registers */
/*-----------------------*/

/* Data Bus Width */
#define DataBus16               (1<<0)
#define DataBus8                (2<<0)
#define DBW                     (3<<0)

/* Number of Wait States */
#define B_NWS                   2
#define WaitState1              (0<<B_NWS)
#define WaitState2              (1<<B_NWS)
#define WaitState3              (2<<B_NWS)
#define WaitState4              (3<<B_NWS)
#define WaitState5              (4<<B_NWS)
#define WaitState6              (5<<B_NWS)
#define WaitState7              (6<<B_NWS)
#define WaitState8              (7<<B_NWS)
#define NWS                     (7<<B_NWS)

/* Wait State Enable */
#define WaitStateDisable        (0<<5)
#define WaitStateEnable         (1<<5)
#define WSE                     (1<<5)

/* Page size */
#define PageSize1M              (0<<7)
#define PageSize4M              (1<<7)
#define PageSize16M             (2<<7)
#define PageSize64M             (3<<7)
#define PAGES                   (3<<7)

/* Number of Data Float Output Time Clock Cycle */
#define B_TDF                   9
#define tDF_0cycle              (0<<B_TDF)
#define tDF_1cycle              (1<<B_TDF)
#define tDF_2cycle              (2<<B_TDF)
#define tDF_3cycle              (3<<B_TDF)
#define tDF_4cycle              (4<<B_TDF)
#define tDF_5cycle              (5<<B_TDF)
#define tDF_6cycle              (6<<B_TDF)
#define tDF_7cycle              (7<<B_TDF)
#define TDF                     (7<<B_TDF)

/* Byte Access Type */
#define ByteWriteAccessType (0<<12)
#define ByteSelectAccessType    (1<<12)
#define BAT                     1<<12)

/* Chip Select Enable */
#define CSEnable                (1<<13)
#define CSDisable               (0<<13)
#define CSE                     (1<<13)

#define BA                      ((u_int)(0xFFF)<<20)

/*-------------------------*/
/* Memory Control Register */
/*-------------------------*/

/* Address Line Enable */
#define ALE                     (7<<0)
#define BankSize16M             (0<<0)
#define BankSize8M              (4<<0)
#define BankSize4M              (5<<0)
#define BankSize2M              (6<<0)
#define BankSize1M              (7<<0)

/* Data Read Protocol */
#define StandardReadProtocol    (0<<4)
#define EarlyReadProtocol       (1<<4)
#define DRP                     (1<<4)

/*------------------------*/
/* Remap Control Register */
/*------------------------*/

#define RCB                     (1<<0)

/*--------------------------------*/
/* Device Dependancies Definition */
/*--------------------------------*/

#ifdef AT91M40400
/* External Bus Interface User Interface BAse Address */
#define EBI_BASE            ((StructEBI *) 0xFFE00000)
#endif

#endif /* ebi_h */
