/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_macrodriver.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements general head file.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef MODULEID_H
#define MODULEID_H
/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "iodefine.h"
#include "r_cg_interrupthandlers.h"
#include "r_cg_mpc.h"


/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#ifndef __TYPEDEF__
#define DI()    asm("cpsid i") /* Disable IRQ interrupt (Set CPSR.I bit to 1)  */
#define EI()    asm("cpsie i") /* Enable IRQ interrupt (Clear CPSR.I bit to 0) */
#define nop()   asm("nop")

/* Status list definition */
#define MD_STATUSBASE        (0x00U)
#define MD_OK                (MD_STATUSBASE + 0x00U) /* register setting OK */
#define MD_SPT               (MD_STATUSBASE + 0x01U) /* IIC stop */
#define MD_NACK              (MD_STATUSBASE + 0x02U) /* IIC no ACK */
#define MD_BUSY1             (MD_STATUSBASE + 0x03U) /* busy 1 */
#define MD_BUSY2             (MD_STATUSBASE + 0x04U) /* busy 2 */

/* Error list definition */
#define MD_ERRORBASE         (0x80U)
#define MD_ERROR             (MD_ERRORBASE + 0x00U)  /* error */
#define MD_ARGERROR          (MD_ERRORBASE + 0x01U)  /* error argument input error */
#define MD_ERROR1            (MD_ERRORBASE + 0x02U)  /* error 1 */
#define MD_ERROR2            (MD_ERRORBASE + 0x03U)  /* error 2 */
#define MD_ERROR3            (MD_ERRORBASE + 0x04U)  /* error 3 */
#define MD_ERROR4            (MD_ERRORBASE + 0x05U)  /* error 4 */
#define MD_ERROR5            (MD_ERRORBASE + 0x06U)  /* error 5 */

/* MSTP macro definition */
#define MSTP_CMTW1      SYSTEM.MSTPCRA.BIT.MSTPCRA0
#define MSTP_CMTW0      SYSTEM.MSTPCRA.BIT.MSTPCRA1
#define MSTP_CMT2       SYSTEM.MSTPCRA.BIT.MSTPCRA2
#define MSTP_CMT1       SYSTEM.MSTPCRA.BIT.MSTPCRA3
#define MSTP_CMT0       SYSTEM.MSTPCRA.BIT.MSTPCRA4
#define MSTP_PPG1       SYSTEM.MSTPCRA.BIT.MSTPCRA5
#define MSTP_PPG0       SYSTEM.MSTPCRA.BIT.MSTPCRA6
#define MSTP_TPU1       SYSTEM.MSTPCRA.BIT.MSTPCRA7
#define MSTP_TPU0       SYSTEM.MSTPCRA.BIT.MSTPCRA8
#define MSTP_GPTA       SYSTEM.MSTPCRA.BIT.MSTPCRA9
#define MSTP_MTU3       SYSTEM.MSTPCRA.BIT.MSTPCRA11

#define MSTP_RSCAN      SYSTEM.MSTPCRB.BIT.MSTPCRB1
#define MSTP_RIIC1      SYSTEM.MSTPCRB.BIT.MSTPCRB2
#define MSTP_RIIC0      SYSTEM.MSTPCRB.BIT.MSTPCRB3
#define MSTP_SCIFA4     SYSTEM.MSTPCRB.BIT.MSTPCRB5
#define MSTP_SCIFA3     SYSTEM.MSTPCRB.BIT.MSTPCRB6
#define MSTP_SCIFA2     SYSTEM.MSTPCRB.BIT.MSTPCRB7
#define MSTP_SCIFA1     SYSTEM.MSTPCRB.BIT.MSTPCRB8
#define MSTP_SCIFA0     SYSTEM.MSTPCRB.BIT.MSTPCRB9
#define MSTP_RSPI3      SYSTEM.MSTPCRB.BIT.MSTPCRB10
#define MSTP_RSPI2      SYSTEM.MSTPCRB.BIT.MSTPCRB11
#define MSTP_RSPI1      SYSTEM.MSTPCRB.BIT.MSTPCRB12
#define MSTP_RSPI0      SYSTEM.MSTPCRB.BIT.MSTPCRB13
#define MSTP_ETHERSW    SYSTEM.MSTPCRB.BIT.MSTPCRB14
#define MSTP_ECATC      SYSTEM.MSTPCRB.BIT.MSTPCRB15
#define MSTP_EMDIO      SYSTEM.MSTPCRB.BIT.MSTPCRB16
#define MSTP_ERMII      SYSTEM.MSTPCRB.BIT.MSTPCRB17
#define MSTP_HWRTOS     SYSTEM.MSTPCRB.BIT.MSTPCRB18
#define MSTP_CLKOUT25M  SYSTEM.MSTPCRB.BIT.MSTPCRB19

#define MSTP_USB        SYSTEM.MSTPCRC.BIT.MSTPCRC1
#define MSTP_DSMIF      SYSTEM.MSTPCRC.BIT.MSTPCRC2
#define MSTP_TEMPS      SYSTEM.MSTPCRC.BIT.MSTPCRC3
#define MSTP_S12ADC1    SYSTEM.MSTPCRC.BIT.MSTPCRC4
#define MSTP_S12ADC0    SYSTEM.MSTPCRC.BIT.MSTPCRC5
#define MSTP_ELC        SYSTEM.MSTPCRC.BIT.MSTPCRC6
#define MSTP_BSC        SYSTEM.MSTPCRC.BIT.MSTPCRC7
#define MSTP_CKIO       SYSTEM.MSTPCRC.BIT.MSTPCRC8
#define MSTP_SPIBSC     SYSTEM.MSTPCRC.BIT.MSTPCRC9
#define MSTP_DOC        SYSTEM.MSTPCRC.BIT.MSTPCRC10
#define MSTP_CRC        SYSTEM.MSTPCRC.BIT.MSTPCRC11
#define MSTP_CLMA2      SYSTEM.MSTPCRC.BIT.MSTPCRC12
#define MSTP_CLMA1      SYSTEM.MSTPCRC.BIT.MSTPCRC13
#define MSTP_CLMA0      SYSTEM.MSTPCRC.BIT.MSTPCRC14

#define MSTP_SSI        SYSTEM.MSTPCRD.BIT.MSTPCRD2

#define MSTP_DMAC1      SYSTEM.MSTPCRE.BIT.MSTPCRE4
#define MSTP_DMAC0      SYSTEM.MSTPCRE.BIT.MSTPCRE5

#define MSTP_CORESIGHT  SYSTEM.MSTPCRF.BIT.MSTPCRF0

#define	__MSTP( x )		MSTP ## x
#define	 _MSTP( x )		__MSTP( x )
#define	  MSTP( x )		_MSTP( _ ## x )
#endif

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
#ifndef __TYPEDEF__
typedef signed char         int8_t;
typedef unsigned char       uint8_t;
typedef signed short        int16_t;
typedef unsigned short      uint16_t;
typedef signed long         int32_t;
typedef unsigned long       uint32_t;
typedef unsigned short      MD_STATUS;
#define __TYPEDEF__
#endif

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/

#endif
