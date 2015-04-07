/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name     : ostm_iodefine.h
* Version       : 0.01
* Device(s)     : Aragon
* Tool-Chain    : DS-5 Ver 5.8
*                 ARM Complier 
*               : 
* H/W Platform  : Aragon CPU Board
* Description   : Aragon Sample Program vecotr.s
*******************************************************************************/
/*******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 27.07.2012 0.01		éQçléëóøÅFsec11_OSTM_120601.pdf
*******************************************************************************/
#ifndef __OSTM_IODEFINE_H__
#define __OSTM_IODEFINE_H__

#include "typedefine.h"

struct st_ostm_n {                              /* struct OSTM  */
       _UDWORD OSTMnCMP;                        /* OSTMnCMP     */
       _UDWORD OSTMnCNT;                        /* OSTMnCNT     */
       _UBYTE wk0[8];                           /*              */
       union {                                  /* OSTMnTE      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OSTMnTE:1;           /*   OSTMnTE    */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } OSTMnTE;                         /*              */
       _UBYTE wk1[3];                           /*              */
       union {                                  /* OSTMnTS      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OSTMnTS:1;           /*   OSTMnTS    */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } OSTMnTS;                         /*              */
       _UBYTE wk2[3];                           /*              */
       union {                                  /* OSTMnTT      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OSTMnTT:1;           /*   OSTMnTT    */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } OSTMnTT;                         /*              */
       _UBYTE wk3[7];                           /*              */
       union {                                  /* OSTMnCTL     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OSTMnMD0:1;          /*   OSTMnMD0   */
                    _UBYTE OSTMnMD1:1;          /*   OSTMnMD1   */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } OSTMnCTL;                        /*              */
};                                              /*              */

#define	OSTM0		(*(volatile struct st_ostm_n *)0xFCFEC000)   /* OSTM0 Address */
#define	OSTM1		(*(volatile struct st_ostm_n *)0xFCFEC400)   /* OSTM1 Address */


#endif /* __OSTM_IODEFINE_H__ */

/* End of File */
