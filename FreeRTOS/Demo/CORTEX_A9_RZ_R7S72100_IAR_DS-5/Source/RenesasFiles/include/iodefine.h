/*******************************************************************************
*   DISCLAIMER
*
*   This software is supplied by Renesas Electronics Corporation and is only
*   intended for use with Renesas products. No other uses are authorized.
*
*   This software is owned by Renesas Electronics Corporation and is protected under
*   all applicable laws, including copyright laws.
*
*   THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES
*   REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY,
*   INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
*   PARTICULAR PURPOSE AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY
*   DISCLAIMED.
*
*   TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
*   ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
*   FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES
*   FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS
*   AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
*
*   Renesas reserves the right, without notice, to make changes to this
*   software and to discontinue the availability of this software.
*   By using this software, you agree to the additional terms and
*   conditions found by accessing the following link:
*   http://www.renesas.com/disclaimer
********************************************************************************
* Copyright (C) 2010(2011) Renesas Electronics Corporation. All rights reserved.
**************************** Technical reference data **************************
*   System Name : SH7269 Sample Program
*   File Name   : iodefine.h
*   Abstract    : SH7269 IO define file
*   Version     : 0.11.00
*   Device      : SH7269

*   Tool-Chain  : High-performance Embedded Workshop (Ver.4.07.00).
*               : C/C++ compiler package for the SuperH RISC engine family
*               :                              (Ver.9.03 Release02).
*   OS          : None
*   H/W Platform: R0K57269(CPU board)
*   Description :
********************************************************************************
*   History     : Sep.02,2010 Ver.0.01.00 Preliminary version issued
*               : Oct.06.2010 Ver.0.02.00 VDC4.GR1_AB1 modified
*               : Oct.07.2010 Ver.0.03.00 VDC4.GR1_AB1 type definition modified
*               : Oct.19.2010 Ver.0.04.00 MMC.CE_DMA_MODE added
*                                         MMC.CE_BOOT deleted
*               : Nov.09.2010 Ver.0.05.00 VDC4.GR3_CLUT_INT.GR3_LINE added
*               : Jan.28.2011 Ver.0.06.00 DVDEC.ADDCR->ADCCR1 changed
*                                         DVDEC.ADCCR1.AGCMODEXA->AGCMODE changed
*                                         DVDEC.INSCR deleted
*                                         DVDEC.AGCCR2.AGCMAXGAIN deleted
*                                         DVDEC.AGCCR2.VIDEOGAIN deleted
*                                         DVDEC.AGCCR2.VIDEOGAIN deleted
*                                         DVDEC.CROMASR2.NCOMODE deleted
*                                         DVDEC.DCPSR3~5 deleted
*                                         DVDEC.YCSCR1 deleted
*                                         DVDEC.YCSCR3~7,9,11 added
*                                         DVDEC.YCSCR8.HFIL_TAP_SEL added
*                                         DVDEC.YCSCR12.DET2_MIX_C added
*                                         DVDEC.YCSCR12.DET2_MIX_Y added
*                                         DVDEC.DCPCR9.CLP_FIL_SEL deleted
*                                         DVDEC.DCPCR10~13 deleted
*                                         DVDEC.PGA_UPDATE added
*                                         DVDEC.PGACR added
*                                         DVDEC.ADCCR2 added
*                                         module SPIBSC added
*               : Feb.23.2011 Ver.0.07.00 CPG.STBCR7.MSTP75 added
*               : Feb.28.2011 Ver.0.08.00 PORT.PBCR5 modified
*                                         PORT.PBCR4 modified
*                                         PORT.PBCR3 modified
*                                         JCU.JCSTS deleted
*                                         VDC4.INP_SEL_CNT.INP_VSP_SYNC_SEL deleted
*                                         VDC4.SCL0_DS4.RES_DS_H_INIPHASE deleted
*                                         VDC4.GR1_AB1.GR1_ARC_ON deleted
*                                         VDC4.GR1_AB1.GR1_ARC_DISP_ON deleted
*                                         VDC4.GR1_AB4 deleted
*                                         VDC4.GR1_AB5 deleted
*                                         VDC4.GR1_AB6 deleted
*                                         VDC4.GR1_AB7.GR1_ARC_DEF deleted
*                                         VDC4.GR1_MON deleted
*                                         VDC4.ADJ_MTX_MODE.MTX_MD->ADJ_MTX_MD changed
*                                         VDC4.OUT_SET.OUT_PIXEL_INV_ON deleted
*                                         VDC4.OUT_SET.OUT_SUM_MOVE deleted
*               : Mar.02.2011 Ver.0.09.00 JCU.JCQTBL0 modified
*                                         JCU.JCQTBL1 modified
*                                         JCU.JCQTBL2 modified
*                                         JCU.JCQTBL3 modified
*                                         JCU.JCHTBD0 modified
*                                         JCU.JCHTBA0 modified
*                                         JCU.JCHTBD1 modified
*                                         JCU.JCHTBA1 modified
*               : Apr.04.2011 Ver.0.10.00 CPG.SWRSTCR2.JCUSRST added
*               : May.09.2011 Ver.0.11.00 BSC.ACSWR deleted
*                                         BSC.ACKEYR deleted
*                                         USB.USBACSWR1 deleted
*******************************************************************************/
#ifndef _IODEFINE_H_
#define _IODEFINE_H_

#include "typedefine.h"

/* new iodefine ADC */

struct st_adc
{                                                          /*  ADC             */
    unsigned short DRA;                                    /*  DRA             */
    unsigned short DRB;                                    /*  DRB             */
    unsigned short DRC;                                    /*  DRC             */
    unsigned short DRD;                                    /*  DRD             */
    unsigned short DRE;                                    /*  DRE             */
    unsigned short DRF;                                    /*  DRF             */
    unsigned short DRG;                                    /*  DRG             */
    unsigned short DRH;                                    /*  DRH             */
    unsigned char  dummy32[16];                            /*                  */
    unsigned short MPHA;                                   /*  MPHA            */
    unsigned short MPLA;                                   /*  MPLA            */
    unsigned short MPHB;                                   /*  MPHB            */
    unsigned short MPLB;                                   /*  MPLB            */
    unsigned short MPHC;                                   /*  MPHC            */
    unsigned short MPLC;                                   /*  MPLC            */
    unsigned short MPHD;                                   /*  MPHD            */
    unsigned short MPLD;                                   /*  MPLD            */
    unsigned short MPHE;                                   /*  MPHE            */
    unsigned short MPLE;                                   /*  MPLE            */
    unsigned short MPHF;                                   /*  MPHF            */
    unsigned short MPLF;                                   /*  MPLF            */
    unsigned short MPHG;                                   /*  MPHG            */
    unsigned short MPLG;                                   /*  MPLG            */
    unsigned short MPHH;                                   /*  MPHH            */
    unsigned short MPLH;                                   /*  MPLH            */
    unsigned char  dummy33[32];                            /*                  */
    unsigned short SR;                                     /*  SR              */
    unsigned short MPER;                                   /*  MPER            */
    unsigned short MPSR;                                   /*  MPSR            */
};

#define ADCDRA ADC.DRA
#define ADCDRB ADC.DRB
#define ADCDRC ADC.DRC
#define ADCDRD ADC.DRD
#define ADCDRE ADC.DRE
#define ADCDRF ADC.DRF
#define ADCDRG ADC.DRG
#define ADCDRH ADC.DRH
#define ADCMPHA ADC.MPHA
#define ADCMPLA ADC.MPLA
#define ADCMPHB ADC.MPHB
#define ADCMPLB ADC.MPLB
#define ADCMPHC ADC.MPHC
#define ADCMPLC ADC.MPLC
#define ADCMPHD ADC.MPHD
#define ADCMPLD ADC.MPLD
#define ADCMPHE ADC.MPHE
#define ADCMPLE ADC.MPLE
#define ADCMPHF ADC.MPHF
#define ADCMPLF ADC.MPLF
#define ADCMPHG ADC.MPHG
#define ADCMPLG ADC.MPLG
#define ADCMPHH ADC.MPHH
#define ADCMPLH ADC.MPLH
#define ADCSR ADC.SR
#define ADCMPER ADC.MPER
#define ADCMPSR ADC.MPSR

#define ADC     (*(volatile struct st_adc     *)0xE8005800) /* ADC */

/* new iodefine ADC */


	#if	0
struct st_cpg {                                 /* struct CPG   */
       union {                                  /* FRQCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD CKOEN2:1;            /*   CKOEN2     */
                    _UWORD CKOEN:2;             /*   CKOEN      */
                    _UWORD :2;                  /*              */
                    _UWORD IFC:2;               /*   IFC        */
                    _UWORD :2;                  /*              */
                    _UWORD BFC:2;               /*   BFC        */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } FRQCR;                           /*              */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* STBCR1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE STBY:1;              /*   STBY       */
                    _UBYTE DEEP:1;              /*   DEEP       */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } STBCR1;                          /*              */
       _UBYTE wk1[3];                           /*              */
       union {                                  /* STBCR2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP10:1;            /*   MSTP10     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP8:1;             /*   MSTP8      */
                    _UBYTE MSTP7:1;             /*   MSTP7      */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } STBCR2;                          /*              */
       _UBYTE wk2[999];                         /*              */
       union {                                  /* SYSCR1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE RAME3:1;             /*   RAME3      */
                    _UBYTE RAME2:1;             /*   RAME2      */
                    _UBYTE RAME1:1;             /*   RAME1      */
                    _UBYTE RAME0:1;             /*   RAME0      */
                    } BIT;                      /*              */
             } SYSCR1;                          /*              */
       _UBYTE wk3[3];                           /*              */
       union {                                  /* SYSCR2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE RAMWE3:1;            /*   RAMWE3     */
                    _UBYTE RAMWE2:1;            /*   RAMWE2     */
                    _UBYTE RAMWE1:1;            /*   RAMWE1     */
                    _UBYTE RAMWE0:1;            /*   RAMWE0     */
                    } BIT;                      /*              */
             } SYSCR2;                          /*              */
       _UBYTE wk4[3];                           /*              */
       union {                                  /* STBCR3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE HIZ:1;               /*   HIZ        */
                    _UBYTE MSTP36:1;            /*   MSTP36     */
                    _UBYTE MSTP35:1;            /*   MSTP35     */
                    _UBYTE :1;                  /*   MSTP34     */
                    _UBYTE :1;                  /*   MSTP33     */
                    _UBYTE MSTP32:1;            /*   MSTP32     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP30:1;            /*   MSTP30     */
                    } BIT;                      /*              */
             } STBCR3;                          /*              */
       _UBYTE wk5[3];                           /*              */
       union {                                  /* STBCR4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP47:1;            /*   MSTP47     */
                    _UBYTE MSTP46:1;            /*   MSTP46     */
                    _UBYTE MSTP45:1;            /*   MSTP45     */
                    _UBYTE MSTP44:1;            /*   MSTP44     */
                    _UBYTE MSTP43:1;            /*   MSTP43     */
                    _UBYTE MSTP42:1;            /*   MSTP42     */
                    _UBYTE MSTP41:1;            /*   MSTP41     */
                    _UBYTE MSTP40:1;            /*   MSTP40     */
                    } BIT;                      /*              */
             } STBCR4;                          /*              */
       _UBYTE wk6[3];                           /*              */
       union {                                  /* STBCR5       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP57:1;            /*   MSTP57     */
                    _UBYTE MSTP56:1;            /*   MSTP56     */
                    _UBYTE MSTP55:1;            /*   MSTP55     */
                    _UBYTE MSTP54:1;            /*   MSTP54     */
                    _UBYTE MSTP53:1;            /*   MSTP53     */
                    _UBYTE MSTP52:1;            /*   MSTP52     */
                    _UBYTE MSTP51:1;            /*   MSTP51     */
                    _UBYTE MSTP50:1;            /*   MSTP50     */
                    } BIT;                      /*              */
             } STBCR5;                          /*              */
       _UBYTE wk7[3];                           /*              */
       union {                                  /* STBCR6       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP67:1;            /*   MSTP67     */
                    _UBYTE MSTP66:1;            /*   MSTP66     */
                    _UBYTE MSTP65:1;            /*   MSTP65     */
                    _UBYTE MSTP64:1;            /*   MSTP64     */
                    _UBYTE MSTP63:1;            /*   MSTP63     */
                    _UBYTE MSTP62:1;            /*   MSTP62     */
                    _UBYTE MSTP61:1;            /*   MSTP61     */
                    _UBYTE MSTP60:1;            /*   MSTP60     */
                    } BIT;                      /*              */
             } STBCR6;                          /*              */
       _UBYTE wk8[3];                           /*              */
       union {                                  /* STBCR7       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP77:1;            /*   MSTP77     */
                    _UBYTE MSTP76:1;            /*   MSTP76     */
                    _UBYTE MSTP75:1;            /*   MSTP75     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP73:1;            /*   MSTP73     */
                    _UBYTE MSTP72:1;            /*   MSTP72     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP70:1;            /*   MSTP70     */
                    } BIT;                      /*              */
             } STBCR7;                          /*              */
       _UBYTE wk9[3];                           /*              */
       union {                                  /* STBCR8       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP87:1;            /*   MSTP87     */
                    _UBYTE MSTP86:1;            /*   MSTP86     */
                    _UBYTE MSTP85:1;            /*   MSTP85     */
                    _UBYTE MSTP84:1;            /*   MSTP84     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP82:1;            /*   MSTP82     */
                    _UBYTE MSTP81:1;            /*   MSTP81     */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } STBCR8;                          /*              */
       _UBYTE wk10[3];                          /*              */
       union {                                  /* SYSCR3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE VRAME5:1;            /*   VRAME5     */
                    _UBYTE VRAME4:1;            /*   VRAME4     */
                    _UBYTE VRAME3:1;            /*   VRAME3     */
                    _UBYTE VRAME2:1;            /*   VRAME2     */
                    _UBYTE VRAME1:1;            /*   VRAME1     */
                    _UBYTE VRAME0:1;            /*   VRAME0     */
                    } BIT;                      /*              */
             } SYSCR3;                          /*              */
       _UBYTE wk11[3];                          /*              */
       union {                                  /* SYSCR4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE VRAMWE5:1;           /*   VRAMWE5    */
                    _UBYTE VRAMWE4:1;           /*   VRAMWE4    */
                    _UBYTE VRAMWE3:1;           /*   VRAMWE3    */
                    _UBYTE VRAMWE2:1;           /*   VRAMWE2    */
                    _UBYTE VRAMWE1:1;           /*   VRAMWE1    */
                    _UBYTE VRAMWE0:1;           /*   VRAMWE0    */
                    } BIT;                      /*              */
             } SYSCR4;                          /*              */
       _UBYTE wk12[3];                          /*              */
       union {                                  /* SYSCR5       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE RRAMWE3:1;           /*   RRAMWE3    */
                    _UBYTE RRAMWE2:1;           /*   RRAMWE2    */
                    _UBYTE RRAMWE1:1;           /*   RRAMWE1    */
                    _UBYTE RRAMWE0:1;           /*   RRAMWE0    */
                    } BIT;                      /*              */
             } SYSCR5;                          /*              */
       _UBYTE wk13[7];                          /*              */
       union {                                  /* SWRSTCR1     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE AXTALE:1;            /*   AXTALE     */
                    _UBYTE SSIF5SRST:1;         /*   SSIF5SRST  */
                    _UBYTE SSIF4SRST:1;         /*   SSIF4SRST  */
                    _UBYTE IEBSRST:1;           /*   IEBSRST    */
                    _UBYTE SSIF3SRST:1;         /*   SSIF3SRST  */
                    _UBYTE SSIF2SRST:1;         /*   SSIF2SRST  */
                    _UBYTE SSIF1SRST:1;         /*   SSIF1SRST  */
                    _UBYTE SSIF0SRST:1;         /*   SSIF0SRST  */
                    } BIT;                      /*              */
             } SWRSTCR1;                        /*              */
       _UBYTE wk14[3];                          /*              */
       union {                                  /* SWRSTCR2     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :3;                  /*              */
                    _UBYTE JCUSRST:1;           /*   JCUSRST    */
                    _UBYTE RGPVGSRST:1;         /*   SSIF3SRST  */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } SWRSTCR2;                        /*              */
       _UBYTE wk15[11];                         /*              */
       union {                                  /* STBCR9       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP97:1;            /*   MSTP97     */
                    _UBYTE MSTP96:1;            /*   MSTP96     */
                    _UBYTE MSTP95:1;            /*   MSTP95     */
                    _UBYTE MSTP94:1;            /*   MSTP94     */
                    _UBYTE MSTP93:1;            /*   MSTP93     */
                    _UBYTE MSTP92:1;            /*   MSTP92     */
                    _UBYTE MSTP91:1;            /*   MSTP91     */
                    _UBYTE MSTP90:1;            /*   MSTP90     */
                    } BIT;                      /*              */
             } STBCR9;                          /*              */
       _UBYTE wk16[3];                          /*              */
       union {                                  /* STBCR10      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP107:1;           /*   MSTP107    */
                    _UBYTE MSTP106:1;           /*   MSTP106    */
                    _UBYTE MSTP105:1;           /*   MSTP105    */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP103:1;           /*   MSTP103    */
                    _UBYTE MSTP102:1;           /*   MSTP102    */
                    _UBYTE MSTP101:1;           /*   MSTP101    */
                    _UBYTE MSTP100:1;           /*   MSTP100    */
                    } BIT;                      /*              */
             } STBCR10;                         /*              */
       _UBYTE wk17[25531];                      /*              */
       union {                                  /* RRAMKP       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE RRAMKP3:1;           /*   RRAMKP3    */
                    _UBYTE RRAMKP2:1;           /*   RRAMKP2    */
                    _UBYTE RRAMKP1:1;           /*   RRAMKP1    */
                    _UBYTE RRAMKP0:1;           /*   RRAMKP0    */
                    } BIT;                      /*              */
             } RRAMKP;                          /*              */
       _UBYTE wk18[1];                          /*              */
       union {                                  /* DSCTR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE EBUSKEEPE:1;         /*   EBUSKEEPE  */
                    _UBYTE RAMBOOT:1;           /*   RAMBOOT    */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } DSCTR;                           /*              */
       _UBYTE wk19[1];                          /*              */
       union {                                  /* DSSSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD PJ23:1;              /*   PJ23       */
                    _UWORD PJ22:1;              /*   PJ22       */
                    _UWORD PJ21:1;              /*   PJ21       */
                    _UWORD PJ20:1;              /*   PJ20       */
                    _UWORD PG3:1;               /*   PG3        */
                    _UWORD PG2:1;               /*   PG2        */
                    _UWORD NMI:1;               /*   NMI        */
                    _UWORD :1;                  /*              */
                    _UWORD RTCAR:1;             /*   RTCAR      */
                    _UWORD PF19:1;              /*   PF19       */
                    _UWORD PF18:1;              /*   PF18       */
                    _UWORD PF17:1;              /*   PF17       */
                    _UWORD PF16:1;              /*   PF16       */
                    _UWORD PC7:1;               /*   PC7        */
                    _UWORD PC5:1;               /*   PC5        */
                    } BIT;                      /*              */
             } DSSSR;                           /*              */
       union {                                  /* DSESR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD PJ23E:1;             /*   PJ23E      */
                    _UWORD PJ22E:1;             /*   PJ22E      */
                    _UWORD PJ21E:1;             /*   PJ21E      */
                    _UWORD PJ20E:1;             /*   PJ20E      */
                    _UWORD PG3E:1;              /*   PG3E       */
                    _UWORD PG2E:1;              /*   PG2E       */
                    _UWORD NMIE:1;              /*   NMIE       */
                    _UWORD :1;                  /*              */
                    _UWORD :1;                  /*              */
                    _UWORD PF19E:1;             /*   PF19E      */
                    _UWORD PF18E:1;             /*   PF18E      */
                    _UWORD PF17E:1;             /*   PF17E      */
                    _UWORD PF16E:1;             /*   PF16E      */
                    _UWORD PC7E:1;              /*   PC7E       */
                    _UWORD PC5E:1;              /*   PC5E       */
                    } BIT;                      /*              */
             } DSESR;                           /*              */
       union {                                  /* DSFR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD IOKEEP:1;            /*   IOKEEP     */
                    _UWORD PJ23F:1;             /*   PJ23F      */
                    _UWORD PJ22F:1;             /*   PJ22F      */
                    _UWORD PJ21F:1;             /*   PJ21F      */
                    _UWORD PJ20F:1;             /*   PJ20F      */
                    _UWORD PG3F:1;              /*   PG3F       */
                    _UWORD PG2F:1;              /*   PG2F       */
                    _UWORD NMIF:1;              /*   NMIF       */
                    _UWORD :1;                  /*              */
                    _UWORD RTCARF:1;            /*   RTCARF     */
                    _UWORD PF19F:1;             /*   PF19F      */
                    _UWORD PF18F:1;             /*   PF18F      */
                    _UWORD PF17F:1;             /*   PF17F      */
                    _UWORD PF16F:1;             /*   PF16F      */
                    _UWORD PC7F:1;              /*   PC7F       */
                    _UWORD PC5F:1;              /*   PC5F       */
                    } BIT;                      /*              */
             } DSFR;                            /*              */
       _UBYTE wk20[6];                          /*              */
       union {                                  /* XTALCTR      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE GAIN:1;              /*   GAIN       */
                    } BIT;                      /*              */
             } XTALCTR;                         /*              */
};                                              /*              */
struct st_intc {                                /* struct INTC  */
       union {                                  /* ICR0         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD NMIL:1;              /*   NMIL       */
                    _UWORD :6;                  /*              */
                    _UWORD NMIE:1;              /*   NMIE       */
                    _UWORD :6;                  /*              */
                    _UWORD NMIF:1;              /*   NMIF       */
                    _UWORD NMIM:1;              /*   NMIM       */
                    } BIT;                      /*              */
             } ICR0;                            /*              */
       union {                                  /* ICR1         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD IRQ71S:1;            /*   IRQ71S     */
                    _UWORD IRQ70S:1;            /*   IRQ70S     */
                    _UWORD IRQ61S:1;            /*   IRQ61S     */
                    _UWORD IRQ60S:1;            /*   IRQ60S     */
                    _UWORD IRQ51S:1;            /*   IRQ51S     */
                    _UWORD IRQ50S:1;            /*   IRQ50S     */
                    _UWORD IRQ41S:1;            /*   IRQ41S     */
                    _UWORD IRQ40S:1;            /*   IRQ40S     */
                    _UWORD IRQ31S:1;            /*   IRQ31S     */
                    _UWORD IRQ30S:1;            /*   IRQ30S     */
                    _UWORD IRQ21S:1;            /*   IRQ21S     */
                    _UWORD IRQ20S:1;            /*   IRQ20S     */
                    _UWORD IRQ11S:1;            /*   IRQ11S     */
                    _UWORD IRQ10S:1;            /*   IRQ10S     */
                    _UWORD IRQ01S:1;            /*   IRQ01S     */
                    _UWORD IRQ00S:1;            /*   IRQ00S     */
                    } BIT;                      /*              */
             } ICR1;                            /*              */
       union {                                  /* ICR2         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD PINT7S:1;            /*   PINT7S     */
                    _UWORD PINT6S:1;            /*   PINT6S     */
                    _UWORD PINT5S:1;            /*   PINT5S     */
                    _UWORD PINT4S:1;            /*   PINT4S     */
                    _UWORD PINT3S:1;            /*   PINT3S     */
                    _UWORD PINT2S:1;            /*   PINT2S     */
                    _UWORD PINT1S:1;            /*   PINT1S     */
                    _UWORD PINT0S:1;            /*   PINT0S     */
                    } BIT;                      /*              */
             } ICR2;                            /*              */
       union {                                  /* IRQRR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD IRQ7F:1;             /*   IRQ7F      */
                    _UWORD IRQ6F:1;             /*   IRQ6F      */
                    _UWORD IRQ5F:1;             /*   IRQ5F      */
                    _UWORD IRQ4F:1;             /*   IRQ4F      */
                    _UWORD IRQ3F:1;             /*   IRQ3F      */
                    _UWORD IRQ2F:1;             /*   IRQ2F      */
                    _UWORD IRQ1F:1;             /*   IRQ1F      */
                    _UWORD IRQ0F:1;             /*   IRQ0F      */
                    } BIT;                      /*              */
             } IRQRR;                           /*              */
       union {                                  /* PINTER       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD PINT7E:1;            /*   PINT7E     */
                    _UWORD PINT6E:1;            /*   PINT6E     */
                    _UWORD PINT5E:1;            /*   PINT5E     */
                    _UWORD PINT4E:1;            /*   PINT4E     */
                    _UWORD PINT3E:1;            /*   PINT3E     */
                    _UWORD PINT2E:1;            /*   PINT2E     */
                    _UWORD PINT1E:1;            /*   PINT1E     */
                    _UWORD PINT0E:1;            /*   PINT0E     */
                    } BIT;                      /*              */
             } PINTER;                          /*              */
       union {                                  /* PIRR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD PINT7R:1;            /*   PINT7R     */
                    _UWORD PINT6R:1;            /*   PINT6R     */
                    _UWORD PINT5R:1;            /*   PINT5R     */
                    _UWORD PINT4R:1;            /*   PINT4R     */
                    _UWORD PINT3R:1;            /*   PINT3R     */
                    _UWORD PINT2R:1;            /*   PINT2R     */
                    _UWORD PINT1R:1;            /*   PINT1R     */
                    _UWORD PINT0R:1;            /*   PINT0R     */
                    } BIT;                      /*              */
             } PIRR;                            /*              */
       union {                                  /* IBCR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD E15:1;               /*   E15        */
                    _UWORD E14:1;               /*   E14        */
                    _UWORD E13:1;               /*   E13        */
                    _UWORD E12:1;               /*   E12        */
                    _UWORD E11:1;               /*   E11        */
                    _UWORD E10:1;               /*   E10        */
                    _UWORD E9:1;                /*   E9         */
                    _UWORD E8:1;                /*   E8         */
                    _UWORD E7:1;                /*   E7         */
                    _UWORD E6:1;                /*   E6         */
                    _UWORD E5:1;                /*   E5         */
                    _UWORD E4:1;                /*   E4         */
                    _UWORD E3:1;                /*   E3         */
                    _UWORD E2:1;                /*   E2         */
                    _UWORD E1:1;                /*   E1         */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } IBCR;                            /*              */
       union {                                  /* IBNR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BE:2;                /*   BE         */
                    _UWORD BOVE:1;              /*   BOVE       */
                    _UWORD :9;                  /*              */
                    _UWORD BN:4;                /*   BN         */
                    } BIT;                      /*              */
             } IBNR;                            /*              */
       _UBYTE wk0[8];                           /*              */
       union {                                  /* IPR01        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _IRQ0:4;             /*   _IRQ0      */
                    _UWORD _IRQ1:4;             /*   _IRQ1      */
                    _UWORD _IRQ2:4;             /*   _IRQ2      */
                    _UWORD _IRQ3:4;             /*   _IRQ3      */
                    } BIT;                      /*              */
             } IPR01;                           /*              */
       union {                                  /* IPR02        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _IRQ4:4;             /*   _IRQ4      */
                    _UWORD _IRQ5:4;             /*   _IRQ5      */
                    _UWORD _IRQ6:4;             /*   _IRQ6      */
                    _UWORD _IRQ7:4;             /*   _IRQ7      */
                    } BIT;                      /*              */
             } IPR02;                           /*              */
       _UBYTE wk1[4];                           /*              */
       union {                                  /* IPR05        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _PINT:4;             /*   PINT7-0    */
                    _UWORD :12;                 /*              */
                    } BIT;                      /*              */
             } IPR05;                           /*              */
       _UBYTE wk2[990];                         /*              */
       union {                                  /* IPR06        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _DMAC0:4;            /*   _DMAC0     */
                    _UWORD _DMAC1:4;            /*   _DMAC1     */
                    _UWORD _DMAC2:4;            /*   _DMAC2     */
                    _UWORD _DMAC3:4;            /*   _DMAC3     */
                    } BIT;                      /*              */
             } IPR06;                           /*              */
       union {                                  /* IPR07        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _DMAC4:4;            /*   _DMAC4     */
                    _UWORD _DMAC5:4;            /*   _DMAC5     */
                    _UWORD _DMAC6:4;            /*   _DMAC6     */
                    _UWORD _DMAC7:4;            /*   _DMAC7     */
                    } BIT;                      /*              */
             } IPR07;                           /*              */
       union {                                  /* IPR08        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _DMAC8:4;            /*   _DMAC8     */
                    _UWORD _DMAC9:4;            /*   _DMAC9     */
                    _UWORD _DMAC10:4;           /*   _DMAC10    */
                    _UWORD _DMAC11:4;           /*   _DMAC11    */
                    } BIT;                      /*              */
             } IPR08;                           /*              */
       union {                                  /* IPR09        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _DMAC12:4;           /*   _DMAC12    */
                    _UWORD _DMAC13:4;           /*   _DMAC13    */
                    _UWORD _DMAC14:4;           /*   _DMAC14    */
                    _UWORD _DMAC15:4;           /*   _DMAC15    */
                    } BIT;                      /*              */
             } IPR09;                           /*              */
       union {                                  /* IPR10        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _USB:4;              /*   _USB       */
                    _UWORD _VDC40:4;            /*   _VDC40     */
                    _UWORD _VDC41:4;            /*   _VDC41     */
                    _UWORD _VDC42:4;            /*   _VDC42     */
                    } BIT;                      /*              */
             } IPR10;                           /*              */
       union {                                  /* IPR11        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _IMRLS:4;            /*    IMRLS     */
                    _UWORD _JCU:4;              /*    JCU       */
                    _UWORD _DISCOM:4;           /*    DISCOM    */
                    _UWORD _RGPVG:4;            /*    RGPVG     */
                    } BIT;                      /*              */
             } IPR11;                           /*              */
       union {                                  /* IPR12        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _CMT0:4;             /*   _CMT0      */
                    _UWORD _CMT1:4;             /*   _CMT1      */
                    _UWORD _BSC:4;              /*   _BSC       */
                    _UWORD _WDT:4;              /*   _WDT       */
                    } BIT;                      /*              */
             } IPR12;                           /*              */
       union {                                  /* IPR13        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _MTU00:4;            /*   _MTU00     */
                    _UWORD _MTU01:4;            /*   _MTU01     */
                    _UWORD _MTU10:4;            /*   _MTU10     */
                    _UWORD _MTU11:4;            /*   _MTU11     */
                    } BIT;                      /*              */
             } IPR13;                           /*              */
       union {                                  /* IPR14        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _MTU20:4;            /*   _MTU20     */
                    _UWORD _MTU21:4;            /*   _MTU21     */
                    _UWORD _MTU30:4;            /*   _MTU30     */
                    _UWORD _MTU31:4;            /*   _MTU31     */
                    } BIT;                      /*              */
             } IPR14;                           /*              */
       union {                                  /* IPR15        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _MTU40:4;            /*   _MTU40     */
                    _UWORD _MTU41:4;            /*   _MTU41     */
                    _UWORD _PWM1:4;             /*   _PWM1      */
                    _UWORD _PWM2:4;             /*   _PWM2      */
                    } BIT;                      /*              */
             } IPR15;                           /*              */
       union {                                  /* IPR16        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _SDG0:4;             /*   _SDG0      */
                    _UWORD _SDG1:4;             /*   _SDG1      */
                    _UWORD _SDG2:4;             /*   _SDG2      */
                    _UWORD _SDG3:4;             /*   _SDG3      */
                    } BIT;                      /*              */
             } IPR16;                           /*              */
       union {                                  /* IPR17        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _ADC:4;              /*   _ADC       */
                    _UWORD _SSI0:4;             /*   _SSI0      */
                    _UWORD _SSI1:4;             /*   _SSI1      */
                    _UWORD _SSI2:4;             /*   _SSI2      */
                    } BIT;                      /*              */
             } IPR17;                           /*              */
       union {                                  /* IPR18        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _SSI3:4;             /*   _SSI3      */
                    _UWORD _SSI4:4;             /*   _SSI4      */
                    _UWORD _SSI5:4;             /*   _SSI5      */
                    _UWORD _SPDIF:4;            /*   _SPDIF     */
                    } BIT;                      /*              */
             } IPR18;                           /*              */
       union {                                  /* IPR19        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _IIC30:4;            /*   _IIC30     */
                    _UWORD _IIC31:4;            /*   _IIC31     */
                    _UWORD _IIC32:4;            /*   _IIC32     */
                    _UWORD _IIC33:4;            /*   _IIC33     */
                    } BIT;                      /*              */
             } IPR19;                           /*              */
       union {                                  /* IPR20        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _SCIF0:4;            /*   _SCIF0     */
                    _UWORD _SCIF1:4;            /*   _SCIF1     */
                    _UWORD _SCIF2:4;            /*   _SCIF2     */
                    _UWORD _SCIF3:4;            /*   _SCIF3     */
                    } BIT;                      /*              */
             } IPR20;                           /*              */
       union {                                  /* IPR21        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _SCIF4:4;            /*   _SCIF4     */
                    _UWORD _SCIF5:4;            /*   _SCIF5     */
                    _UWORD _SCIF6:4;            /*   _SCIF6     */
                    _UWORD _SCIF7:4;            /*   _SCIF7     */
                    } BIT;                      /*              */
             } IPR21;                           /*              */
       union {                                  /* IPR22        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _SIOF:4;             /*   _SIOF      */
                    _UWORD _RCAN0:4;            /*   _RCAN0     */
                    _UWORD _RCAN1:4;            /*   _RCAN1     */
                    _UWORD _RCAN2:4;            /*   _RCAN2     */
                    } BIT;                      /*              */
             } IPR22;                           /*              */
       union {                                  /* IPR23        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _RSPI0:4;            /*   _RSPI0     */
                    _UWORD _RSPI1:4;            /*   _RSPI1     */
                    _UWORD _RQSPI0:4;           /*   _RQSPI0    */
                    _UWORD _RQSPI1:4;           /*   _RQSPI1    */
                    } BIT;                      /*              */
             } IPR23;                           /*              */
       union {                                  /* IPR24        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _IEB:4;              /*   _IEB       */
                    _UWORD _ROMDEC:4;           /*   _ROMDEC    */
                    _UWORD _FLCTL:4;            /*   _FLCTL     */
                    _UWORD _MMC:4;              /*   _MMC       */
                    } BIT;                      /*              */
             } IPR24;                           /*              */
       union {                                  /* IPR25        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _SDHI0:4;            /*   _SDHI0     */
                    _UWORD _SDHI1:4;            /*   _SDHI1     */
                    _UWORD _RTC:4;              /*   _RTC       */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } IPR25;                           /*              */
       union {                                  /* IPR26        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD _SRC0:4;             /*   _SRC0      */
                    _UWORD _SRC1:4;             /*   _SRC1      */
                    _UWORD _SRC2:4;             /*   _SRC2      */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } IPR26;                           /*              */
};                                              /*              */
	#endif
struct st_ccnt {                                /* struct CCNT  */
       union {                                  /* CCR1         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :20;                /*              */
                    _UDWORD ICF:1;              /*   ICF        */
                    _UDWORD :2;                 /*              */
                    _UDWORD ICE:1;              /*   ICE        */
                    _UDWORD :4;                 /*              */
                    _UDWORD OCF:1;              /*   OCF        */
                    _UDWORD :1;                 /*              */
                    _UDWORD WT:1;               /*   WT         */
                    _UDWORD OCE:1;              /*   OCE        */
                    } BIT;                      /*              */
             } CCR1;                            /*              */
       union {                                  /* CCR2         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :15;                /*              */
                    _UDWORD LE:1;               /*   LE         */
                    _UDWORD :6;                 /*              */
                    _UDWORD W3LOAD:1;           /*   W3LOAD     */
                    _UDWORD W3LOCK:1;           /*   W3LOCK     */
                    _UDWORD :6;                 /*              */
                    _UDWORD W2LOAD:1;           /*   W2LOAD     */
                    _UDWORD W2LOCK:1;           /*   W2LOCK     */
                    } BIT;                      /*              */
             } CCR2;                            /*              */
};
	#if	0
union CSnBCR{                                   /* CSnBCR       */
      _UDWORD LONG;                             /*  Long Access */
      struct {                                  /*  Bit Access  */
             _UDWORD :1;                        /*              */
             _UDWORD IWW:3;                     /*   IWW        */
             _UDWORD IWRWD:3;                   /*   IWRWD      */
             _UDWORD IWRWS:3;                   /*   IWRWS      */
             _UDWORD IWRRD:3;                   /*   IWRRD      */
             _UDWORD IWRRS:3;                   /*   IWRRS      */
             _UDWORD :1;                        /*              */
             _UDWORD TYPE:3;                    /*   TYPE       */
             _UDWORD ENDIAN:1;                  /*   ENDIAN     */
             _UDWORD BSZ:2;                     /*   BSZ        */
             _UDWORD :9;                        /*              */
             } BIT;                             /*              */
};                                              /*              */
struct st_bsc {                                 /* struct BSC   */
       union {                                  /* CMNCR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :20;                /*              */
                    _UDWORD BLOCK:1;            /*   BLOCK      */
                    _UDWORD DPRTY:2;            /*   DPRTY      */
                    _UDWORD DMAIW:3;            /*   DMAIW      */
                    _UDWORD DMAIWA:1;           /*   DMAIWA     */
                    _UDWORD :3;                 /*              */
                    _UDWORD HIZMEM:1;           /*   HIZMEM     */
                    _UDWORD HIZCNT:1;           /*   HIZCNT     */
                    } BIT;                      /*              */
             } CMNCR;                           /*              */
       union CSnBCR CS0BCR;                     /* CS0BCR       */
       union CSnBCR CS1BCR;                     /* CS1BCR       */
       union CSnBCR CS2BCR;                     /* CS2BCR       */
       union CSnBCR CS3BCR;                     /* CS3BCR       */
       union CSnBCR CS4BCR;                     /* CS4BCR       */
       union CSnBCR CS5BCR;                     /* CS5BCR       */
       _UBYTE wk0[12];                          /*              */
       union {                                  /* CS0WCR       */
             union {                            /* CS0WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :11;         /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :7;          /*              */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :4;          /*              */
                           _UDWORD HW:2;        /*   HW         */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             union {                            /* CS0WCR(BROM_ASY) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :10;         /*              */
                           _UDWORD BST:2;       /*   BST        */
                           _UDWORD :2;          /*              */
                           _UDWORD BW:2;        /*   BW         */
                           _UDWORD :5;          /*              */
                           _UDWORD W:4;         /*   W          */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :6;          /*              */
                           } BIT;               /*              */
                    } BROM_ASY;                 /*              */
             union {                            /* CS0WCR(BROM_SY) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :14;         /*              */
                           _UDWORD BW:2;        /*   BW         */
                           _UDWORD :5;          /*              */
                           _UDWORD W:4;         /*   W          */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :6;          /*              */
                           } BIT;               /*              */
                    } BROM_SY;                  /*              */
             } CS0WCR;
       union {                                  /* CS1WCR       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :11;                /*              */
                    _UDWORD BAS:1;              /*   BAS        */
                    _UDWORD :1;                 /*              */
                    _UDWORD WW:3;               /*   WW         */
                    _UDWORD :3;                 /*              */
                    _UDWORD SW:2;               /*   SW         */
                    _UDWORD WR:4;               /*   WR         */
                    _UDWORD WM:1;               /*   WM         */
                    _UDWORD :4;                 /*              */
                    _UDWORD HW:2;               /*   HW         */
                    } BIT;                      /*              */
             } CS1WCR;                          /*              */
       union {                                  /* CS2WCR       */
             union {                            /* CS2WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :11;         /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :9;          /*              */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :6;          /*              */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             union {                            /* CS2WCR(SDRAM) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :23;         /*              */
                           _UDWORD A2CL:2;      /*   A2CL       */
                           _UDWORD :7;          /*              */
                           } BIT;               /*              */
                    } SDRAM;                    /*              */
             } CS2WCR;                          /*              */
       union {                                  /* CS3WCR       */
             union {                            /* CS3WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :11;         /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :9;          /*              */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :6;          /*              */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             union {                            /* CS3WCR(SDRAM) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :17;         /*              */
                           _UDWORD WTRP:2;      /*   WTRP       */
                           _UDWORD :1;          /*              */
                           _UDWORD WTRCD:2;     /*   WTRCD      */
                           _UDWORD :1;          /*              */
                           _UDWORD A3CL:2;      /*   A3CL       */
                           _UDWORD :2;          /*              */
                           _UDWORD TRWL:2;      /*   TRWL       */
                           _UDWORD :1;          /*              */
                           _UDWORD WTRC:2;      /*   WTRC       */
                           } BIT;               /*              */
                    } SDRAM;                    /*              */
             } CS3WCR;                          /*              */
       union {                                  /* CS4WCR       */
              union {                           /* CS4WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :11;         /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :1;          /*              */
                           _UDWORD WW:3;        /*   WW         */
                           _UDWORD :3;          /*              */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :4;          /*              */
                           _UDWORD HW:2;        /*   HW         */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
              union {                           /* CS4WCR(BROM_ASY) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :10;         /*              */
                           _UDWORD BST:2;       /*   BST        */
                           _UDWORD :2;          /*              */
                           _UDWORD BW:2;        /*   BW         */
                           _UDWORD :3;          /*              */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD W:4;         /*   W          */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :4;          /*              */
                           _UDWORD HW:2;        /*   HW         */
                           } BIT;               /*              */
                    } BROM_ASY;                 /*              */
             } CS4WCR;                          /*              */
       union {                                  /* CS5WCR       */
              union {                           /* CS5WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :10;         /*              */
                           _UDWORD SZSEL:1;     /*   SZSEL      */
                           _UDWORD MPXWBAS:1;   /*   MPXW/BAS   */
                           _UDWORD :1;          /*              */
                           _UDWORD WW:3;        /*   WW         */
                           _UDWORD :3;          /*              */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :4;          /*              */
                           _UDWORD HW:2;        /*   HW         */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
              union {                           /* CS5WCR(PCMCIA) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :10;         /*              */
                           _UDWORD SA:2;        /*   SA         */
                           _UDWORD :5;          /*              */
                           _UDWORD TED:4;       /*   TED        */
                           _UDWORD PCW:4;       /*   PCW        */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD :2;          /*              */
                           _UDWORD TEH:4;       /*   TEH        */
                           } BIT;               /*              */
                    } PCMCIA;                   /*              */
             } CS5WCR;                          /*              */
       _UBYTE wk1[12];                          /*              */
       union {                                  /* SDCR         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :11;                /*              */
                    _UDWORD A2ROW:2;            /*   A2ROW      */
                    _UDWORD :1;                 /*              */
                    _UDWORD A2COL:2;            /*   A2COL      */
                    _UDWORD :2;                 /*              */
                    _UDWORD DEEP:1;             /*   DEEP       */
                    _UDWORD :1;                 /*              */
                    _UDWORD RFSH:1;             /*   RFSH       */
                    _UDWORD RMODE:1;            /*   RMODE      */
                    _UDWORD PDOWN:1;            /*   PDOWN      */
                    _UDWORD BACTV:1;            /*   BACTV      */
                    _UDWORD :3;                 /*              */
                    _UDWORD A3ROW:2;            /*   A3ROW      */
                    _UDWORD :1;                 /*              */
                    _UDWORD A3COL:2;            /*   A3COL      */
                    } BIT;                      /*              */
             } SDCR;                            /*              */
       union {                                  /* RTCSR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :24;                /*              */
                    _UDWORD CMF:1;              /*   CMF        */
                    _UDWORD CMIE:1;             /*   CMIE       */
                    _UDWORD CKS:3;              /*   CKS        */
                    _UDWORD RRC:3;              /*   RRC        */
                    } BIT;                      /*              */
             } RTCSR;                           /*              */
       union {                                  /* RTCNT        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RTCNT;                           /*              */
       union {                                  /* RTCOR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RTCOR;                           /*              */
};                                              /*              */
struct st_dmac {                                /* struct DMAC  */
       union {                                  /* SAR0         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR0;                            /*              */
       union {                                  /* DAR0         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR0;                            /*              */
       union {                                  /* DMATCR0      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR0;                         /*              */
       union {                                  /* CHCR0        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE DO:1;                /*   DO         */
                    _UBYTE TL:1;                /*   TL         */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE AM:1;                /*   AM         */
                    _UBYTE AL:1;                /*   AL         */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE DL:1;                /*   DL         */
                    _UBYTE DS:1;                /*   DS         */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR0;                           /*              */
       union {                                  /* SAR1         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR1;                            /*              */
       union {                                  /* DAR1         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR1;                            /*              */
       union {                                  /* DMATCR1      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR1;                         /*              */
       union {                                  /* CHCR1        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :3;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :2;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :2;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR1;                           /*              */
       union {                                  /* SAR2         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR2;                            /*              */
       union {                                  /* DAR2         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR2;                            /*              */
       union {                                  /* DMATCR2      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR2;                         /*              */
       union {                                  /* CHCR2        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR2;                           /*              */
       union {                                  /* SAR3         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR3;                            /*              */
       union {                                  /* DAR3         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR3;                            /*              */
       union {                                  /* DMATCR3      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR3;                         /*              */
       union {                                  /* CHCR3        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR3;                           /*              */
       union {                                  /* SAR4         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR4;                            /*              */
       union {                                  /* DAR4         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR4;                            /*              */
       union {                                  /* DMATCR4      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR4;                         /*              */
       union {                                  /* CHCR4        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR4;                           /*              */
       union {                                  /* SAR5         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR5;                            /*              */
       union {                                  /* DAR5         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR5;                            /*              */
       union {                                  /* DMATCR5      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR5;                         /*              */
       union {                                  /* CHCR5        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR5;                           /*              */
       union {                                  /* SAR6         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR6;                            /*              */
       union {                                  /* DAR6         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR6;                            /*              */
       union {                                  /* DMATCR6      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR6;                         /*              */
       union {                                  /* CHCR6        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR6;                           /*              */
       union {                                  /* SAR7         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR7;                            /*              */
       union {                                  /* DAR7         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR7;                            /*              */
       union {                                  /* DMATCR7      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR7;                         /*              */
       union {                                  /* CHCR7        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR7;                           /*              */
       union {                                  /* SAR8         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR8;                            /*              */
       union {                                  /* DAR8         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR8;                            /*              */
       union {                                  /* DMATCR8      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR8;                         /*              */
       union {                                  /* CHCR8        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR8;                           /*              */
       union {                                  /* SAR9         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR9;                            /*              */
       union {                                  /* DAR9         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR9;                            /*              */
       union {                                  /* DMATCR9      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR9;                         /*              */
       union {                                  /* CHCR9        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR9;                           /*              */
       union {                                  /* SAR10        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR10;                           /*              */
       union {                                  /* DAR10        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR10;                           /*              */
       union {                                  /* DMATCR10     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR10;                        /*              */
       union {                                  /* CHCR10       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR10;                          /*              */
       union {                                  /* SAR11        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR11;                           /*              */
       union {                                  /* DAR11        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR11;                           /*              */
       union {                                  /* DMATCR11     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR11;                        /*              */
       union {                                  /* CHCR11       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR11;                          /*              */
       union {                                  /* SAR12        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR12;                           /*              */
       union {                                  /* DAR12        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR12;                           /*              */
       union {                                  /* DMATCR12     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR12;                        /*              */
       union {                                  /* CHCR12       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR12;                          /*              */
       union {                                  /* SAR13        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR13;                           /*              */
       union {                                  /* DAR13        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR13;                           /*              */
       union {                                  /* DMATCR13     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR13;                        /*              */
       union {                                  /* CHCR13       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR13;                          /*              */
       union {                                  /* SAR14        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR14;                           /*              */
       union {                                  /* DAR14        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR14;                           /*              */
       union {                                  /* DMATCR14     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR14;                        /*              */
       union {                                  /* CHCR14       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR14;                          /*              */
       union {                                  /* SAR15        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } SAR15;                           /*              */
       union {                                  /* DAR15        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DAR15;                           /*              */
       union {                                  /* DMATCR15     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } DMATCR15;                        /*              */
       union {                                  /* CHCR15       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE TC:1;                /*   TC         */
                    _UBYTE :1;                  /*              */
                    _UBYTE RLDSAR:1;            /*   RLDSAR     */
                    _UBYTE RLDDAR:1;            /*   RLDDAR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE DAF:1;               /*   DAF        */
                    _UBYTE SAF:1;               /*   SAF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TEMASK:1;            /*   TEMASK     */
                    _UBYTE HE:1;                /*   HE         */
                    _UBYTE HIE:1;               /*   HIE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE DM:2;                /*   DM         */
                    _UBYTE SM:2;                /*   SM         */
                    _UBYTE RS:4;                /*   RS         */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE TB:1;                /*   TB         */
                    _UBYTE TS:2;                /*   TS         */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE TE:1;                /*   TE         */
                    _UBYTE DE:1;                /*   DE         */
                    } BIT;                      /*              */
             } CHCR15;                          /*              */
       union {                                  /* RSAR0        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR0;                           /*              */
       union {                                  /* RDAR0        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR0;                           /*              */
       union {                                  /* RDMATCR0     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR0;                        /*              */
       _UBYTE wk0[4];                           /*              */
       union {                                  /* RSAR1        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR1;                           /*              */
       union {                                  /* RDAR1        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR1;                           /*              */
       union {                                  /* RDMATCR1     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR1;                        /*              */
       _UBYTE wk1[4];                           /*              */
       union {                                  /* RSAR2        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR2;                           /*              */
       union {                                  /* RDAR2        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR2;                           /*              */
       union {                                  /* RDMATCR2     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR2;                        /*              */
       _UBYTE wk2[4];                           /*              */
       union {                                  /* RSAR3        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR3;                           /*              */
       union {                                  /* RDAR3        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR3;                           /*              */
       union {                                  /* RDMATCR3     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR3;                        /*              */
       _UBYTE wk3[4];                           /*              */
       union {                                  /* RSAR4        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR4;                           /*              */
       union {                                  /* RDAR4        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR4;                           /*              */
       union {                                  /* RDMATCR4     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR4;                        /*              */
       _UBYTE wk4[4];                           /*              */
       union {                                  /* RSAR5        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR5;                           /*              */
       union {                                  /* RDAR5        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR5;                           /*              */
       union {                                  /* RDMATCR5     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR5;                        /*              */
       _UBYTE wk5[4];                           /*              */
       union {                                  /* RSAR6        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR6;                           /*              */
       union {                                  /* RDAR6        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR6;                           /*              */
       union {                                  /* RDMATCR6     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR6;                        /*              */
       _UBYTE wk6[4];                           /*              */
       union {                                  /* RSAR7        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR7;                           /*              */
       union {                                  /* RDAR7        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR7;                           /*              */
       union {                                  /* RDMATCR7     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR7;                        /*              */
       _UBYTE wk7[4];                           /*              */
       union {                                  /* RSAR8        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR8;                           /*              */
       union {                                  /* RDAR8        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR8;                           /*              */
       union {                                  /* RDMATCR8     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR8;                        /*              */
       _UBYTE wk8[4];                           /*              */
       union {                                  /* RSAR9        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR9;                           /*              */
       union {                                  /* RDAR9        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR9;                           /*              */
       union {                                  /* RDMATCR9     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR9;                        /*              */
       _UBYTE wk9[4];                           /*              */
       union {                                  /* RSAR10       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR10;                          /*              */
       union {                                  /* RDAR10       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR10;                          /*              */
       union {                                  /* RDMATCR10    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR10;                       /*              */
       _UBYTE wk10[4];                          /*              */
       union {                                  /* RSAR11       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR11;                          /*              */
       union {                                  /* RDAR11       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR11;                          /*              */
       union {                                  /* RDMATCR11    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR11;                       /*              */
       _UBYTE wk11[4];                          /*              */
       union {                                  /* RSAR12       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR12;                          /*              */
       union {                                  /* RDAR12       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR12;                          /*              */
       union {                                  /* RDMATCR12    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR12;                       /*              */
       _UBYTE wk12[4];                          /*              */
       union {                                  /* RSAR13       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR13;                          /*              */
       union {                                  /* RDAR13       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR13;                          /*              */
       union {                                  /* RDMATCR13    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR13;                       /*              */
       _UBYTE wk13[4];                          /*              */
       union {                                  /* RSAR14       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR14;                          /*              */
       union {                                  /* RDAR14       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR14;                          /*              */
       union {                                  /* RDMATCR14    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR14;                       /*              */
       _UBYTE wk14[4];                          /*              */
       union {                                  /* RSAR15       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RSAR15;                          /*              */
       union {                                  /* RDAR15       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDAR15;                          /*              */
       union {                                  /* RDMATCR15    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RDMATCR15;                       /*              */
       _UBYTE wk15[4];                          /*              */
       union {                                  /* DMAOR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD :2;                  /*              */
                    _UWORD CMS:2;               /*   CMS        */
                    _UWORD :2;                  /*              */
                    _UWORD PR:2;                /*   PR         */
                    _UWORD :5;                  /*              */
                    _UWORD AE:1;                /*   AE         */
                    _UWORD NMIF:1;              /*   NMIF       */
                    _UWORD DME:1;               /*   DME        */
                    } BIT;                      /*              */
             } DMAOR;                           /*              */
       _UBYTE wk16[254];                        /*              */
       union {                                  /* DMARS0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH1:8;               /*   CH1        */
                    _UWORD CH0:8;               /*   CH0        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH1MID:6;            /*   CH1MID     */
                    _UWORD CH1RID:2;            /*   CH1RID     */
                    _UWORD CH0MID:6;            /*   CH0MID     */
                    _UWORD CH0RID:2;            /*   CH0RID     */
                    } BIT;                      /*              */
             } DMARS0;                          /*              */
       _UBYTE wk17[2];                          /*              */
       union {                                  /* DMARS1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH3:8;               /*   CH3        */
                    _UWORD CH2:8;               /*   CH2        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH3MID:6;            /*   CH3ID     */
                    _UWORD CH3RID:2;            /*   CH3RID     */
                    _UWORD CH2MID:6;            /*   CH2MID     */
                    _UWORD CH2RID:2;            /*   CH2RID     */
                    } BIT;                      /*              */
             } DMARS1;                          /*              */
       _UBYTE wk18[2];                          /*              */
       union {                                  /* DMARS2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH5:8;               /*   CH5        */
                    _UWORD CH4:8;               /*   CH4        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH5MID:6;            /*   CH5MID     */
                    _UWORD CH5RID:2;            /*   CH5RID     */
                    _UWORD CH4MID:6;            /*   CH4MID     */
                    _UWORD CH4RID:2;            /*   CH4RID     */
                    } BIT;                      /*              */
             } DMARS2;                          /*              */
       _UBYTE wk19[2];                          /*              */
       union {                                  /* DMARS3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH7:8;               /*   CH7        */
                    _UWORD CH6:8;               /*   CH6        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH7MID:6;            /*   CH7MID     */
                    _UWORD CH7RID:2;            /*   CH7RID     */
                    _UWORD CH6MID:6;            /*   CH6MID     */
                    _UWORD CH6RID:2;            /*   CH6RID     */
                    } BIT;                      /*              */
             } DMARS3;                          /*              */
       _UBYTE wk20[2];                          /*              */
       union {                                  /* DMARS4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH9:8;               /*   CH9        */
                    _UWORD CH8:8;               /*   CH8        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH9MID:6;            /*   CH9MID     */
                    _UWORD CH9RID:2;            /*   CH9RID     */
                    _UWORD CH8MID:6;            /*   CH8MID     */
                    _UWORD CH8RID:2;            /*   CH8RID     */
                    } BIT;                      /*              */
             } DMARS4;                          /*              */
       _UBYTE wk21[2];                          /*              */
       union {                                  /* DMARS5       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH11:8;              /*   CH11       */
                    _UWORD CH10:8;              /*   CH10       */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH11MID:6;           /*   CH11MID    */
                    _UWORD CH11RID:2;           /*   CH11RID    */
                    _UWORD CH10MID:6;           /*   CH10MID    */
                    _UWORD CH10RID:2;           /*   CH10RID    */
                    } BIT;                      /*              */
             } DMARS5;                          /*              */
       _UBYTE wk22[2];                          /*              */
       union {                                  /* DMARS6       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH13:8;              /*   CH13       */
                    _UWORD CH12:8;              /*   CH12       */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH13MID:6;           /*   CH13MID    */
                    _UWORD CH13RID:2;           /*   CH13RID    */
                    _UWORD CH12MID:6;           /*   CH12MID    */
                    _UWORD CH12RID:2;           /*   CH12RID    */
                    } BIT;                      /*              */
             } DMARS6;                          /*              */
       _UBYTE wk23[2];                          /*              */
       union {                                  /* DMARS7       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UWORD CH15:8;              /*   CH15       */
                    _UWORD CH14:8;              /*   CH14       */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD CH15MID:6;           /*   CH15MID    */
                    _UWORD CH15RID:2;           /*   CH15RID    */
                    _UWORD CH14MID:6;           /*   CH14MID    */
                    _UWORD CH14RID:2;           /*   CH14RID    */
                    } BIT;                      /*              */
             } DMARS7;                          /*              */
};                                              /*              */
	#endif
#if 0
struct st_mtu2 {                                /* struct MTU2  */
       union {                                  /* TCR_2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE CCLR:2;              /*   CCLR       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    } BIT;                      /*              */
             } TCR_2;                           /*              */
       union {                                  /* TMDR_2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE MD:4;                /*   MD         */
                    } BIT;                      /*              */
             } TMDR_2;                          /*              */
       union {                                  /* TIOR_2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOB:4;               /*   IOB        */
                    _UBYTE IOA:4;               /*   IOA        */
                    } BIT;                      /*              */
             } TIOR_2;                          /*              */
       _UBYTE wk0[1];                           /*              */
       union {                                  /* TIER_2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    _UBYTE :1;                  /*              */
                    _UBYTE TCIEU:1;             /*   TCIEU      */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE :2;                  /*              */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    } BIT;                      /*              */
             } TIER_2;                          /*              */
       union {                                  /* TSR_2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    _UBYTE :1;                  /*              */
                    _UBYTE TCFU:1;              /*   TCFU       */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    } BIT;                      /*              */
             } TSR_2;                           /*              */
       union {                                  /* TCNT_2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_2;                          /*              */
       union {                                  /* TGRA_2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_2;                          /*              */
       union {                                  /* TGRB_2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_2;                          /*              */
       _UBYTE wk1[500];                         /*              */
       union {                                  /* TCR_3        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CCLR:3;              /*   CCLR       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    } BIT;                      /*              */
             } TCR_3;                           /*              */
       union {                                  /* TCR_4        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CCLR:3;              /*   CCLR       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    } BIT;                      /*              */
             } TCR_4;                           /*              */
       union {                                  /* TMDR_3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE BFB:1;               /*   BFB        */
                    _UBYTE BFA:1;               /*   BFA        */
                    _UBYTE MD:4;                /*   MD         */
                    } BIT;                      /*              */
             } TMDR_3;                          /*              */
       union {                                  /* TMDR_4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE BFB:1;               /*   BFB        */
                    _UBYTE BFA:1;               /*   BFA        */
                    _UBYTE MD:4;                /*   MD         */
                    } BIT;                      /*              */
             } TMDR_4;                          /*              */
       union {                                  /* TIORH_3      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOB:4;               /*   IOB        */
                    _UBYTE IOA:4;               /*   IOA        */
                    } BIT;                      /*              */
             } TIORH_3;                         /*              */
       union {                                  /* TIORL_3      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOD:4;               /*   IOD        */
                    _UBYTE IOC:4;               /*   IOC        */
                    } BIT;                      /*              */
             } TIORL_3;                         /*              */
       union {                                  /* TIORH_4      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOB:4;               /*   IOB        */
                    _UBYTE IOA:4;               /*   IOA        */
                    } BIT;                      /*              */
             } TIORH_4;                         /*              */
       union {                                  /* TIORL_4      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOD:4;               /*   IOD        */
                    _UBYTE IOC:4;               /*   IOC        */
                    } BIT;                      /*              */
             } TIORL_4;                         /*              */
       union {                                  /* TIER_3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE TGIED:1;             /*   TGIED      */
                    _UBYTE TGIEC:1;             /*   TGIEC      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    } BIT;                      /*              */
             } TIER_3;                          /*              */
       union {                                  /* TIER_4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    _UBYTE TTGE2:1;             /*   TTGE2      */
                    _UBYTE :1;                  /*              */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE TGIED:1;             /*   TGIED      */
                    _UBYTE TGIEC:1;             /*   TGIEC      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    } BIT;                      /*              */
             } TIER_4;                          /*              */
       union {                                  /* TOER         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE OE4D:1;              /*   OE4D       */
                    _UBYTE OE4C:1;              /*   OE4C       */
                    _UBYTE OE3D:1;              /*   OE3D       */
                    _UBYTE OE4B:1;              /*   OE4B       */
                    _UBYTE OE4A:1;              /*   OE4A       */
                    _UBYTE OE3B:1;              /*   OE3B       */
                    } BIT;                      /*              */
             } TOER;                            /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* TGCR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE BDC:1;               /*   BDC        */
                    _UBYTE N:1;                 /*   N          */
                    _UBYTE P:1;                 /*   P          */
                    _UBYTE FB:1;                /*   FB         */
                    _UBYTE WF:1;                /*   WF         */
                    _UBYTE VF:1;                /*   VF         */
                    _UBYTE UF:1;                /*   UF         */
                    } BIT;                      /*              */
             } TGCR;                            /*              */
       union {                                  /* TOCR1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PSYE:1;              /*   PSYE       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TOCL:1;              /*   TOCL       */
                    _UBYTE TOCS:1;              /*   TOCS       */
                    _UBYTE OLSN:1;              /*   OLSN       */
                    _UBYTE OLSP:1;              /*   OLSP       */
                    } BIT;                      /*              */
             } TOCR1;                           /*              */
       union {                                  /* TOCR2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BF:2;                /*   BF         */
                    _UBYTE OLS3N:1;             /*   OLS3N      */
                    _UBYTE OLS3P:1;             /*   OLS3P      */
                    _UBYTE OLS2N:1;             /*   OLS2N      */
                    _UBYTE OLS2P:1;             /*   OLS2P      */
                    _UBYTE OLS1N:1;             /*   OLS1N      */
                    _UBYTE OLS1P:1;             /*   OLS1P      */
                    } BIT;                      /*              */
             } TOCR2;                           /*              */
       union {                                  /* TCNT_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_3;                          /*              */
       union {                                  /* TCNT_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_4;                          /*              */
       union {                                  /* TCDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCDR;                            /*              */
       union {                                  /* TDDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TDDR;                            /*              */
       union {                                  /* TGRA_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_3;                          /*              */
       union {                                  /* TGRB_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_3;                          /*              */
       union {                                  /* TGRA_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_4;                          /*              */
       union {                                  /* TGRB_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_4;                          /*              */
       union {                                  /* TCNTS       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNTS;                           /*              */
       union {                                  /* TCBR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCBR;                            /*              */
       union {                                  /* TGRC_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRC_3;                          /*              */
       union {                                  /* TGRD_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRD_3;                          /*              */
       union {                                  /* TGRC_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRC_4;                          /*              */
       union {                                  /* TGRD_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRD_4;                          /*              */
       union {                                  /* TSR_3        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    } BIT;                      /*              */
             } TSR_3;                           /*              */
       union {                                  /* TSR_4        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    } BIT;                      /*              */
             } TSR_4;                           /*              */
       _UBYTE wk3[2];                           /*              */
       union {                                  /* TITCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE T3AEN:1;             /*   T3AEN      */
                    _UBYTE _3ACOR:3;            /*   _3ACOR     */
                    _UBYTE T4VEN:1;             /*   T4VEN      */
                    _UBYTE _4VCOR:3;            /*   _4VCOR     */
                    } BIT;                      /*              */
             } TITCR;                           /*              */
       union {                                  /* TITCNT       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE _3ACNT:3;            /*   _3ACNT     */
                    _UBYTE :1;                  /*              */
                    _UBYTE _4VCNT:3;            /*   _4VCNT     */
                    } BIT;                      /*              */
             } TITCNT;                          /*              */
       union {                                  /* TBTER        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE BTE:2;               /*   BTE        */
                    } BIT;                      /*              */
             } TBTER;                           /*              */
       _UBYTE wk4[1];                           /*              */
       union {                                  /* TDER         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE TDER:1;              /*   TDER       */
                    } BIT;                      /*              */
             } TDER;                            /*              */
       _UBYTE wk5[1];                           /*              */
       union {                                  /* TOLBR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE OLS3N:1;             /*   OLS3N      */
                    _UBYTE OLS3P:1;             /*   OLS3P      */
                    _UBYTE OLS2N:1;             /*   OLS2N      */
                    _UBYTE OLS2P:1;             /*   OLS2P      */
                    _UBYTE OLS1N:1;             /*   OLS1N      */
                    _UBYTE OLS1P:1;             /*   OLS1P      */
                    } BIT;                      /*              */
             } TOLBR;                           /*              */
       _UBYTE wk6[1];                           /*              */
       union {                                  /* TBTM_3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE TTSB:1;              /*   TTSB       */
                    _UBYTE TTSA:1;              /*   TTSA       */
                    } BIT;                      /*              */
             } TBTM_3;                          /*              */
       union {                                  /* TBTM_4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE TTSB:1;              /*   TTSB       */
                    _UBYTE TTSA:1;              /*   TTSA       */
                    } BIT;                      /*              */
             } TBTM_4;                          /*              */
       _UBYTE wk7[6];                           /*              */
       union {                                  /* TADCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BF:2;                /*   BF         */
                    _UWORD :6;                  /*              */
                    _UWORD UT4AE:1;             /*   UT4AE      */
                    _UWORD DT4AE:1;             /*   DT4AE      */
                    _UWORD UT4BE:1;             /*   UT4BE      */
                    _UWORD DT4BE:1;             /*   DT4BE      */
                    _UWORD ITA3AE:1;            /*   ITA3AE     */
                    _UWORD ITA4VE:1;            /*   ITA4VE     */
                    _UWORD ITB3AE:1;            /*   ITB3AE     */
                    _UWORD ITB4VE:1;            /*   ITB4VE     */
                    } BIT;                      /*              */
             } TADCR;                           /*              */
       _UBYTE wk8[2];                           /*              */
       union {                                  /* TADCORA_4    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCORA_4;                       /*              */
       union {                                  /* TADCORB_4    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCORB_4;                       /*              */
       union {                                  /* TADCOBRA_4   */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCOBRA_4;                      /*              */
       union {                                  /* TADCOBRB_4   */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCOBRB_4;                      /*              */
       _UBYTE wk9[20];                          /*              */
       union {                                  /* TWCR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CCE:1;               /*   CCE        */
                    _UBYTE :6;                  /*              */
                    _UBYTE WRE:1;               /*   WRE        */
                    } BIT;                      /*              */
             } TWCR;                            /*              */
       _UBYTE wk10[31];                         /*              */
       union {                                  /* TSTR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CST4:1;              /*   CST4       */
                    _UBYTE CST3:1;              /*   CST3       */
                    _UBYTE :3;                  /*              */
                    _UBYTE CST2:1;              /*   CST2       */
                    _UBYTE CST1:1;              /*   CST1       */
                    _UBYTE CST0:1;              /*   CST0       */
                    } BIT;                      /*              */
             } TSTR;                            /*              */
       union {                                  /* TSYR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SYNC4:1;             /*   SYNC4      */
                    _UBYTE SYNC3:1;             /*   SYNC3      */
                    _UBYTE :3;                  /*              */
                    _UBYTE SYNC2:1;             /*   SYNC2      */
                    _UBYTE SYNC1:1;             /*   SYNC1      */
                    _UBYTE SYNC0:1;             /*   SYNC0      */
                    } BIT;                      /*              */
             } TSYR;                            /*              */
       _UBYTE wk11[2];                          /*              */
       union {                                  /* TRWER        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE RWE:1;               /*   RWE        */
                    } BIT;                      /*              */
             } TRWER;                           /*              */
       _UBYTE wk12[123];                        /*              */
       union {                                  /* TCR_0        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CCLR:3;              /*   CCLR       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    } BIT;                      /*              */
             } TCR_0;                           /*              */
       union {                                  /* TMDR_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE BFE:1;               /*   BFE        */
                    _UBYTE BFB:1;               /*   BFB        */
                    _UBYTE BFA:1;               /*   BFA        */
                    _UBYTE MD:4;                /*   MD         */
                    } BIT;                      /*              */
             } TMDR_0;                          /*              */
       union {                                  /* TIORH_0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOB:4;               /*   IOB        */
                    _UBYTE IOA:4;               /*   IOA        */
                    } BIT;                      /*              */
             } TIORH_0;                         /*              */
       union {                                  /* TIORL_0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOD:4;               /*   IOD        */
                    _UBYTE IOC:4;               /*   IOC        */
                    } BIT;                      /*              */
             } TIORL_0;                         /*              */
       union {                                  /* TIER_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE TGIED:1;             /*   TGIED      */
                    _UBYTE TGIEC:1;             /*   TGIEC      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    } BIT;                      /*              */
             } TIER_0;                          /*              */
       union {                                  /* TSR_0        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    } BIT;                      /*              */
             } TSR_0;                           /*              */
       union {                                  /* TCNT_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_0;                          /*              */
       union {                                  /* TGRA_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_0;                          /*              */
       union {                                  /* TGRB_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_0;                          /*              */
       union {                                  /* TGRC_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRC_0;                          /*              */
       union {                                  /* TGRD_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRD_0;                          /*              */
       _UBYTE wk13[16];                         /*              */
       union {                                  /* TGRE_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRE_0;                          /*              */
       union {                                  /* TGRF_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRF_0;                          /*              */
       union {                                  /* TIER2_0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTGE2:1;             /*   TTGE2      */
                    _UBYTE :5;                  /*              */
                    _UBYTE TGIEF:1;             /*   TGIEF      */
                    _UBYTE TGIEE:1;             /*   TGIEE      */
                    } BIT;                      /*              */
             } TIER2_0;                         /*              */
       union {                                  /* TSR2_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE TGFF:1;              /*   TGFF       */
                    _UBYTE TGFE:1;              /*   TGFE       */
                    } BIT;                      /*              */
             } TSR2_0;                          /*              */
       union {                                  /* TBTM_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE TTSE:1;              /*   TTSE       */
                    _UBYTE TTSB:1;              /*   TTSB       */
                    _UBYTE TTSA:1;              /*   TTSA       */
                    } BIT;                      /*              */
             } TBTM_0;                          /*              */
       _UBYTE wk14[89];                         /*              */
       union {                                  /* TCR_1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE CCLR:2;              /*   CCLR       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    } BIT;                      /*              */
             } TCR_1;                           /*              */
       union {                                  /* TMDR_1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE MD:4;                /*   MD         */
                    } BIT;                      /*              */
             } TMDR_1;                          /*              */
       union {                                  /* TIOR_1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOB:4;               /*   IOB        */
                    _UBYTE IOA:4;               /*   IOA        */
                    } BIT;                      /*              */
             } TIOR_1;                          /*              */
       _UBYTE wk15[1];                          /*              */
       union {                                  /* TIER_1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    _UBYTE :1;                  /*              */
                    _UBYTE TCIEU:1;             /*   TCIEU      */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE :2;                  /*              */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    } BIT;                      /*              */
             } TIER_1;                          /*              */
       union {                                  /* TSR_1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    _UBYTE :1;                  /*              */
                    _UBYTE TCFU:1;              /*   TCFU       */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    } BIT;                      /*              */
             } TSR_1;                           /*              */
       union {                                  /* TCNT_1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_1;                          /*              */
       union {                                  /* TGRA_1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_1;                          /*              */
       union {                                  /* TGRB_1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_1;                          /*              */
       _UBYTE wk16[4];                          /*              */
       union {                                  /* TICCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE I2BE:1;              /*   I2BE       */
                    _UBYTE I2AE:1;              /*   I2AE       */
                    _UBYTE I1BE:1;              /*   I1BE       */
                    _UBYTE I1AE:1;              /*   I1AE       */
                    } BIT;                      /*              */
             } TICCR;                           /*              */
};                                              /*              */
#endif

struct st_cmt {                                 /* struct CMT   */
       union {                                  /* CMSTR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :14;                 /*              */
                    _UWORD STR1:1;              /*   STR1       */
                    _UWORD STR0:1;              /*   STR0       */
                    } BIT;                      /*              */
             } CMSTR;                           /*              */
       union {                                  /* CMCSR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD CMF:1;               /*   CMF        */
                    _UWORD CMIE:1;              /*   CMIE       */
                    _UWORD :4;                  /*              */
                    _UWORD CKS:2;               /*   CKS        */
                    } BIT;                      /*              */
             } CMCSR0;                          /*              */
       union {                                  /* CMCNT0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } CMCNT0;                          /*              */
       union {                                  /* CMCOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } CMCOR0;                          /*              */
       union {                                  /* CMCSR1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD CMF:1;               /*   CMF        */
                    _UWORD CMIE:1;              /*   CMIE       */
                    _UWORD :4;                  /*              */
                    _UWORD CKS:2;               /*   CKS        */
                    } BIT;                      /*              */
             } CMCSR1;                          /*              */
       union {                                  /* CMCNT1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } CMCNT1;                          /*              */
       union {                                  /* CMCOR1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } CMCOR1;                          /*              */
};                                              /*              */
union un_wdt {                                  /* union WDT    */
             struct {                           /* Read  Access */
                    union {                     /* WTCSR        */
                          _UBYTE BYTE;          /*  Byte Access */
                          struct {              /*  Bit  Access */
                                 _UBYTE IOVF:1; /*    IOVF      */
                                 _UBYTE WTIT:1; /*    WT/IT     */
                                 _UBYTE TME:1;  /*    TME       */
                                 _UBYTE :2;     /*              */
                                 _UBYTE CKS:3;  /*    CKS       */
                                 } BIT;         /*              */
                          } WTCSR;              /*              */
                    _UBYTE wk1;                 /*              */
                    _UBYTE WTCNT;               /* WTCNT        */
                    _UBYTE wk2;                 /*              */
                    union {                     /* WRCSR        */
                          _UBYTE BYTE;          /*  Byte Access */
                          struct {              /*  Bit  Access */
                                 _UBYTE WOVF:1; /*    WOVF      */
                                 _UBYTE RSTE:1; /*    RSTE      */
                                 _UBYTE RSTS:1; /*    RSTS      */
                                 _UBYTE :5;     /*              */
                                 } BIT;         /*              */
                          } WRCSR;              /*              */
                    } READ;                     /*              */
             struct {                           /* Write Access */
                    _UWORD WTCSR;               /* WTCSR        */
                    _UWORD WTCNT;               /* WTCNT        */
                    _UWORD WRCSR;               /* WRCSR        */
                    } WRITE;                    /*              */
};                                              /*              */
struct st_rtc {                                 /* struct RTC   */
       union {                                  /* R64CNT       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE _1Hz:1;              /*   _1Hz       */
                    _UBYTE _2Hz:1;              /*   _2Hz       */
                    _UBYTE _4Hz:1;              /*   _4Hz       */
                    _UBYTE _8Hz:1;              /*   _8Hz       */
                    _UBYTE _16Hz:1;             /*   _16Hz      */
                    _UBYTE _32Hz:1;             /*   _32Hz      */
                    _UBYTE _64Hz:1;             /*   _64Hz      */
                    } BIT;                      /*              */
             } R64CNT;                          /*              */
       _UBYTE wk0[1];                           /*              */
       _UBYTE RSECCNT;                          /* RSECCNT      */
       _UBYTE wk1[1];                           /*              */
       _UBYTE RMINCNT;                          /* RMINCNT      */
       _UBYTE wk2[1];                           /*              */
       _UBYTE RHRCNT;                           /* RHRCNT       */
       _UBYTE wk3[1];                           /*              */
       _UBYTE RWKCNT;                           /* RWKCNT       */
       _UBYTE wk4[1];                           /*              */
       _UBYTE RDAYCNT;                          /* RDAYCNT      */
       _UBYTE wk5[1];                           /*              */
       _UBYTE RMONCNT;                          /* RMONCNT      */
       _UBYTE wk6[1];                           /*              */
       _UWORD RYRCNT;                           /* RYRCNT       */
       union {                                  /* RSECAR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ENB:1;               /*   ENB        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RSECAR;                          /*              */
       _UBYTE wk7[1];                           /*              */
       union {                                  /* RMINAR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ENB:1;               /*   ENB        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RMINAR;                          /*              */
       _UBYTE wk8[1];                           /*              */
       union {                                  /* RHRAR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ENB:1;               /*   ENB        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RHRAR;                           /*              */
       _UBYTE wk9[1];                           /*              */
       union {                                  /* RWKAR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ENB:1;               /*   ENB        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RWKAR;                           /*              */
       _UBYTE wk10[1];                          /*              */
       union {                                  /* RDAYAR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ENB:1;               /*   ENB        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RDAYAR;                          /*              */
       _UBYTE wk11[1];                          /*              */
       union {                                  /* RMONAR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ENB:1;               /*   ENB        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RMONAR;                          /*              */
       _UBYTE wk12[1];                          /*              */
       union {                                  /* RCR1         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CF:1;                /*   CF         */
                    _UBYTE :2;                  /*              */
                    _UBYTE CIE:1;               /*   CIE        */
                    _UBYTE AIE:1;               /*   AIE        */
                    _UBYTE :2;                  /*              */
                    _UBYTE AF:1;                /*   AF         */
                    } BIT;                      /*              */
             } RCR1;                            /*              */
       _UBYTE wk13[1];                          /*              */
       union {                                  /* RCR2         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE PEF:1;               /*   PEF        */
                    _UBYTE PES:3;               /*   PES        */
                    _UBYTE RTCEN:1;             /*   RTCEN      */
                    _UBYTE ADJ:1;               /*   ADJ        */
                    _UBYTE RESET:1;             /*   RESET      */
                    _UBYTE START:1;             /*   START      */
                    } BIT;                      /*              */
             } RCR2;                            /*              */
       _UBYTE wk14[1];                          /*              */
       _UWORD RYRAR;                            /* RYRAR        */
       _UBYTE wk15[2];                          /*              */
       union {                                  /* RCR3         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ENB:1;               /*   ENB        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RCR3;                            /*              */
       _UBYTE wk16[1];                          /*              */
       union {                                  /* RCR5         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE RCKSEL:2;            /*   RCKSEL     */
                    } BIT;                      /*              */
             } RCR5;                            /*              */
       _UBYTE wk17[2];                          /*              */
       _UBYTE wk18[1];                          /*              */
       union {                                  /* RFRH         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SEL64:1;             /*   SEL64      */
                    _UWORD :12;                 /*              */
                    _UWORD RFC18:1;             /*   RFC[18]    */
                    _UWORD RFC17:1;             /*   RFC[17]    */
                    _UWORD RFC16:1;             /*   RFC[16]    */
                    } BIT;                      /*              */
             } RFRH;                            /*              */
       union {                                  /* RFRL         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD RFC15:1;             /*   RFC[15]    */
                    _UWORD RFC14:1;             /*   RFC[14]    */
                    _UWORD RFC13:1;             /*   RFC[13]    */
                    _UWORD RFC12:1;             /*   RFC[12]    */
                    _UWORD RFC11:1;             /*   RFC[11]    */
                    _UWORD RFC10:1;             /*   RFC[10]    */
                    _UWORD RFC9:1;              /*   RFC[9]     */
                    _UWORD RFC8:1;              /*   RFC[8]     */
                    _UWORD RFC7:1;              /*   RFC[7]     */
                    _UWORD RFC6:1;              /*   RFC[6]     */
                    _UWORD RFC5:1;              /*   RFC[5]     */
                    _UWORD RFC4:1;              /*   RFC[4]     */
                    _UWORD RFC3:1;              /*   RFC[3]     */
                    _UWORD RFC2:1;              /*   RFC[2]     */
                    _UWORD RFC1:1;              /*   RFC[1]     */
                    _UWORD RFC0:1;              /*   RFC[0]     */
                    } BIT;                      /*              */
             } RFRL;                            /*              */
};                                              /*              */
	#if	0
struct st_scif02346 {                           /* struct SCIF  */
       union {                                  /* SCSMR_0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD CA:1;                /*   C/A        */
                    _UWORD CHR:1;               /*   CHR        */
                    _UWORD PE:1;                /*   PE         */
                    _UWORD OE:1;                /*   O/E        */
                    _UWORD STOP:1;              /*   STOP       */
                    _UWORD :1;                  /*              */
                    _UWORD CKS:2;               /*   CKS        */
                    } BIT;                      /*              */
             } SCSMR;                           /*              */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* SCBRR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCBRR;                           /*              */
       _UBYTE wk1[3];                           /*              */
       union {                                  /* SCSCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TIE:1;               /*   TIE        */
                    _UWORD RIE:1;               /*   RIE        */
                    _UWORD TE:1;                /*   TE         */
                    _UWORD RE:1;                /*   RE         */
                    _UWORD REIE:1;              /*   REIE       */
                    _UWORD :1;                  /*              */
                    _UWORD CKE:2;               /*   CKE        */
                    } BIT;                      /*              */
             } SCSCR;                           /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* SCFTDR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCFTDR;                          /*              */
       _UBYTE wk3[3];                           /*              */
       union {                                  /* SCFSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PERN:4;              /*   PERN       */
                    _UWORD FERN:4;              /*   FERN       */
                    _UWORD ER:1;                /*   ER         */
                    _UWORD TEND:1;              /*   TEND       */
                    _UWORD TDFE:1;              /*   TDFE       */
                    _UWORD BRK:1;               /*   BRK        */
                    _UWORD FER:1;               /*   FER        */
                    _UWORD PER:1;               /*   PER        */
                    _UWORD RDF:1;               /*   RDF        */
                    _UWORD DR:1;                /*   DR         */
                    } BIT;                      /*              */
             } SCFSR;                           /*              */
       _UBYTE wk4[2];                           /*              */
       union {                                  /* SCFRDR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCFRDR;                          /*              */
       _UBYTE wk5[3];                           /*              */
       union {                                  /* SCFCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :5;                  /*              */
                    _UWORD RSTRG:3;             /*   RSTRG      */
                    _UWORD RTRG:2;              /*   RTRG       */
                    _UWORD TTRG:2;              /*   TTRG       */
                    _UWORD MCE:1;               /*   MCE        */
                    _UWORD TFRST:1;             /*   TFRST      */
                    _UWORD RFRST:1;             /*   RFRST      */
                    _UWORD LOOP:1;              /*   LOOP       */
                    } BIT;                      /*              */
             } SCFCR;                           /*              */
       _UBYTE wk6[2];                           /*              */
       union {                                  /* SCFDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD T:5;                 /*   T          */
                    _UWORD :3;                  /*              */
                    _UWORD R:5;                 /*   R          */
                    } BIT;                      /*              */
             } SCFDR;                           /*              */
       _UBYTE wk7[2];                           /*              */
       union {                                  /* SCSPTR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :12;                 /*              */
                    _UWORD SCKIO:1;             /*   SCKIO      */
                    _UWORD SCKDT:1;             /*   SCKDT      */
                    _UWORD SPB2IO:1;            /*   SPB2IO     */
                    _UWORD SPB2DT:1;            /*   SPB2DT     */
                    } BIT;                      /*              */
             } SCSPTR;                          /*              */
       _UBYTE wk8[2];                           /*              */
       union {                                  /* SCLSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :15;                 /*              */
                    _UWORD ORER:1;              /*   ORER       */
                    } BIT;                      /*              */
             } SCLSR;                           /*              */
       _UBYTE wk9[2];                           /*              */
       union {                                  /* SCEMR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD BGDM:1;              /*   BGDM       */
                    _UWORD :6;                  /*              */
                    _UWORD ABCS:1;              /*   ABCS       */
                    } BIT;                      /*              */
             } SCEMR;                           /*              */
};                                              /*              */
struct st_scif157 {                             /* struct SCIF  */
       union {                                  /* SCSMR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD CA:1;                /*   C/A        */
                    _UWORD CHR:1;               /*   CHR        */
                    _UWORD PE:1;                /*   PE         */
                    _UWORD OE:1;                /*   O/E        */
                    _UWORD STOP:1;              /*   STOP       */
                    _UWORD :1;                  /*              */
                    _UWORD CKS:2;               /*   CKS        */
                    } BIT;                      /*              */
             } SCSMR;                           /*              */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* SCBRR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCBRR;                           /*              */
       _UBYTE wk1[3];                           /*              */
       union {                                  /* SCSCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TIE:1;               /*   TIE        */
                    _UWORD RIE:1;               /*   RIE        */
                    _UWORD TE:1;                /*   TE         */
                    _UWORD RE:1;                /*   RE         */
                    _UWORD REIE:1;              /*   REIE       */
                    _UWORD :1;                  /*              */
                    _UWORD CKE:2;               /*   CKE        */
                    } BIT;                      /*              */
             } SCSCR  ;                         /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* SCFTDR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCFTDR;                          /*              */
       _UBYTE wk3[3];                           /*              */
       union {                                  /* SCFSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PERN:4;              /*   PERN       */
                    _UWORD FERN:4;              /*   FERN       */
                    _UWORD ER:1;                /*   ER         */
                    _UWORD TEND:1;              /*   TEND       */
                    _UWORD TDFE:1;              /*   TDFE       */
                    _UWORD BRK:1;               /*   BRK        */
                    _UWORD FER:1;               /*   FER        */
                    _UWORD PER:1;               /*   PER        */
                    _UWORD RDF:1;               /*   RDF        */
                    _UWORD DR:1;                /*   DR         */
                    } BIT;                      /*              */
             } SCFSR  ;                         /*              */
       _UBYTE wk4[2];                           /*              */
       union {                                  /* SCFRDR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCFRDR;                          /*              */
       _UBYTE wk5[3];                           /*              */
       union {                                  /* SCFCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :5;                  /*              */
                    _UWORD RSTRG:3;             /*   RSTRG      */
                    _UWORD RTRG:2;              /*   RTRG       */
                    _UWORD TTRG:2;              /*   TTRG       */
                    _UWORD MCE:1;               /*   MCE        */
                    _UWORD TFRST:1;             /*   TFRST      */
                    _UWORD RFRST:1;             /*   RFRST      */
                    _UWORD LOOP:1;              /*   LOOP       */
                    } BIT;                      /*              */
             } SCFCR;                           /*              */
       _UBYTE wk6[2];                           /*              */
       union {                                  /* SCFDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD T:5;                 /*   T          */
                    _UWORD :3;                  /*              */
                    _UWORD R:5;                 /*   R          */
                    } BIT;                      /*              */
             } SCFDR;                           /*              */
       _UBYTE wk7[2];                           /*              */
       union {                                  /* SCSPTR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD RTSIO:1;             /*   RTSIO      */
                    _UWORD RTSDT:1;             /*   RTSDT      */
                    _UWORD CTSIO:1;             /*   CTSIO      */
                    _UWORD CTSDT:1;             /*   CTSDT      */
                    _UWORD SCKIO:1;             /*   SCKIO      */
                    _UWORD SCKDT:1;             /*   SCKDT      */
                    _UWORD SPB2IO:1;            /*   SPB2IO     */
                    _UWORD SPB2DT:1;            /*   SPB2DT     */
                    } BIT;                      /*              */
             } SCSPTR;                          /*              */
       _UBYTE wk8[2];                           /*              */
       union {                                  /* SCLSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :15;                 /*              */
                    _UWORD ORER:1;              /*   ORER       */
                    } BIT;                      /*              */
             } SCLSR;                           /*              */
       _UBYTE wk9[2];                           /*              */
       union {                                  /* SCEMR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD BGDM:1;              /*   BGDM       */
                    _UWORD :6;                  /*              */
                    _UWORD ABCS:1;              /*   ABCS       */
                    } BIT;                      /*              */
             } SCEMR;                           /*              */
};                                              /*              */
	#endif
struct st_rspi {                                /* struct RSPI  */
       union {                                  /* SPCR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SPRIE:1;             /*   SPRIE      */
                    _UBYTE SPE:1;               /*   SPE        */
                    _UBYTE SPTIE:1;             /*   SPTIE      */
                    _UBYTE SPEIE:1;             /*   SPEIE      */
                    _UBYTE MSTR:1;              /*   MSTR       */
                    _UBYTE MODFEN:1;            /*   MODFEN     */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } SPCR;                            /*              */
       union {                                  /* SSLP         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE SSL0P:1;             /*   SSL0P      */
                    } BIT;                      /*              */
             } SSLP;                            /*              */
       union {                                  /* SPPCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE MOIFE:1;             /*   MOIFE      */
                    _UBYTE MOIFV:1;             /*   MOIFV      */
                    _UBYTE :3;                  /*              */
                    _UBYTE SPLP:1;              /*   SPLP       */
                    } BIT;                      /*              */
             } SPPCR;                           /*              */
       union {                                  /* SPSR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SPRF:1;              /*   SPRF       */
                    _UBYTE TEND:1;              /*   TEND       */
                    _UBYTE SPTEF:1;             /*   SPTEF      */
                    _UBYTE :2;                  /*              */
                    _UBYTE MODF:1;              /*   MODF       */
                    _UBYTE :1;                  /*              */
                    _UBYTE OVRF:1;              /*   OVRF       */
                    } BIT;                      /*              */
             } SPSR;                            /*              */
       union {                                  /* SPDR         */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD;                       /*  Word Access */
             _UBYTE BYTE;                       /*  Byte Access */
             } SPDR;                            /*              */
       union {                                  /* SPSCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE SPSLN:2;             /*   SPSLN      */
                    } BIT;                      /*              */
             } SPSCR;                           /*              */
       union {                                  /* SPSSR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE SPCP:2;              /*   SPCP       */
                    } BIT;                      /*              */
             } SPSSR;                           /*              */
       union {                                  /* SPBR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SPR:8;               /*   SPR        */
                    } BIT;                      /*              */
             } SPBR;                            /*              */
       union {                                  /* SPDCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TXDMY:1;             /*   TXDMY      */
                    _UBYTE SPLW:2;              /*   SPLW       */
                    _UBYTE :5;                  /*              */
                    } BIT;                      /*              */
             } SPDCR;                           /*              */
       union {                                  /* SPCKD        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE SCKDL:3;             /*   SCKDL      */
                    } BIT;                      /*              */
             } SPCKD;                           /*              */
       union {                                  /* SSLND        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE SLNDL:3;             /*   SLNDL      */
                    } BIT;                      /*              */
             } SSLND;                           /*              */
       union {                                  /* SPND         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE SPNDL:3;             /*   SPNDL      */
                    } BIT;                      /*              */
             } SPND;                            /*              */
       _UBYTE wk0[1];                           /*              */
       union {                                  /* SPCMD0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD :3;                  /*              */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD0;                          /*              */
       union {                                  /* SPCMD1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD :3;                  /*              */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD1 ;                         /*              */
       union {                                  /* SPCMD2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD :3;                  /*              */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD2 ;                         /*              */
       union {                                  /* SPCMD3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD :3;                  /*              */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD3 ;                         /*              */
       _UBYTE wk1[8];                           /*              */
       union {                                  /* SPBFCR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TXRST:1;             /*   TXRST      */
                    _UBYTE RXRST:1;             /*   RXRST      */
                    _UBYTE TXTRG:2;             /*   TXTRG      */
                    _UBYTE :1;                  /*              */
                    _UBYTE RXTRG:3;             /*   RXTRG      */
                    } BIT;                      /*              */
             } SPBFCR;                          /*              */
       _UBYTE wk2[1];                           /*              */
       union {                                  /* SPBFDR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :4;                  /*              */
                    _UWORD T:4 ;                /*   T          */
                    _UWORD :2;                  /*              */
                    _UWORD R:6;                 /*   R          */
                    } BIT;                      /*              */
             } SPBFDR;                          /*              */
};                                              /*              */
	#if	0
struct st_iic3 {                                /* struct IIC3  */
       union {                                  /* ICCR1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ICE:1;               /*   ICE        */
                    _UBYTE RCVD:1;              /*   RCVD       */
                    _UBYTE MST:1;               /*   MST        */
                    _UBYTE TRS:1;               /*   TRS        */
                    _UBYTE CKS:4;               /*   CKS        */
                    } BIT;                      /*              */
             } ICCR1;                           /*              */
       union {                                  /* ICCR2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BBSY:1;              /*   BBSY       */
                    _UBYTE SCP:1;               /*   SCP        */
                    _UBYTE SDAO:1;              /*   SDAO       */
                    _UBYTE SDAOP:1;             /*   SDAOP      */
                    _UBYTE SCLO:1;              /*   SCLO       */
                    _UBYTE :1;                  /*              */
                    _UBYTE IICRST:1;            /*   IICRST     */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } ICCR2;                           /*              */
       union {                                  /* ICMR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MLS:1;               /*   MLS        */
                    _UBYTE :3;                  /*              */
                    _UBYTE BCWP:1;              /*   BCWP       */
                    _UBYTE BC:3;                /*   BC         */
                    } BIT;                      /*              */
             } ICMR;                            /*              */
       union {                                  /* ICIER        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TIE:1;               /*   TIE        */
                    _UBYTE TEIE:1;              /*   TEIE       */
                    _UBYTE RIE:1;               /*   RIE        */
                    _UBYTE NAKIE:1;             /*   NAKIE      */
                    _UBYTE STIE:1;              /*   STIE       */
                    _UBYTE ACKE:1;              /*   ACKE       */
                    _UBYTE ACKBR:1;             /*   ACKBR      */
                    _UBYTE ACKBT:1;             /*   ACKBT      */
                    } BIT;                      /*              */
             } ICIER;                           /*              */
       union {                                  /* ICSR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TDRE:1;              /*   TDRE       */
                    _UBYTE TEND:1;              /*   TEND       */
                    _UBYTE RDRF:1;              /*   RDRF       */
                    _UBYTE NACKF:1;             /*   NACKF      */
                    _UBYTE STOP:1;              /*   STOP       */
                    _UBYTE ALOVE:1;             /*   AL/OVE     */
                    _UBYTE AAS:1;               /*   AAS        */
                    _UBYTE ADZ:1;               /*   ADZ        */
                    } BIT;                      /*              */
             } ICSR;                            /*              */
       union {                                  /* SAR          */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SVA:7;               /*   SVA        */
                    _UBYTE FS:1;                /*   FS         */
                    } BIT;                      /*              */
             } SAR;                             /*              */
       _UBYTE ICDRT;                            /* ICDRT        */
       _UBYTE ICDRR;                            /* ICDRR        */
       union {                                  /* NF2CYC       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :3;                  /*              */
                    _UBYTE CKS4:1;              /*   CKS4       */
                    _UBYTE :2;                  /*              */
                    _UBYTE PRS:1;               /*   PRS        */
                    _UBYTE NF2CYC:1;            /*   NF2CYC     */
                    } BIT;                      /*              */
             } NF2CYC;                          /*              */
};                                              /*              */
	#endif
struct st_ssif {                                /* struct SSIF  */
       union {                                  /* SSICR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :1;                 /*              */
                    _UDWORD CKS:1;              /*   CKS        */
                    _UDWORD TUIEN:1;            /*   TUIEN      */
                    _UDWORD TOIEN:1;            /*   TOIEN      */
                    _UDWORD RUIEN:1;            /*   RUIEN      */
                    _UDWORD ROIEN:1;            /*   ROIEN      */
                    _UDWORD IIEN:1;             /*   IIEN       */
                    _UDWORD :1;                 /*              */
                    _UDWORD CHNL:2;             /*   CHNL       */
                    _UDWORD DWL:3;              /*   DWL        */
                    _UDWORD SWL:3;              /*   SWL        */
                    _UDWORD SCKD:1;             /*   SCKD       */
                    _UDWORD SWSD:1;             /*   SWSD       */
                    _UDWORD SCKP:1;             /*   SCKP       */
                    _UDWORD SWSP:1;             /*   SWSP       */
                    _UDWORD SPDP:1;             /*   SPDP       */
                    _UDWORD SDTA:1;             /*   SDTA       */
                    _UDWORD PDTA:1;             /*   PDTA       */
                    _UDWORD DEL:1;              /*   DEL        */
                    _UDWORD CKDV:4;             /*   CKDV       */
                    _UDWORD MUEN:1;             /*   MUEN       */
                    _UDWORD :1;                 /*              */
                    _UDWORD TEN:1;              /*   TEN        */
                    _UDWORD REN:1;              /*   REN        */
                    } BIT;                      /*              */
             } SSICR;                           /*              */
       union {                                  /* SSISR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE HH;                  /*   High, High */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE LL;                  /*   Low, Low   */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD :2;                 /*              */
                    _UDWORD TUIRQ:1;            /*   TUIRQ      */
                    _UDWORD TOIRQ:1;            /*   TOIRQ      */
                    _UDWORD RUIRQ:1;            /*   RUIRQ      */
                    _UDWORD ROIRQ:1;            /*   ROIRQ      */
                    _UDWORD IIRQ:1;             /*   IIRQ       */
                    _UDWORD :18;                /*              */
                    _UDWORD TCHNO:2;            /*   TCHNO      */
                    _UDWORD TSWNO:1;            /*   TSWNO      */
                    _UDWORD RCHNO:2;            /*   RCHNO      */
                    _UDWORD RSWNO:1;            /*   RSWNO      */
                    _UDWORD IDST:1;             /*   IDST       */
                    } BIT;                      /*              */
             } SSISR;                           /*              */
       _UBYTE wk0[8];                           /*              */
       union {                                  /* SSIFCR       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :24;                /*              */
                    _UDWORD TTRG:2;             /*   TTRG       */
                    _UDWORD RTRG:2;             /*   RTRG       */
                    _UDWORD TIE:1;              /*   TIE        */
                    _UDWORD RIE:1;              /*   RIE        */
                    _UDWORD TFRST:1;            /*   TFRST      */
                    _UDWORD RFRST:1;            /*   RFRST      */
                    } BIT;                      /*              */
             } SSIFCR;                          /*              */
       union {                                  /* SSIFSR       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :4;                 /*              */
                    _UDWORD TDC:4;              /*   TDC        */
                    _UDWORD :7;                 /*              */
                    _UDWORD TDE:1;              /*   TDE        */
                    _UDWORD :4;                 /*              */
                    _UDWORD RDC:4;              /*   RDC        */
                    _UDWORD :7;                 /*              */
                    _UDWORD RDF:1;              /*   RDF        */
                    } BIT;                      /*              */
             } SSIFSR;                          /*              */
       _UDWORD SSIFTDR;                         /* SSIFTDR      */
       _UDWORD SSIFRDR;                         /* SSIFRDR      */
       union {                                  /* SSITDMR      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :23;                /*              */
                    _UDWORD CONT:1;             /*   CONT       */
                    _UDWORD :7;                 /*              */
                    _UDWORD TDM:1;              /*   TDM        */
                    } BIT;                      /*              */
             } SSITDMR;                         /*              */
};                                              /*              */
struct st_siof {                                /* struct SIOF  */
       union {                                  /* SIMDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TRMD:2;              /*   TRMD       */
                    _UWORD SYNCAT:1;            /*   SYNCAT     */
                    _UWORD REDG:1;              /*   REDG       */
                    _UWORD FL:4;                /*   FL         */
                    _UWORD TXDIZ:1;             /*   TXDIZ      */
                    _UWORD :1;                  /*              */
                    _UWORD SYNCAC:1;            /*   SYNCAC     */
                    _UWORD SYNCDL:1;            /*   SYNCDL     */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } SIMDR;                           /*              */
       union {                                  /* SISCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD MSSEL:1;             /*   MSSEL      */
                    _UWORD :2;                  /*              */
                    _UWORD BRPS:5;              /*   BRPS       */
                    _UWORD :5;                  /*              */
                    _UWORD BRDV:3;              /*   BRDV       */
                    } BIT;                      /*              */
             } SISCR;                           /*              */
       union {                                  /* SITDAR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TDLE:1;              /*   TDLE       */
                    _UWORD :3;                  /*              */
                    _UWORD TDLA:4;              /*   TDLA       */
                    _UWORD TDRE:1;              /*   TDRE       */
                    _UWORD TLREP:1;             /*   TLREP      */
                    _UWORD :2;                  /*              */
                    _UWORD TDRA:4;              /*   TDRA       */
                    } BIT;                      /*              */
             } SITDAR;                          /*              */
       union {                                  /* SIRDAR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD RDLE:1;              /*   RDLE       */
                    _UWORD :3;                  /*              */
                    _UWORD RDLA:4;              /*   RDLA       */
                    _UWORD RDRE:1;              /*   RDRE       */
                    _UWORD :3;                  /*              */
                    _UWORD RDRA:4;              /*   RDRA       */
                    } BIT;                      /*              */
             } SIRDAR;                          /*              */
       _UBYTE wk0[4];                           /*              */
       union {                                  /* SICTR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKE:1;              /*   SCKE       */
                    _UWORD FSE:1;               /*   FSE        */
                    _UWORD :4;                  /*              */
                    _UWORD TXE:1;               /*   TXE        */
                    _UWORD RXE:1;               /*   RXE        */
                    _UWORD :6;                  /*              */
                    _UWORD TXRST:1;             /*   TXRST      */
                    _UWORD RXRST:1;             /*   RXRST      */
                    } BIT;                      /*              */
             } SICTR;                           /*              */
       _UBYTE wk1[2];                           /*              */
       union {                                  /* SIFCTR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TFWM:3;              /*   TFWM       */
                    _UWORD TFUA:5;              /*   TFUA       */
                    _UWORD RFWM:3;              /*   RFWM       */
                    _UWORD RFUA:5;              /*   RFUA       */
                    } BIT;                      /*              */
             } SIFCTR;                          /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* SISTR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :2;                  /*              */
                    _UWORD TFEMP:1;             /*   TFEMP      */
                    _UWORD TDREQ:1;             /*   TDREQ      */
                    _UWORD :2;                  /*              */
                    _UWORD RFFUL:1 ;            /*   RFFUL      */
                    _UWORD RDREQ:1;             /*   RDREQ      */
                    _UWORD :3;                  /*              */
                    _UWORD FSERR:1;             /*   FSERR      */
                    _UWORD TFOVF:1;             /*   TFOVF      */
                    _UWORD TFUDF:1;             /*   TFUDF      */
                    _UWORD RFUDF:1;             /*   RFUDF      */
                    _UWORD RFOVF:1;             /*   RFOVF      */
                    } BIT;                      /*              */
             } SISTR;                           /*              */
       union {                                  /* SIIER        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TDMAE:1;             /*   TDMAE      */
                    _UWORD :1;                  /*              */
                    _UWORD TFEMPE:1;            /*   TFEMPE     */
                    _UWORD TDREQE:1;            /*   TDREQE     */
                    _UWORD RDMAE:1;             /*   RDMAE      */
                    _UWORD :1;                  /*              */
                    _UWORD RFFULE:1;            /*   RFFULE     */
                    _UWORD RDREQE:1;            /*   RDREQE     */
                    _UWORD :3;                  /*              */
                    _UWORD FSERRE:1;            /*   FSERRE     */
                    _UWORD TFOVFE:1;            /*   TFOVFE     */
                    _UWORD TFUDFE:1;            /*   TFUDFE     */
                    _UWORD RFUDFE:1;            /*   RFUDFE     */
                    _UWORD RFOVFE:1;            /*   RFOVFE     */
                    } BIT;                      /*              */
             } SIIER;                           /*              */
       _UBYTE wk3[8];                           /*              */
       union {                                  /* SITDR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD SITDL:16;            /*   SITDL      */
                    _UWORD SITDR:16;            /*   SITDR      */
                    } BIT;                      /*              */
             } SITDR;                           /*              */
       union {                                  /* SIRDR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             struct {                           /*  Bit Access  */
                    _UWORD SIRDL:16;            /*   SIRDL      */
                    _UWORD SIRDR:16;            /*   SIRDR      */
                    } BIT;                      /*              */
             } SIRDR;                           /*              */
};
union un_mb3116{                                /* MB31-MB16    */
      _UWORD WORD;                              /*  Word Access */
      struct {                                  /*  Bit Access  */
             _UWORD MB31:1;                     /*   MB31       */
             _UWORD MB30:1;                     /*   MB30       */
             _UWORD MB29:1;                     /*   MB29       */
             _UWORD MB28:1;                     /*   MB28       */
             _UWORD MB27:1;                     /*   MB27       */
             _UWORD MB26:1;                     /*   MB26       */
             _UWORD MB25:1;                     /*   MB25       */
             _UWORD MB24:1;                     /*   MB24       */
             _UWORD MB23:1;                     /*   MB23       */
             _UWORD MB22:1;                     /*   MB22       */
             _UWORD MB21:1;                     /*   MB21       */
             _UWORD MB20:1;                     /*   MB20       */
             _UWORD MB19:1;                     /*   MB19       */
             _UWORD MB18:1;                     /*   MB18       */
             _UWORD MB17:1;                     /*   MB17       */
             _UWORD MB16:1;                     /*   MB16       */
             } BIT;                             /*              */
};
union un_mb15_0{                                /* MB15-MB0     */
      _UWORD WORD;                              /*  Word Access */
      struct {                                  /*  Bit Access  */
             _UWORD MB15:1;                     /*   MB15       */
             _UWORD MB14:1;                     /*   MB14       */
             _UWORD MB13:1;                     /*   MB13       */
             _UWORD MB12:1;                     /*   MB12       */
             _UWORD MB11:1;                     /*   MB11       */
             _UWORD MB10:1;                     /*   MB10       */
             _UWORD MB9:1;                      /*   MB9        */
             _UWORD MB8:1;                      /*   MB8        */
             _UWORD MB7:1;                      /*   MB7        */
             _UWORD MB6:1;                      /*   MB6        */
             _UWORD MB5:1;                      /*   MB5        */
             _UWORD MB4:1;                      /*   MB4        */
             _UWORD MB3:1;                      /*   MB3        */
             _UWORD MB2:1;                      /*   MB2        */
             _UWORD MB1:1;                      /*   MB1        */
             _UWORD MB0:1;                      /*   MB0        */
             } BIT;                             /*              */
};
union un_mb15_1{                                /* MB15-MB1     */
      _UWORD WORD;                              /*  Word Access */
      struct {                                  /*  Bit Access  */
             _UWORD MB15:1;                     /*   MB15       */
             _UWORD MB14:1;                     /*   MB14       */
             _UWORD MB13:1;                     /*   MB13       */
             _UWORD MB12:1;                     /*   MB12       */
             _UWORD MB11:1;                     /*   MB11       */
             _UWORD MB10:1;                     /*   MB10       */
             _UWORD MB9:1;                      /*   MB9        */
             _UWORD MB8:1;                      /*   MB8        */
             _UWORD MB7:1;                      /*   MB7        */
             _UWORD MB6:1;                      /*   MB6        */
             _UWORD MB5:1;                      /*   MB5        */
             _UWORD MB4:1;                      /*   MB4        */
             _UWORD MB3:1;                      /*   MB3        */
             _UWORD MB2:1;                      /*   MB2        */
             _UWORD MB1:1;                      /*   MB1        */
             _UWORD :1;                         /*              */
             } BIT;                             /*              */
};
struct st_rcan {                                /* struct RCAN  */
       union {                                  /* MCR          */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD IDR  :1;             /*   IDR        */
                    _UWORD AHBO :1;             /*   AHBO       */
                    _UWORD      :3;             /*              */
                    _UWORD TST  :3;             /*   TST        */
                    _UWORD AWM  :1;             /*   AWM        */
                    _UWORD HTBO :1;             /*   HTBO       */
                    _UWORD SLPM :1;             /*   SLPM       */
                    _UWORD      :2;             /*              */
                    _UWORD MTP  :1;             /*   MTP        */
                    _UWORD HLTRQ:1;             /*   HLTRQ      */
                    _UWORD RSTRQ:1;             /*   RSTRQ      */
                    } BIT;                      /*              */
             } MCR;                             /*              */
       union {                                  /* GSR          */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :10;                 /*              */
                    _UWORD EPS:1;               /*   EPS        */
                    _UWORD HSS:1;               /*   HSS        */
                    _UWORD RS:1;                /*   RS         */
                    _UWORD MTPF:1;              /*   MTPF       */
                    _UWORD TRWF:1;              /*   TRWF       */
                    _UWORD BOF:1;               /*   BOF        */
                    } BIT;                      /*              */
             } GSR;                             /*              */
       union {                                  /* BCR1         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TSG1:4;              /*   TSG1       */
                    _UWORD :1;                  /*              */
                    _UWORD TSG2:3;              /*   TSG2       */
                    _UWORD :2;                  /*              */
                    _UWORD SJW:2;               /*   SJW        */
                    _UWORD :3;                  /*              */
                    _UWORD BSP:1;               /*   BSP        */
                    } BIT;                      /*              */
             } BCR1;                            /*              */
       union {                                  /* BCR0         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD BRP:8;               /*   BRP        */
                    } BIT;                      /*              */
             } BCR0;                            /*              */
       union {                                  /* IRR          */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TCMI1 :1;            /*   TCMI1      */
                    _UWORD TCMI0 :1;            /*   TCMI0      */
                    _UWORD TOI   :1;            /*   TOI        */
                    _UWORD BASMIF:1;            /*   BASMIF     */
                    _UWORD TCMI2 :1;            /*   TCMI2      */
                    _UWORD SNSMI :1;            /*   SNSMI      */
                    _UWORD MOOIF :1;            /*   MOOIF      */
                    _UWORD MBEIF :1;            /*   MBEIF      */
                    _UWORD OLF   :1;            /*   OLF        */
                    _UWORD BOFIF :1;            /*   BOFIF      */
                    _UWORD EPIF  :1;            /*   EPIF       */
                    _UWORD RECWIF:1;            /*   RECWIF     */
                    _UWORD TECWIF:1;            /*   TECWIF     */
                    _UWORD RFRIF :1;            /*   RFRIF      */
                    _UWORD DFRIF :1;            /*   DFRIF      */
                    _UWORD RSTIF :1;            /*   RSTIF      */
                    } BIT;                      /*              */
             } IRR;                             /*              */
       union {                                  /* IMR          */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TCMI1M:1;            /*   TCMI1M     */
                    _UWORD TCMI0M:1;            /*   TCMI0M     */
                    _UWORD TOIM  :1;            /*   TOIM       */
                    _UWORD BASMIM:1;            /*   BASMIM     */
                    _UWORD TCMI2M:1;            /*   TCMI2M     */
                    _UWORD SNSMIM:1;            /*   SNSMIM     */
                    _UWORD MOOIM :1;            /*   MOOIM      */
                    _UWORD MBEIM :1;            /*   MBEIM      */
                    _UWORD OLFM  :1;            /*   OLFM       */
                    _UWORD BOFIM :1;            /*   BOFIM      */
                    _UWORD EPIM  :1;            /*   EPIM       */
                    _UWORD RECWIM:1;            /*   RECWIM     */
                    _UWORD TECWIM:1;            /*   TECWIM     */
                    _UWORD RFRIM :1;            /*   RFRIM      */
                    _UWORD DFRIM :1;            /*   DFRIM      */
                    _UWORD RSTIM :1;            /*   RSTIM      */
                    } BIT;                      /*              */
             } IMR;                             /*              */
       union {                                  /* TEC_REC      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TEC:8;               /*   TEC        */
                    _UWORD REC:8;               /*   REC        */
                    } BIT;                      /*              */
             } TEC_REC  ;                       /*              */
       _UBYTE wk0[18];                          /*              */
       union{                                   /* TXPR0        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD MB31:1;             /*   MB31       */
                    _UDWORD MB30:1;             /*   MB30       */
                    _UDWORD MB29:1;             /*   MB29       */
                    _UDWORD MB28:1;             /*   MB28       */
                    _UDWORD MB27:1;             /*   MB27       */
                    _UDWORD MB26:1;             /*   MB26       */
                    _UDWORD MB25:1;             /*   MB25       */
                    _UDWORD MB24:1;             /*   MB24       */
                    _UDWORD MB23:1;             /*   MB23       */
                    _UDWORD MB22:1;             /*   MB22       */
                    _UDWORD MB21:1;             /*   MB21       */
                    _UDWORD MB20:1;             /*   MB20       */
                    _UDWORD MB19:1;             /*   MB19       */
                    _UDWORD MB18:1;             /*   MB18       */
                    _UDWORD MB17:1;             /*   MB17       */
                    _UDWORD MB16:1;             /*   MB16       */
                    _UDWORD MB15:1;             /*   MB15       */
                    _UDWORD MB14:1;             /*   MB14       */
                    _UDWORD MB13:1;             /*   MB13       */
                    _UDWORD MB12:1;             /*   MB12       */
                    _UDWORD MB11:1;             /*   MB11       */
                    _UDWORD MB10:1;             /*   MB10       */
                    _UDWORD MB9:1;              /*   MB9        */
                    _UDWORD MB8:1;              /*   MB8        */
                    _UDWORD MB7:1;              /*   MB7        */
                    _UDWORD MB6:1;              /*   MB6        */
                    _UDWORD MB5:1;              /*   MB5        */
                    _UDWORD MB4:1;              /*   MB4        */
                    _UDWORD MB3:1;              /*   MB3        */
                    _UDWORD MB2:1;              /*   MB2        */
                    _UDWORD MB1:1;              /*   MB1        */
                    } BIT;                      /*              */
             } TXPR0  ;                         /*              */
       _UBYTE wk1[4];                           /*              */
       union un_mb3116 TXCR1;                   /* TXCR1        */
       union un_mb15_1 TXCR0;                   /* TXCR0        */
       _UBYTE wk2[4];                           /*              */
       union un_mb3116 TXACK1;                  /* TXACK1       */
       union un_mb15_1 TXACK0;                  /* TXACK0       */
       _UBYTE wk3[4];                           /*              */
       union un_mb3116 ABACK1;                  /* ABACK1       */
       union un_mb15_1 ABACK0;                  /* ABACK0       */
       _UBYTE wk4[4];                           /*              */
       union un_mb3116 RXPR1;                   /* RXPR1        */
       union un_mb15_0 RXPR0;                   /* RXPR0        */
       _UBYTE wk5[4];                           /*              */
       union un_mb3116 RFPR1;                   /* RFPR1        */
       union un_mb15_0 RFPR0;                   /* RFPR0        */
       _UBYTE wk6[4];                           /*              */
       union un_mb3116 MBIMR1;                  /* MBIMR1       */
       union un_mb15_0 MBIMR0;                  /* MBIMR0       */
       _UBYTE wk7[4];                           /*              */
       union un_mb3116 UMSR1;                   /* UMSR1        */
       union un_mb15_0 UMSR0;                   /* UMSR0        */
       _UBYTE wk8[36];                          /*              */
       union {                                  /* TTCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TE:1;                /*   TE         */
                    _UWORD TS:1;                /*   TS         */
                    _UWORD CANC :1;             /*   CANC       */
                    _UWORD CME2:1;              /*   CME2       */
                    _UWORD CME1:1;              /*   CME1       */
                    _UWORD CME0:1;              /*   CME0       */
                    _UWORD :3;                  /*              */
                    _UWORD TCSC:1;              /*   TCSC       */
                    _UWORD TPSC :6;             /*   TPSC       */
                    } BIT;                      /*              */
             } TTCR0;                           /*              */
       _UBYTE wk9[2];                           /*              */
       union {                                  /* CMAX_TEW     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :5;                  /*              */
                    _UWORD CMAX:3;              /*   CMAX       */
                    _UWORD :4;                  /*              */
                    _UWORD TEW:4 ;              /*   TEW        */
                    } BIT;                      /*              */
             } CMAX_TEW;                        /*              */
       _UWORD RFTROFF;                          /* RFTROFF      */
       union {                                  /* TSR          */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :11;                 /*              */
                    _UWORD SNSM:1;              /*   SNSM       */
                    _UWORD TCMF2:1;             /*   TCMF2      */
                    _UWORD TCMF1:1;             /*   TCMF1      */
                    _UWORD TCMF0:1;             /*   TCMF0      */
                    _UWORD TO_NGR_ME:1;         /*   TO_NGR_ME  */
                    } BIT;                      /*              */
             } TSR;                             /*              */
       _UWORD CCR;                              /* CCR          */
       _UWORD TCNTR;                            /* TCNTR        */
       _UBYTE wk10[2];                          /*              */
       _UWORD CYCTR;                            /* CYCTR        */
       _UBYTE wk11[2];                          /*              */
       _UWORD RFMK;                             /* RFMK         */
       _UBYTE wk12[2];                          /*              */
       _UWORD TCMR0;                            /* TCMR0        */
       _UBYTE wk13[2];                          /*              */
       _UWORD TCMR1;                            /* TCMR1        */
       _UBYTE wk14[2];                          /*              */
       _UWORD TCMR2;                            /* TCMR2        */
       _UBYTE wk15[2];                          /*              */
       _UWORD TTTSEL;                           /* TTTSEL       */
       _UBYTE wk16[90];                         /*              */
       struct {
             union {                            /* CONTROL0     */
                   _UDWORD LONG;                /*  Long Access */
                   struct {                     /*  Word Access */
                          _UWORD H;             /*   High       */
                          _UWORD L;             /*   Low        */
                          } WORD;               /*              */
                   struct {                     /*  Bit Access  */
                          _UDWORD IDE:1;        /*   IDE        */
                          _UDWORD RTR:1;        /*   RTR        */
                          _UDWORD :1;           /*              */
                          _UDWORD STDID:11;     /*   STDID      */
                          _UDWORD EXTID:18;     /*   EXTID      */
                          } BIT;                /*              */
                   } CONTROL0;                  /*              */
             union {                            /* LAFM         */
                   _UDWORD LONG;                /*  Long Access */
                   struct {                     /*  Word Access */
                          _UWORD H;             /*   High       */
                          _UWORD L;             /*   Low        */
                          } WORD;               /*              */
                   struct {                     /*  Bit Access  */
                          _UDWORD IDE:1;        /*   IDE        */
                          _UDWORD :2;           /*              */
                          _UDWORD STDID_LAFM:11;/*   STDID_LAFM */
                          _UDWORD EXTID_LAFM:18;/*   EXTID_LAFM */
                          } BIT;                /*              */
                   } LAFM;                      /*              */
             _UBYTE MSG_DATA[8];                /* MSG_DATA     */
             union {                            /* CONTROL1     */
                   _UWORD WORD;                 /*  Word Access */
                   struct {                     /*  Byte Access */
                          _UBYTE H;             /*   High       */
                          _UBYTE L;             /*   Low        */
                          } BYTE;               /*              */
                   struct {                     /*  Bit Access  */
                          _UWORD :2;            /*              */
                          _UWORD NMC:1;         /*   NMC        */
                          _UWORD ATX:1;         /*   ATX        */
                          _UWORD DART:1;        /*   DART       */
                          _UWORD MBC:3;         /*   MBC        */
                          _UWORD :4;            /*              */
                          _UWORD DLC:4;         /*   DLC        */
                          } BIT;                /*              */
                   } CONTROL1;                  /*              */
             _UWORD TIMESTAMP;                  /* TIMESTAMP    */
             _UWORD TTT;                        /* TTT          */
             union {                            /* TTC          */
                   _UWORD WORD;                 /*  Word Access */
                   struct {                     /*  Bit Access  */
                          _UWORD TTW:2;         /*   TTW        */
                          _UWORD Offset:6;      /*   Offset     */
                          _UWORD :5;            /*              */
                          _UWORD rep_factor:3;  /*   rep_factor */
                          } BIT;                /*              */
                   } TTC;                       /*              */
             _UBYTE wk17[8];                      /*              */
       } MB[32];                                /*              */
};                                              /*              */
struct st_ieb {                                 /* struct IEB   */
       union {                                  /* IECTR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE IOL:1;               /*   IOL        */
                    _UBYTE DEE:1;               /*   DEE        */
                    _UBYTE :1;                  /*              */
                    _UBYTE RE:1;                /*   RE         */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } IECTR;                           /*              */
       union {                                  /* IECMR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE CMD:3;               /*   CMD        */
                    } BIT;                      /*              */
             } IECMR;                           /*              */
       union {                                  /* IEMCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SS:1;                /*   SS         */
                    _UBYTE RN:3;                /*   RN         */
                    _UBYTE CTL:4;               /*   CTL        */
                    } BIT;                      /*              */
             } IEMCR;                           /*              */
       union {                                  /* IEAR1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IARL4:4;             /*   IARL4      */
                    _UBYTE IMD:2;               /*   IMD        */
                    _UBYTE :1;                  /*              */
                    _UBYTE STE:1;               /*   STE        */
                    } BIT;                      /*              */
             } IEAR1;                           /*              */
       union {                                  /* IEAR2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IARU8:8;             /*   IARU8      */
                    } BIT;                      /*              */
             } IEAR2;                           /*              */
       union {                                  /* IESA1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ISAL4:4;             /*   ISAL4      */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } IESA1;                           /*              */
       union {                                  /* IESA2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ISAU8:8;             /*   ISAU8      */
                    } BIT;                      /*              */
             } IESA2;                           /*              */
       _UBYTE IETBFL;                           /* IETBFL       */
       _UBYTE wk0[1];                           /*              */
       union {                                  /* IEMA1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IMAL4:4;             /*   IMAL4      */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } IEMA1;                           /*              */
       union {                                  /* IEMA2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IMAU8:8;             /*   IMAU8      */
                    } BIT;                      /*              */
             } IEMA2;                           /*              */
       union {                                  /* IERCTL       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE RCTL:4;              /*   RCTL       */
                    } BIT;                      /*              */
             } IERCTL;                          /*              */
       _UBYTE IERBFL;                           /* IERBFL       */
       _UBYTE wk1[1];                           /*              */
       union {                                  /* IELA1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ILAL8:8;             /*   ILAL8      */
                    } BIT;                      /*              */
             } IELA1;                           /*              */
       union {                                  /* IELA2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE ILAU4:4;             /*   ILAU4      */
                    } BIT;                      /*              */
             } IELA2;                           /*              */
       union {                                  /* IEFLG        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CMX:1;               /*   CMX        */
                    _UBYTE MRQ:1;               /*   MRQ        */
                    _UBYTE SRQ:1;               /*   SRQ        */
                    _UBYTE SRE:1;               /*   SRE        */
                    _UBYTE LCK:1;               /*   LCK        */
                    _UBYTE :1;                  /*              */
                    _UBYTE RSS:1;               /*   RSS        */
                    _UBYTE GG:1;                /*   GG         */
                    } BIT;                      /*              */
             } IEFLG;                           /*              */
       union {                                  /* IETSR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE TXS:1;               /*   TXS        */
                    _UBYTE TXF:1;               /*   TXF        */
                    _UBYTE :1;                  /*              */
                    _UBYTE TXEAL:1;             /*   TXEAL      */
                    _UBYTE TXETTME:1;           /*   TXETTME    */
                    _UBYTE TXERO:1;             /*   TXERO      */
                    _UBYTE TXEACK:1;            /*   TXEACK     */
                    } BIT;                      /*              */
             } IETSR;                           /*              */
       union {                                  /* IEIET        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE TXSE:1;              /*   TXSE       */
                    _UBYTE TXFE:1;              /*   TXFE       */
                    _UBYTE :1;                  /*              */
                    _UBYTE TXEALE:1;            /*   TXEALE     */
                    _UBYTE TXETTMEE:1;          /*   TXETTMEE   */
                    _UBYTE TXEROE:1;            /*   TXEROE     */
                    _UBYTE TXEACKE:1;           /*   TXEACKE    */
                    } BIT;                      /*              */
             } IEIET;                           /*              */
       _UBYTE wk2[1];                           /*              */
       union {                                  /* IERSR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE RXBSY:1;             /*   RXBSY      */
                    _UBYTE RXS:1;               /*   RXS        */
                    _UBYTE RXF:1;               /*   RXF        */
                    _UBYTE RXEDE:1;             /*   RXEDE      */
                    _UBYTE RXEOVE:1;            /*   RXEOVE     */
                    _UBYTE RXERTME:1;           /*   RXERTME    */
                    _UBYTE RXEDLE:1;            /*   RXEDLE     */
                    _UBYTE RXEPE:1;             /*   RXEPE      */
                    } BIT;                      /*              */
             } IERSR;                           /*              */
       union {                                  /* IEIER        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE RXBSYE:1;            /*   RXBSYE     */
                    _UBYTE RXSE:1;              /*   RXSE       */
                    _UBYTE RXFE:1;              /*   RXFE       */
                    _UBYTE RXEDEE:1;            /*   RXEDEE     */
                    _UBYTE RXEOVEE:1;           /*   RXEOVEE    */
                    _UBYTE RXERTMEE:1;          /*   RXERTMEE   */
                    _UBYTE RXEDLEE:1;           /*   RXEDLEE    */
                    _UBYTE RXEPEE:1;            /*   RXEPEE     */
                    } BIT;                      /*              */
             } IEIER;                           /*              */
       _UBYTE wk3[2];                           /*              */
       union {                                  /* IECKSR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :3;                  /*              */
                    _UBYTE CKS3:1;              /*   CKS3       */
                    _UBYTE :1;                  /*              */
                    _UBYTE CKS:3;               /*   CKS        */
                    } BIT;                      /*              */
             } IECKSR;                          /*              */
       _UBYTE wk4[231];                         /*              */
       union {                                  /* IETB001-128  */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TB:8;                /*  TB          */
                    } BIT;                      /*              */
             } IETB[128];                       /*              */
       _UBYTE wk5[128];                         /*              */
       union {                                  /* IERB001-128  */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE RB:8;                /*  RB          */
                    } BIT;                      /*              */
             } IERB[128];                       /*              */
};                                              /*              */
struct st_spdif {                               /* struct SPDIF */
       _UDWORD TLCA;                            /* TLCA         */
       _UDWORD TRCA;                            /* TRCA         */
       union {                                  /* TLCS         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :2;                 /*              */
                    _UDWORD CLAC:2;             /*   CLAC       */
                    _UDWORD FS:4;               /*   FS         */
                    _UDWORD CHNO:4;             /*   CHNO       */
                    _UDWORD SRCNO:4;            /*   SRCNO      */
                    _UDWORD CATCD:8;            /*   CATCD      */
                    _UDWORD :2;                 /*              */
                    _UDWORD CTL:5;              /*   CTL        */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } TLCS;                            /*              */
       union {                                  /* TRCS         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :2;                 /*              */
                    _UDWORD CLAC:2;             /*   CLAC       */
                    _UDWORD FS:4;               /*   FS         */
                    _UDWORD CHNO:4;             /*   CHNO       */
                    _UDWORD SRCNO:4;            /*   SRCNO      */
                    _UDWORD CATCD:8;            /*   CATCD      */
                    _UDWORD :2;                 /*              */
                    _UDWORD CTL:5;              /*   CTL        */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } TRCS;                            /*              */
       _UDWORD TUI;                             /* TUI          */
       _UDWORD RLCA;                            /* RLCA         */
       _UDWORD RRCA;                            /* RRCA         */
       union {                                  /* RLCS         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :2;                 /*              */
                    _UDWORD CLAC:2;             /*   CLAC       */
                    _UDWORD FS:4;               /*   FS         */
                    _UDWORD CHNO:4;             /*   CHNO       */
                    _UDWORD SRCNO:4;            /*   SRCNO      */
                    _UDWORD CATCD:8;            /*   CATCD      */
                    _UDWORD :2;                 /*              */
                    _UDWORD CTL:5;              /*   CTL        */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } RLCS;                            /*              */
       union {                                  /* RRCS         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :2;                 /*              */
                    _UDWORD CLAC:2;             /*   CLAC       */
                    _UDWORD FS:4;               /*   FS         */
                    _UDWORD CHNO:4;             /*   CHNO       */
                    _UDWORD SRCNO:4;            /*   SRCNO      */
                    _UDWORD CATCD:8;            /*   CATCD      */
                    _UDWORD :2;                 /*              */
                    _UDWORD CTL:5;              /*   CTL        */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } RRCS;                            /*              */
       _UDWORD RUI;                             /* RUI          */
       union {                                  /* CTRL         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :3;                 /*              */
                    _UDWORD CKS:1;              /*   CKS        */
                    _UDWORD :1;                 /*              */
                    _UDWORD PB:1;               /*   PB         */
                    _UDWORD RASS:2;             /*   RASS       */
                    _UDWORD TASS:2;             /*   TASS       */
                    _UDWORD RDE:1;              /*   RDE        */
                    _UDWORD TDE:1;              /*   TDE        */
                    _UDWORD NCSI:1;             /*   NCSI       */
                    _UDWORD AOS:1;              /*   AOS        */
                    _UDWORD RME:1;              /*   RME        */
                    _UDWORD TME:1;              /*   TME        */
                    _UDWORD REIE:1;             /*   REIE       */
                    _UDWORD TEIE:1;             /*   TEIE       */
                    _UDWORD UBOI:1;             /*   UBOI       */
                    _UDWORD UBUI:1;             /*   UBUI       */
                    _UDWORD CREI:1;             /*   CREI       */
                    _UDWORD PAEI:1;             /*   PAEI       */
                    _UDWORD PREI:1;             /*   PREI       */
                    _UDWORD CSEI:1;             /*   CSEI       */
                    _UDWORD ABOI:1;             /*   ABOI       */
                    _UDWORD ABUI:1;             /*   ABUI       */
                    _UDWORD RUII:1;             /*   RUII       */
                    _UDWORD TUII:1;             /*   TUII       */
                    _UDWORD RCSI:1;             /*   RCSI       */
                    _UDWORD RCBI:1;             /*   RCBI       */
                    _UDWORD TCSI:1;             /*   TCSI       */
                    _UDWORD TCBI:1;             /*   TCBI       */
                    } BIT;                      /*              */
             } CTRL;                            /*              */
       union {                                  /* STAT         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :15;                /*              */
                    _UDWORD CMD:1;              /*   CMD        */
                    _UDWORD RIS:1;              /*   RIS        */
                    _UDWORD TIS:1;              /*   TIS        */
                    _UDWORD UBO:1;              /*   UBO        */
                    _UDWORD UBU:1;              /*   UBU        */
                    _UDWORD CE:1;               /*   CE         */
                    _UDWORD PARE:1;             /*   PARE       */
                    _UDWORD PREE:1;             /*   PREE       */
                    _UDWORD CSE:1;              /*   CSE        */
                    _UDWORD ABO:1;              /*   ABO        */
                    _UDWORD ABU:1;              /*   ABU        */
                    _UDWORD RUIR:1;             /*   RUIR       */
                    _UDWORD TUIR:1;             /*   TUIR       */
                    _UDWORD CSRX:1;             /*   CSRX       */
                    _UDWORD CBRX:1;             /*   CBRX       */
                    _UDWORD CSTX:1;             /*   CSTX       */
                    _UDWORD CBTX:1;             /*   CBTX       */
                    } BIT;                      /*              */
             } STAT;                            /*              */
       _UDWORD TDAD;                            /* TDAD         */
       _UDWORD RDAD;                            /* RDAD         */
};                                              /*              */
struct st_romdec {                              /* struct ROMDEC */
       union {                                  /* CROMEN       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SUBC_EN:1;           /*   SUBC_EN    */
                    _UBYTE CROM_EN:1;           /*   CROM_EN    */
                    _UBYTE CROM_STP:1;          /*   CROM_STP   */
                    _UBYTE :5;                  /*              */
                    } BIT;                      /*              */
             } CROMEN;                          /*              */
       union {                                  /* CROMSY0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SY_AUT:1;            /*   SY_AUT     */
                    _UBYTE SY_IEN:1;            /*   SY_IEN     */
                    _UBYTE SY_DEN:1;            /*   SY_DEN     */
                    _UBYTE :5;                  /*              */
                    } BIT;                      /*              */
             } CROMSY0;                         /*              */
       union {                                  /* CROMCTL0     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MD_DESC:1;           /*   MD_DESC    */
                    _UBYTE :1;                  /*              */
                    _UBYTE MD_AUTO:1;           /*   MD_AUTO    */
                    _UBYTE MD_AUTOS1:1;         /*   MD_AUTOS1  */
                    _UBYTE MD_AUTOS2:1;         /*   MD_AUTOS2  */
                    _UBYTE MD_SEC:3;            /*   MD_SEC     */
                    } BIT;                      /*              */
             } CROMCTL0;                        /*              */
       union {                                  /* CROMCTL1     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE M2F2EDC:1;           /*   M2F2EDC    */
                    _UBYTE MD_DEC:3;            /*   MD_DEC     */
                    _UBYTE :2;                  /*              */
                    _UBYTE MD_PQREP:2;          /*   MD_PQREP   */
                    } BIT;                      /*              */
             } CROMCTL1;                        /*              */
       _UBYTE wk0[1];                           /*              */
       union {                                  /* CROMCTL3     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE STP_ECC:1;           /*   STP_ECC    */
                    _UBYTE STP_EDC:1;           /*   STP_EDC    */
                    _UBYTE :1;                  /*              */
                    _UBYTE STP_MD:1;            /*   STP_MD     */
                    _UBYTE STP_MIN:1;           /*   STP_MIN    */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } CROMCTL3;                        /*              */
       union {                                  /* CROMCTL4     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE LINKOFF:1;           /*   LINKOFF    */
                    _UBYTE LINK2:1;             /*   LINK2      */
                    _UBYTE :1;                  /*              */
                    _UBYTE EROSEL:1;            /*   EROSEL     */
                    _UBYTE NO_ECC:1;            /*   NO_ECC     */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } CROMCTL4;                        /*              */
       union {                                  /* CROMCTL5     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE MSF_LBA_SEL:1;       /*   MSF_LBA_SEL */
                    } BIT;                      /*              */
             } CROMCTL5;                        /*              */
       union {                                  /* CROMST0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE ST_SYIL:1;           /*   ST_SYIL    */
                    _UBYTE ST_SYNO:1;           /*   ST_SYNO    */
                    _UBYTE ST_BLKS:1;           /*   ST_BLKS    */
                    _UBYTE ST_BLKL:1;           /*   ST_BLKL    */
                    _UBYTE ST_SECS:1;           /*   ST_SECS    */
                    _UBYTE ST_SECL:1;           /*   ST_SECL    */
                    } BIT;                      /*              */
             } CROMST0;                         /*              */
       union {                                  /* CROMST1      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE ER2_HEAD0:1;         /*   ER2_HEAD0  */
                    _UBYTE ER2_HEAD1:1;         /*   ER2_HEAD1  */
                    _UBYTE ER2_HEAD2:1;         /*   ER2_HEAD2  */
                    _UBYTE ER2_HEAD3:1;         /*   ER2_HEAD3  */
                    } BIT;                      /*              */
             } CROMST1;                         /*              */
       _UBYTE wk1[1];                           /*              */
       union {                                  /* CROMST3      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ER2_SHEAD0:1;        /*   ER2_SHEAD0 */
                    _UBYTE ER2_SHEAD1:1;        /*   ER2_SHEAD1 */
                    _UBYTE ER2_SHEAD2:1;        /*   ER2_SHEAD2 */
                    _UBYTE ER2_SHEAD3:1;        /*   ER2_SHEAD3 */
                    _UBYTE ER2_SHEAD4:1;        /*   ER2_SHEAD4 */
                    _UBYTE ER2_SHEAD5:1;        /*   ER2_SHEAD5 */
                    _UBYTE ER2_SHEAD6:1;        /*   ER2_SHEAD6 */
                    _UBYTE ER2_SHEAD7:1;        /*   ER2_SHEAD7 */
                    } BIT;                      /*              */
             } CROMST3;                         /*              */
       union {                                  /* CROMST4      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE NG_MD:1;             /*   NG_MD      */
                    _UBYTE NG_MDCMP1:1;         /*   NG_MDCMP1  */
                    _UBYTE NG_MDCMP2:1;         /*   NG_MDCMP2  */
                    _UBYTE NG_MDCMP3:1;         /*   NG_MDCMP3  */
                    _UBYTE NG_MDCMP4:1;         /*   NG_MDCMP4  */
                    _UBYTE NG_MDDEF:1;          /*   NG_MDDEF   */
                    _UBYTE NG_MDTIM1:1;         /*   NG_MDTIM1  */
                    _UBYTE NG_MDTIM2:1;         /*   NG_MDTIM2  */
                    } BIT;                      /*              */
             } CROMST4;                         /*              */
       union {                                  /* CROMST5      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ST_AMD:3;            /*   ST_AMD     */
                    _UBYTE ST_MDX:1;            /*   ST_MDX     */
                    _UBYTE LINK_ON:1;           /*   LINK_ON    */
                    _UBYTE LINK_DET:1;          /*   LINK_DET   */
                    _UBYTE LINK_SDET:1;         /*   LINK_SDET  */
                    _UBYTE LINK_OUT1:1;         /*   LINK_OUT1  */
                    } BIT;                      /*              */
             } CROMST5;                         /*              */
       union {                                  /* CROMST6      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ST_ERR:1;            /*   ST_ERR     */
                    _UBYTE :1;                  /*              */
                    _UBYTE ST_ECCABT:1;         /*   ST_ECCABT  */
                    _UBYTE ST_ECCNG:1;          /*   ST_ECCNG   */
                    _UBYTE ST_ECCP:1;           /*   ST_ECCP    */
                    _UBYTE ST_ECCQ:1;           /*   ST_ECCQ    */
                    _UBYTE ST_EDC1:1;           /*   ST_EDC1    */
                    _UBYTE ST_EDC2:1;           /*   ST_EDC2    */
                    } BIT;                      /*              */
             } CROMST6;                         /*              */
       _UBYTE wk2[5];                           /*              */
       union {                                  /* CBUFST0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BUF_REF:1;           /*   BUF_REF    */
                    _UBYTE BUF_ACT:1;           /*   BUF_ACT    */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } CBUFST0;                         /*              */
       union {                                  /* CBUFST1      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BUF_ECC:1;           /*   BUF_ECC    */
                    _UBYTE BUF_EDC:1;           /*   BUF_EDC    */
                    _UBYTE :1;                  /*              */
                    _UBYTE BUF_MD:1;            /*   BUF_MD     */
                    _UBYTE BUF_MIN:1;           /*   BUF_MIN    */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } CBUFST1;                         /*              */
       union {                                  /* CBUFST2      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BUF_NG:1;            /*   BUF_NG     */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } CBUFST2;                         /*              */
       _UBYTE wk3[1];                           /*              */
       _UBYTE HEAD00;                           /* HEAD00       */
       _UBYTE HEAD01;                           /* HEAD01       */
       _UBYTE HEAD02;                           /* HEAD02       */
       _UBYTE HEAD03;                           /* HEAD03       */
       _UBYTE SHEAD00;                          /* SHEAD00      */
       _UBYTE SHEAD01;                          /* SHEAD01      */
       _UBYTE SHEAD02;                          /* SHEAD02      */
       _UBYTE SHEAD03;                          /* SHEAD03      */
       _UBYTE SHEAD04;                          /* SHEAD04      */
       _UBYTE SHEAD05;                          /* SHEAD05      */
       _UBYTE SHEAD06;                          /* SHEAD06      */
       _UBYTE SHEAD07;                          /* SHEAD07      */
       _UBYTE HEAD20;                           /* HEAD20       */
       _UBYTE HEAD21;                           /* HEAD21       */
       _UBYTE HEAD22;                           /* HEAD22       */
       _UBYTE HEAD23;                           /* HEAD23       */
       _UBYTE SHEAD20;                          /* SHEAD20      */
       _UBYTE SHEAD21;                          /* SHEAD21      */
       _UBYTE SHEAD22;                          /* SHEAD22      */
       _UBYTE SHEAD23;                          /* SHEAD23      */
       _UBYTE SHEAD24;                          /* SHEAD24      */
       _UBYTE SHEAD25;                          /* SHEAD25      */
       _UBYTE SHEAD26;                          /* SHEAD26      */
       _UBYTE SHEAD27;                          /* SHEAD27      */
       _UBYTE wk4[16];                          /*              */
       union {                                  /* CBUFCTL0     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CBUF_AUT:1;          /*   CBUF_AUT   */
                    _UBYTE CBUF_EN:1;           /*   CBUF_EN    */
                    _UBYTE CBUF_LINK:1;         /*   CBUF_LINK  */
                    _UBYTE CBUF_MD:2;           /*   CBUF_MD    */
                    _UBYTE CBUF_TS:1;           /*   CBUF_TS    */
                    _UBYTE CBUF_Q:1;            /*   CBUF_Q     */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } CBUFCTL0;                        /*              */
       _UBYTE CBUFCTL1;                         /* CBUFCTL1     */
       _UBYTE CBUFCTL2;                         /* CBUFCTL2     */
       _UBYTE CBUFCTL3;                         /* CBUFCTL3     */
       _UBYTE wk5[1];                           /*              */
       union {                                  /* CROMST0M     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE ST_SYILM:1;          /*   ST_SYILM   */
                    _UBYTE ST_SYNOM:1;          /*   ST_SYNOM   */
                    _UBYTE ST_BLKSM:1;          /*   ST_BLKSM   */
                    _UBYTE ST_BLKLM:1;          /*   ST_BLKLM   */
                    _UBYTE ST_SECSM:1;          /*   ST_SECSM   */
                    _UBYTE ST_SECLM:1;          /*   ST_SECLM   */
                    } BIT;                      /*              */
             } CROMST0M;                        /*              */
       _UBYTE wk6[186];                         /*              */
       union {                                  /* ROMDECRST    */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE LOGICRST:1;          /*   LOGICRST   */
                    _UBYTE RAMRST:1;            /*   RAMRST     */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } ROMDECRST;                       /*              */
       union {                                  /* RSTSTAT      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE RAMCLRST:1;          /*   RAMCLRST   */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } RSTSTAT;                         /*              */
       union {                                  /* SSI          */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BYTEND:1;            /*   BYTEND     */
                    _UBYTE BITEND:1;            /*   BITEND     */
                    _UBYTE BUFEND0:2;           /*   BUFEND0    */
                    _UBYTE BUFEND1:2;           /*   BUFEND1    */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } SSI;                             /*              */
       _UBYTE wk7[5];                           /*              */
       union {                                  /* INTHOLD      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE ISEC:1;              /*   ISEC       */
                    _UBYTE ITARG:1;             /*   ITARG      */
                    _UBYTE ISY:1;               /*   ISY        */
                    _UBYTE IERR:1;              /*   IERR       */
                    _UBYTE IBUF:1;              /*   IBUF       */
                    _UBYTE IREADY:1;            /*   IREADY     */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } INTHOLD;                         /*              */
       union {                                  /* INHINT       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE INHISEC:1;           /*   INHISEC    */
                    _UBYTE INHITARG:1;          /*   INHITARG   */
                    _UBYTE INHISY:1;            /*   INHISY     */
                    _UBYTE INHIERR:1;           /*   INHIERR    */
                    _UBYTE INHIBUF:1;           /*   INHIBUF    */
                    _UBYTE INHIREADY:1;         /*   INHIREADY  */
                    _UBYTE PREINHREQDM:1;       /*   PREINHREQDM */
                    _UBYTE PREINHIREADY:1;      /*   PREINHIREADY */
                    } BIT;                      /*              */
             } INHINT;                          /*              */
       _UBYTE wk8[246];                         /*              */
       _UDWORD STRMDIN;                         /* STRMDIN      */
       _UWORD STRMDOUT;                         /* STRMDOUT     */
};


#if 0 /* 新iodefine.hのADC定義を用いるため不要 */
	                                            /*              */
struct st_adc {                                 /* struct ADC   */
       union {                                  /* ADDRA        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRA;                           /*              */
       union {                                  /* ADDRB        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRB;                           /*              */
       union {                                  /* ADDRC        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRC;                           /*              */
       union {                                  /* ADDRD        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRD;                           /*              */
       union {                                  /* ADDRE        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRE;                           /*              */
       union {                                  /* ADDRF        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRF;                           /*              */
       union {                                  /* ADDRG        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRG;                           /*              */
       union {                                  /* ADDRH        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } ADDRH;                           /*              */
       _UBYTE wk0[16];                          /*              */
       union {                                  /* ADCSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD ADF:1;               /*   ADF        */
                    _UWORD ADIE:1;              /*   ADIE       */
                    _UWORD ADST:1;              /*   ADST       */
                    _UWORD TRGS:4;              /*   TRGS       */
                    _UWORD CKS:3;               /*   CKS        */
                    _UWORD MDS:3;               /*   MDS        */
                    _UWORD CH:3;                /*   CH         */
                    } BIT;                      /*              */
             } ADCSR;                           /*              */
};                                              /*              */
#endif



struct st_flctl {                               /* struct FLCTL */
       union {                                  /* FLCMNCR      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :10;                 /*              */
                    _UDWORD BUSYON:1;           /*   BUSYON     */
                    _UDWORD :2;                 /*              */
                    _UDWORD SNAND:1;            /*   SNAND      */
                    _UDWORD QTSEL:1;            /*   QTSEL      */
                    _UDWORD :5;                 /*              */
                    _UDWORD ACM:2;              /*   ACM        */
                    _UDWORD NANDWF:1;           /*   NANDWF     */
                    _UDWORD :5;                 /*              */
                    _UDWORD CE:1;               /*   CE         */
                    _UDWORD :3;                 /*              */
                    } BIT;                      /*              */
             } FLCMNCR;                         /*              */
       union {                                  /* FLCMDCR      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ADRCNT2:1;          /*   ADRCNT2    */
                    _UDWORD SCTCNT_:4;          /*   SCTCNT     */
                    _UDWORD ADRMD:1;            /*   ADRMD      */
                    _UDWORD CDSRC:1;            /*   CDSRC      */
                    _UDWORD DOSR:1;             /*   DOSR       */
                    _UDWORD :2;                 /*              */
                    _UDWORD SELRW:1;            /*   SELRW      */
                    _UDWORD DOADR:1;            /*   DOADR      */
                    _UDWORD ADRCNT:2;           /*   ADRCNT     */
                    _UDWORD DOCMD2:1;           /*   DOCMD2     */
                    _UDWORD DOCMD1:1;           /*   DOCMD1     */
                    _UDWORD SCTCNT:16;          /*   SCTCNT     */
                    } BIT;                      /*              */
             } FLCMDCR;                         /*              */
       union {                                  /* FLCMCDR      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :16;                /*              */
                    _UDWORD CMD2:8;             /*   CMD2       */
                    _UDWORD CMD1:8;             /*   CMD1       */
                    } BIT;                      /*              */
             } FLCMCDR;                         /*              */
       _UDWORD  FLADR;                          /* FLADR        */
       _UDWORD  FLDATAR;                        /* FLDATAR      */
       union {                                  /* FLDTCNTR     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ECFLW:8;            /*   ECFLW      */
                    _UDWORD DTFLW:8;            /*   DTFLW      */
                    _UDWORD :4;                 /*              */
                    _UDWORD DTCNT:12;           /*   DTCNT      */
                    } BIT;                      /*              */
             } FLDTCNTR;                        /*              */
       union {                                  /* FLINTDMACR   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :10;                 /*              */
                    _UDWORD FIFOTRG:2;          /*   FIFOTRG    */
                    _UDWORD AC1CLR:1;           /*   AC1CLR     */
                    _UDWORD AC0CLR:1;           /*   AC0CLR     */
                    _UDWORD DREQ1EN:1;          /*   DREQ1EN    */
                    _UDWORD DREQ0EN:1;          /*   DREQ0EN    */
                    _UDWORD :7;                 /*              */
                    _UDWORD STERB:1;            /*   STERB      */
                    _UDWORD BTOERB:1;           /*   BTOERB     */
                    _UDWORD TRREQF1:1;          /*   TRREQF1    */
                    _UDWORD TRREQF0:1;          /*   TRREQF0    */
                    _UDWORD STERINTE:1;         /*   STERINTE   */
                    _UDWORD RBERINTE:1;         /*   RBERINTE   */
                    _UDWORD TEINTE:1;           /*   TEINTE     */
                    _UDWORD TRINTE1:1;          /*   TRINTE1    */
                    _UDWORD TRINTE0:1;          /*   TRINTE0    */
                    } BIT;                      /*              */
             } FLINTDMACR;                      /*              */
       union {                                  /* FLBSYTMR     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD RBTMOUT:20;         /*   RBTMOUT    */
                    } BIT;                      /*              */
             } FLBSYTMR;                        /*              */
       union {                                  /* FLBSYCNT     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD STAT:8;             /*   STAT       */
                    _UDWORD :4;                 /*              */
                    _UDWORD RBTIMCNT:20;        /*   RBTIMCNT   */
                    } BIT;                      /*              */
             } FLBSYCNT;                        /*              */
       _UBYTE wk0[8];                           /*              */
       union {                                  /* FLTRCR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE TRSTAT:1;            /*   TRSTAT     */
                    _UBYTE TREND:1;             /*   TREND      */
                    _UBYTE TRSTRT:1;            /*   TRSTRT     */
                    } BIT;                      /*              */
             } FLTRCR;                          /*              */
       _UBYTE wk1[11];                          /*              */
       union {                                  /* FLHOLDCR     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :31;                /*              */
                    _UDWORD HOLDEN:1;           /*   HOLDEN     */
                    } BIT;                      /*              */
             } FLHOLDCR;                        /*              */
       _UDWORD FLADR2;                          /* FLADR2       */
       _UBYTE wk2[16];                          /*              */
       _UDWORD FLDTFIFO;                        /* FLDTFIFO     */
       _UBYTE wk3[12];                          /*              */
       _UDWORD FLECFIFO;                        /* FLECFIFO     */
};                                              /*              */
	#if	0
struct st_usb {                                 /* struct USB   */
       union {                                  /* SYSCFG       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :5;                  /*              */
                    _UWORD SCKE:1;              /*   SCKE       */
                    _UWORD :2;                  /*              */
                    _UWORD HSE:1;               /*   HSE        */
                    _UWORD DCFM:1;              /*   DCFM       */
                    _UWORD DRPD:1;              /*   DRPD       */
                    _UWORD DPRPU:1;             /*   DPRPU      */
                    _UWORD UCKFSEL:1;           /*   UCKFSEL    */
                    _UWORD UCKPSEL:1;           /*   UCKPSEL    */
                    _UWORD UPLLE:1;             /*   UPLLE    */
                    _UWORD USBE:1;              /*   USBE       */
                    } BIT;                      /*              */
             } SYSCFG;                          /*              */
       union {                                  /* BUSWAIT      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :12;                 /*              */
                    _UWORD BWAIT:4;             /*   BWAIT      */
                    } BIT;                      /*              */
             } BUSWAIT;                         /*              */
       union {                                  /* SYSSTS       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :14;                 /*              */
                    _UWORD LNST:2;              /*   LNST       */
                    } BIT;                      /*              */
             } SYSSTS;                          /*              */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* DVSTCTR      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :7;                  /*              */
                    _UWORD WKUP:1;              /*   WKUP       */
                    _UWORD RWUPE:1;             /*   RWUPE      */
                    _UWORD USBRST:1;            /*   USBRST     */
                    _UWORD RESUME:1;            /*   RESUME     */
                    _UWORD UACT:1;              /*   UACT       */
                    _UWORD :1;                  /*              */
                    _UWORD RHST:3;              /*   RHST       */
                    } BIT;                      /*              */
             } DVSTCTR;                         /*              */
       _UBYTE wk1[2];                           /*              */
       union {                                  /* TESTMODE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :12;                 /*              */
                    _UWORD UTST:4;              /*   UTST       */
                    } BIT;                      /*              */
             } TESTMODE;                        /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* D0FBCFG      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :11;                 /*              */
                    _UWORD TENDE:1;             /*   TENDE      */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } D0FBCFG;                         /*              */
       union {                                  /* D1FBCFG      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :11;                 /*              */
                    _UWORD TENDE:1;             /*   TENDE      */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } D1FBCFG;                         /*              */
       union {                                  /* CFIFO        */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD;                       /*  Word Access */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } CFIFO;                           /*              */
       union {                                  /* D0FIFO       */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD;                       /*  Word Access */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFO;                          /*              */
       union {                                  /* D1FIFO       */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD;                       /*  Word Access */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFO;                          /*              */
       union {                                  /* CFIFOSEL     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD RCNT:1;              /*   RCNT       */
                    _UWORD REW:1;               /*   REW        */
                    _UWORD :2;                  /*              */
                    _UWORD MBW:2;               /*   MBW        */
                    _UWORD :1;                  /*              */
                    _UWORD BIGEND:1;            /*   BIGEND     */
                    _UWORD :2;                  /*              */
                    _UWORD ISEL:1;              /*   ISEL       */
                    _UWORD :1;                  /*              */
                    _UWORD CURPIPE:4;           /*   CURPIPE    */
                    } BIT;                      /*              */
             } CFIFOSEL;                        /*              */
       union {                                  /* CFIFOCTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BVAL:1;              /*   BVAL       */
                    _UWORD BCLR:1;              /*   BCLR       */
                    _UWORD FRDY:1;              /*   FRDY       */
                    _UWORD :1;                  /*              */
                    _UWORD DTLN:12;             /*   DTLN       */
                    } BIT;                      /*              */
             } CFIFOCTR;                        /*              */
       _UBYTE wk3[4];                           /*              */
       union {                                  /* D0FIFOSEL    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD RCNT:1;              /*   RCNT       */
                    _UWORD REW:1;               /*   REW        */
                    _UWORD DCLRM:1;             /*   DCLRM      */
                    _UWORD DREQE:1;             /*   DREQE      */
                    _UWORD MBW:2;               /*   MBW        */
                    _UWORD :1;                  /*              */
                    _UWORD BIGEND:1;            /*   BIGEND     */
                    _UWORD :4;                  /*              */
                    _UWORD CURPIPE:4;           /*   CURPIPE    */
                    } BIT;                      /*              */
             } D0FIFOSEL;                       /*              */
       union {                                  /* D0FIFOCTR    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BVAL:1;              /*   BVAL       */
                    _UWORD BCLR:1;              /*   BCLR       */
                    _UWORD FRDY:1;              /*   FRDY       */
                    _UWORD :1;                  /*              */
                    _UWORD DTLN:12;             /*   DTLN       */
                    } BIT;                      /*              */
             } D0FIFOCTR;                       /*              */
       union {                                  /* D1FIFOSEL    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD RCNT:1;              /*   RCNT       */
                    _UWORD REW:1;               /*   REW        */
                    _UWORD DCLRM:1;             /*   DCLRM      */
                    _UWORD DREQE:1;             /*   DREQE      */
                    _UWORD MBW:2;               /*   MBW        */
                    _UWORD :1;                  /*              */
                    _UWORD BIGEND:1;            /*   BIGEND     */
                    _UWORD :4;                  /*              */
                    _UWORD CURPIPE:4;           /*   CURPIPE    */
                    } BIT;                      /*              */
             } D1FIFOSEL;                       /*              */
       union {                                  /* D1FIFOCTR    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BVAL:1;              /*   BVAL       */
                    _UWORD BCLR:1;              /*   BCLR       */
                    _UWORD FRDY:1;              /*   FRDY       */
                    _UWORD :1;                  /*              */
                    _UWORD DTLN:12;             /*   DTLN       */
                    } BIT;                      /*              */
             } D1FIFOCTR;                       /*              */
       union {                                  /* INTENB0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD VBSE:1;              /*   VBSE       */
                    _UWORD RSME:1;              /*   RSME       */
                    _UWORD SOFE:1;              /*   SOFE       */
                    _UWORD DVSE:1;              /*   DVSE       */
                    _UWORD CTRE:1;              /*   CTRE       */
                    _UWORD BEMPE:1;             /*   BEMPE      */
                    _UWORD NRDYE:1;             /*   NRDYE      */
                    _UWORD BRDYE:1;             /*   BRDYE      */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } INTENB0;                         /*              */
       union {                                  /* INTENB1      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD BCHGE:1;             /*   BCHGE      */
                    _UWORD :1;                  /*              */
                    _UWORD DTCHE:1;             /*   DTCHE      */
                    _UWORD ATTCHE:1;            /*   ATTCHE     */
                    _UWORD :4;                  /*              */
                    _UWORD EOFERRE:1;           /*   EOFERRE    */
                    _UWORD SIGNE:1;             /*   SIGNE      */
                    _UWORD SACKE:1;             /*   SACKE      */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } INTENB1;                         /*              */
       _UBYTE wk4[2];                           /*              */
       union {                                  /* BRDYENB      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD PIPE9BRDYE:1;        /*   PIPE9BRDYE */
                    _UWORD PIPE8BRDYE:1;        /*   PIPE8BRDYE */
                    _UWORD PIPE7BRDYE:1;        /*   PIPE7BRDYE */
                    _UWORD PIPE6BRDYE:1;        /*   PIPE6BRDYE */
                    _UWORD PIPE5BRDYE:1;        /*   PIPE5BRDYE */
                    _UWORD PIPE4BRDYE:1;        /*   PIPE4BRDYE */
                    _UWORD PIPE3BRDYE:1;        /*   PIPE3BRDYE */
                    _UWORD PIPE2BRDYE:1;        /*   PIPE2BRDYE */
                    _UWORD PIPE1BRDYE:1;        /*   PIPE1BRDYE */
                    _UWORD PIPE0BRDYE:1;        /*   PIPE0BRDYE */
                    } BIT;                      /*              */
             } BRDYENB;                         /*              */
       union {                                  /* NRDYENB      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD PIPE9NRDYE:1;        /*   PIPE9NRDYE */
                    _UWORD PIPE8NRDYE:1;        /*   PIPE8NRDYE */
                    _UWORD PIPE7NRDYE:1;        /*   PIPE7NRDYE */
                    _UWORD PIPE6NRDYE:1;        /*   PIPE6NRDYE */
                    _UWORD PIPE5NRDYE:1;        /*   PIPE5NRDYE */
                    _UWORD PIPE4NRDYE:1;        /*   PIPE4NRDYE */
                    _UWORD PIPE3NRDYE:1;        /*   PIPE3NRDYE */
                    _UWORD PIPE2NRDYE:1;        /*   PIPE2NRDYE */
                    _UWORD PIPE1NRDYE:1;        /*   PIPE1NRDYE */
                    _UWORD PIPE0NRDYE:1;        /*   PIPE0NRDYE */
                    } BIT;                      /*              */
             } NRDYENB;                         /*              */
       union {                                  /* BEMPENB      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD PIPE9BEMPE:1;        /*   PIPE9BEMPE */
                    _UWORD PIPE8BEMPE:1;        /*   PIPE8BEMPE */
                    _UWORD PIPE7BEMPE:1;        /*   PIPE7BEMPE */
                    _UWORD PIPE6BEMPE:1;        /*   PIPE6BEMPE */
                    _UWORD PIPE5BEMPE:1;        /*   PIPE5BEMPE */
                    _UWORD PIPE4BEMPE:1;        /*   PIPE4BEMPE */
                    _UWORD PIPE3BEMPE:1;        /*   PIPE3BEMPE */
                    _UWORD PIPE2BEMPE:1;        /*   PIPE2BEMPE */
                    _UWORD PIPE1BEMPE:1;        /*   PIPE1BEMPE */
                    _UWORD PIPE0BEMPE:1;        /*   PIPE0BEMPE */
                    } BIT;                      /*              */
             } BEMPENB;                         /*              */
       union {                                  /* SOFCFG       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :7;                  /*              */
                    _UWORD TRNENSEL:1;          /*   TRNENSEL   */
                    _UWORD :1;                  /*              */
                    _UWORD BRDYM:1;             /*   BRDYM      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } SOFCFG;                          /*              */
       _UBYTE wk5[2];                           /*              */
       union {                                  /* INTSTS0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD VBINT:1;             /*   VBINT      */
                    _UWORD RESM:1;              /*   RESM       */
                    _UWORD SOFR:1;              /*   SOFR       */
                    _UWORD DVST:1;              /*   DVST       */
                    _UWORD CTRT:1;              /*   CTRT       */
                    _UWORD BEMP:1;              /*   BEMP       */
                    _UWORD NRDY:1;              /*   NRDY       */
                    _UWORD BRDY:1;              /*   BRDY       */
                    _UWORD VBSTS:1;             /*   VBSTS      */
                    _UWORD DVSQ:3;              /*   DVSQ       */
                    _UWORD VALID:1;             /*   VALID      */
                    _UWORD CTSQ:3;              /*   CTSQ       */
                    } BIT;                      /*              */
             } INTSTS0;                         /*              */
       union {                                  /* INTSTS1      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD BCHG:1;              /*   BCHG       */
                    _UWORD :1;                  /*              */
                    _UWORD DTCH:1;              /*   DTCH       */
                    _UWORD ATTCH:1;             /*   ATTCH      */
                    _UWORD :4;                  /*              */
                    _UWORD EOFERR:1;            /*   EOFERR     */
                    _UWORD SIGN:1;              /*   SIGN       */
                    _UWORD SACK:1;              /*   SACK       */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } INTSTS1;                         /*              */
       _UBYTE wk6[2];                           /*              */
       union {                                  /* BRDYSTS      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD PIPE9BRDY:1;         /*   PIPE9BRDY  */
                    _UWORD PIPE8BRDY:1;         /*   PIPE8BRDY  */
                    _UWORD PIPE7BRDY:1;         /*   PIPE7BRDY  */
                    _UWORD PIPE6BRDY:1;         /*   PIPE6BRDY  */
                    _UWORD PIPE5BRDY:1;         /*   PIPE5BRDY  */
                    _UWORD PIPE4BRDY:1;         /*   PIPE4BRDY  */
                    _UWORD PIPE3BRDY:1;         /*   PIPE3BRDY  */
                    _UWORD PIPE2BRDY:1;         /*   PIPE2BRDY  */
                    _UWORD PIPE1BRDY:1;         /*   PIPE1BRDY  */
                    _UWORD PIPE0BRDY:1;         /*   PIPE0BRDY  */
                    } BIT;                      /*              */
             } BRDYSTS;                         /*              */
       union {                                  /* NRDYSTS      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD PIPE9NRDY:1;         /*   PIPE9NRDY  */
                    _UWORD PIPE8NRDY:1;         /*   PIPE8NRDY  */
                    _UWORD PIPE7NRDY:1;         /*   PIPE7NRDY  */
                    _UWORD PIPE6NRDY:1;         /*   PIPE6NRDY  */
                    _UWORD PIPE5NRDY:1;         /*   PIPE5NRDY  */
                    _UWORD PIPE4NRDY:1;         /*   PIPE4NRDY  */
                    _UWORD PIPE3NRDY:1;         /*   PIPE3NRDY  */
                    _UWORD PIPE2NRDY:1;         /*   PIPE2NRDY  */
                    _UWORD PIPE1NRDY:1;         /*   PIPE1NRDY  */
                    _UWORD PIPE0NRDY:1;         /*   PIPE0NRDY  */
                    } BIT;                      /*              */
             } NRDYSTS;                         /*              */
       union {                                  /* BEMPSTS      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD PIPE9BEMP:1;         /*   PIPE9BEMP  */
                    _UWORD PIPE8BEMP:1;         /*   PIPE8BEMP  */
                    _UWORD PIPE7BEMP:1;         /*   PIPE7BEMP  */
                    _UWORD PIPE6BEMP:1;         /*   PIPE6BEMP  */
                    _UWORD PIPE5BEMP:1;         /*   PIPE5BEMP  */
                    _UWORD PIPE4BEMP:1;         /*   PIPE4BEMP  */
                    _UWORD PIPE3BEMP:1;         /*   PIPE3BEMP  */
                    _UWORD PIPE2BEMP:1;         /*   PIPE2BEMP  */
                    _UWORD PIPE1BEMP:1;         /*   PIPE1BEMP  */
                    _UWORD PIPE0BEMP:1;         /*   PIPE0BEMP  */
                    } BIT;                      /*              */
             } BEMPSTS;                         /*              */
       union {                                  /* FRMNUM       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD OVRN:1;              /*   OVRN       */
                    _UWORD CRCE:1;              /*   CRCE       */
                    _UWORD :3;                  /*              */
                    _UWORD FRNM:11;             /*   FRNM       */
                    } BIT;                      /*              */
             } FRMNUM;                          /*              */
       union {                                  /* UFRMNUM      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :13;                 /*              */
                    _UWORD UFRNM:3;             /*   UFRNM      */
                    } BIT;                      /*              */
             } UFRMNUM;                         /*              */
       union {                                  /* USBADDR      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :9;                  /*              */
                    _UWORD USBADDR:7;           /*   USBADDR    */
                    } BIT;                      /*              */
             } USBADDR;                         /*              */
       _UBYTE wk7[2];                           /*              */
       union {                                  /* USBREQ       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BREQUEST:8;          /*   BREQUEST   */
                    _UWORD BMREQUESTTYPE:8;     /*   BMREQUESTTYPE */
                    } BIT;                      /*              */
             } USBREQ;                          /*              */
       _UWORD USBVAL;                           /* USBVAL       */
       _UWORD USBINDX;                          /* USBINDX      */
       _UWORD USBLENG;                          /* USBLENG      */
       union {                                  /* DCPCFG       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :11;                 /*              */
                    _UWORD DIR:1;               /*   DIR        */
                    _UWORD :4;                  /*              */
                    } BIT;                      /*              */
             } DCPCFG;                          /*              */
       union {                                  /* DCPMAXP      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD DEVSEL:4;            /*   DEVSEL     */
                    _UWORD :5;                  /*              */
                    _UWORD MXPS:7;              /*   MXPS       */
                    } BIT;                      /*              */
             } DCPMAXP;                         /*              */
       union {                                  /* DCPCTR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD SUREQ:1;             /*   SUREQ      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD SUREQCLR:1;          /*   SUREQCLR   */
                    _UWORD :2;                  /*              */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD PINGE:1;             /*   PINGE      */
                    _UWORD :1;                  /*              */
                    _UWORD CCPL:1;              /*   CCPL       */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } DCPCTR;                          /*              */
       _UBYTE wk8[2];                           /*              */
       union {                                  /* PIPESEL      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :12;                 /*              */
                    _UWORD PIPESEL:4;           /*   PIPESEL    */
                    } BIT;                      /*              */
             } PIPESEL;                         /*              */
       _UBYTE wk9[2];                           /*              */
       union {                                  /* PIPECFG      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TYPE:2;              /*   TYPE       */
                    _UWORD :3;                  /*              */
                    _UWORD BFRE:1;              /*   BFRE       */
                    _UWORD DBLB:1;              /*   DBLB       */
                    _UWORD CNTMD:1;             /*   CNTMD      */
                    _UWORD SHTNAK:1;            /*   SHTNAK     */
                    _UWORD :2;                  /*              */
                    _UWORD DIR:1;               /*   DIR        */
                    _UWORD EPNUM:4;             /*   EPNUM      */
                    } BIT;                      /*              */
             } PIPECFG;                         /*              */
       union {                                  /* PIPEBUF      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD BUFSIZE:5;           /*   BUFSIZE    */
                    _UWORD :3;                  /*              */
                    _UWORD BUFNMB:7;            /*   BUFNMB     */
                    } BIT;                      /*              */
             } PIPEBUF;                         /*              */
       union {                                  /* PIPEMAXP     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD DEVSEL:4;            /*   DEVSEL     */
                    _UWORD :1;                  /*              */
                    _UWORD MXPS:11;             /*   MXPS       */
                    } BIT;                      /*              */
             } PIPEMAXP;                        /*              */
       union {                                  /* PIPEPERI     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD IFIS:1;              /*   IFIS       */
                    _UWORD :9;                  /*              */
                    _UWORD IITV:3;              /*   IITV       */
                    } BIT;                      /*              */
             } PIPEPERI;                        /*              */
       union {                                  /* PIPE1CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :1;                  /*              */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE1CTR;                        /*              */
       union {                                  /* PIPE2CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :1;                  /*              */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE2CTR;                        /*              */
       union {                                  /* PIPE3CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :1;                  /*              */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE3CTR;                        /*              */
       union {                                  /* PIPE4CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :1;                  /*              */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE4CTR;                        /*              */
       union {                                  /* PIPE5CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :1;                  /*              */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE5CTR;                        /*              */
       union {                                  /* PIPE6CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD :1;                  /*              */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :2;                  /*              */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE6CTR;                        /*              */
       union {                                  /* PIPE7CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD :1;                  /*              */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :2;                  /*              */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE7CTR;                        /*              */
       union {                                  /* PIPE8CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD :1;                  /*              */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :2;                  /*              */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE8CTR;                        /*              */
       union {                                  /* PIPE9CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BSTS:1;              /*   BSTS       */
                    _UWORD :1;                  /*              */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD :2;                  /*              */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD :3;                  /*              */
                    _UWORD PID:2;               /*   PID        */
                    } BIT;                      /*              */
             } PIPE9CTR;                        /*              */
       _UBYTE wk10[14];                         /*              */
       union {                                  /* PIPE1TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } PIPE1TRE;                        /*              */
       _UWORD PIPE1TRN;                         /* PIPE1TRN     */
       union {                                  /* PIPE2TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } PIPE2TRE;                        /*              */
       _UWORD PIPE2TRN;                         /* PIPE2TRN     */
       union {                                  /* PIPE3TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } PIPE3TRE;                        /*              */
       _UWORD PIPE3TRN;                         /* PIPE3TRN     */
       union {                                  /* PIPE4TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } PIPE4TRE;                        /*              */
       _UWORD PIPE4TRN;                         /* PIPE4TRN     */
       union {                                  /* PIPE5TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } PIPE5TRE;                        /*              */
       _UWORD PIPE5TRN;                         /* PIPE5TRN     */
       _UBYTE wk11[44];                         /*              */
       union {                                  /* DEVADD0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD0;                         /*              */
       union {                                  /* DEVADD1      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD1;                         /*              */
       union {                                  /* DEVADD2      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD2;                         /*              */
       union {                                  /* DEVADD3      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD3;                         /*              */
       union {                                  /* DEVADD4      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD4;                         /*              */
       union {                                  /* DEVADD5      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD5;                         /*              */
       union {                                  /* DEVADD6      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD6;                         /*              */
       union {                                  /* DEVADD7      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD7;                         /*              */
       union {                                  /* DEVADD8      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD8;                         /*              */
       union {                                  /* DEVADD9      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADD9;                         /*              */
       union {                                  /* DEVADDA      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :1;                  /*              */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } DEVADDA;                         /*              */
};                                              /*              */
	#endif
struct st_vdc4 {                                       /* struct VDC4  */
       union {                                         /* INP_UPDATE   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD INP_EXT_UPDATE:1;          /*   INP_EXT_UPDATE */
                    _UDWORD :3;                        /*              */
                    _UDWORD INP_IMG_UPDATE:1;          /*   INP_IMG_UPDATE */
                    } BIT;                             /*              */
             } INP_UPDATE;                             /*              */
       union {                                         /* INP_SEL_CNT  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :11;                        /*              */
                    _UWORD INP_SEL:1;                  /*   INP_SEL    */
                    _UWORD :4;                         /*              */
                    _UWORD :1;                         /*              */
                    _UWORD INP_FORMAT:3;               /*   INP_FORMAT */
                    _UWORD :3;                         /*              */
                    _UWORD INP_PXD_EDGE:1;             /*   INP_PXD_EDGE */
                    _UWORD :3;                         /*              */
                    _UWORD INP_VS_EDGE:1;              /*   INP_VS_EDGE */
                    _UWORD :3;                         /*              */
                    _UWORD INP_HS_EDGE:1;              /*   INP_HS_EDGE */
                    } BIT;                             /*              */
             } INP_SEL_CNT;                            /*              */
       union {                                         /* INP_EXT_SYNC_CNT */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD INP_ENDIAN_ON:1;            /*   INP_ENDIAN_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INP_SWAP_ON:1;              /*   INP_SWAP_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INP_VS_INV:1;               /*   INP_VS_INV */
                    _UWORD :3;                         /*              */
                    _UWORD INP_HS_INV:1;               /*   INP_HS_INV */
                    _UWORD :7;                         /*              */
                    _UWORD INP_H_EDGE_SEL:1;           /*   INP_H_EDGE_SEL */
                    _UWORD :3;                         /*              */
                    _UWORD INP_F525_625:1;             /*   INP_F525_625 */
                    _UWORD :2;                         /*              */
                    _UWORD INP_H_POS:2;                /*   INP_H_POS  */
                    } BIT;                             /*              */
             } INP_EXT_SYNC_CNT;                       /*              */
       union {                                         /* INP_VSYNC_PH_ADJ */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD INP_FH50:10;                /*   INP_FH50   */
                    _UWORD :6;                         /*              */
                    _UWORD INP_FH25:10;                /*   INP_FH25   */
                    } BIT;                             /*              */
             } INP_VSYNC_PH_ADJ;                       /*              */
       union {                                         /* INP_DLY_ADJ  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD INP_VS_DLY_L:3;             /*   INP_VS_DLY_L */
                    _UWORD INP_FLD_DLY:8;              /*   INP_FLD_DLY */
                    _UWORD INP_VS_DLY:8;               /*   INP_VS_DLY */
                    _UWORD INP_HS_DLY:8;               /*   INP_HS_DLY */
                    } BIT;                             /*              */
             } INP_DLY_ADJ;                            /*              */
       _UBYTE wk0[108];                                /*              */
       union {                                         /* IMGCNT_UPDATE */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD IMGCNT_VEN:1;              /*   IMGCNT_VEN */
                    } BIT;                             /*              */
             } IMGCNT_UPDATE;                          /*              */
       union {                                         /* IMGCNT_NR_CNT0 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :11;                        /*              */
                    _UWORD NR1D_MD:1;                  /*   NR1D_MD    */
                    _UWORD :3;                         /*              */
                    _UWORD NR1D_ON:1;                  /*   NR1D_ON    */
                    _UWORD :1;                         /*              */
                    _UWORD NR1D_Y_TH:7;                /*   NR1D_Y_TH  */
                    _UWORD :2;                         /*              */
                    _UWORD NR1D_Y_TAP:2;               /*   NR1D_Y_TAP */
                    _UWORD :2;                         /*              */
                    _UWORD NR1D_Y_GAIN:2;              /*   NR1D_Y_GAIN */
                    } BIT;                             /*              */
             } IMGCNT_NR_CNT0;                         /*              */
       union {                                         /* IMGCNT_NR_CNT1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD NR1D_CB_TH:7;               /*   NR1D_CB_TH */
                    _UWORD :2;                         /*              */
                    _UWORD NR1D_CB_TAP:2;              /*   NR1D_CB_TAP */
                    _UWORD :2;                         /*              */
                    _UWORD NR1D_CB_GAIN:2;             /*   NR1D_CB_GAIN */
                    _UWORD :1;                         /*              */
                    _UWORD NR1D_CR_TH:7;               /*   NR1D_CR_TH */
                    _UWORD :2;                         /*              */
                    _UWORD NR1D_CR_TAP:2;              /*   NR1D_CR_TAP */
                    _UWORD :2;                         /*              */
                    _UWORD NR1D_CR_GAIN:2;             /*   NR1D_CR_GAIN */
                    } BIT;                             /*              */
             } IMGCNT_NR_CNT1;                         /*              */
       _UBYTE wk1[20];                                 /*              */
       union {                                         /* IMGCNT_MTX_MODE */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :30;                       /*              */
                    _UDWORD IMGCNT_MTX_MD:2;           /*   IMGCNT_MTX_MD */
                    } BIT;                             /*              */
             } IMGCNT_MTX_MODE;                        /*              */
       union {                                         /* IMGCNT_MTX_YG_ADJ0 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD IMGCNT_MTX_YG:8;            /*   IMGCNT_MTX_YG */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_GG:11;           /*   IMGCNT_MTX_GG */
                    } BIT;                             /*              */
             } IMGCNT_MTX_YG_ADJ0;                     /*              */
       union {                                         /* IMGCNT_MTX_YG_ADJ1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_GB:11;           /*   IMGCNT_MTX_GB */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_GR:11;           /*   IMGCNT_MTX_GR */
                    } BIT;                             /*              */
             } IMGCNT_MTX_YG_ADJ1;                     /*              */
       union {                                         /* IMGCNT_MTX_CBB_ADJ0 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD IMGCNT_MTX_B:8;             /*   IMGCNT_MTX_B */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_BG:11;           /*   IMGCNT_MTX_BG */
                    } BIT;                             /*              */
             } IMGCNT_MTX_CBB_ADJ0;                    /*              */
       union {                                         /* IMGCNT_MTX_CBB_ADJ1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_BB:11;           /*   IMGCNT_MTX_BB */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_BR:11;           /*   IMGCNT_MTX_BR */
                    } BIT;                             /*              */
             } IMGCNT_MTX_CBB_ADJ1;                    /*              */
       union {                                         /* IMGCNT_MTX_CRR_ADJ0 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD IMGCNT_MTX_R:8;             /*   IMGCNT_MTX_R */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_RG:11;           /*   IMGCNT_MTX_RG */
                    } BIT;                             /*              */
             } IMGCNT_MTX_CRR_ADJ0;                    /*              */
       union {                                         /* IMGCNT_MTX_CRR_ADJ1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_RB:11;           /*   IMGCNT_MTX_RB */
                    _UWORD :5;                         /*              */
                    _UWORD IMGCNT_MTX_RR:11;           /*   IMGCNT_MTX_RR */
                    } BIT;                             /*              */
             } IMGCNT_MTX_CRR_ADJ1;                    /*              */
       _UBYTE wk2[68];                                 /*              */
       union {                                         /* SCL0_UPDATE  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :18;                       /*              */
                    _UDWORD SCL0_VEN_D:1;              /*   SCL0_VEN_D */
                    _UDWORD SCL0_VEN_C:1;              /*   SCL0_VEN_C */
                    _UDWORD :3;                        /*              */
                    _UDWORD SCL0_UPDATE:1;             /*   SCL0_UPDATE */
                    _UDWORD :3;                        /*              */
                    _UDWORD SCL0_VEN_B:1;              /*   SCL0_VEN_B */
                    _UDWORD :3;                        /*              */
                    _UDWORD SCL0_VEN_A:1;              /*   SCL0_VEN_A */
                    } BIT;                             /*              */
             } SCL0_UPDATE;                            /*              */
       union {                                         /* SCL0_FRC1    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD RES_VMASK:16;               /*   RES_VMASK  */
                    _UWORD :15;                        /*              */
                    _UWORD RES_VMASK_ON:1;             /*   RES_VMASK_ON */
                    } BIT;                             /*              */
             } SCL0_FRC1;                              /*              */
       union {                                         /* SCL0_FRC2    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD RES_VLACK:16;               /*   RES_VLACK  */
                    _UWORD :15;                        /*              */
                    _UWORD RES_VLACK_ON:1;             /*   RES_VLACK_ON */
                    } BIT;                             /*              */
             } SCL0_FRC2;                              /*              */
       union {                                         /* SCL0_FRC3    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD RES_VS_SEL:1;              /*   RES_VS_SEL */
                    } BIT;                             /*              */
             } SCL0_FRC3;                              /*              */
       union {                                         /* SCL0_FRC4    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_FV:11;                  /*   RES_FV     */
                    _UWORD :5;                         /*              */
                    _UWORD RES_FH:11;                  /*   RES_FH     */
                    } BIT;                             /*              */
             } SCL0_FRC4;                              /*              */
       union {                                         /* SCL0_FRC5    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :23;                       /*              */
                    _UDWORD RES_FLD_DLY_SEL:1;         /*   RES_FLD_DLY_SEL */
                    _UDWORD RES_VSDLY:8;               /*   RES_VSDLY  */
                    } BIT;                             /*              */
             } SCL0_FRC5;                              /*              */
       union {                                         /* SCL0_FRC6    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_F_VS:11;                /*   RES_F_VS   */
                    _UWORD :5;                         /*              */
                    _UWORD RES_F_VW:11;                /*   RES_F_VW   */
                    } BIT;                             /*              */
             } SCL0_FRC6;                              /*              */
       union {                                         /* SCL0_FRC7    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_F_HS:11;                /*   RES_F_HS   */
                    _UWORD :5;                         /*              */
                    _UWORD RES_F_HW:11;                /*   RES_F_HW   */
                    } BIT;                             /*              */
             } SCL0_FRC7;                              /*              */
       _UBYTE wk3[4];                                  /*              */
       union {                                         /* SCL0_FRC9    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD RES_QVLOCK:1;              /*   RES_QVLOCK */
                    _UDWORD :3;                        /*              */
                    _UDWORD RES_QVLACK:1;              /*   RES_QVLACK */
                    } BIT;                             /*              */
             } SCL0_FRC9;                              /*              */
       _UBYTE wk4[4];                                  /*              */
       union {                                         /* SCL0_DS1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD RES_DS_V_ON:1;             /*   RES_DS_V_ON */
                    _UDWORD :3;                        /*              */
                    _UDWORD RES_DS_H_ON:1;             /*   RES_DS_H_ON */
                    } BIT;                             /*              */
             } SCL0_DS1;                               /*              */
       union {                                         /* SCL0_DS2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_VS:11;                  /*   RES_VS     */
                    _UWORD :5;                         /*              */
                    _UWORD RES_VW:11;                  /*   RES_VW     */
                    } BIT;                             /*              */
             } SCL0_DS2;                               /*              */
       union {                                         /* SCL0_DS3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_HS:11;                  /*   RES_HS     */
                    _UWORD :5;                         /*              */
                    _UWORD RES_HW:11;                  /*   RES_HW     */
                    } BIT;                             /*              */
             } SCL0_DS3;                               /*              */
       union {                                         /* SCL0_DS4     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD RES_PFIL_SEL:1;             /*   RES_PFIL_SEL */
                    _UWORD RES_DS_H_INTERPOTYP:1;      /*   RES_DS_H_INTERPOTYP */
                    _UWORD :12;                        /*              */
                    _UWORD RES_DS_H_RATIO:16;          /*   RES_DS_H_RATIO */
                    } BIT;                             /*              */
             } SCL0_DS4;                               /*              */
       union {                                         /* SCL0_DS5     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD RES_V_INTERPOTYP:1;         /*   RES_V_INTERPOTYP */
                    _UWORD RES_TOP_INIPHASE:12;        /*   RES_TOP_INIPHASE */
                    _UWORD :4;                         /*              */
                    _UWORD RES_BTM_INIPHASE:12;        /*   RES_BTM_INIPHASE */
                    } BIT;                             /*              */
             } SCL0_DS5;                               /*              */
       union {                                         /* SCL0_DS6     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :16;                        /*              */
                    _UWORD RES_V_RATIO:16;             /*   RES_V_RATIO */
                    } BIT;                             /*              */
             } SCL0_DS6;                               /*              */
       union {                                         /* SCL0_DS7     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_OUT_VW:11;              /*   RES_OUT_VW */
                    _UWORD :5;                         /*              */
                    _UWORD RES_OUT_HW:11;              /*   RES_OUT_HW */
                    } BIT;                             /*              */
             } SCL0_DS7;                               /*              */
       union {                                         /* SCL0_US1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD RES_US_V_ON:1;             /*   RES_US_V_ON */
                    _UDWORD :3;                        /*              */
                    _UDWORD RES_US_H_ON:1;             /*   RES_US_H_ON */
                    } BIT;                             /*              */
             } SCL0_US1;                               /*              */
       union {                                         /* SCL0_US2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_P_VS:11;                /*   RES_P_VS   */
                    _UWORD :5;                         /*              */
                    _UWORD RES_P_VW:11;                /*   RES_P_VW   */
                    } BIT;                             /*              */
             } SCL0_US2;                               /*              */
       union {                                         /* SCL0_US3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_P_HS:11;                /*   RES_P_HS   */
                    _UWORD :5;                         /*              */
                    _UWORD RES_P_HW:11;                /*   RES_P_HW   */
                    } BIT;                             /*              */
             } SCL0_US3;                               /*              */
       union {                                         /* SCL0_US4     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_IN_VW:11;               /*   RES_IN_VW  */
                    _UWORD :5;                         /*              */
                    _UWORD RES_IN_HW:11;               /*   RES_IN_HW  */
                    } BIT;                             /*              */
             } SCL0_US4;                               /*              */
       union {                                         /* SCL0_US5     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :16;                        /*              */
                    _UWORD RES_US_H_RATIO:16;          /*   RES_US_H_RATIO */
                    } BIT;                             /*              */
             } SCL0_US5;                               /*              */
       union {                                         /* SCL0_US6     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD RES_US_H_INTERPOTYP:1;      /*   RES_US_H_INTERPOTYP */
                    _UWORD RES_US_HT_INIPHASE:12;      /*   RES_US_HT_INIPHASE */
                    _UWORD :4;                         /*              */
                    _UWORD RES_US_HB_INIPHASE:12;      /*   RES_US_HB_INIPHASE */
                    } BIT;                             /*              */
             } SCL0_US6;                               /*              */
       union {                                         /* SCL0_US7     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :16;                        /*              */
                    _UWORD RES_HCUT:8;                 /*   RES_HCUT   */
                    _UWORD RES_VCUT:8;                 /*   RES_VCUT   */
                    } BIT;                             /*              */
             } SCL0_US7;                               /*              */
       union {                                         /* SCL0_US8     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD RES_IBUS_SYNC_SEL:1;       /*   RES_IBUS_SYNC_SEL */
                    _UDWORD :3;                        /*              */
                    _UDWORD RES_DISP_ON:1;             /*   RES_DISP_ON */
                    } BIT;                             /*              */
             } SCL0_US8;                               /*              */
       _UBYTE wk5[4];                                  /*              */
       union {                                         /* SCL0_OVR1    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD RES_BK_COL_R:8;             /*   RES_BK_COL_R */
                    _UWORD RES_BK_COL_G:8;             /*   RES_BK_COL_G */
                    _UWORD RES_BK_COL_B:8;             /*   RES_BK_COL_B */
                    } BIT;                             /*              */
             } SCL0_OVR1;                              /*              */
       _UBYTE wk6[16];                                 /*              */
       union {                                         /* SCL1_UPDATE  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD SCL1_VEN_B:1;              /*   SCL1_VEN_B */
                    _UDWORD :3;                        /*              */
                    _UDWORD SCL1_VEN_A:1;              /*   SCL1_VEN_A */
                    } BIT;                             /*              */
             } SCL1_UPDATE;                            /*              */
       _UBYTE wk7[4];                                  /*              */
       union {                                         /* SCL1_WR1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD RES_DS_WR_MD:3;            /*   RES_DS_WR_MD */
                    _UDWORD RES_MD:2;                  /*   RES_MD     */
                    _UDWORD RES_LOOP:1;                /*   RES_LOOP   */
                    _UDWORD RES_BST_MD:1;              /*   RES_BST_MD */
                    } BIT;                             /*              */
             } SCL1_WR1;                               /*              */
       union {                                         /* SCL1_WR2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RES_BASE:32;               /*   RES_BASE   */
                    } BIT;                             /*              */
             } SCL1_WR2;                               /*              */
       union {                                         /* SCL1_WR3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD RES_LN_OFF:15;              /*   RES_LN_OFF */
                    _UWORD :6;                         /*              */
                    _UWORD RES_FLM_NUM:10;             /*   RES_FLM_NUM */
                    } BIT;                             /*              */
             } SCL1_WR3;                               /*              */
       union {                                         /* SCL1_WR4     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :9;                        /*              */
                    _UDWORD RES_FLM_OFF:23;            /*   RES_FLM_OFF */
                    } BIT;                             /*              */
             } SCL1_WR4;                               /*              */
       _UBYTE wk8[4];                                  /*              */
       union {                                         /* SCL1_WR5     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :19;                       /*              */
                    _UDWORD RES_INTER:1;               /*   RES_INTER  */
                    _UDWORD :2;                        /*              */
                    _UDWORD RES_FS_RATE:2;             /*   RES_FS_RATE */
                    _UDWORD :3;                        /*              */
                    _UDWORD RES_FLD_SEL:1;             /*   RES_FLD_SEL */
                    _UDWORD :3;                        /*              */
                    _UDWORD RES_WENB:1;                /*   RES_WENB   */
                    } BIT;                             /*              */
             } SCL1_WR5;                               /*              */
       union {                                         /* SCL1_WR6     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD RES_DTH_ON:1;              /*   RES_DTH_ON */
                    _UDWORD :3;                        /*              */
                    _UDWORD RES_BITDEC_ON:1;           /*   RES_BITDEC_ON */
                    } BIT;                             /*              */
             } SCL1_WR6;                               /*              */
       union {                                         /* SCL1_WR7     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD RES_OVERFLOW:1;             /*   RES_OVERFLOW */
                    _UWORD :6;                         /*              */
                    _UWORD RES_FLM_CNT:10;             /*   RES_FLM_CNT */
                    } BIT;                             /*              */
             } SCL1_WR7;                               /*              */
       _UBYTE wk9[88];                                 /*              */
       union {                                         /* GR1_UPDATE   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD GR1_P_VEN:1;               /*   GR1_P_VEN  */
                    _UDWORD :3;                        /*              */
                    _UDWORD GR1_IBUS_VEN:1;            /*   GR1_IBUS_VEN */
                    } BIT;                             /*              */
             } GR1_UPDATE;                             /*              */
       union {                                         /* GR1_FLM_RD   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GR1_R_ENB:1;               /*   GR1_R_ENB  */
                    } BIT;                             /*              */
             } GR1_FLM_RD;                             /*              */
       union {                                         /* GR1_FLM1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD GR1_LN_OFF_DIR:1;           /*   GR1_LN_OFF_DIR */
                    _UWORD :6;                         /*              */
                    _UWORD GR1_FLM_SEL:2;              /*   GR1_FLM_SEL */
                    _UWORD :3;                         /*              */
                    _UWORD GR1_IMR_FLM_INV:1;          /*   GR1_IMR_FLM_INV */
                    _UWORD :3;                         /*              */
                    _UWORD GR1_BST_MD:1;               /*   GR1_BST_MD */
                    } BIT;                             /*              */
             } GR1_FLM1;                               /*              */
       union {                                         /* GR1_FLM2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD GR1_BASE:32;               /*   GR1_BASE   */
                    } BIT;                             /*              */
             } GR1_FLM2;                               /*              */
       union {                                         /* GR1_FLM3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD GR1_LN_OFF:15;              /*   GR1_LN_OFF */
                    _UWORD :6;                         /*              */
                    _UWORD GR1_FLM_NUM:10;             /*   GR1_FLM_NUM */
                    } BIT;                             /*              */
             } GR1_FLM3;                               /*              */
       union {                                         /* GR1_FLM4     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :9;                        /*              */
                    _UDWORD GR1_FLM_OFF:23;            /*   GR1_FLM_OFF */
                    } BIT;                             /*              */
             } GR1_FLM4;                               /*              */
       union {                                         /* GR1_FLM5     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD GR1_FLM_LNUM:10;            /*   GR1_FLM_LNUM */
                    _UWORD :6;                         /*              */
                    _UWORD GR1_FLM_LOOP:10;            /*   GR1_FLM_LOOP */
                    } BIT;                             /*              */
             } GR1_FLM5;                               /*              */
       union {                                         /* GR1_FLM6     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR1_FORMAT:4;               /*   GR1_FORMAT */
                    _UWORD :2;                         /*              */
                    _UWORD GR1_HW:10;                  /*   GR1_HW     */
                    _UWORD GR1_YCC_SWAP:3;             /*   GR1_YCC_SWAP */
                    _UWORD GR1_ENDIAN_ON:1;            /*   GR1_ENDIAN_ON */
                    _UWORD :3;                         /*              */
                    _UWORD GR1_CNV444_MD:1;            /*   GR1_CNV444_MD */
                    _UWORD :2;                         /*              */
                    _UWORD GR1_STA_POS:6;              /*   GR1_STA_POS */
                    } BIT;                             /*              */
             } GR1_FLM6;                               /*              */
       union {                                         /* GR1_AB1      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :16;                        /*              */
                    _UWORD :11;                        /*              */
                    _UWORD GR1_GRC_DISP_ON:1;          /*   GR1_GRC_DISP_ON */
                    _UWORD :2;                         /*              */
                    _UWORD GR1_DISP_SEL:2;             /*   GR1_DISP_SEL */
                    } BIT;                             /*              */
             } GR1_AB1;                                /*              */
       union {                                         /* GR1_AB2      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR1_GRC_VS:11;              /*   GR1_GRC_VS */
                    _UWORD :5;                         /*              */
                    _UWORD GR1_GRC_VW:11;              /*   GR1_GRC_VW */
                    } BIT;                             /*              */
             } GR1_AB2;                                /*              */
       union {                                         /* GR1_AB3      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR1_GRC_HS:11;              /*   GR1_GRC_HS */
                    _UWORD :5;                         /*              */
                    _UWORD GR1_GRC_HW:11;              /*   GR1_GRC_HW */
                    } BIT;                             /*              */
             } GR1_AB3;                                /*              */
       _UBYTE wk10_0[12];                              /*              */
       union {                                         /* GR1_AB7      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :16;                        /*              */
                    _UWORD :15;                        /*              */
                    _UWORD GR1_CK_ON:1;                /*   GR1_CK_ON  */
                    } BIT;                             /*              */
             } GR1_AB7;                                /*              */
       union {                                         /* GR1_AB8      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR1_CK_KCLUT:8;             /*   GR1_CK_KCLUT */
                    _UWORD GR1_CK_KG:8;                /*   GR1_CK_KG  */
                    _UWORD GR1_CK_KB:8;                /*   GR1_CK_KB  */
                    _UWORD GR1_CK_KR:8;                /*   GR1_CK_KR  */
                    } BIT;                             /*              */
             } GR1_AB8;                                /*              */
       union {                                         /* GR1_AB9      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR1_CK_A:8;                 /*   GR1_CK_A   */
                    _UWORD GR1_CK_G:8;                 /*   GR1_CK_G   */
                    _UWORD GR1_CK_B:8;                 /*   GR1_CK_B   */
                    _UWORD GR1_CK_R:8;                 /*   GR1_CK_R   */
                    } BIT;                             /*              */
             } GR1_AB9;                                /*              */
       union {                                         /* GR1_AB10     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR1_A0:8;                   /*   GR1_A0     */
                    _UWORD GR1_G0:8;                   /*   GR1_G0     */
                    _UWORD GR1_B0:8;                   /*   GR1_B0     */
                    _UWORD GR1_R0:8;                   /*   GR1_R0     */
                    } BIT;                             /*              */
             } GR1_AB10;                               /*              */
       union {                                         /* GR1_AB11     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR1_A1:8;                   /*   GR1_A1     */
                    _UWORD GR1_G1:8;                   /*   GR1_G1     */
                    _UWORD GR1_B1:8;                   /*   GR1_B1     */
                    _UWORD GR1_R1:8;                   /*   GR1_R1     */
                    } BIT;                             /*              */
             } GR1_AB11;                               /*              */
       union {                                         /* GR1_BASE     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GR1_BASE_G:8;               /*   GR1_BASE_G */
                    _UWORD GR1_BASE_B:8;               /*   GR1_BASE_B */
                    _UWORD GR1_BASE_R:8;               /*   GR1_BASE_R */
                    } BIT;                             /*              */
             } GR1_BASE;                               /*              */
       union {                                         /* GR1_CLUT     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD GR1_CLT_SEL:1;              /*   GR1_CLT_SEL */
                    _UWORD :16;                        /*              */
                    } BIT;                             /*              */
             } GR1_CLUT;                               /*              */
       _UBYTE wk10[44];                                /*              */
       union {                                         /* ADJ_UPDATE   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD ADJ_VEN:1;                 /*   ADJ_VEN    */
                    } BIT;                             /*              */
             } ADJ_UPDATE;                             /*              */
       union {                                         /* ADJ_BKSTR_SET */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD BKSTR_ON:1;                 /*   BKSTR_ON   */
                    _UWORD BKSTR_ST:4;                 /*   BKSTR_ST   */
                    _UWORD BKSTR_D:4;                  /*   BKSTR_D    */
                    _UWORD :3;                         /*              */
                    _UWORD BKSTR_T1:5;                 /*   BKSTR_T1   */
                    _UWORD :3;                         /*              */
                    _UWORD BKSTR_T2:5;                 /*   BKSTR_T2   */
                    } BIT;                             /*              */
             } ADJ_BKSTR_SET;                          /*              */
       union {                                         /* ADJ_ENH_TIM1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD ENH_MD:1;                  /*   ENH_MD     */
                    _UDWORD :3;                        /*              */
                    _UDWORD ENH_DISP_ON:1;             /*   ENH_DISP_ON */
                    } BIT;                             /*              */
             } ADJ_ENH_TIM1;                           /*              */
       union {                                         /* ADJ_ENH_TIM2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD ENH_VS:11;                  /*   ENH_VS     */
                    _UWORD :5;                         /*              */
                    _UWORD ENH_VW:11;                  /*   ENH_VW     */
                    } BIT;                             /*              */
             } ADJ_ENH_TIM2;                           /*              */
       union {                                         /* ADJ_ENH_TIM3 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD ENH_HS:11;                  /*   ENH_HS     */
                    _UWORD :5;                         /*              */
                    _UWORD ENH_HW:11;                  /*   ENH_HW     */
                    } BIT;                             /*              */
             } ADJ_ENH_TIM3;                           /*              */
       union {                                         /* ADJ_ENH_SHP1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD SHP_H_ON:1;                 /*   SHP_H_ON   */
                    _UWORD :9;                         /*              */
                    _UWORD SHP_H1_CORE:7;              /*   SHP_H1_CORE */
                    } BIT;                             /*              */
             } ADJ_ENH_SHP1;                           /*              */
       union {                                         /* ADJ_ENH_SHP2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD SHP_H1_CLIP_O:8;            /*   SHP_H1_CLIP_O */
                    _UWORD SHP_H1_CLIP_U:8;            /*   SHP_H1_CLIP_U */
                    _UWORD SHP_H1_GAIN_O:8;            /*   SHP_H1_GAIN_O */
                    _UWORD SHP_H1_GAIN_U:8;            /*   SHP_H1_GAIN_U */
                    } BIT;                             /*              */
             } ADJ_ENH_SHP2;                           /*              */
       union {                                         /* ADJ_ENH_SHP3 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD SHP_H2_LPF_SEL:1;           /*   SHP_H2_LPF_SEL */
                    _UWORD :9;                         /*              */
                    _UWORD SHP_H2_CORE:7;              /*   SHP_H2_CORE */
                    } BIT;                             /*              */
             } ADJ_ENH_SHP3;                           /*              */
       union {                                         /* ADJ_ENH_SHP4 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD SHP_H2_CLIP_O:8;            /*   SHP_H2_CLIP_O */
                    _UWORD SHP_H2_CLIP_U:8;            /*   SHP_H2_CLIP_U */
                    _UWORD SHP_H2_GAIN_O:8;            /*   SHP_H2_GAIN_O */
                    _UWORD SHP_H2_GAIN_U:8;            /*   SHP_H2_GAIN_U */
                    } BIT;                             /*              */
             } ADJ_ENH_SHP4;                           /*              */
       union {                                         /* ADJ_ENH_SHP5 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD SHP_H3_CORE:7;             /*   SHP_H3_CORE */
                    } BIT;                             /*              */
             } ADJ_ENH_SHP5;                           /*              */
       union {                                         /* ADJ_ENH_SHP6 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD SHP_H3_CLIP_O:8;            /*   SHP_H3_CLIP_O */
                    _UWORD SHP_H3_CLIP_U:8;            /*   SHP_H3_CLIP_U */
                    _UWORD SHP_H3_GAIN_O:8;            /*   SHP_H3_GAIN_O */
                    _UWORD SHP_H3_GAIN_U:8;            /*   SHP_H3_GAIN_U */
                    } BIT;                             /*              */
             } ADJ_ENH_SHP6;                           /*              */
       union {                                         /* ADJ_ENH_LTI1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD LTI_H_ON:1;                 /*   LTI_H_ON   */
                    _UWORD :6;                         /*              */
                    _UWORD LTI_H2_LPF_SEL:1;           /*   LTI_H2_LPF_SEL */
                    _UWORD LTI_H2_INC_ZERO:8;          /*   LTI_H2_INC_ZERO */
                    _UWORD LTI_H2_GAIN:8;              /*   LTI_H2_GAIN */
                    _UWORD LTI_H2_CORE:8;              /*   LTI_H2_CORE */
                    } BIT;                             /*              */
             } ADJ_ENH_LTI1;                           /*              */
       union {                                         /* ADJ_ENH_LTI2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD LTI_H4_MEDIAN_TAP_SEL:1;    /*   LTI_H4_MEDIAN_TAP_SEL */
                    _UWORD LTI_H4_INC_ZERO:8;          /*   LTI_H4_INC_ZERO */
                    _UWORD LTI_H4_GAIN:8;              /*   LTI_H4_GAIN */
                    _UWORD LTI_H4_CORE:8;              /*   LTI_H4_CORE */
                    } BIT;                             /*              */
             } ADJ_ENH_LTI2;                           /*              */
       union {                                         /* ADJ_MTX_MODE */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :30;                       /*              */
                    _UDWORD ADJ_MTX_MD:2;              /*   ADJ_MTX_MD */
                    } BIT;                             /*              */
             } ADJ_MTX_MODE;                           /*              */
       union {                                         /* ADJ_MTX_YG_ADJ0 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD ADJ_MTX_YG:8;               /*   ADJ_MTX_YG */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_GG:11;              /*   ADJ_MTX_GG */
                    } BIT;                             /*              */
             } ADJ_MTX_YG_ADJ0;                        /*              */
       union {                                         /* ADJ_MTX_YG_ADJ1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_GB:11;              /*   ADJ_MTX_GB */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_GR:11;              /*   ADJ_MTX_GR */
                    } BIT;                             /*              */
             } ADJ_MTX_YG_ADJ1;                        /*              */
       union {                                         /* ADJ_MTX_CBB_ADJ0 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD ADJ_MTX_B:8;                /*   ADJ_MTX_B  */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_BG:11;              /*   ADJ_MTX_BG */
                    } BIT;                             /*              */
             } ADJ_MTX_CBB_ADJ0;                       /*              */
       union {                                         /* ADJ_MTX_CBB_ADJ1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_BB:11;              /*   ADJ_MTX_BB */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_BR:11;              /*   ADJ_MTX_BR */
                    } BIT;                             /*              */
             } ADJ_MTX_CBB_ADJ1;                       /*              */
       union {                                         /* ADJ_MTX_CRR_ADJ0 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD ADJ_MTX_R:8;                /*   ADJ_MTX_R  */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_RG:11;              /*   ADJ_MTX_RG */
                    } BIT;                             /*              */
             } ADJ_MTX_CRR_ADJ0;                       /*              */
       union {                                         /* ADJ_MTX_CRR_ADJ1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_RB:11;              /*   ADJ_MTX_RB */
                    _UWORD :5;                         /*              */
                    _UWORD ADJ_MTX_RR:11;              /*   ADJ_MTX_RR */
                    } BIT;                             /*              */
             } ADJ_MTX_CRR_ADJ1;                       /*              */
       _UBYTE wk11[48];                                /*              */
       union {                                         /* GR2_UPDATE   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD GR2_P_VEN:1;               /*   GR2_P_VEN  */
                    _UDWORD :3;                        /*              */
                    _UDWORD GR2_IBUS_VEN:1;            /*   GR2_IBUS_VEN */
                    } BIT;                             /*              */
             } GR2_UPDATE;                             /*              */
       union {                                         /* GR2_FLM_RD   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GR2_R_ENB:1;               /*   GR2_R_ENB  */
                    } BIT;                             /*              */
             } GR2_FLM_RD;                             /*              */
       union {                                         /* GR2_FLM1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD GR2_LN_OFF_DIR:1;           /*   GR2_LN_OFF_DIR */
                    _UWORD :6;                         /*              */
                    _UWORD GR2_FLM_SEL:2;              /*   GR2_FLM_SEL */
                    _UWORD :7;                         /*              */
                    _UWORD GR2_BST_MD:1;               /*   GR2_BST_MD */
                    } BIT;                             /*              */
             } GR2_FLM1;                               /*              */
       union {                                         /* GR2_FLM2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD GR2_BASE:32;               /*   GR2_BASE   */
                    } BIT;                             /*              */
             } GR2_FLM2;                               /*              */
       union {                                         /* GR2_FLM3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD GR2_LN_OFF:15;              /*   GR2_LN_OFF */
                    _UWORD :6;                         /*              */
                    _UWORD GR2_FLM_NUM:10;             /*   GR2_FLM_NUM */
                    } BIT;                             /*              */
             } GR2_FLM3;                               /*              */
       union {                                         /* GR2_FLM4     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :9;                        /*              */
                    _UDWORD GR2_FLM_OFF:23;            /*   GR2_FLM_OFF */
                    } BIT;                             /*              */
             } GR2_FLM4;                               /*              */
       union {                                         /* GR2_FLM5     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD GR2_FLM_LNUM:10;            /*   GR2_FLM_LNUM */
                    _UWORD :6;                         /*              */
                    _UWORD GR2_FLM_LOOP:10;            /*   GR2_FLM_LOOP */
                    } BIT;                             /*              */
             } GR2_FLM5;                               /*              */
       union {                                         /* GR2_FLM6     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR2_FORMAT:4;               /*   GR2_FORMAT */
                    _UWORD :2;                         /*              */
                    _UWORD GR2_HW:10;                  /*   GR2_HW     */
                    _UWORD :3;                         /*              */
                    _UWORD GR2_ENDIAN_ON:1;            /*   GR2_ENDIAN_ON */
                    _UWORD :6;                         /*              */
                    _UWORD GR2_STA_POS:6;              /*   GR2_STA_POS */
                    } BIT;                             /*              */
             } GR2_FLM6;                               /*              */
       union {                                         /* GR2_AB1      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :19;                       /*              */
                    _UDWORD GR2_ARC_ON:1;              /*   GR2_ARC_ON */
                    _UDWORD :3;                        /*              */
                    _UDWORD GR2_ARC_DISP_ON:1;         /*   GR2_ARC_DISP_ON */
                    _UDWORD :3;                        /*              */
                    _UDWORD GR2_GRC_DISP_ON:1;         /*   GR2_GRC_DISP_ON */
                    _UDWORD :2;                        /*              */
                    _UDWORD GR2_DISP_SEL:2;            /*   GR2_DISP_SEL */
                    } BIT;                             /*              */
             } GR2_AB1;                                /*              */
       union {                                         /* GR2_AB2      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_GRC_VS:11;              /*   GR2_GRC_VS */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_GRC_VW:11;              /*   GR2_GRC_VW */
                    } BIT;                             /*              */
             } GR2_AB2;                                /*              */
       union {                                         /* GR2_AB3      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_GRC_HS:11;              /*   GR2_GRC_HS */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_GRC_HW:11;              /*   GR2_GRC_HW */
                    } BIT;                             /*              */
             } GR2_AB3;                                /*              */
       union {                                         /* GR2_AB4      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_ARC_VS:11;              /*   GR2_ARC_VS */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_ARC_VW:11;              /*   GR2_ARC_VW */
                    } BIT;                             /*              */
             } GR2_AB4;                                /*              */
       union {                                         /* GR2_AB5      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_ARC_HS:11;              /*   GR2_ARC_HS */
                    _UWORD :5;                         /*              */
                    _UWORD GR2_ARC_HW:11;              /*   GR2_ARC_HW */
                    } BIT;                             /*              */
             } GR2_AB5;                                /*              */
       union {                                         /* GR2_AB6      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD GR2_ARC_MODE:1;             /*   GR2_ARC_MODE */
                    _UWORD GR2_ARC_COEF:8;             /*   GR2_ARC_COEF */
                    _UWORD :8;                         /*              */
                    _UWORD GR2_ARC_RATE:8;             /*   GR2_ARC_RATE */
                    } BIT;                             /*              */
             } GR2_AB6;                                /*              */
       union {                                         /* GR2_AB7      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GR2_ARC_DEF:8;              /*   GR2_ARC_DEF */
                    _UWORD :15;                        /*              */
                    _UWORD GR2_CK_ON:1;                /*   GR2_CK_ON  */
                    } BIT;                             /*              */
             } GR2_AB7;                                /*              */
       union {                                         /* GR2_AB8      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR2_CK_KCLUT:8;             /*   GR2_CK_KCLUT */
                    _UWORD GR2_CK_KG:8;                /*   GR2_CK_KG  */
                    _UWORD GR2_CK_KB:8;                /*   GR2_CK_KB  */
                    _UWORD GR2_CK_KR:8;                /*   GR2_CK_KR  */
                    } BIT;                             /*              */
             } GR2_AB8;                                /*              */
       union {                                         /* GR2_AB9      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR2_CK_A:8;                 /*   GR2_CK_A   */
                    _UWORD GR2_CK_G:8;                 /*   GR2_CK_G   */
                    _UWORD GR2_CK_B:8;                 /*   GR2_CK_B   */
                    _UWORD GR2_CK_R:8;                 /*   GR2_CK_R   */
                    } BIT;                             /*              */
             } GR2_AB9;                                /*              */
       union {                                         /* GR2_AB10     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR2_A0:8;                   /*   GR2_A0     */
                    _UWORD GR2_G0:8;                   /*   GR2_G0     */
                    _UWORD GR2_B0:8;                   /*   GR2_B0     */
                    _UWORD GR2_R0:8;                   /*   GR2_R0     */
                    } BIT;                             /*              */
             } GR2_AB10;                               /*              */
       union {                                         /* GR2_AB11     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR2_A1:8;                   /*   GR2_A1     */
                    _UWORD GR2_G1:8;                   /*   GR2_G1     */
                    _UWORD GR2_B1:8;                   /*   GR2_B1     */
                    _UWORD GR2_R1:8;                   /*   GR2_R1     */
                    } BIT;                             /*              */
             } GR2_AB11;                               /*              */
       union {                                         /* GR2_BASE     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GR2_BASE_G:8;               /*   GR2_BASE_G */
                    _UWORD GR2_BASE_B:8;               /*   GR2_BASE_B */
                    _UWORD GR2_BASE_R:8;               /*   GR2_BASE_R */
                    } BIT;                             /*              */
             } GR2_BASE;                               /*              */
       union {                                         /* GR2_CLUT     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD GR2_CLT_SEL:1;              /*   GR2_CLT_SEL */
                    _UWORD :16;                        /*              */
                    } BIT;                             /*              */
             } GR2_CLUT;                               /*              */
       union {                                         /* GR2_MON      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GR2_ARC_ST:1;              /*   GR2_ARC_ST */
                    } BIT;                             /*              */
             } GR2_MON;                                /*              */
       _UBYTE wk12[40];                                /*              */
       union {                                         /* GR3_UPDATE   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD GR3_P_VEN:1;               /*   GR3_P_VEN  */
                    _UDWORD :3;                        /*              */
                    _UDWORD GR3_IBUS_VEN:1;            /*   GR3_IBUS_VEN */
                    } BIT;                             /*              */
             } GR3_UPDATE;                             /*              */
       union {                                         /* GR3_FLM_RD   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GR3_R_ENB:1;               /*   GR3_R_ENB  */
                    } BIT;                             /*              */
             } GR3_FLM_RD;                             /*              */
       union {                                         /* GR3_FLM1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD GR3_LN_OFF_DIR:1;           /*   GR3_LN_OFF_DIR */
                    _UWORD :6;                         /*              */
                    _UWORD GR3_FLM_SEL:2;              /*   GR3_FLM_SEL */
                    _UWORD :7;                         /*              */
                    _UWORD GR3_BST_MD:1;               /*   GR3_BST_MD */
                    } BIT;                             /*              */
             } GR3_FLM1;                               /*              */
       union {                                         /* GR3_FLM2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD GR3_BASE:32;               /*   GR3_BASE   */
                    } BIT;                             /*              */
             } GR3_FLM2;                               /*              */
       union {                                         /* GR3_FLM3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD GR3_LN_OFF:15;              /*   GR3_LN_OFF */
                    _UWORD :6;                         /*              */
                    _UWORD GR3_FLM_NUM:10;             /*   GR3_FLM_NUM */
                    } BIT;                             /*              */
             } GR3_FLM3;                               /*              */
       union {                                         /* GR3_FLM4     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :9;                        /*              */
                    _UDWORD GR3_FLM_OFF:23;            /*   GR3_FLM_OFF */
                    } BIT;                             /*              */
             } GR3_FLM4;                               /*              */
       union {                                         /* GR3_FLM5     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD GR3_FLM_LNUM:10;            /*   GR3_FLM_LNUM */
                    _UWORD :6;                         /*              */
                    _UWORD GR3_FLM_LOOP:10;            /*   GR3_FLM_LOOP */
                    } BIT;                             /*              */
             } GR3_FLM5;                               /*              */
       union {                                         /* GR3_FLM6     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR3_FORMAT:4;               /*   GR3_FORMAT */
                    _UWORD :2;                         /*              */
                    _UWORD GR3_HW:10;                  /*   GR3_HW     */
                    _UWORD :3;                         /*              */
                    _UWORD GR3_ENDIAN_ON:1;            /*   GR3_ENDIAN_ON */
                    _UWORD :6;                         /*              */
                    _UWORD GR3_STA_POS:6;              /*   GR3_STA_POS */
                    } BIT;                             /*              */
             } GR3_FLM6;                               /*              */
       union {                                         /* GR3_AB1      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :19;                       /*              */
                    _UDWORD GR3_ARC_ON:1;              /*   GR3_ARC_ON */
                    _UDWORD :3;                        /*              */
                    _UDWORD GR3_ARC_DISP_ON:1;         /*   GR3_ARC_DISP_ON */
                    _UDWORD :3;                        /*              */
                    _UDWORD GR3_GRC_DISP_ON:1;         /*   GR3_GRC_DISP_ON */
                    _UDWORD :2;                        /*              */
                    _UDWORD GR3_DISP_SEL:2;            /*   GR3_DISP_SEL */
                    } BIT;                             /*              */
             } GR3_AB1;                                /*              */
       union {                                         /* GR3_AB2      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_GRC_VS:11;              /*   GR3_GRC_VS */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_GRC_VW:11;              /*   GR3_GRC_VW */
                    } BIT;                             /*              */
             } GR3_AB2;                                /*              */
       union {                                         /* GR3_AB3      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_GRC_HS:11;              /*   GR3_GRC_HS */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_GRC_HW:11;              /*   GR3_GRC_HW */
                    } BIT;                             /*              */
             } GR3_AB3;                                /*              */
       union {                                         /* GR3_AB4      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_ARC_VS:11;              /*   GR3_ARC_VS */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_ARC_VW:11;              /*   GR3_ARC_VW */
                    } BIT;                             /*              */
             } GR3_AB4;                                /*              */
       union {                                         /* GR3_AB5      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_ARC_HS:11;              /*   GR3_ARC_HS */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_ARC_HW:11;              /*   GR3_ARC_HW */
                    } BIT;                             /*              */
             } GR3_AB5;                                /*              */
       union {                                         /* GR3_AB6      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD GR3_ARC_MODE:1;             /*   GR3_ARC_MODE */
                    _UWORD GR3_ARC_COEF:8;             /*   GR3_ARC_COEF */
                    _UWORD :8;                         /*              */
                    _UWORD GR3_ARC_RATE:8;             /*   GR3_ARC_RATE */
                    } BIT;                             /*              */
             } GR3_AB6;                                /*              */
       union {                                         /* GR3_AB7      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GR3_ARC_DEF:8;              /*   GR3_ARC_DEF */
                    _UWORD :15;                        /*              */
                    _UWORD GR3_CK_ON:1;                /*   GR3_CK_ON  */
                    } BIT;                             /*              */
             } GR3_AB7;                                /*              */
       union {                                         /* GR3_AB8      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR3_CK_KCLUT:8;             /*   GR3_CK_KCLUT */
                    _UWORD GR3_CK_KG:8;                /*   GR3_CK_KG  */
                    _UWORD GR3_CK_KB:8;                /*   GR3_CK_KB  */
                    _UWORD GR3_CK_KR:8;                /*   GR3_CK_KR  */
                    } BIT;                             /*              */
             } GR3_AB8;                                /*              */
       union {                                         /* GR3_AB9      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR3_CK_A:8;                 /*   GR3_CK_A   */
                    _UWORD GR3_CK_G:8;                 /*   GR3_CK_G   */
                    _UWORD GR3_CK_B:8;                 /*   GR3_CK_B   */
                    _UWORD GR3_CK_R:8;                 /*   GR3_CK_R   */
                    } BIT;                             /*              */
             } GR3_AB9;                                /*              */
       union {                                         /* GR3_AB10     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR3_A0:8;                   /*   GR3_A0     */
                    _UWORD GR3_G0:8;                   /*   GR3_G0     */
                    _UWORD GR3_B0:8;                   /*   GR3_B0     */
                    _UWORD GR3_R0:8;                   /*   GR3_R0     */
                    } BIT;                             /*              */
             } GR3_AB10;                               /*              */
       union {                                         /* GR3_AB11     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GR3_A1:8;                   /*   GR3_A1     */
                    _UWORD GR3_G1:8;                   /*   GR3_G1     */
                    _UWORD GR3_B1:8;                   /*   GR3_B1     */
                    _UWORD GR3_R1:8;                   /*   GR3_R1     */
                    } BIT;                             /*              */
             } GR3_AB11;                               /*              */
       union {                                         /* GR3_BASE     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GR3_BASE_G:8;               /*   GR3_BASE_G */
                    _UWORD GR3_BASE_B:8;               /*   GR3_BASE_B */
                    _UWORD GR3_BASE_R:8;               /*   GR3_BASE_R */
                    } BIT;                             /*              */
             } GR3_BASE;                               /*              */
       union {                                         /* GR3_CLUT_INT */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD GR3_CLT_SEL:1;              /*   GR3_CLT_SEL */
                    _UWORD :5;                         /*              */
                    _UWORD GR3_LINE:11;                /*              */
                    } BIT;                             /*              */
             } GR3_CLUT_INT;                           /*              */
       union {                                         /* GR3_MON      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GR3_ARC_ST:1;              /*   GR3_ARC_ST */
                    } BIT;                             /*              */
             } GR3_MON;                                /*              */
       _UBYTE wk13[40];                                /*              */
       union {                                         /* GAM_G_UPDATE */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GAM_G_VEN:1;               /*   GAM_G_VEN  */
                    } BIT;                             /*              */
             } GAM_G_UPDATE;                           /*              */
       union {                                         /* GAM_SW       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GAM_ON:1;                  /*   GAM_ON     */
                    } BIT;                             /*              */
             } GAM_SW;                                 /*              */
       union {                                         /* GAM_G_LUT1   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_00:11;           /*   GAM_G_GAIN_00 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_01:11;           /*   GAM_G_GAIN_01 */
                    } BIT;                             /*              */
             } GAM_G_LUT1;                             /*              */
       union {                                         /* GAM_G_LUT2   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_02:11;           /*   GAM_G_GAIN_02 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_03:11;           /*   GAM_G_GAIN_03 */
                    } BIT;                             /*              */
             } GAM_G_LUT2;                             /*              */
       union {                                         /* GAM_G_LUT3   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_04:11;           /*   GAM_G_GAIN_04 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_05:11;           /*   GAM_G_GAIN_05 */
                    } BIT;                             /*              */
             } GAM_G_LUT3;                             /*              */
       union {                                         /* GAM_G_LUT4   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_06:11;           /*   GAM_G_GAIN_06 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_07:11;           /*   GAM_G_GAIN_07 */
                    } BIT;                             /*              */
             } GAM_G_LUT4;                             /*              */
       union {                                         /* GAM_G_LUT5   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_08:11;           /*   GAM_G_GAIN_08 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_09:11;           /*   GAM_G_GAIN_09 */
                    } BIT;                             /*              */
             } GAM_G_LUT5;                             /*              */
       union {                                         /* GAM_G_LUT6   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_10:11;           /*   GAM_G_GAIN_10 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_11:11;           /*   GAM_G_GAIN_11 */
                    } BIT;                             /*              */
             } GAM_G_LUT6;                             /*              */
       union {                                         /* GAM_G_LUT7   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_12:11;           /*   GAM_G_GAIN_12 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_13:11;           /*   GAM_G_GAIN_13 */
                    } BIT;                             /*              */
             } GAM_G_LUT7;                             /*              */
       union {                                         /* GAM_G_LUT8   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_14:11;           /*   GAM_G_GAIN_14 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_15:11;           /*   GAM_G_GAIN_15 */
                    } BIT;                             /*              */
             } GAM_G_LUT8;                             /*              */
       union {                                         /* GAM_G_LUT9   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_16:11;           /*   GAM_G_GAIN_16 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_17:11;           /*   GAM_G_GAIN_17 */
                    } BIT;                             /*              */
             } GAM_G_LUT9;                             /*              */
       union {                                         /* GAM_G_LUT10  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_18:11;           /*   GAM_G_GAIN_18 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_19:11;           /*   GAM_G_GAIN_19 */
                    } BIT;                             /*              */
             } GAM_G_LUT10;                            /*              */
       union {                                         /* GAM_G_LUT11  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_20:11;           /*   GAM_G_GAIN_20 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_21:11;           /*   GAM_G_GAIN_21 */
                    } BIT;                             /*              */
             } GAM_G_LUT11;                            /*              */
       union {                                         /* GAM_G_LUT12  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_22:11;           /*   GAM_G_GAIN_22 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_23:11;           /*   GAM_G_GAIN_23 */
                    } BIT;                             /*              */
             } GAM_G_LUT12;                            /*              */
       union {                                         /* GAM_G_LUT13  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_24:11;           /*   GAM_G_GAIN_24 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_25:11;           /*   GAM_G_GAIN_25 */
                    } BIT;                             /*              */
             } GAM_G_LUT13;                            /*              */
       union {                                         /* GAM_G_LUT14  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_26:11;           /*   GAM_G_GAIN_26 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_27:11;           /*   GAM_G_GAIN_27 */
                    } BIT;                             /*              */
             } GAM_G_LUT14;                            /*              */
       union {                                         /* GAM_G_LUT15  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_28:11;           /*   GAM_G_GAIN_28 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_29:11;           /*   GAM_G_GAIN_29 */
                    } BIT;                             /*              */
             } GAM_G_LUT15;                            /*              */
       union {                                         /* GAM_G_LUT16  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_30:11;           /*   GAM_G_GAIN_30 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_G_GAIN_31:11;           /*   GAM_G_GAIN_31 */
                    } BIT;                             /*              */
             } GAM_G_LUT16;                            /*              */
       union {                                         /* GAM_G_AREA1  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GAM_G_TH_01:8;              /*   GAM_G_TH_01 */
                    _UWORD GAM_G_TH_02:8;              /*   GAM_G_TH_02 */
                    _UWORD GAM_G_TH_03:8;              /*   GAM_G_TH_03 */
                    } BIT;                             /*              */
             } GAM_G_AREA1;                            /*              */
       union {                                         /* GAM_G_AREA2  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_G_TH_04:8;              /*   GAM_G_TH_04 */
                    _UWORD GAM_G_TH_05:8;              /*   GAM_G_TH_05 */
                    _UWORD GAM_G_TH_06:8;              /*   GAM_G_TH_06 */
                    _UWORD GAM_G_TH_07:8;              /*   GAM_G_TH_07 */
                    } BIT;                             /*              */
             } GAM_G_AREA2;                            /*              */
       union {                                         /* GAM_G_AREA3  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_G_TH_08:8;              /*   GAM_G_TH_08 */
                    _UWORD GAM_G_TH_09:8;              /*   GAM_G_TH_09 */
                    _UWORD GAM_G_TH_10:8;              /*   GAM_G_TH_10 */
                    _UWORD GAM_G_TH_11:8;              /*   GAM_G_TH_11 */
                    } BIT;                             /*              */
             } GAM_G_AREA3;                            /*              */
       union {                                         /* GAM_G_AREA4  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_G_TH_12:8;              /*   GAM_G_TH_12 */
                    _UWORD GAM_G_TH_13:8;              /*   GAM_G_TH_13 */
                    _UWORD GAM_G_TH_14:8;              /*   GAM_G_TH_14 */
                    _UWORD GAM_G_TH_15:8;              /*   GAM_G_TH_15 */
                    } BIT;                             /*              */
             } GAM_G_AREA4;                            /*              */
       union {                                         /* GAM_G_AREA5  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_G_TH_16:8;              /*   GAM_G_TH_16 */
                    _UWORD GAM_G_TH_17:8;              /*   GAM_G_TH_17 */
                    _UWORD GAM_G_TH_18:8;              /*   GAM_G_TH_18 */
                    _UWORD GAM_G_TH_19:8;              /*   GAM_G_TH_19 */
                    } BIT;                             /*              */
             } GAM_G_AREA5;                            /*              */
       union {                                         /* GAM_G_AREA6  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_G_TH_20:8;              /*   GAM_G_TH_20 */
                    _UWORD GAM_G_TH_21:8;              /*   GAM_G_TH_21 */
                    _UWORD GAM_G_TH_22:8;              /*   GAM_G_TH_22 */
                    _UWORD GAM_G_TH_23:8;              /*   GAM_G_TH_23 */
                    } BIT;                             /*              */
             } GAM_G_AREA6;                            /*              */
       union {                                         /* GAM_G_AREA7  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_G_TH_24:8;              /*   GAM_G_TH_24 */
                    _UWORD GAM_G_TH_25:8;              /*   GAM_G_TH_25 */
                    _UWORD GAM_G_TH_26:8;              /*   GAM_G_TH_26 */
                    _UWORD GAM_G_TH_27:8;              /*   GAM_G_TH_27 */
                    } BIT;                             /*              */
             } GAM_G_AREA7;                            /*              */
       union {                                         /* GAM_G_AREA8  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_G_TH_28:8;              /*   GAM_G_TH_28 */
                    _UWORD GAM_G_TH_29:8;              /*   GAM_G_TH_29 */
                    _UWORD GAM_G_TH_30:8;              /*   GAM_G_TH_30 */
                    _UWORD GAM_G_TH_31:8;              /*   GAM_G_TH_31 */
                    } BIT;                             /*              */
             } GAM_G_AREA8;                            /*              */
       _UBYTE wk14[24];                                /*              */
       union {                                         /* GAM_B_UPDATE */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GAM_B_VEN:1;               /*   GAM_B_VEN  */
                    } BIT;                             /*              */
             } GAM_B_UPDATE;                           /*              */
       _UBYTE wk15[4];                                 /*              */
       union {                                         /* GAM_B_LUT1   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_00:11;           /*   GAM_B_GAIN_00 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_01:11;           /*   GAM_B_GAIN_01 */
                    } BIT;                             /*              */
             } GAM_B_LUT1;                             /*              */
       union {                                         /* GAM_B_LUT2   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_02:11;           /*   GAM_B_GAIN_02 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_03:11;           /*   GAM_B_GAIN_03 */
                    } BIT;                             /*              */
             } GAM_B_LUT2;                             /*              */
       union {                                         /* GAM_B_LUT3   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_04:11;           /*   GAM_B_GAIN_04 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_05:11;           /*   GAM_B_GAIN_05 */
                    } BIT;                             /*              */
             } GAM_B_LUT3;                             /*              */
       union {                                         /* GAM_B_LUT4   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_06:11;           /*   GAM_B_GAIN_06 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_07:11;           /*   GAM_B_GAIN_07 */
                    } BIT;                             /*              */
             } GAM_B_LUT4;                             /*              */
       union {                                         /* GAM_B_LUT5   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_08:11;           /*   GAM_B_GAIN_08 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_09:11;           /*   GAM_B_GAIN_09 */
                    } BIT;                             /*              */
             } GAM_B_LUT5;                             /*              */
       union {                                         /* GAM_B_LUT6   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_10:11;           /*   GAM_B_GAIN_10 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_11:11;           /*   GAM_B_GAIN_11 */
                    } BIT;                             /*              */
             } GAM_B_LUT6;                             /*              */
       union {                                         /* GAM_B_LUT7   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_12:11;           /*   GAM_B_GAIN_12 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_13:11;           /*   GAM_B_GAIN_13 */
                    } BIT;                             /*              */
             } GAM_B_LUT7;                             /*              */
       union {                                         /* GAM_B_LUT8   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_14:11;           /*   GAM_B_GAIN_14 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_15:11;           /*   GAM_B_GAIN_15 */
                    } BIT;                             /*              */
             } GAM_B_LUT8;                             /*              */
       union {                                         /* GAM_B_LUT9   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_16:11;           /*   GAM_B_GAIN_16 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_17:11;           /*   GAM_B_GAIN_17 */
                    } BIT;                             /*              */
             } GAM_B_LUT9;                             /*              */
       union {                                         /* GAM_B_LUT10  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_18:11;           /*   GAM_B_GAIN_18 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_19:11;           /*   GAM_B_GAIN_19 */
                    } BIT;                             /*              */
             } GAM_B_LUT10;                            /*              */
       union {                                         /* GAM_B_LUT11  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_20:11;           /*   GAM_B_GAIN_20 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_21:11;           /*   GAM_B_GAIN_21 */
                    } BIT;                             /*              */
             } GAM_B_LUT11;                            /*              */
       union {                                         /* GAM_B_LUT12  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_22:11;           /*   GAM_B_GAIN_22 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_23:11;           /*   GAM_B_GAIN_23 */
                    } BIT;                             /*              */
             } GAM_B_LUT12;                            /*              */
       union {                                         /* GAM_B_LUT13  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_24:11;           /*   GAM_B_GAIN_24 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_25:11;           /*   GAM_B_GAIN_25 */
                    } BIT;                             /*              */
             } GAM_B_LUT13;                            /*              */
       union {                                         /* GAM_B_LUT14  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_26:11;           /*   GAM_B_GAIN_26 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_27:11;           /*   GAM_B_GAIN_27 */
                    } BIT;                             /*              */
             } GAM_B_LUT14;                            /*              */
       union {                                         /* GAM_B_LUT15  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_28:11;           /*   GAM_B_GAIN_28 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_29:11;           /*   GAM_B_GAIN_29 */
                    } BIT;                             /*              */
             } GAM_B_LUT15;                            /*              */
       union {                                         /* GAM_B_LUT16  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_30:11;           /*   GAM_B_GAIN_30 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_B_GAIN_31:11;           /*   GAM_B_GAIN_31 */
                    } BIT;                             /*              */
             } GAM_B_LUT16;                            /*              */
       union {                                         /* GAM_B_AREA1  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GAM_B_TH_01:8;              /*   GAM_B_TH_01 */
                    _UWORD GAM_B_TH_02:8;              /*   GAM_B_TH_02 */
                    _UWORD GAM_B_TH_03:8;              /*   GAM_B_TH_03 */
                    } BIT;                             /*              */
             } GAM_B_AREA1;                            /*              */
       union {                                         /* GAM_B_AREA2  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_B_TH_04:8;              /*   GAM_B_TH_04 */
                    _UWORD GAM_B_TH_05:8;              /*   GAM_B_TH_05 */
                    _UWORD GAM_B_TH_06:8;              /*   GAM_B_TH_06 */
                    _UWORD GAM_B_TH_07:8;              /*   GAM_B_TH_07 */
                    } BIT;                             /*              */
             } GAM_B_AREA2;                            /*              */
       union {                                         /* GAM_B_AREA3  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_B_TH_08:8;              /*   GAM_B_TH_08 */
                    _UWORD GAM_B_TH_09:8;              /*   GAM_B_TH_09 */
                    _UWORD GAM_B_TH_10:8;              /*   GAM_B_TH_10 */
                    _UWORD GAM_B_TH_11:8;              /*   GAM_B_TH_11 */
                    } BIT;                             /*              */
             } GAM_B_AREA3;                            /*              */
       union {                                         /* GAM_B_AREA4  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_B_TH_12:8;              /*   GAM_B_TH_12 */
                    _UWORD GAM_B_TH_13:8;              /*   GAM_B_TH_13 */
                    _UWORD GAM_B_TH_14:8;              /*   GAM_B_TH_14 */
                    _UWORD GAM_B_TH_15:8;              /*   GAM_B_TH_15 */
                    } BIT;                             /*              */
             } GAM_B_AREA4;                            /*              */
       union {                                         /* GAM_B_AREA5  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_B_TH_16:8;              /*   GAM_B_TH_16 */
                    _UWORD GAM_B_TH_17:8;              /*   GAM_B_TH_17 */
                    _UWORD GAM_B_TH_18:8;              /*   GAM_B_TH_18 */
                    _UWORD GAM_B_TH_19:8;              /*   GAM_B_TH_19 */
                    } BIT;                             /*              */
             } GAM_B_AREA5;                            /*              */
       union {                                         /* GAM_B_AREA6  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_B_TH_20:8;              /*   GAM_B_TH_20 */
                    _UWORD GAM_B_TH_21:8;              /*   GAM_B_TH_21 */
                    _UWORD GAM_B_TH_22:8;              /*   GAM_B_TH_22 */
                    _UWORD GAM_B_TH_23:8;              /*   GAM_B_TH_23 */
                    } BIT;                             /*              */
             } GAM_B_AREA6;                            /*              */
       union {                                         /* GAM_B_AREA7  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_B_TH_24:8;              /*   GAM_B_TH_24 */
                    _UWORD GAM_B_TH_25:8;              /*   GAM_B_TH_25 */
                    _UWORD GAM_B_TH_26:8;              /*   GAM_B_TH_26 */
                    _UWORD GAM_B_TH_27:8;              /*   GAM_B_TH_27 */
                    } BIT;                             /*              */
             } GAM_B_AREA7;                            /*              */
       union {                                         /* GAM_B_AREA8  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_B_TH_28:8;              /*   GAM_B_TH_28 */
                    _UWORD GAM_B_TH_29:8;              /*   GAM_B_TH_29 */
                    _UWORD GAM_B_TH_30:8;              /*   GAM_B_TH_30 */
                    _UWORD GAM_B_TH_31:8;              /*   GAM_B_TH_31 */
                    } BIT;                             /*              */
             } GAM_B_AREA8;                            /*              */
       _UBYTE wk16[24];                                /*              */
       union {                                         /* GAM_R_UPDATE */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD GAM_R_VEN:1;               /*   GAM_R_VEN  */
                    } BIT;                             /*              */
             } GAM_R_UPDATE;                           /*              */
       _UBYTE wk17[4];                                 /*              */
       union {                                         /* GAM_R_LUT1   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_00:11;           /*   GAM_R_GAIN_00 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_01:11;           /*   GAM_R_GAIN_01 */
                    } BIT;                             /*              */
             } GAM_R_LUT1;                             /*              */
       union {                                         /* GAM_R_LUT2   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_02:11;           /*   GAM_R_GAIN_02 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_03:11;           /*   GAM_R_GAIN_03 */
                    } BIT;                             /*              */
             } GAM_R_LUT2;                             /*              */
       union {                                         /* GAM_R_LUT3   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_04:11;           /*   GAM_R_GAIN_04 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_05:11;           /*   GAM_R_GAIN_05 */
                    } BIT;                             /*              */
             } GAM_R_LUT3;                             /*              */
       union {                                         /* GAM_R_LUT4   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_06:11;           /*   GAM_R_GAIN_06 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_07:11;           /*   GAM_R_GAIN_07 */
                    } BIT;                             /*              */
             } GAM_R_LUT4;                             /*              */
       union {                                         /* GAM_R_LUT5   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_08:11;           /*   GAM_R_GAIN_08 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_09:11;           /*   GAM_R_GAIN_09 */
                    } BIT;                             /*              */
             } GAM_R_LUT5;                             /*              */
       union {                                         /* GAM_R_LUT6   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_10:11;           /*   GAM_R_GAIN_10 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_11:11;           /*   GAM_R_GAIN_11 */
                    } BIT;                             /*              */
             } GAM_R_LUT6;                             /*              */
       union {                                         /* GAM_R_LUT7   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_12:11;           /*   GAM_R_GAIN_12 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_13:11;           /*   GAM_R_GAIN_13 */
                    } BIT;                             /*              */
             } GAM_R_LUT7;                             /*              */
       union {                                         /* GAM_R_LUT8   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_14:11;           /*   GAM_R_GAIN_14 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_15:11;           /*   GAM_R_GAIN_15 */
                    } BIT;                             /*              */
             } GAM_R_LUT8;                             /*              */
       union {                                         /* GAM_R_LUT9   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_16:11;           /*   GAM_R_GAIN_16 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_17:11;           /*   GAM_R_GAIN_17 */
                    } BIT;                             /*              */
             } GAM_R_LUT9;                             /*              */
       union {                                         /* GAM_R_LUT10  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_18:11;           /*   GAM_R_GAIN_18 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_19:11;           /*   GAM_R_GAIN_19 */
                    } BIT;                             /*              */
             } GAM_R_LUT10;                            /*              */
       union {                                         /* GAM_R_LUT11  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_20:11;           /*   GAM_R_GAIN_20 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_21:11;           /*   GAM_R_GAIN_21 */
                    } BIT;                             /*              */
             } GAM_R_LUT11;                            /*              */
       union {                                         /* GAM_R_LUT12  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_22:11;           /*   GAM_R_GAIN_22 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_23:11;           /*   GAM_R_GAIN_23 */
                    } BIT;                             /*              */
             } GAM_R_LUT12;                            /*              */
       union {                                         /* GAM_R_LUT13  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_24:11;           /*   GAM_R_GAIN_24 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_25:11;           /*   GAM_R_GAIN_25 */
                    } BIT;                             /*              */
             } GAM_R_LUT13;                            /*              */
       union {                                         /* GAM_R_LUT14  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_26:11;           /*   GAM_R_GAIN_26 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_27:11;           /*   GAM_R_GAIN_27 */
                    } BIT;                             /*              */
             } GAM_R_LUT14;                            /*              */
       union {                                         /* GAM_R_LUT15  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_28:11;           /*   GAM_R_GAIN_28 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_29:11;           /*   GAM_R_GAIN_29 */
                    } BIT;                             /*              */
             } GAM_R_LUT15;                            /*              */
       union {                                         /* GAM_R_LUT16  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_30:11;           /*   GAM_R_GAIN_30 */
                    _UWORD :5;                         /*              */
                    _UWORD GAM_R_GAIN_31:11;           /*   GAM_R_GAIN_31 */
                    } BIT;                             /*              */
             } GAM_R_LUT16;                            /*              */
       union {                                         /* GAM_R_AREA1  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD GAM_R_TH_01:8;              /*   GAM_R_TH_01 */
                    _UWORD GAM_R_TH_02:8;              /*   GAM_R_TH_02 */
                    _UWORD GAM_R_TH_03:8;              /*   GAM_R_TH_03 */
                    } BIT;                             /*              */
             } GAM_R_AREA1;                            /*              */
       union {                                         /* GAM_R_AREA2  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_R_TH_04:8;              /*   GAM_R_TH_04 */
                    _UWORD GAM_R_TH_05:8;              /*   GAM_R_TH_05 */
                    _UWORD GAM_R_TH_06:8;              /*   GAM_R_TH_06 */
                    _UWORD GAM_R_TH_07:8;              /*   GAM_R_TH_07 */
                    } BIT;                             /*              */
             } GAM_R_AREA2;                            /*              */
       union {                                         /* GAM_R_AREA3  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_R_TH_08:8;              /*   GAM_R_TH_08 */
                    _UWORD GAM_R_TH_09:8;              /*   GAM_R_TH_09 */
                    _UWORD GAM_R_TH_10:8;              /*   GAM_R_TH_10 */
                    _UWORD GAM_R_TH_11:8;              /*   GAM_R_TH_11 */
                    } BIT;                             /*              */
             } GAM_R_AREA3;                            /*              */
       union {                                         /* GAM_R_AREA4  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_R_TH_12:8;              /*   GAM_R_TH_12 */
                    _UWORD GAM_R_TH_13:8;              /*   GAM_R_TH_13 */
                    _UWORD GAM_R_TH_14:8;              /*   GAM_R_TH_14 */
                    _UWORD GAM_R_TH_15:8;              /*   GAM_R_TH_15 */
                    } BIT;                             /*              */
             } GAM_R_AREA4;                            /*              */
       union {                                         /* GAM_R_AREA5  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_R_TH_16:8;              /*   GAM_R_TH_16 */
                    _UWORD GAM_R_TH_17:8;              /*   GAM_R_TH_17 */
                    _UWORD GAM_R_TH_18:8;              /*   GAM_R_TH_18 */
                    _UWORD GAM_R_TH_19:8;              /*   GAM_R_TH_19 */
                    } BIT;                             /*              */
             } GAM_R_AREA5;                            /*              */
       union {                                         /* GAM_R_AREA6  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_R_TH_20:8;              /*   GAM_R_TH_20 */
                    _UWORD GAM_R_TH_21:8;              /*   GAM_R_TH_21 */
                    _UWORD GAM_R_TH_22:8;              /*   GAM_R_TH_22 */
                    _UWORD GAM_R_TH_23:8;              /*   GAM_R_TH_23 */
                    } BIT;                             /*              */
             } GAM_R_AREA6;                            /*              */
       union {                                         /* GAM_R_AREA7  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_R_TH_24:8;              /*   GAM_R_TH_24 */
                    _UWORD GAM_R_TH_25:8;              /*   GAM_R_TH_25 */
                    _UWORD GAM_R_TH_26:8;              /*   GAM_R_TH_26 */
                    _UWORD GAM_R_TH_27:8;              /*   GAM_R_TH_27 */
                    } BIT;                             /*              */
             } GAM_R_AREA7;                            /*              */
       union {                                         /* GAM_R_AREA8  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD GAM_R_TH_28:8;              /*   GAM_R_TH_28 */
                    _UWORD GAM_R_TH_29:8;              /*   GAM_R_TH_29 */
                    _UWORD GAM_R_TH_30:8;              /*   GAM_R_TH_30 */
                    _UWORD GAM_R_TH_31:8;              /*   GAM_R_TH_31 */
                    } BIT;                             /*              */
             } GAM_R_AREA8;                            /*              */
       _UBYTE wk18[24];                                /*              */
       union {                                         /* TCON_UPDATE  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD TCON_VEN:1;                /*   TCON_VEN   */
                    } BIT;                             /*              */
             } TCON_UPDATE;                            /*              */
       union {                                         /* TCON_TIM     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_HALF:11;               /*   TCON_HALF  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_OFFSET:11;             /*   TCON_OFFSET */
                    } BIT;                             /*              */
             } TCON_TIM;                               /*              */
       union {                                         /* TCON_TIM_STVA1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STVA_VS:11;            /*   TCON_STVA_VS */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STVA_VW:11;            /*   TCON_STVA_VW */
                    } BIT;                             /*              */
             } TCON_TIM_STVA1;                         /*              */
       union {                                         /* TCON_TIM_STVA2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD TCON_STVA_INV:1;           /*   TCON_STVA_INV */
                    _UDWORD :1;                        /*              */
                    _UDWORD TCON_STVA_SEL:3;           /*   TCON_STVA_SEL */
                    } BIT;                             /*              */
             } TCON_TIM_STVA2;                         /*              */
       union {                                         /* TCON_TIM_STVB1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STVB_VS:11;            /*   TCON_STVB_VS */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STVB_VW:11;            /*   TCON_STVB_VW */
                    } BIT;                             /*              */
             } TCON_TIM_STVB1;                         /*              */
       union {                                         /* TCON_TIM_STVB2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD TCON_STVB_INV:1;           /*   TCON_STVB_INV */
                    _UDWORD :1;                        /*              */
                    _UDWORD TCON_STVB_SEL:3;           /*   TCON_STVB_SEL */
                    } BIT;                             /*              */
             } TCON_TIM_STVB2;                         /*              */
       union {                                         /* TCON_TIM_STH1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STH_HS:11;             /*   TCON_STH_HS */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STH_HW:11;             /*   TCON_STH_HW */
                    } BIT;                             /*              */
             } TCON_TIM_STH1;                          /*              */
       union {                                         /* TCON_TIM_STH2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :23;                       /*              */
                    _UDWORD TCON_STH_HS_SEL:1;         /*   TCON_STH_HS_SEL */
                    _UDWORD :3;                        /*              */
                    _UDWORD TCON_STH_INV:1;            /*   TCON_STH_INV */
                    _UDWORD :1;                        /*              */
                    _UDWORD TCON_STH_SEL:3;            /*   TCON_STH_SEL */
                    } BIT;                             /*              */
             } TCON_TIM_STH2;                          /*              */
       union {                                         /* TCON_TIM_STB1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STB_HS:11;             /*   TCON_STB_HS */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_STB_HW:11;             /*   TCON_STB_HW */
                    } BIT;                             /*              */
             } TCON_TIM_STB1;                          /*              */
       union {                                         /* TCON_TIM_STB2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :23;                       /*              */
                    _UDWORD TCON_STB_HS_SEL:1;         /*   TCON_STB_HS_SEL */
                    _UDWORD :3;                        /*              */
                    _UDWORD TCON_STB_INV:1;            /*   TCON_STB_INV */
                    _UDWORD :1;                        /*              */
                    _UDWORD TCON_STB_SEL:3;            /*   TCON_STB_SEL */
                    } BIT;                             /*              */
             } TCON_TIM_STB2;                          /*              */
       union {                                         /* TCON_TIM_CPV1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_CPV_HS:11;             /*   TCON_CPV_HS */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_CPV_HW:11;             /*   TCON_CPV_HW */
                    } BIT;                             /*              */
             } TCON_TIM_CPV1;                          /*              */
       union {                                         /* TCON_TIM_CPV2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :23;                       /*              */
                    _UDWORD TCON_CPV_HS_SEL:1;         /*   TCON_CPV_HS_SEL */
                    _UDWORD :3;                        /*              */
                    _UDWORD TCON_CPV_INV:1;            /*   TCON_CPV_INV */
                    _UDWORD :1;                        /*              */
                    _UDWORD TCON_CPV_SEL:3;            /*   TCON_CPV_SEL */
                    } BIT;                             /*              */
             } TCON_TIM_CPV2;                          /*              */
       union {                                         /* TCON_TIM_POLA1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_POLA_HS:11;            /*   TCON_POLA_HS */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_POLA_HW:11;            /*   TCON_POLA_HW */
                    } BIT;                             /*              */
             } TCON_TIM_POLA1;                         /*              */
       union {                                         /* TCON_TIM_POLA2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :18;                       /*              */
                    _UDWORD TCON_POLA_MD:2;            /*   TCON_POLA_MD */
                    _UDWORD :3;                        /*              */
                    _UDWORD TCON_POLA_HS_SEL:1;        /*   TCON_POLA_HS_SEL */
                    _UDWORD :3;                        /*              */
                    _UDWORD TCON_POLA_INV:1;           /*   TCON_POLA_INV */
                    _UDWORD :1;                        /*              */
                    _UDWORD TCON_POLA_SEL:3;           /*   TCON_POLA_SEL */
                    } BIT;                             /*              */
             } TCON_TIM_POLA2;                         /*              */
       union {                                         /* TCON_TIM_POLB1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_POLB_HS:11;            /*   TCON_POLB_HS */
                    _UWORD :5;                         /*              */
                    _UWORD TCON_POLB_HW:11;            /*   TCON_POLB_HW */
                    } BIT;                             /*              */
             } TCON_TIM_POLB1;                         /*              */
       union {                                         /* TCON_TIM_POLB2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :18;                       /*              */
                    _UDWORD TCON_POLB_MD:2;            /*   TCON_POLB_MD */
                    _UDWORD :3;                        /*              */
                    _UDWORD TCON_POLB_HS_SEL:1;        /*   TCON_POLB_HS_SEL */
                    _UDWORD :3;                        /*              */
                    _UDWORD TCON_POLB_INV:1;           /*   TCON_POLB_INV */
                    _UDWORD :1;                        /*              */
                    _UDWORD TCON_POLB_SEL:3;           /*   TCON_POLB_SEL */
                    } BIT;                             /*              */
             } TCON_TIM_POLB2;                         /*              */
       union {                                         /* TCON_TIM_DE  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD TCON_DE_INV:1;             /*   TCON_DE_INV */
                    } BIT;                             /*              */
             } TCON_TIM_DE;                            /*              */
       _UBYTE wk19[60];                                /*              */
       union {                                         /* OUT_UPDATE   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD OUTCNT_VEN:1;              /*   OUTCNT_VEN */
                    } BIT;                             /*              */
             } OUT_UPDATE;                             /*              */
       union {                                         /* OUT_SET      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD OUT_ENDIAN_ON:1;            /*   OUT_ENDIAN_ON */
                    _UWORD :3;                         /*              */
                    _UWORD OUT_SWAP_ON:1;              /*   OUT_SWAP_ON */
                    _UWORD :8;                         /*              */
                    _UWORD :2;                         /*              */
                    _UWORD OUT_FORMAT:2;               /*   OUT_FORMAT */
                    _UWORD :2;                         /*              */
                    _UWORD OUT_FRQ_SEL:2;              /*   OUT_FRQ_SEL */
                    _UWORD :3;                         /*              */
                    _UWORD OUT_DIR_SEL:1;              /*   OUT_DIR_SEL */
                    _UWORD :2;                         /*              */
                    _UWORD OUT_PHASE:2;                /*   OUT_PHASE  */
                    } BIT;                             /*              */
             } OUT_SET;                                /*              */
       union {                                         /* OUT_BRIGHT1  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD PBRT_G:10;                 /*   PBRT_G     */
                    } BIT;                             /*              */
             } OUT_BRIGHT1;                            /*              */
       union {                                         /* OUT_BRIGHT2  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD PBRT_B:10;                  /*   PBRT_B     */
                    _UWORD :6;                         /*              */
                    _UWORD PBRT_R:10;                  /*   PBRT_R     */
                    } BIT;                             /*              */
             } OUT_BRIGHT2;                            /*              */
       union {                                         /* OUT_CONTRAST */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :8;                         /*              */
                    _UWORD CONT_G:8;                   /*   CONT_G     */
                    _UWORD CONT_B:8;                   /*   CONT_B     */
                    _UWORD CONT_R:8;                   /*   CONT_R     */
                    } BIT;                             /*              */
             } OUT_CONTRAST;                           /*              */
       union {                                         /* OUT_PDTHA    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :10;                        /*              */
                    _UWORD PDTH_SEL:2;                 /*   PDTH_SEL   */
                    _UWORD :2;                         /*              */
                    _UWORD PDTH_FORMAT:2;              /*   PDTH_FORMAT */
                    _UWORD :2;                         /*              */
                    _UWORD PDTH_PA:2;                  /*   PDTH_PA    */
                    _UWORD :2;                         /*              */
                    _UWORD PDTH_PB:2;                  /*   PDTH_PB    */
                    _UWORD :2;                         /*              */
                    _UWORD PDTH_PC:2;                  /*   PDTH_PC    */
                    _UWORD :2;                         /*              */
                    _UWORD PDTH_PD:2;                  /*   PDTH_PD    */
                    } BIT;                             /*              */
             } OUT_PDTHA;                              /*              */
       _UBYTE wk20[12];                                /*              */
       union {                                         /* OUT_CLK_PHASE */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :19;                       /*              */
                    _UDWORD OUTCNT_FRONT_GAM:1;        /*   OUTCNT_FRONT_GAM */
                    _UDWORD :3;                        /*              */
                    _UDWORD OUTCNT_LCD_EDGE:1;         /*   OUTCNT_LCD_EDGE */
                    _UDWORD :1;                        /*              */
                    _UDWORD OUTCNT_STVA_EDGE:1;        /*   OUTCNT_STVA_EDGE */
                    _UDWORD OUTCNT_STVB_EDGE:1;        /*   OUTCNT_STVB_EDGE */
                    _UDWORD OUTCNT_STH_EDGE:1;         /*   OUTCNT_STH_EDGE */
                    _UDWORD OUTCNT_STB_EDGE:1;         /*   OUTCNT_STB_EDGE */
                    _UDWORD OUTCNT_CPV_EDGE:1;         /*   OUTCNT_CPV_EDGE */
                    _UDWORD OUTCNT_POLA_EDGE:1;        /*   OUTCNT_POLA_EDGE */
                    _UDWORD OUTCNT_POLB_EDGE:1;        /*   OUTCNT_POLB_EDGE */
                    } BIT;                             /*              */
             } OUT_CLK_PHASE;                          /*              */
       _UBYTE wk21[88];                                /*              */
       union {                                         /* SYSCNT_INT1  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD INT_STA8:1;                /*   INT_STA8   */
                    } BIT;                             /*              */
             } SYSCNT_INT1;                            /*              */
       union {                                         /* SYSCNT_INT2  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA7:1;                 /*   INT_STA7   */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA6:1;                 /*   INT_STA6   */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA5:1;                 /*   INT_STA5   */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA4:1;                 /*   INT_STA4   */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA3:1;                 /*   INT_STA3   */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA2:1;                 /*   INT_STA2   */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA1:1;                 /*   INT_STA1   */
                    _UWORD :3;                         /*              */
                    _UWORD INT_STA0:1;                 /*   INT_STA0   */
                    } BIT;                             /*              */
             } SYSCNT_INT2;                            /*              */
       union {                                         /* SYSCNT_INT3  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD INT_OUT8_ON:1;             /*   INT_OUT8_ON */
                    } BIT;                             /*              */
             } SYSCNT_INT3;                            /*              */
       union {                                         /* SYSCNT_INT4  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT7_ON:1;              /*   INT_OUT7_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT6_ON:1;              /*   INT_OUT6_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT5_ON:1;              /*   INT_OUT5_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT4_ON:1;              /*   INT_OUT4_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT3_ON:1;              /*   INT_OUT3_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT2_ON:1;              /*   INT_OUT2_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT1_ON:1;              /*   INT_OUT1_ON */
                    _UWORD :3;                         /*              */
                    _UWORD INT_OUT0_ON:1;              /*   INT_OUT0_ON */
                    } BIT;                             /*              */
             } SYSCNT_INT4;                            /*              */
       union {                                         /* SYSCNT_PANEL_CLK */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD PANEL_ICKSEL:2;             /*   PANEL_ICKSEL */
                    _UWORD :3;                         /*              */
                    _UWORD PANEL_ICKEN:1;              /*   PANEL_ICKEN */
                    _UWORD :2;                         /*              */
                    _UWORD PANEL_DCDR:6;               /*   PANEL_DCDR */
                    } BIT;                             /*              */
             } SYSCNT_PANEL_CLK;                       /*              */
       union {                                         /* SYSCNT_CLUT  */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD GR3_CLT_SEL_ST:1;           /*   GR3_CLT_SEL_ST */
                    _UWORD :3;                         /*              */
                    _UWORD GR2_CLT_SEL_ST:1;           /*   GR2_CLT_SEL_ST */
                    _UWORD :3;                         /*              */
                    _UWORD GR1_CLT_SEL_ST:1;           /*   GR1_CLT_SEL_ST */
                    } BIT;                             /*              */
             } SYSCNT_CLUT;                            /*              */
};                                                     /*              */
struct st_src {                                 /* struct SRC  */
       union {                                  /* SRCID        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             } SRCID;                           /*              */
       union {                                  /* SRCOD        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD H;                   /*   High       */
                    _UWORD L;                   /*   Low        */
                    } WORD;                     /*              */
             } SRCOD;                           /*              */
       union {                                  /* SRCIDCTRL    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD IED:1;               /*   IED        */
                    _UWORD IEN:1;               /*   IEN        */
                    _UWORD :6;                  /*              */
                    _UWORD IFTRG:2;             /*   IFTRG      */
                    } BIT;                      /*              */
             } SRCIDCTRL;                       /*              */
       union {                                  /* SRCODCTRL    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :5;                  /*              */
                    _UWORD OCH:1;               /*   OCH        */
                    _UWORD OED:1;               /*   OED        */
                    _UWORD OEN:1;               /*   OEN        */
                    _UWORD :6;                  /*              */
                    _UWORD OFTRG:2;             /*   OFTRG      */
                    } BIT;                      /*              */
             } SRCODCTRL;                       /*              */
       union {                                  /* SRCCTRL      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :2;                  /*              */
                    _UWORD CEEN:1;              /*   CEEN       */
                    _UWORD SRCEN:1;             /*   SRCEN      */
                    _UWORD UDEN:1;              /*   UDEN       */
                    _UWORD OVEN:1;              /*   OVEN       */
                    _UWORD FL:1;                /*   FL         */
                    _UWORD CL:1;                /*   CL         */
                    _UWORD IFS:4;               /*   IFS        */
                    _UWORD :1;                  /*              */
                    _UWORD OFS:3;               /*   OFS        */
                    } BIT;                      /*              */
             } SRCCTRL;                         /*              */
       union {                                  /* SRCSTAT      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD OFDN:5;              /*   OFDN       */
                    _UWORD IFDN:4;              /*   IFDN       */
                    _UWORD :1;                  /*              */
                    _UWORD CEF:1;               /*   CEF        */
                    _UWORD FLF:1;               /*   FLF        */
                    _UWORD UDF:1;               /*   UDF        */
                    _UWORD OVF:1;               /*   OVF        */
                    _UWORD IINT:1;              /*   IINT       */
                    _UWORD OINT:1;              /*   OINT       */
                    } BIT;                      /*              */
             } SRCSTAT;                         /*              */
};                                              /*              */
	#if	0
struct st_gpio {                                /* struct GPIO  */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* PAIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE PA1IOR:1;            /*   PA1IOR     */
                    _UBYTE :7;                  /*              */
                    _UBYTE PA0IOR:1;            /*   PA0IOR     */
                    } BIT;                      /*              */
             } PAIOR0;                          /*              */
       _UBYTE wk1[2];                           /*              */
       union {                                  /* PADR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE PA1DR:1;             /*   PA1DR      */
                    _UBYTE :7;                  /*              */
                    _UBYTE PA0DR:1;             /*   PA0DR      */
                    } BIT;                      /*              */
             } PADR0;                           /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* PAPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE :6;                  /*              */
                    _UBYTE PA1PR:1;             /*   PA1PR      */
                    _UBYTE PA0PR:1;             /*   PA0PR      */
                    } BIT;                      /*              */
             } PAPR0;                           /*              */
       _UBYTE wk3[8];                           /*              */
       union {                                  /* PBCR5        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE PB22MD:3;            /*   PB22MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB21MD:2;            /*   PB21MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB20MD:3;            /*   PB20MD     */
                    } BIT;                      /*              */
             } PBCR5;                           /*              */
       union {                                  /* PBCR4        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB19MD:3;            /*   PB19MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB18MD:3;            /*   PB18MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB17MD:3;            /*   PB17MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB16MD:3;            /*   PB16MD     */
                    } BIT;                      /*              */
             } PBCR4;                           /*              */
       union {                                  /* PBCR3        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB15MD:3;            /*   PB15MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB14MD:3;            /*   PB14MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB13MD:3;            /*   PB13MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB12MD:2;            /*   PB12MD     */
                    } BIT;                      /*              */
             } PBCR3;                           /*              */
       union {                                  /* PBCR2        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB11MD:2;            /*   PB11MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB10MD:2;            /*   PB10MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB9MD:2;             /*   PB9MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB8MD:2;             /*   PB8MD      */
                    } BIT;                      /*              */
             } PBCR2;                           /*              */
       union {                                  /* PBCR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB7MD:2;             /*   PB7MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB6MD:2;             /*   PB6MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB5MD:2;             /*   PB5MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB4MD:2;             /*   PB4MD      */
                    } BIT;                      /*              */
             } PBCR1;                           /*              */
       union {                                  /* PBCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB3MD:2;             /*   PB3MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB2MD:2;             /*   PB2MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PB1MD:2;             /*   PB1MD      */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } PBCR0;                           /*              */
       union {                                  /* PBIOR1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB22IOR:1;           /*   PB22IOR    */
                    _UBYTE PB21IOR:1;           /*   PB21IOR    */
                    _UBYTE PB20IOR:1;           /*   PB20IOR    */
                    _UBYTE PB19IOR:1;           /*   PB19IOR    */
                    _UBYTE PB18IOR:1;           /*   PB18IOR    */
                    _UBYTE PB17IOR:1;           /*   PB17IOR    */
                    _UBYTE PB16IOR:1;           /*   PB16IOR    */
                    } BIT;                      /*              */
             } PBIOR1;                          /*              */
       union {                                  /* PBIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PB15IOR:1;           /*   PB15IOR    */
                    _UBYTE PB14IOR:1;           /*   PB14IOR    */
                    _UBYTE PB13IOR:1;           /*   PB13IOR    */
                    _UBYTE PB12IOR:1;           /*   PB12IOR    */
                    _UBYTE PB11IOR:1;           /*   PB11IOR    */
                    _UBYTE PB10IOR:1;           /*   PB10IOR    */
                    _UBYTE PB9IOR:1;            /*   PB9IOR     */
                    _UBYTE PB8IOR:1;            /*   PB8IOR     */
                    _UBYTE PB7IOR:1;            /*   PB7IOR     */
                    _UBYTE PB6IOR:1;            /*   PB6IOR     */
                    _UBYTE PB5IOR:1;            /*   PB5IOR     */
                    _UBYTE PB4IOR:1;            /*   PB4IOR     */
                    _UBYTE PB3IOR:1;            /*   PB3IOR     */
                    _UBYTE PB2IOR:1;            /*   PB2IOR     */
                    _UBYTE PB1IOR:1;            /*   PB1IOR     */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } PBIOR0;                          /*              */
       union {                                  /* PBDR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB22DR:1;            /*   PB22DR     */
                    _UBYTE PB21DR:1;            /*   PB21DR     */
                    _UBYTE PB20DR:1;            /*   PB20DR     */
                    _UBYTE PB19DR:1;            /*   PB19DR     */
                    _UBYTE PB18DR:1;            /*   PB18DR     */
                    _UBYTE PB17DR:1;            /*   PB17DR     */
                    _UBYTE PB16DR:1;            /*   PB16DR     */
                    } BIT;                      /*              */
             } PBDR1;                           /*              */
       union {                                  /* PBDR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PB15DR:1;            /*   PB15DR     */
                    _UBYTE PB14DR:1;            /*   PB14DR     */
                    _UBYTE PB13DR:1;            /*   PB13DR     */
                    _UBYTE PB12DR:1;            /*   PB12DR     */
                    _UBYTE PB11DR:1;            /*   PB11DR     */
                    _UBYTE PB10DR:1;            /*   PB10DR     */
                    _UBYTE PB9DR:1;             /*   PB9DR      */
                    _UBYTE PB8DR:1;             /*   PB8DR      */
                    _UBYTE PB7DR:1;             /*   PB7DR      */
                    _UBYTE PB6DR:1;             /*   PB6DR      */
                    _UBYTE PB5DR:1;             /*   PB5DR      */
                    _UBYTE PB4DR:1;             /*   PB4DR      */
                    _UBYTE PB3DR:1;             /*   PB3DR      */
                    _UBYTE PB2DR:1;             /*   PB2DR      */
                    _UBYTE PB1DR:1;             /*   PB1DR      */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } PBDR0;                           /*              */
       union {                                  /* PBPR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE :1;                  /*              */
                    _UBYTE PB22PR:1;            /*   PB22PR     */
                    _UBYTE PB21PR:1;            /*   PB21PR     */
                    _UBYTE PB20PR:1;            /*   PB20PR     */
                    _UBYTE PB19PR:1;            /*   PB19PR     */
                    _UBYTE PB18PR:1;            /*   PB18PR     */
                    _UBYTE PB17PR:1;            /*   PB17PR     */
                    _UBYTE PB16PR:1;            /*   PB16PR     */
                    } BIT;                      /*              */
             } PBPR1;                           /*              */
       union {                                  /* PBPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PB15PR:1;            /*   PB15PR     */
                    _UBYTE PB14PR:1;            /*   PB14PR     */
                    _UBYTE PB13PR:1;            /*   PB13PR     */
                    _UBYTE PB12PR:1;            /*   PB12PR     */
                    _UBYTE PB11PR:1;            /*   PB11PR     */
                    _UBYTE PB10PR:1;            /*   PB10PR     */
                    _UBYTE PB9PR:1;             /*   PB9PR      */
                    _UBYTE PB8PR:1;             /*   PB8PR      */
                    _UBYTE PB7PR:1;             /*   PB7PR      */
                    _UBYTE PB6PR:1;             /*   PB6PR      */
                    _UBYTE PB5PR:1;             /*   PB5PR      */
                    _UBYTE PB4PR:1;             /*   PB4PR      */
                    _UBYTE PB3PR:1;             /*   PB3PR      */
                    _UBYTE PB2PR:1;             /*   PB2PR      */
                    _UBYTE PB1PR:1;             /*   PB1PR      */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } PBPR0;                           /*              */
       _UBYTE wk4[14];                          /*              */
       union {                                  /* PCCR2        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE :5;                  /*              */
                    _UBYTE PC8MD:3;             /*   PC8MD      */
                    } BIT;                      /*              */
             } PCCR2;                           /*              */
       union {                                  /* PCCR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PC7MD:3;             /*   PC7MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PC6MD:3;             /*   PC6MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PC5MD:3;             /*   PC5MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PC4MD:2;             /*   PC4MD      */
                    } BIT;                      /*              */
             } PCCR1;                           /*              */
       union {                                  /* PCCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PC3MD:2;             /*   PC3MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PC2MD:2;             /*   PC2MD      */
                    _UBYTE :3;                  /*              */
                    _UBYTE PC1MD:1;             /*   PC1MD      */
                    _UBYTE :3;                  /*              */
                    _UBYTE PC0MD:1;             /*   PC0MD      */
                    } BIT;                      /*              */
             } PCCR0;                           /*              */
       _UBYTE wk5[2];                           /*              */
       union {                                  /* PCIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE PC8IOR:1;            /*   PC8IOR     */
                    _UBYTE PC7IOR:1;            /*   PC7IOR     */
                    _UBYTE PC6IOR:1;            /*   PC6IOR     */
                    _UBYTE PC5IOR:1;            /*   PC5IOR     */
                    _UBYTE PC4IOR:1;            /*   PC4IOR     */
                    _UBYTE PC3IOR:1;            /*   PC3IOR     */
                    _UBYTE PC2IOR:1;            /*   PC2IOR     */
                    _UBYTE PC1IOR:1;            /*   PC1IOR     */
                    _UBYTE PC0IOR:1;            /*   PC0IOR     */
                    } BIT;                      /*              */
             } PCIOR0;                          /*              */
       _UBYTE wk6[2];                           /*              */
       union {                                  /* PCDR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE PC8DR:1;             /*   PC8DR      */
                    _UBYTE PC7DR:1;             /*   PC7DR      */
                    _UBYTE PC6DR:1;             /*   PC6DR      */
                    _UBYTE PC5DR:1;             /*   PC5DR      */
                    _UBYTE PC4DR:1;             /*   PC4DR      */
                    _UBYTE PC3DR:1;             /*   PC3DR      */
                    _UBYTE PC2DR:1;             /*   PC2DR      */
                    _UBYTE PC1DR:1;             /*   PC1DR      */
                    _UBYTE PC0DR:1;             /*   PC0DR      */
                    } BIT;                      /*              */
             } PCDR0;                           /*              */
       _UBYTE wk7[2];                           /*              */
       union {                                  /* PCPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE PC8PR:1;             /*   PC8PR      */
                    _UBYTE PC7PR:1;             /*   PC7PR      */
                    _UBYTE PC6PR:1;             /*   PC6PR      */
                    _UBYTE PC5PR:1;             /*   PC5PR      */
                    _UBYTE PC4PR:1;             /*   PC4PR      */
                    _UBYTE PC3PR:1;             /*   PC3PR      */
                    _UBYTE PC2PR:1;             /*   PC2PR      */
                    _UBYTE PC1PR:1;             /*   PC1PR      */
                    _UBYTE PC0PR:1;             /*   PC0PR      */
                    } BIT;                      /*              */
             } PCPR0;                           /*              */
       _UBYTE wk8[12];                          /*              */
       union {                                  /* PDCR3        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD15MD:2;            /*   PD15MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD14MD:2;            /*   PD14MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD13MD:2;            /*   PD13MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD12MD:2;            /*   PD12MD     */
                    } BIT;                      /*              */
             } PDCR3;                           /*              */
       union {                                  /* PDCR2        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD11MD:2;            /*   PD11MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD10MD:2;            /*   PD10MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD9MD:2;             /*   PD9MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD8MD:2;             /*   PD8MD      */
                    } BIT;                      /*              */
             } PDCR2;                           /*              */
       union {                                  /* PDCR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD7MD:2;             /*   PD7MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD6MD:2;             /*   PD6MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD5MD:2;             /*   PD5MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD4MD:2;             /*   PD4MD      */
                    } BIT;                      /*              */
             } PDCR1;                           /*              */
       union {                                  /* PDCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD3MD:2;             /*   PD3MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD2MD:2;             /*   PD2MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD1MD:2;             /*   PD1MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PD0MD:2;             /*   PD0MD      */
                    } BIT;                      /*              */
             } PDCR0;                           /*              */
       _UBYTE wk9[2];                           /*              */
       union {                                  /* PDIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PD15IOR:1;           /*   PD15IOR    */
                    _UBYTE PD14IOR:1;           /*   PD14IOR    */
                    _UBYTE PD13IOR:1;           /*   PD13IOR    */
                    _UBYTE PD12IOR:1;           /*   PD12IOR    */
                    _UBYTE PD11IOR:1;           /*   PD11IOR    */
                    _UBYTE PD10IOR:1;           /*   PD10IOR    */
                    _UBYTE PD9IOR:1;            /*   PD9IOR     */
                    _UBYTE PD8IOR:1;            /*   PD8IOR     */
                    _UBYTE PD7IOR:1;            /*   PD7IOR     */
                    _UBYTE PD6IOR:1;            /*   PD6IOR     */
                    _UBYTE PD5IOR:1;            /*   PD5IOR     */
                    _UBYTE PD4IOR:1;            /*   PD4IOR     */
                    _UBYTE PD3IOR:1;            /*   PD3IOR     */
                    _UBYTE PD2IOR:1;            /*   PD2IOR     */
                    _UBYTE PD1IOR:1;            /*   PD1IOR     */
                    _UBYTE PD0IOR:1;            /*   PD0IOR     */
                    } BIT;                      /*              */
             } PDIOR0;                          /*              */
       _UBYTE wk10[2];                          /*              */
       union {                                  /* PDDR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PD15DR:1;            /*   PD15DR     */
                    _UBYTE PD14DR:1;            /*   PD14DR     */
                    _UBYTE PD13DR:1;            /*   PD13DR     */
                    _UBYTE PD12DR:1;            /*   PD12DR     */
                    _UBYTE PD11DR:1;            /*   PD11DR     */
                    _UBYTE PD10DR:1;            /*   PD10DR     */
                    _UBYTE PD9DR:1;             /*   PD9DR      */
                    _UBYTE PD8DR:1;             /*   PD8DR      */
                    _UBYTE PD7DR:1;             /*   PD7DR      */
                    _UBYTE PD6DR:1;             /*   PD6DR      */
                    _UBYTE PD5DR:1;             /*   PD5DR      */
                    _UBYTE PD4DR:1;             /*   PD4DR      */
                    _UBYTE PD3DR:1;             /*   PD3DR      */
                    _UBYTE PD2DR:1;             /*   PD2DR      */
                    _UBYTE PD1DR:1;             /*   PD1DR      */
                    _UBYTE PD0DR:1;             /*   PD0DR      */
                    } BIT;                      /*              */
             } PDDR0;                           /*              */
       _UBYTE wk11[2];                          /*              */
       union {                                  /* PDPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PD15PR:1;            /*   PD15PR     */
                    _UBYTE PD14PR:1;            /*   PD14PR     */
                    _UBYTE PD13PR:1;            /*   PD13PR     */
                    _UBYTE PD12PR:1;            /*   PD12PR     */
                    _UBYTE PD11PR:1;            /*   PD11PR     */
                    _UBYTE PD10PR:1;            /*   PD10PR     */
                    _UBYTE PD9PR:1;             /*   PD9PR      */
                    _UBYTE PD8PR:1;             /*   PD8PR      */
                    _UBYTE PD7PR:1;             /*   PD7PR      */
                    _UBYTE PD6PR:1;             /*   PD6PR      */
                    _UBYTE PD5PR:1;             /*   PD5PR      */
                    _UBYTE PD4PR:1;             /*   PD4PR      */
                    _UBYTE PD3PR:1;             /*   PD3PR      */
                    _UBYTE PD2PR:1;             /*   PD2PR      */
                    _UBYTE PD1PR:1;             /*   PD1PR      */
                    _UBYTE PD0PR:1;             /*   PD0PR      */
                    } BIT;                      /*              */
             } PDPR0;                           /*              */
       _UBYTE wk12[16];                         /*              */
       union {                                  /* PECR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PE7MD:2;             /*   PE7MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PE6MD:2;             /*   PE6MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PE5MD:2;             /*   PE5MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PE4MD:2;             /*   PE4MD      */
                    } BIT;                      /*              */
             } PECR1;                           /*              */
       union {                                  /* PECR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PE3MD:3;             /*   PE3MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PE2MD:3;             /*   PE2MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PE1MD:3;             /*   PE1MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PE0MD:2;             /*   PE0MD      */
                    } BIT;                      /*              */
             } PECR0;                           /*              */
       _UBYTE wk13[2];                          /*              */
       union {                                  /* PEIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE PE7IOR:1;            /*   PE7IOR     */
                    _UBYTE PE6IOR:1;            /*   PE6IOR     */
                    _UBYTE PE5IOR:1;            /*   PE5IOR     */
                    _UBYTE PE4IOR:1;            /*   PE4IOR     */
                    _UBYTE PE3IOR:1;            /*   PE3IOR     */
                    _UBYTE PE2IOR:1;            /*   PE2IOR     */
                    _UBYTE PE1IOR:1;            /*   PE1IOR     */
                    _UBYTE PE0IOR:1;            /*   PE0IOR     */
                    } BIT;                      /*              */
             } PEIOR0;                          /*              */
       _UBYTE wk14[2];                          /*              */
       union {                                  /* PEDR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE PE7DR:1;             /*   PE7DR      */
                    _UBYTE PE6DR:1;             /*   PE6DR      */
                    _UBYTE PE5DR:1;             /*   PE5DR      */
                    _UBYTE PE4DR:1;             /*   PE4DR      */
                    _UBYTE PE3DR:1;             /*   PE3DR      */
                    _UBYTE PE2DR:1;             /*   PE2DR      */
                    _UBYTE PE1DR:1;             /*   PE1DR      */
                    _UBYTE PE0DR:1;             /*   PE0DR      */
                    } BIT;                      /*              */
             } PEDR0;                           /*              */
       _UBYTE wk15[2];                          /*              */
       union {                                  /* PEPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE PE7PR:1;             /*   PE7PR      */
                    _UBYTE PE6PR:1;             /*   PE6PR      */
                    _UBYTE PE5PR:1;             /*   PE5PR      */
                    _UBYTE PE4PR:1;             /*   PE4PR      */
                    _UBYTE PE3PR:1;             /*   PE3PR      */
                    _UBYTE PE2PR:1;             /*   PE2PR      */
                    _UBYTE PE1PR:1;             /*   PE1PR      */
                    _UBYTE PE0PR:1;             /*   PE0PR      */
                    } BIT;                      /*              */
             } PEPR0;                           /*              */
       _UBYTE wk16[6];                          /*              */
       union {                                  /* PFCR6        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF23MD :3;           /*   PF23MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF22MD :3;           /*   PF22MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF21MD :3;           /*   PF21MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF20MD :3;           /*   PF20MD     */
                    } BIT;                      /*              */
             } PFCR6;                           /*              */
       union {                                  /* PFCR5        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF19MD :3;           /*   PF19MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF18MD :3;           /*   PF18MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF17MD :3;           /*   PF17MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF16MD :3;           /*   PF16MD     */
                    } BIT;                      /*              */
             } PFCR5;                           /*              */
       union {                                  /* PFCR4        */
             _UWORD WORD;                       /* Read/Write Access */
             } PFCR4;                           /* Writing H'5A in the upper byte */
       union {                                  /* PFCR3        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE PF14MD:3;            /*   PF14MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF13MD:3;            /*   PF13MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF12MD:3;            /*   PF12MD     */
                    } BIT;                      /*              */
             } PFCR3;                           /*              */
       union {                                  /* PFCR2        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF11MD:3;            /*   PF11MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF10MD:3;            /*   PF10MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF9MD:3;             /*   PF9MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF8MD:3;             /*   PF8MD      */
                    } BIT;                      /*              */
             } PFCR2;                           /*              */
       union {                                  /* PFCR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF7MD:3;             /*   PF7MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF6MD:3;             /*   PF6MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF5MD:3;             /*   PF5MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF4MD:3;             /*   PF4MD      */
                    } BIT;                      /*              */
             } PFCR1;                           /*              */
       union {                                  /* PFCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF3MD:3;             /*   PF3MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF2MD:3;             /*   PF2MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF1MD:3;             /*   PF1MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PF0MD:3;             /*   PF0MD      */
                    } BIT;                      /*              */
             } PFCR0;                           /*              */
       union {                                  /* PFIOR1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE PF23IOR:1;           /*   PF23IOR    */
                    _UBYTE PF22IOR:1;           /*   PF22IOR    */
                    _UBYTE PF21IOR:1;           /*   PF21IOR    */
                    _UBYTE PF20IOR:1;           /*   PF20IOR    */
                    _UBYTE PF19IOR:1;           /*   PF19IOR    */
                    _UBYTE PF18IOR:1;           /*   PF18IOR    */
                    _UBYTE PF17IOR:1;           /*   PF17IOR    */
                    _UBYTE PF16IOR:1;           /*   PF16IOR    */
                    } BIT;                      /*              */
             } PFIOR1;                          /*              */
       union {                                  /* PFIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PF15IOR:1;           /*   PF15IOR    */
                    _UBYTE PF14IOR:1;           /*   PF14IOR    */
                    _UBYTE PF13IOR:1;           /*   PF13IOR    */
                    _UBYTE PF12IOR:1;           /*   PF12IOR    */
                    _UBYTE PF11IOR:1;           /*   PF11IOR    */
                    _UBYTE PF10IOR:1;           /*   PF10IOR    */
                    _UBYTE PF9IOR:1;            /*   PF9IOR     */
                    _UBYTE PF8IOR:1;            /*   PF8IOR     */
                    _UBYTE PF7IOR:1;            /*   PF7IOR     */
                    _UBYTE PF6IOR:1;            /*   PF6IOR     */
                    _UBYTE PF5IOR:1;            /*   PF5IOR     */
                    _UBYTE PF4IOR:1;            /*   PF4IOR     */
                    _UBYTE PF3IOR:1;            /*   PF3IOR     */
                    _UBYTE PF2IOR:1;            /*   PF2IOR     */
                    _UBYTE PF1IOR:1;            /*   PF1IOR     */
                    _UBYTE PF0IOR:1;            /*   PF0IOR     */
                    } BIT;                      /*              */
             } PFIOR0;                          /*              */
       union {                                  /* PFDR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE PF23DR:1;            /*   PF23DR     */
                    _UBYTE PF22DR:1;            /*   PF22DR     */
                    _UBYTE PF21DR:1;            /*   PF21DR     */
                    _UBYTE PF20DR:1;            /*   PF20DR     */
                    _UBYTE PF19DR:1;            /*   PF19DR     */
                    _UBYTE PF18DR:1;            /*   PF18DR     */
                    _UBYTE PF17DR:1;            /*   PF17DR     */
                    _UBYTE PF16DR:1;            /*   PF16DR     */
                    } BIT;                      /*              */
             } PFDR1;                           /*              */
       union {                                  /* PFDR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PF15DR:1;            /*   PF15DR     */
                    _UBYTE PF14DR:1;            /*   PF14DR     */
                    _UBYTE PF13DR:1;            /*   PF13DR     */
                    _UBYTE PF12DR:1;            /*   PF12DR     */
                    _UBYTE PF11DR:1;            /*   PF11DR     */
                    _UBYTE PF10DR:1;            /*   PF10DR     */
                    _UBYTE PF9DR:1;             /*   PF9DR      */
                    _UBYTE PF8DR:1;             /*   PF8DR      */
                    _UBYTE PF7DR:1;             /*   PF7DR      */
                    _UBYTE PF6DR:1;             /*   PF6DR      */
                    _UBYTE PF5DR:1;             /*   PF5DR      */
                    _UBYTE PF4DR:1;             /*   PF4DR      */
                    _UBYTE PF3DR:1;             /*   PF3DR      */
                    _UBYTE PF2DR:1;             /*   PF2DR      */
                    _UBYTE PF1DR:1;             /*   PF1DR      */
                    _UBYTE PF0DR:1;             /*   PF0DR      */
                    } BIT;                      /*              */
             } PFDR0;                           /*              */
       union {                                  /* PFPR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE PF23PR:1;            /*   PF23PR     */
                    _UBYTE PF22PR:1;            /*   PF22PR     */
                    _UBYTE PF21PR:1;            /*   PF21PR     */
                    _UBYTE PF20PR:1;            /*   PF20PR     */
                    _UBYTE PF19PR:1;            /*   PF19PR     */
                    _UBYTE PF18PR:1;            /*   PF18PR     */
                    _UBYTE PF17PR:1;            /*   PF17PR     */
                    _UBYTE PF16PR:1;            /*   PF16PR     */
                    } BIT;                      /*              */
             } PFPR1;                           /*              */
       union {                                  /* PFPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PF15PR:1;            /*   PF15PR     */
                    _UBYTE PF14PR:1;            /*   PF14PR     */
                    _UBYTE PF13PR:1;            /*   PF13PR     */
                    _UBYTE PF12PR:1;            /*   PF12PR     */
                    _UBYTE PF11PR:1;            /*   PF11PR     */
                    _UBYTE PF10PR:1;            /*   PF10PR     */
                    _UBYTE PF9PR:1;             /*   PF9PR      */
                    _UBYTE PF8PR:1;             /*   PF8PR      */
                    _UBYTE PF7PR:1;             /*   PF7PR      */
                    _UBYTE PF6PR:1;             /*   PF6PR      */
                    _UBYTE PF5PR:1;             /*   PF5PR      */
                    _UBYTE PF4PR:1;             /*   PF4PR      */
                    _UBYTE PF3PR:1;             /*   PF3PR      */
                    _UBYTE PF2PR:1;             /*   PF2PR      */
                    _UBYTE PF1PR:1;             /*   PF1PR      */
                    _UBYTE PF0PR:1;             /*   PF0PR      */
                    } BIT;                      /*              */
             } PFPR0;                           /*              */
       _UBYTE wk17[6];                          /*              */
       union {                                  /* PGCR6        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG27MD:2;            /*   PG27MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG26MD:2;            /*   PG26MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG25MD:2;            /*   PG25MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG24MD:2;            /*   PG24MD     */
                    } BIT;                      /*              */
             } PGCR6;                           /*              */
       union {                                  /* PGCR5        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG23MD:3;            /*   PG23MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG22MD:3;            /*   PG22MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG21MD:3;            /*   PG21MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG20MD:3;            /*   PG20MD     */
                    } BIT;                      /*              */
             } PGCR5;                           /*              */
       union {                                  /* PGCR4        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG19MD:3;            /*   PG19MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG18MD:3;            /*   PG18MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG17MD:2;            /*   PG17MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG16MD:2;            /*   PG16MD     */
                    } BIT;                      /*              */
             } PGCR4;                           /*              */
       union {                                  /* PGCR3        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG15MD:2;            /*   PG15MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG14MD:2;            /*   PG14MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG13MD:2;            /*   PG13MD     */
                    _UBYTE :2;                  /*              */
                    _UBYTE PG12MD:2;            /*   PG12MD     */
                    } BIT;                      /*              */
             } PGCR3;                           /*              */
       union {                                  /* PGCR2        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG11MD:3;            /*   PG11MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG10MD:3;            /*   PG10MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG9MD:3;             /*   PG9MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG8MD:3;             /*   PG8MD      */
                    } BIT;                      /*              */
             } PGCR2;                           /*              */
       union {                                  /* PGCR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG7MD:3;             /*   PG7MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG6MD:3;             /*   PG6MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG5MD:3;             /*   PG5MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG4MD:3;             /*   PG4MD      */
                    } BIT;                      /*              */
             } PGCR1;                           /*              */
       union {                                  /* PGCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG3MD:3;             /*   PG3MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG2MD:3;             /*   PG2MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG1MD:3;             /*   PG1MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PG0MD:3;             /*   PG0MD      */
                    } BIT;                      /*              */
             } PGCR0;                           /*              */
       union {                                  /* PGIOR1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE PG27IOR:1;           /*   PG27IOR    */
                    _UBYTE PG26IOR:1;           /*   PG26IOR    */
                    _UBYTE PG25IOR:1;           /*   PG25IOR    */
                    _UBYTE PG24IOR:1;           /*   PG24IOR    */
                    _UBYTE PG23IOR:1;           /*   PG23IOR    */
                    _UBYTE PG22IOR:1;           /*   PG22IOR    */
                    _UBYTE PG21IOR:1;           /*   PG21IOR    */
                    _UBYTE PG20IOR:1;           /*   PG20IOR    */
                    _UBYTE PG19IOR:1;           /*   PG19IOR    */
                    _UBYTE PG18IOR:1;           /*   PG18IOR    */
                    _UBYTE PG17IOR:1;           /*   PG17IOR    */
                    _UBYTE PG16IOR:1;           /*   PG16IOR    */
                    } BIT;                      /*              */
             } PGIOR1;                          /*              */
       union {                                  /* PGIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PG15IOR:1;           /*   PG15IOR    */
                    _UBYTE PG14IOR:1;           /*   PG14IOR    */
                    _UBYTE PG13IOR:1;           /*   PG13IOR    */
                    _UBYTE PG12IOR:1;           /*   PG12IOR    */
                    _UBYTE PG11IOR:1;           /*   PG11IOR    */
                    _UBYTE PG10IOR:1;           /*   PG10IOR    */
                    _UBYTE PG9IOR:1;            /*   PG9IOR     */
                    _UBYTE PG8IOR:1;            /*   PG8IOR     */
                    _UBYTE PG7IOR:1;            /*   PG7IOR     */
                    _UBYTE PG6IOR:1;            /*   PG6IOR     */
                    _UBYTE PG5IOR:1;            /*   PG5IOR     */
                    _UBYTE PG4IOR:1;            /*   PG4IOR     */
                    _UBYTE PG3IOR:1;            /*   PG3IOR     */
                    _UBYTE PG2IOR:1;            /*   PG2IOR     */
                    _UBYTE PG1IOR:1;            /*   PG1IOR     */
                    _UBYTE PG0IOR:1;            /*   PG0IOR     */
                    } BIT;                      /*              */
             } PGIOR0;                          /*              */
       union {                                  /* PGDR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE PG27DR:1;            /*   PG27DR     */
                    _UBYTE PG26DR:1;            /*   PG26DR     */
                    _UBYTE PG25DR:1;            /*   PG25DR     */
                    _UBYTE PG24DR:1;            /*   PG24DR     */
                    _UBYTE PG23DR:1;            /*   PG23DR     */
                    _UBYTE PG22DR:1;            /*   PG22DR     */
                    _UBYTE PG21DR:1;            /*   PG21DR     */
                    _UBYTE PG20DR:1;            /*   PG20DR     */
                    _UBYTE PG19DR:1;            /*   PG19DR     */
                    _UBYTE PG18DR:1;            /*   PG18DR     */
                    _UBYTE PG17DR:1;            /*   PG17DR     */
                    _UBYTE PG16DR:1;            /*   PG16DR     */
                    } BIT;                      /*              */
             } PGDR1;                           /*              */
       union {                                  /* PGDR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PG15DR:1;            /*   PG15DR     */
                    _UBYTE PG14DR:1;            /*   PG14DR     */
                    _UBYTE PG13DR:1;            /*   PG13DR     */
                    _UBYTE PG12DR:1;            /*   PG12DR     */
                    _UBYTE PG11DR:1;            /*   PG11DR     */
                    _UBYTE PG10DR:1;            /*   PG10DR     */
                    _UBYTE PG9DR:1;             /*   PG9DR      */
                    _UBYTE PG8DR:1;             /*   PG8DR      */
                    _UBYTE PG7DR:1;             /*   PG7DR      */
                    _UBYTE PG6DR:1;             /*   PG6DR      */
                    _UBYTE PG5DR:1;             /*   PG5DR      */
                    _UBYTE PG4DR:1;             /*   PG4DR      */
                    _UBYTE PG3DR:1;             /*   PG3DR      */
                    _UBYTE PG2DR:1;             /*   PG2DR      */
                    _UBYTE PG1DR:1;             /*   PG1DR      */
                    _UBYTE PG0DR:1;             /*   PG0DR      */
                    } BIT;                      /*              */
             } PGDR0;                           /*              */
       union {                                  /* PGPR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE PG27PR:1;            /*   PG27PR     */
                    _UBYTE PG26PR:1;            /*   PG26PR     */
                    _UBYTE PG25PR:1;            /*   PG25PR     */
                    _UBYTE PG24PR:1;            /*   PG24PR     */
                    _UBYTE PG23PR:1;            /*   PG23PR     */
                    _UBYTE PG22PR:1;            /*   PG22PR     */
                    _UBYTE PG21PR:1;            /*   PG21PR     */
                    _UBYTE PG20PR:1;            /*   PG20PR     */
                    _UBYTE PG19PR:1;            /*   PG19PR     */
                    _UBYTE PG18PR:1;            /*   PG18PR     */
                    _UBYTE PG17PR:1;            /*   PG17PR     */
                    _UBYTE PG16PR:1;            /*   PG16PR     */
                    } BIT;                      /*              */
             } PGPR1;                           /*              */
       union {                                  /* PGPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PG15PR:1;            /*   PG15PR     */
                    _UBYTE PG14PR:1;            /*   PG14PR     */
                    _UBYTE PG13PR:1;            /*   PG13PR     */
                    _UBYTE PG12PR:1;            /*   PG12PR     */
                    _UBYTE PG11PR:1;            /*   PG11PR     */
                    _UBYTE PG10PR:1;            /*   PG10PR     */
                    _UBYTE PG9PR:1;             /*   PG9PR      */
                    _UBYTE PG8PR:1;             /*   PG8PR      */
                    _UBYTE PG7PR:1;             /*   PG7PR      */
                    _UBYTE PG6PR:1;             /*   PG6PR      */
                    _UBYTE PG5PR:1;             /*   PG5PR      */
                    _UBYTE PG4PR:1;             /*   PG4PR      */
                    _UBYTE PG3PR:1;             /*   PG3PR      */
                    _UBYTE PG2PR:1;             /*   PG2PR      */
                    _UBYTE PG1PR:1;             /*   PG1PR      */
                    _UBYTE PG0PR:1;             /*   PG0PR      */
                    } BIT;                      /*              */
             } PGPR0;                           /*              */
       _UBYTE wk18[16];                         /*              */
       union {                                  /* PHCR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH7MD:2;             /*   PH7MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH6MD:2;             /*   PH6MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH5MD:2;             /*   PH5MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH4MD:2;             /*   PH4MD      */
                    } BIT;                      /*              */
             } PHCR1;                           /*              */
       union {                                  /* PHCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH3MD:2;             /*   PH3MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH2MD:2;             /*   PH2MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH1MD:2;             /*   PH1MD      */
                    _UBYTE :2;                  /*              */
                    _UBYTE PH0MD:2;             /*   PH0MD      */
                    } BIT;                      /*              */
             } PHCR0;                           /*              */
       _UBYTE wk19[10];                         /*              */
       union {                                  /* PHPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE PH7PR:1;             /*   PH7PR      */
                    _UBYTE PH6PR:1;             /*   PH6PR      */
                    _UBYTE PH5PR:1;             /*   PH5PR      */
                    _UBYTE PH4PR:1;             /*   PH4PR      */
                    _UBYTE PH3PR:1;             /*   PH3PR      */
                    _UBYTE PH2PR:1;             /*   PH2PR      */
                    _UBYTE PH1PR:1;             /*   PH1PR      */
                    _UBYTE PH0PR:1;             /*   PH0PR      */
                    } BIT;                      /*              */
             } PHPR0;                           /*              */
       _UBYTE wk20[4];                          /*              */
       union {                                  /* PJCR7        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :3;                  /*              */
                    _UBYTE PJ31MD:1;            /*   PJ31MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ30MD:3;            /*   PJ30MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ29MD:3;            /*   PJ29MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ28MD:3;            /*   PJ28MD     */
                    } BIT;                      /*              */
             } PJCR7;                           /*              */
       union {                                  /* PJCR6        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ27MD:3;            /*   PJ27MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ26MD:3;            /*   PJ26MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ25MD:3;            /*   PJ25MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ24MD:3;            /*   PJ24MD     */
                    } BIT;                      /*              */
             } PJCR6;                           /*              */
       union {                                  /* PJCR5        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ23MD:3;            /*   PJ23MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ22MD:3;            /*   PJ22MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ21MD:3;            /*   PJ21MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ20MD:3;            /*   PJ20MD     */
                    } BIT;                      /*              */
             } PJCR5;                           /*              */
       union {                                  /* PJCR4        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ19MD:3;            /*   PJ19MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ18MD:3;            /*   PJ18MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ17MD:3;            /*   PJ17MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ16MD:3;            /*   PJ16MD     */
                    } BIT;                      /*              */
             } PJCR4;                           /*              */
       union {                                  /* PJCR3        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ15MD:3;            /*   PJ15MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ14MD:3;            /*   PJ14MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ13MD:3;            /*   PJ13MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ12MD:3;            /*   PJ12MD     */
                    } BIT;                      /*              */
             } PJCR3;                           /*              */
       union {                                  /* PJCR2        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ11MD:3;            /*   PJ11MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ10MD:3;            /*   PJ10MD     */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ9MD:3;             /*   PJ9MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ8MD:3;             /*   PJ8MD      */
                    } BIT;                      /*              */
             } PJCR2;                           /*              */
       union {                                  /* PJCR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ7MD:3;             /*   PJ7MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ6MD:3;             /*   PJ6MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ5MD:3;             /*   PJ5MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ4MD:3;             /*   PJ4MD      */
                    } BIT;                      /*              */
             } PJCR1;                           /*              */
       union {                                  /* PJCR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ3MD:3;             /*   PJ3MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ2MD:3;             /*   PJ2MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ1MD:3;             /*   PJ1MD      */
                    _UBYTE :1;                  /*              */
                    _UBYTE PJ0MD:3;             /*   PJ0MD      */
                    } BIT;                      /*              */
             } PJCR0;                           /*              */
       union {                                  /* PJIOR1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PJ31IOR:1;           /*   PJ31IOR    */
                    _UBYTE PJ30IOR:1;           /*   PJ30IOR    */
                    _UBYTE PJ29IOR:1;           /*   PJ29IOR    */
                    _UBYTE PJ28IOR:1;           /*   PJ28IOR    */
                    _UBYTE PJ27IOR:1;           /*   PJ27IOR    */
                    _UBYTE PJ26IOR:1;           /*   PJ26IOR    */
                    _UBYTE PJ25IOR:1;           /*   PJ25IOR    */
                    _UBYTE PJ24IOR:1;           /*   PJ24IOR    */
                    _UBYTE PJ23IOR:1;           /*   PJ23IOR    */
                    _UBYTE PJ22IOR:1;           /*   PJ22IOR    */
                    _UBYTE PJ21IOR:1;           /*   PJ21IOR    */
                    _UBYTE PJ20IOR:1;           /*   PJ20IOR    */
                    _UBYTE PJ19IOR:1;           /*   PJ19IOR    */
                    _UBYTE PJ18IOR:1;           /*   PJ18IOR    */
                    _UBYTE PJ17IOR:1;           /*   PJ17IOR    */
                    _UBYTE PJ16IOR:1;           /*   PJ16IOR    */
                    } BIT;                      /*              */
             } PJIOR1;                          /*              */
       union {                                  /* PJIOR0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PJ15IOR:1;           /*   PJ15IOR    */
                    _UBYTE PJ14IOR:1;           /*   PJ14IOR    */
                    _UBYTE PJ13IOR:1;           /*   PJ13IOR    */
                    _UBYTE PJ12IOR:1;           /*   PJ12IOR    */
                    _UBYTE PJ11IOR:1;           /*   PJ11IOR    */
                    _UBYTE PJ10IOR:1;           /*   PJ10IOR    */
                    _UBYTE PJ9IOR:1;            /*   PJ9IOR     */
                    _UBYTE PJ8IOR:1;            /*   PJ8IOR     */
                    _UBYTE PJ7IOR:1;            /*   PJ7IOR     */
                    _UBYTE PJ6IOR:1;            /*   PJ6IOR     */
                    _UBYTE PJ5IOR:1;            /*   PJ5IOR     */
                    _UBYTE PJ4IOR:1;            /*   PJ4IOR     */
                    _UBYTE PJ3IOR:1;            /*   PJ3IOR     */
                    _UBYTE PJ2IOR:1;            /*   PJ2IOR     */
                    _UBYTE PJ1IOR:1;            /*   PJ1IOR     */
                    _UBYTE PJ0IOR:1;            /*   PJ0IOR     */
                    } BIT;                      /*              */
             } PJIOR0;                          /*              */
       union {                                  /* PJDR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PJ31DR:1;            /*   PJ31DR     */
                    _UBYTE PJ30DR:1;            /*   PJ30DR     */
                    _UBYTE PJ29DR:1;            /*   PJ29DR     */
                    _UBYTE PJ28DR:1;            /*   PJ28DR     */
                    _UBYTE PJ27DR:1;            /*   PJ27DR     */
                    _UBYTE PJ26DR:1;            /*   PJ26DR     */
                    _UBYTE PJ25DR:1;            /*   PJ25DR     */
                    _UBYTE PJ24DR:1;            /*   PJ24DR     */
                    _UBYTE PJ23DR:1;            /*   PJ23DR     */
                    _UBYTE PJ22DR:1;            /*   PJ22DR     */
                    _UBYTE PJ21DR:1;            /*   PJ21DR     */
                    _UBYTE PJ20DR:1;            /*   PJ20DR     */
                    _UBYTE PJ19DR:1;            /*   PJ19DR     */
                    _UBYTE PJ18DR:1;            /*   PJ18DR     */
                    _UBYTE PJ17DR:1;            /*   PJ17DR     */
                    _UBYTE PJ16DR:1;            /*   PJ16DR     */
                    } BIT;                      /*              */
             } PJDR1;                           /*              */
       union {                                  /* PJDR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PJ15DR:1;            /*   PJ15DR     */
                    _UBYTE PJ14DR:1;            /*   PJ14DR     */
                    _UBYTE PJ13DR:1;            /*   PJ13DR     */
                    _UBYTE PJ12DR:1;            /*   PJ12DR     */
                    _UBYTE PJ11DR:1;            /*   PJ11DR     */
                    _UBYTE PJ10DR:1;            /*   PJ10DR     */
                    _UBYTE PJ9DR:1;             /*   PJ9DR      */
                    _UBYTE PJ8DR:1;             /*   PJ8DR      */
                    _UBYTE PJ7DR:1;             /*   PJ7DR      */
                    _UBYTE PJ6DR:1;             /*   PJ6DR      */
                    _UBYTE PJ5DR:1;             /*   PJ5DR      */
                    _UBYTE PJ4DR:1;             /*   PJ4DR      */
                    _UBYTE PJ3DR:1;             /*   PJ3DR      */
                    _UBYTE PJ2DR:1;             /*   PJ2DR      */
                    _UBYTE PJ1DR:1;             /*   PJ1DR      */
                    _UBYTE PJ0DR:1;             /*   PJ0DR      */
                    } BIT;                      /*              */
             } PJDR0;                           /*              */
       union {                                  /* PJPR1        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PJ31PR:1;            /*   PJ31PR     */
                    _UBYTE PJ30PR:1;            /*   PJ30PR     */
                    _UBYTE PJ29PR:1;            /*   PJ29PR     */
                    _UBYTE PJ28PR:1;            /*   PJ28PR     */
                    _UBYTE PJ27PR:1;            /*   PJ27PR     */
                    _UBYTE PJ26PR:1;            /*   PJ26PR     */
                    _UBYTE PJ25PR:1;            /*   PJ25PR     */
                    _UBYTE PJ24PR:1;            /*   PJ24PR     */
                    _UBYTE PJ23PR:1;            /*   PJ23PR     */
                    _UBYTE PJ22PR:1;            /*   PJ22PR     */
                    _UBYTE PJ21PR:1;            /*   PJ21PR     */
                    _UBYTE PJ20PR:1;            /*   PJ20PR     */
                    _UBYTE PJ19PR:1;            /*   PJ19PR     */
                    _UBYTE PJ18PR:1;            /*   PJ18PR     */
                    _UBYTE PJ17PR:1;            /*   PJ17PR     */
                    _UBYTE PJ16PR:1;            /*   PJ16PR     */
                    } BIT;                      /*              */
             } PJPR1;
       union {                                  /* PJPR0        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE PJ15PR:1;            /*   PJ15PR     */
                    _UBYTE PJ14PR:1;            /*   PJ14PR     */
                    _UBYTE PJ13PR:1;            /*   PJ13PR     */
                    _UBYTE PJ12PR:1;            /*   PJ12PR     */
                    _UBYTE PJ11PR:1;            /*   PJ11PR     */
                    _UBYTE PJ10PR:1;            /*   PJ10PR     */
                    _UBYTE PJ9PR:1;             /*   PJ9PR      */
                    _UBYTE PJ8PR:1;             /*   PJ8PR      */
                    _UBYTE PJ7PR:1;             /*   PJ7PR      */
                    _UBYTE PJ6PR:1;             /*   PJ6PR      */
                    _UBYTE PJ5PR:1;             /*   PJ5PR      */
                    _UBYTE PJ4PR:1;             /*   PJ4PR      */
                    _UBYTE PJ3PR:1;             /*   PJ3PR      */
                    _UBYTE PJ2PR:1;             /*   PJ2PR      */
                    _UBYTE PJ1PR:1;             /*   PJ1PR      */
                    _UBYTE PJ0PR:1;             /*   PJ0PR      */
                    } BIT;                      /*              */
             } PJPR0;                           /*              */
       _UBYTE wk21[34];                         /*              */
       union {                                  /* SNCR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Byte Access */
                    _UBYTE H;                   /*   High       */
                    _UBYTE L;                   /*   Low        */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UBYTE :8;                  /*              */
                    _UBYTE :2;                  /*              */
                    _UBYTE SSI5NCE:1;           /*   SSI5NCE    */
                    _UBYTE SSI4NCE:1;           /*   SSI4NCE    */
                    _UBYTE SSI3NCE:1;           /*   SSI3NCE    */
                    _UBYTE SSI2NCE:1;           /*   SSI2NCE    */
                    _UBYTE SSI1NCE:1;           /*   SSI1NCE    */
                    _UBYTE SSI0NCE:1;           /*   SSI0NCE    */
                    } BIT;                      /*              */
             }SNCR;                             /*              */
};                                              /*              */
	#endif
struct st_hudi {                                /* struct HUDI  */
       union {                                  /* SDIR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD TI:8;                /*   TI         */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } SDIR;                            /*              */
};                                              /*              */
struct st_pwm {                                 /* struct PWM   */
       union {                                  /* PWBTCR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BTC2G:1;             /*   BTC2G      */
                    _UBYTE BTC2E:1;             /*   BTC2E      */
                    _UBYTE BTC2C:1;             /*   BTC2C      */
                    _UBYTE BTC2A:1;             /*   BTC2A      */
                    _UBYTE BTC1G:1;             /*   BTC1G      */
                    _UBYTE BTC1E:1;             /*   BTC1E      */
                    _UBYTE BTC1C:1;             /*   BTC1C      */
                    _UBYTE BTC1A:1;             /*   BTC1A      */
                    } BIT;                      /*              */
             } PWBTCR;                          /*              */
       _UBYTE wk0[217];                         /*              */
       union {                                  /* PWCR1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE CMF:1;               /*   CMF        */
                    _UBYTE CST:1;               /*   CST        */
                    _UBYTE CKS:3;               /*   CKS        */
                    } BIT;                      /*              */
             } PWCR1;                           /*              */
       _UBYTE wk1[3];                           /*              */
       union {                                  /* PWPR1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OPS1H:1;             /*   OPS1H      */
                    _UBYTE OPS1G:1;             /*   OPS1G      */
                    _UBYTE OPS1F:1;             /*   OPS1F      */
                    _UBYTE OPS1E:1;             /*   OPS1E      */
                    _UBYTE OPS1D:1;             /*   OPS1D      */
                    _UBYTE OPS1C:1;             /*   OPS1C      */
                    _UBYTE OPS1B:1;             /*   OPS1B      */
                    _UBYTE OPS1A:1;             /*   OPS1A      */
                    } BIT;                      /*              */
             } PWPR1;                           /*              */
       _UBYTE wk2[1];                           /*              */
       union {                                  /* PWCYR1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PWCY15:1;            /*   PWCY15     */
                    _UWORD PWCY14:1;            /*   PWCY14     */
                    _UWORD PWCY13:1;            /*   PWCY13     */
                    _UWORD PWCY12:1;            /*   PWCY12     */
                    _UWORD PWCY11:1;            /*   PWCY11     */
                    _UWORD PWCY10:1;            /*   PWCY10     */
                    _UWORD PWCY9:1;             /*   PWCY9      */
                    _UWORD PWCY8:1;             /*   PWCY8      */
                    _UWORD PWCY7:1;             /*   PWCY7      */
                    _UWORD PWCY6:1;             /*   PWCY6      */
                    _UWORD PWCY5:1;             /*   PWCY5      */
                    _UWORD PWCY4:1;             /*   PWCY4      */
                    _UWORD PWCY3:1;             /*   PWCY3      */
                    _UWORD PWCY2:1;             /*   PWCY2      */
                    _UWORD PWCY1:1;             /*   PWCY1      */
                    _UWORD PWCY0:1;             /*   PWCY0      */
                    } BIT;                      /*              */
             } PWCYR1;                          /*              */
       union {                                  /* PWBFR1A      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR1A;                         /*              */
       union {                                  /* PWBFR1C      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR1C;                         /*              */
       union {                                  /* PWBFR1E      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR1E;                         /*              */
       union {                                  /* PWBFR1G      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR1G;                         /*              */
       union {                                  /* PWCR2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE IE:1;                /*   IE         */
                    _UBYTE CMF:1;               /*   CMF        */
                    _UBYTE CST:1;               /*   CST        */
                    _UBYTE CKS:3;               /*   CKS        */
                    } BIT;                      /*              */
             } PWCR2;                           /*              */
       _UBYTE wk3[3];                           /*              */
       union {                                  /* PWPR2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OPS2H:1;             /*   OPS2H      */
                    _UBYTE OPS2G:1;             /*   OPS2G      */
                    _UBYTE OPS2F:1;             /*   OPS2F      */
                    _UBYTE OPS2E:1;             /*   OPS2E      */
                    _UBYTE OPS2D:1;             /*   OPS2D      */
                    _UBYTE OPS2C:1;             /*   OPS2C      */
                    _UBYTE OPS2B:1;             /*   OPS2B      */
                    _UBYTE OPS2A:1;             /*   OPS2A      */
                    } BIT;                      /*              */
             } PWPR2;                           /*              */
       _UBYTE wk4[1];                           /*              */
       union {                                  /* PWCYR2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PWCY15:1;            /*   PWCY15     */
                    _UWORD PWCY14:1;            /*   PWCY14     */
                    _UWORD PWCY13:1;            /*   PWCY13     */
                    _UWORD PWCY12:1;            /*   PWCY12     */
                    _UWORD PWCY11:1;            /*   PWCY11     */
                    _UWORD PWCY10:1;            /*   PWCY10     */
                    _UWORD PWCY9:1;             /*   PWCY9      */
                    _UWORD PWCY8:1;             /*   PWCY8      */
                    _UWORD PWCY7:1;             /*   PWCY7      */
                    _UWORD PWCY6:1;             /*   PWCY6      */
                    _UWORD PWCY5:1;             /*   PWCY5      */
                    _UWORD PWCY4:1;             /*   PWCY4      */
                    _UWORD PWCY3:1;             /*   PWCY3      */
                    _UWORD PWCY2:1;             /*   PWCY2      */
                    _UWORD PWCY1:1;             /*   PWCY1      */
                    _UWORD PWCY0:1;             /*   PWCY0      */
                    } BIT;                      /*              */
             } PWCYR2;                          /*              */
       union {                                  /* PWBFR2A      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR2A;                         /*              */
       union {                                  /* PWBFR2C      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR2C;                         /*              */
       union {                                  /* PWBFR2E      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR2E;                         /*              */
       union {                                  /* PWBFR2G      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :3;                  /*              */
                    _UWORD OTS:1;               /*   OTS        */
                    _UWORD :2;                  /*              */
                    _UWORD DT9:1;               /*   DT9        */
                    _UWORD DT8:1;               /*   DT8        */
                    _UWORD DT7:1;               /*   DT7        */
                    _UWORD DT6:1;               /*   DT6        */
                    _UWORD DT5:1;               /*   DT5        */
                    _UWORD DT4:1;               /*   DT4        */
                    _UWORD DT3:1;               /*   DT3        */
                    _UWORD DT2:1;               /*   DT2        */
                    _UWORD DT1:1;               /*   DT1        */
                    _UWORD DT0:1;               /*   DT0        */
                    } BIT;                      /*              */
             } PWBFR2G;                         /*              */
};                                              /*              */
struct st_rqspi {                               /* struct RQSPI */
       union {                                  /* SPCR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SPRIE:1;             /*   SPRIE      */
                    _UBYTE SPE:1;               /*   SPE        */
                    _UBYTE SPTIE:1;             /*   SPTIE      */
                    _UBYTE :5;                  /*              */
                    } BIT;                      /*              */
             } SPCR;                            /*              */
       union {                                  /* SSLP         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :7;                  /*              */
                    _UBYTE SSLP:1;              /*   SSLP       */
                    } BIT;                      /*              */
             } SSLP;                            /*              */
       union {                                  /* SPPCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :2;                  /*              */
                    _UBYTE MOIFE:1;             /*   MOIFE      */
                    _UBYTE MOIFV:1;             /*   MOIFV      */
                    _UBYTE :1;                  /*              */
                    _UBYTE IO3FV:1;             /*   IO3FV      */
                    _UBYTE IO2FV:1;             /*   IO2FV      */
                    _UBYTE SPLP:1;              /*   SPLP       */
                    } BIT;                      /*              */
             } SPPCR;                           /*              */
       union {                                  /* SPSR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SPRFF:1;             /*   SPRFF      */
                    _UBYTE TEND:1;              /*   TEND       */
                    _UBYTE SPTEF:1;             /*   SPTEF      */
                    _UBYTE :5;                  /*              */
                    } BIT;                      /*              */
             } SPSR;                            /*              */
       union {                                  /* SPDR         */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD;                       /*  Word Access */
             _UBYTE BYTE;                       /*  Byte Access */
             } SPDR;                            /*              */
       union {                                  /* SPSCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE SPSC:2;              /*   SPSC       */
                    } BIT;                      /*              */
             } SPSCR;                           /*              */
       union {                                  /* SPSSR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE SPSS:2;              /*   SPSS       */
                    } BIT;                      /*              */
             } SPSSR;                           /*              */
       union {                                  /* SPBR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SPBR:8;              /*   SPBR       */
                    } BIT;                      /*              */
             } SPBR;                            /*              */
       union {                                  /* SPDCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TXDMY:1;             /*   TXDMY      */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } SPDCR;                           /*              */
       union {                                  /* SPCKD        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE SCKDL:3;             /*   SCKDL      */
                    } BIT;                      /*              */
             } SPCKD;                           /*              */
       union {                                  /* SSLND        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE SLNDL:3;             /*   SLNDL      */
                    } BIT;                      /*              */
             } SSLND;                           /*              */
       union {                                  /* SPND         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :5;                  /*              */
                    _UBYTE SPNDL:3;             /*   SPNDL      */
                    } BIT;                      /*              */
             } SPND;                            /*              */
       _UBYTE wk0[1];                           /*              */
       union {                                  /* SPCMD0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD SPIMOD:2;            /*   SPIMOD     */
                    _UWORD SPRW:1;              /*   SPRW       */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD0;                          /*              */
       union {                                  /* SPCMD1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD SPIMOD:2;            /*   SPIMOD     */
                    _UWORD SPRW:1;              /*   SPRW       */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD1 ;                         /*              */
       union {                                  /* SPCMD2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD SPIMOD:2;            /*   SPIMOD     */
                    _UWORD SPRW:1;              /*   SPRW       */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD2 ;                         /*              */
       union {                                  /* SPCMD3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SCKDEN:1;            /*   SCKDEN     */
                    _UWORD SLNDEN:1;            /*   SLNDEN     */
                    _UWORD SPNDEN:1;            /*   SPNDEN     */
                    _UWORD LSBF:1;              /*   LSBF       */
                    _UWORD SPB:4;               /*   SPB        */
                    _UWORD SSLKP:1;             /*   SSLKP      */
                    _UWORD SPIMOD:2;            /*   SPIMOD     */
                    _UWORD SPRW:1;              /*   SPRW       */
                    _UWORD BRDV:2;              /*   BRDV       */
                    _UWORD CPOL:1;              /*   CPOL       */
                    _UWORD CPHA:1;              /*   CPHA       */
                    } BIT;                      /*              */
             } SPCMD3 ;                         /*              */
       union {                                  /* SPBFCR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TXRST:1;             /*   TXRST      */
                    _UBYTE RXRST:1;             /*   RXRST      */
                    _UBYTE TXTRG:2;             /*   TXTRG      */
                    _UBYTE :1;                  /*              */
                    _UBYTE RXTRG:3;             /*   RXTRG      */
                    } BIT;                      /*              */
             } SPBFCR;                          /*              */
       _UBYTE wk1[1];                           /*              */
       union {                                  /* SPBDCR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :2;                  /*              */
                    _UWORD TXBC:6 ;             /*   TXBC       */
                    _UWORD :2;                  /*              */
                    _UWORD RXBC:6;              /*   RXBC       */
                    } BIT;                      /*              */
             } SPBDCR;                          /*              */
       union {                                  /* SPBMUL0      */
             _UDWORD LONG;                      /*  Long Access */
             } SPBMUL0;                         /*              */
       union {                                  /* SPBMUL1      */
             _UDWORD LONG;                      /*  Long Access */
             } SPBMUL1;                         /*              */
       union {                                  /* SPBMUL2      */
             _UDWORD LONG;                      /*  Long Access */
             } SPBMUL2;                         /*              */
       union {                                  /* SPBMUL3      */
             _UDWORD LONG;                      /*  Long Access */
             } SPBMUL3;                         /*              */
};                                              /*              */
struct st_imrls {                                      /* struct IMRLS */
       union {                                         /* CR           */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :16;                       /*              */
                    _UDWORD SWRST:1;                   /*   SWRST      */
                    _UDWORD :9;                        /*              */
                    _UDWORD RESUME:1;                  /*   RESUME     */
                    _UDWORD STOP:1;                    /*   STOP       */
                    _UDWORD :1;                        /*              */
                    _UDWORD SFE:1;                     /*   SFE        */
                    _UDWORD ARS:1;                     /*   ARS        */
                    _UDWORD RS:1;                      /*   RS         */
                    } BIT;                             /*              */
             } CR;                                     /*              */
       union {                                         /* SR           */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD DSA:1;                     /*   DSA        */
                    _UDWORD :1;                        /*              */
                    _UDWORD STP:1;                     /*   STP        */
                    _UDWORD :1;                        /*              */
                    _UDWORD INT:1;                     /*   INT        */
                    _UDWORD IER:1;                     /*   IER        */
                    _UDWORD TRA:1;                     /*   TRA        */
                    } BIT;                             /*              */
             } SR;                                     /*              */
       union {                                         /* SRCR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD STPCLR:1;                  /*   STPCLR     */
                    _UDWORD :1;                        /*              */
                    _UDWORD INTCLR:1;                  /*   INTCLR     */
                    _UDWORD IERCLR:1;                  /*   IERCLR     */
                    _UDWORD TRACLR:1;                  /*   TRACLR     */
                    } BIT;                             /*              */
             } SRCR;                                   /*              */
       union {                                         /* ICR          */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD STPENB:1;                  /*   STPENB     */
                    _UDWORD :1;                        /*              */
                    _UDWORD INTENB:1;                  /*   INTENB     */
                    _UDWORD IERENB:1;                  /*   IERENB     */
                    _UDWORD TRAENB:1;                  /*   TRAENB     */
                    } BIT;                             /*              */
             } ICR;                                    /*              */
       union {                                         /* IMR          */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :27;                       /*              */
                    _UDWORD STM:1;                     /*   STM        */
                    _UDWORD :1;                        /*              */
                    _UDWORD INM:1;                     /*   INM        */
                    _UDWORD IEM:1;                     /*   IEM        */
                    _UDWORD TRAM:1;                    /*   TRAM       */
                    } BIT;                             /*              */
             } IMR;                                    /*              */
       _UBYTE wk0[4];                                  /*              */
       union {                                         /* DLPR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DLP:32;                    /*   DLP        */
                    } BIT;                             /*              */
             } DLPR;                                   /*              */
       _UBYTE wk1[12];                                 /*              */
       union {                                         /* DLSAR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DLSA:32;                   /*   DLSA       */
                    } BIT;                             /*              */
             } DLSAR;                                  /*              */
       union {                                         /* DSAR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DSAR:32;                   /*   DSAR       */
                    } BIT;                             /*              */
             } DSAR;                                   /*              */
       _UBYTE wk2[4];                                  /*              */
       union {                                         /* DSTR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :19;                       /*              */
                    _UDWORD DSTR:13;                   /*   DSTR       */
                    } BIT;                             /*              */
             } DSTR;                                   /*              */
       _UBYTE wk3[8];                                  /*              */
       union {                                         /* DSAR2        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DSAR2:32;                  /*   DSAR2      */
                    } BIT;                             /*              */
             } DSAR2;                                  /*              */
       union {                                         /* DLSAR2       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DLSA2:32;                  /*   DLSA2      */
                    } BIT;                             /*              */
             } DLSAR2;                                 /*              */
       _UBYTE wk4[16];                                 /*              */
       union {                                         /* TRIMR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD TCM:1;                     /*   TCM        */
                    _UDWORD DUDVM:1;                   /*   DUDVM      */
                    _UDWORD DXDYM:1;                   /*   DXDYM      */
                    _UDWORD AUTOSG:1;                  /*   AUTOSG     */
                    _UDWORD AUTODG:1;                  /*   AUTODG     */
                    _UDWORD BFE:1;                     /*   BFE        */
                    _UDWORD TME:1;                     /*   TME        */
                    } BIT;                             /*              */
             } TRIMR;                                  /*              */
       union {                                         /* TRIMSR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD TCMS:1;                    /*   TCMS       */
                    _UDWORD DUDVMS:1;                  /*   DUDVMS     */
                    _UDWORD DXDYMS:1;                  /*   DXDYMS     */
                    _UDWORD AUTOSGS:1;                 /*   AUTOSGS    */
                    _UDWORD AUTODGS:1;                 /*   AUTODGS    */
                    _UDWORD BFES:1;                    /*   BFES       */
                    _UDWORD TMES:1;                    /*   TMES       */
                    } BIT;                             /*              */
             } TRIMSR;                                 /*              */
       union {                                         /* TRIMCR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD TCMC:1;                    /*   TCMC       */
                    _UDWORD DUDVMC:1;                  /*   DUDVMC     */
                    _UDWORD DXDYMC:1;                  /*   DXDYMC     */
                    _UDWORD AUTOSGC:1;                 /*   AUTOSGC    */
                    _UDWORD AUTODGC:1;                 /*   AUTODGC    */
                    _UDWORD BFEC:1;                    /*   BFEC       */
                    _UDWORD TMEC:1;                    /*   TMEC       */
                    } BIT;                             /*              */
             } TRIMCR;                                 /*              */
       union {                                         /* TRICR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :8;                        /*              */
                    _UDWORD TCV:8;                     /*   TCV        */
                    _UDWORD TCU:8;                     /*   TCU        */
                    _UDWORD TCY:8;                     /*   TCY        */
                    } BIT;                             /*              */
             } TRICR;                                  /*              */
       union {                                         /* UVDPOR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :23;                       /*              */
                    _UDWORD DDP:1;                     /*   DDP        */
                    _UDWORD :5;                        /*              */
                    _UDWORD UVDPO:3;                   /*   UVDPO      */
                    } BIT;                             /*              */
             } UVDPOR;                                 /*              */
       union {                                         /* SUSR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :6;                        /*              */
                    _UDWORD SUW:10;                    /*   SUW        */
                    _UDWORD :6;                        /*              */
                    _UDWORD SVW:10;                    /*   SVW        */
                    } BIT;                             /*              */
             } SUSR;                                   /*              */
       union {                                         /* SVSR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD SVSR:10;                   /*   SVSR       */
                    } BIT;                             /*              */
             } SVSR;                                   /*              */
       _UBYTE wk5[4];                                  /*              */
       union {                                         /* XMINR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :20;                       /*              */
                    _UDWORD XMIN:12;                   /*   XMIN       */
                    } BIT;                             /*              */
             } XMINR;                                  /*              */
       union {                                         /* YMINR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :20;                       /*              */
                    _UDWORD YMIN:12;                   /*   YMIN       */
                    } BIT;                             /*              */
             } YMINR;                                  /*              */
       union {                                         /* XMAXR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :20;                       /*              */
                    _UDWORD XMAX:12;                   /*   XMAX       */
                    } BIT;                             /*              */
             } XMAXR;                                  /*              */
       union {                                         /* YMAXR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :20;                       /*              */
                    _UDWORD YMAX:12;                   /*   YMAX       */
                    } BIT;                             /*              */
             } YMAXR;                                  /*              */
       union {                                         /* AMXSR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD AMXS:10;                   /*   AMXS       */
                    } BIT;                             /*              */
             } AMXSR;                                  /*              */
       union {                                         /* AMYSR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD AMYS:10;                   /*   AMYS       */
                    } BIT;                             /*              */
             } AMYSR;                                  /*              */
       union {                                         /* AMXOR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD AMXO:10;                   /*   AMXO       */
                    } BIT;                             /*              */
             } AMXOR;                                  /*              */
       union {                                         /* AMYOR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD AMYO:10;                   /*   AMYO       */
                    } BIT;                             /*              */
             } AMYOR;                                  /*              */
       union {                                         /* MACR1        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD QWSWPI:1;                  /*   QWSWPI     */
                    _UDWORD QWSWPC:1;                  /*   QWSWPC     */
                    _UDWORD :17;                       /*              */
                    _UDWORD EMAM:1;                    /*   EMAM       */
                    _UDWORD :2;                        /*              */
                    _UDWORD LWSWAP:1;                  /*   LWSWAP     */
                    _UDWORD :9;                        /*              */
                    } BIT;                             /*              */
             } MACR1;                                  /*              */
       _UBYTE wk6[2396];                               /*              */
       union {                                         /* LSPR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD LSPR:10;                   /*   LSPR       */
                    } BIT;                             /*              */
             } LSPR;                                   /*              */
       union {                                         /* LEPR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :22;                       /*              */
                    _UDWORD LEPR:10;                   /*   LEPR       */
                    } BIT;                             /*              */
             } LEPR;                                   /*              */
       union {                                         /* LMSR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :29;                       /*              */
                    _UDWORD LMSR:3;                    /*   LMSR       */
                    } BIT;                             /*              */
             } LMSR;                                   /*              */
};                                                     /*              */
struct st_sdg0 {                                       /* struct SDG0  */
       union {                                         /* SGCR1_0      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGST:1;                     /*   SGST       */
                    _UBYTE STPM:1;                     /*   STPM       */
                    _UBYTE :1;                         /*              */
                    _UBYTE SGCK:2;                     /*   SGCK       */
                    _UBYTE DPF:3;                      /*   DPF        */
                    } BIT;                             /*              */
             } SGCR1_0;                                /*              */
       union {                                         /* SGCSR_0      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGIE:1;                     /*   SGIE       */
                    _UBYTE SGDEF:1;                    /*   SGDEF      */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCSR_0;                                /*              */
       union {                                         /* SGCR2_0      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGEND:1;                    /*   SGEND      */
                    _UBYTE TCHG:1;                     /*   TCHG       */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCR2_0;                                /*              */
       union {                                         /* SGLR_0       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE LD:8;                       /*   LD         */
                    } BIT;                             /*              */
             } SGLR_0;                                 /*              */
       union {                                         /* SGTFR_0      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :1;                         /*              */
                    _UBYTE TONE:7;                     /*   TONE       */
                    } BIT;                             /*              */
             } SGTFR_0;                                /*              */
       union {                                         /* SGSFR_0      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SFS:8;                      /*   SFS        */
                    } BIT;                             /*              */
             } SGSFR_0;                                /*              */
};                                                     /*              */
struct st_sdg1 {                                       /* struct SDG1  */
       union {                                         /* SGCR1_1      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGST:1;                     /*   SGST       */
                    _UBYTE STPM:1;                     /*   STPM       */
                    _UBYTE :1;                         /*              */
                    _UBYTE SGCK:2;                     /*   SGCK       */
                    _UBYTE DPF:3;                      /*   DPF        */
                    } BIT;                             /*              */
             } SGCR1_1;                                /*              */
       union {                                         /* SGCSR_1      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGIE:1;                     /*   SGIE       */
                    _UBYTE SGDEF:1;                    /*   SGDEF      */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCSR_1;                                /*              */
       union {                                         /* SGCR2_1      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGEND:1;                    /*   SGEND      */
                    _UBYTE TCHG:1;                     /*   TCHG       */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCR2_1;                                /*              */
       union {                                         /* SGLR_1       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE LD:8;                       /*   LD         */
                    } BIT;                             /*              */
             } SGLR_1;                                 /*              */
       union {                                         /* SGTFR_1      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :1;                         /*              */
                    _UBYTE TONE:7;                     /*   TONE       */
                    } BIT;                             /*              */
             } SGTFR_1;                                /*              */
       union {                                         /* SGSFR_1      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SFS:8;                      /*   SFS        */
                    } BIT;                             /*              */
             } SGSFR_1;                                /*              */
};                                                     /*              */
struct st_sdg2 {                                       /* struct SDG2  */
       union {                                         /* SGCR1_2      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGST:1;                     /*   SGST       */
                    _UBYTE STPM:1;                     /*   STPM       */
                    _UBYTE :1;                         /*              */
                    _UBYTE SGCK:2;                     /*   SGCK       */
                    _UBYTE DPF:3;                      /*   DPF        */
                    } BIT;                             /*              */
             } SGCR1_2;                                /*              */
       union {                                         /* SGCSR_2      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGIE:1;                     /*   SGIE       */
                    _UBYTE SGDEF:1;                    /*   SGDEF      */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCSR_2;                                /*              */
       union {                                         /* SGCR2_2      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGEND:1;                    /*   SGEND      */
                    _UBYTE TCHG:1;                     /*   TCHG       */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCR2_2;                                /*              */
       union {                                         /* SGLR_2       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE LD:8;                       /*   LD         */
                    } BIT;                             /*              */
             } SGLR_2;                                 /*              */
       union {                                         /* SGTFR_2      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :1;                         /*              */
                    _UBYTE TONE:7;                     /*   TONE       */
                    } BIT;                             /*              */
             } SGTFR_2;                                /*              */
       union {                                         /* SGSFR_2      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SFS:8;                      /*   SFS        */
                    } BIT;                             /*              */
             } SGSFR_2;                                /*              */
};                                                     /*              */
struct st_sdg3 {                                       /* struct SDG3  */
       union {                                         /* SGCR1_3      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGST:1;                     /*   SGST       */
                    _UBYTE STPM:1;                     /*   STPM       */
                    _UBYTE :1;                         /*              */
                    _UBYTE SGCK:2;                     /*   SGCK       */
                    _UBYTE DPF:3;                      /*   DPF        */
                    } BIT;                             /*              */
             } SGCR1_3;                                /*              */
       union {                                         /* SGCSR_3      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGIE:1;                     /*   SGIE       */
                    _UBYTE SGDEF:1;                    /*   SGDEF      */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCSR_3;                                /*              */
       union {                                         /* SGCR2_3      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SGEND:1;                    /*   SGEND      */
                    _UBYTE TCHG:1;                     /*   TCHG       */
                    _UBYTE :6;                         /*              */
                    } BIT;                             /*              */
             } SGCR2_3;                                /*              */
       union {                                         /* SGLR_3       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE LD:8;                       /*   LD         */
                    } BIT;                             /*              */
             } SGLR_3;                                 /*              */
       union {                                         /* SGTFR_3      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :1;                         /*              */
                    _UBYTE TONE:7;                     /*   TONE       */
                    } BIT;                             /*              */
             } SGTFR_3;                                /*              */
       union {                                         /* SGSFR_3      */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE SFS:8;                      /*   SFS        */
                    } BIT;                             /*              */
             } SGSFR_3;                                /*              */
};                                                     /*              */
struct st_mmc {                                        /* struct MMC   */
       union {                                         /* CE_CMD_SET   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD BOOT:1;                     /*   BOOT       */
                    _UWORD CMD:6;                      /*   CMD        */
                    _UWORD RTYP:2;                     /*   RTYP       */
                    _UWORD RBSY:1;                     /*   RBSY       */
                    _UWORD CCSEN:1;                    /*   CCSEN      */
                    _UWORD WDAT:1;                     /*   WDAT       */
                    _UWORD DWEN:1;                     /*   DWEN       */
                    _UWORD CMLTE:1;                    /*   CMLTE      */
                    _UWORD CMD12EN:1;                  /*   CMD12EN    */
                    _UWORD RIDXC:2;                    /*   RIDXC      */
                    _UWORD RCRC7C:2;                   /*   RCRC7C     */
                    _UWORD :1;                         /*              */
                    _UWORD CRC16C:1;                   /*   CRC16C     */
                    _UWORD BOOTACK:1;                  /*   BOOTACK    */
                    _UWORD CRCSTE:1;                   /*   CRCSTE     */
                    _UWORD TBIT:1;                     /*   TBIT       */
                    _UWORD OPDM:1;                     /*   OPDM       */
                    _UWORD CCSH:1;                     /*   CCSH       */
                    _UWORD :3;                         /*              */
                    _UWORD DATW:2;                     /*   DATW       */
                    } BIT;                             /*              */
             } CE_CMD_SET;                             /*              */
       _UBYTE wk0[4];                                  /*              */
       union {                                         /* CE_ARG       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD ARG:32;                    /*   ARG        */
                    } BIT;                             /*              */
             } CE_ARG;                                 /*              */
       union {                                         /* CE_ARG_CMD12 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD C12ARG:32;                 /*   C12ARG     */
                    } BIT;                             /*              */
             } CE_ARG_CMD12;                           /*              */
       union {                                         /* CE_CMD_CTRL  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :30;                       /*              */
                    _UDWORD CCSD:1;                    /*   CCSD       */
                    _UDWORD BREAK:1;                   /*   BREAK      */
                    } BIT;                             /*              */
             } CE_CMD_CTRL;                            /*              */
       union {                                         /* CE_BLOCK_SET */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD BLKCNT:16;                  /*   BLKCNT     */
                    _UWORD BLKSIZ:16;                  /*   BLKSIZ     */
                    } BIT;                             /*              */
             } CE_BLOCK_SET;                           /*              */
       union {                                         /* CE_CLK_CTRL  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :7;                        /*              */
                    _UDWORD CLKEN:1;                   /*   CLKEN      */
                    _UDWORD :4;                        /*              */
                    _UDWORD CLKDIV:4;                  /*   CLKDIV     */
                    _UDWORD :2;                        /*              */
                    _UDWORD SRSPTO:2;                  /*   SRSPTO     */
                    _UDWORD SRBSYTO:4;                 /*   SRBSYTO    */
                    _UDWORD SRWDTO:4;                  /*   SRWDTO     */
                    _UDWORD SCCSTO:4;                  /*   SCCSTO     */
                    } BIT;                             /*              */
             } CE_CLK_CTRL;                            /*              */
       union {                                         /* CE_BUF_ACC   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD DMAWEN:1;                   /*   DMAWEN     */
                    _UWORD DMAREN:1;                   /*   DMAREN     */
                    _UWORD :6;                         /*              */
                    _UWORD BUSW:1;                     /*   BUSW       */
                    _UWORD ATYP:1;                     /*   ATYP       */
                    _UWORD :16;                        /*              */
                    } BIT;                             /*              */
             } CE_BUF_ACC;                             /*              */
       union {                                         /* CE_RESP3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RSP:32;                    /*   RSP        */
                    } BIT;                             /*              */
             } CE_RESP3;                               /*              */
       union {                                         /* CE_RESP2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RSP:32;                    /*   RSP        */
                    } BIT;                             /*              */
             } CE_RESP2;                               /*              */
       union {                                         /* CE_RESP1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RSP:32;                    /*   RSP        */
                    } BIT;                             /*              */
             } CE_RESP1;                               /*              */
       union {                                         /* CE_RESP0     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RSP:32;                    /*   RSP        */
                    } BIT;                             /*              */
             } CE_RESP0;                               /*              */
       union {                                         /* CE_RESP_CMD12 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RSP12:32;                  /*   RSP12      */
                    } BIT;                             /*              */
             } CE_RESP_CMD12;                          /*              */
       union {                                         /* CE_DATA      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD DATA:32;                   /*   DATA       */
                    } BIT;                             /*              */
             } CE_DATA;                                /*              */
       _UBYTE wk1[8];                                  /*              */
       union {                                         /* CE_INT       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD CCSDE:1;                    /*   CCSDE      */
                    _UWORD :2;                         /*              */
                    _UWORD CMD12DRE:1;                 /*   CMD12DRE   */
                    _UWORD CMD12RBE:1;                 /*   CMD12RBE   */
                    _UWORD CMD12CRE:1;                 /*   CMD12CRE   */
                    _UWORD DTRANE:1;                   /*   DTRANE     */
                    _UWORD BUFRE:1;                    /*   BUFRE      */
                    _UWORD BUFWEN:1;                   /*   BUFWEN     */
                    _UWORD BUFREN:1;                   /*   BUFREN     */
                    _UWORD CCSRCV:1;                   /*   CCSRCV     */
                    _UWORD :1;                         /*              */
                    _UWORD RBSYE:1;                    /*   RBSYE      */
                    _UWORD CRSPE:1;                    /*   CRSPE      */
                    _UWORD CMDVIO:1;                   /*   CMDVIO     */
                    _UWORD BUFVIO:1;                   /*   BUFVIO     */
                    _UWORD :2;                         /*              */
                    _UWORD WDATERR:1;                  /*   WDATERR    */
                    _UWORD RDATERR:1;                  /*   RDATERR    */
                    _UWORD RIDXERR:1;                  /*   RIDXERR    */
                    _UWORD RSPERR:1;                   /*   RSPERR     */
                    _UWORD :2;                         /*              */
                    _UWORD CCSTO:1;                    /*   CCSTO      */
                    _UWORD CRCSTO:1;                   /*   CRCSTO     */
                    _UWORD WDATTO:1;                   /*   WDATTO     */
                    _UWORD RDATTO:1;                   /*   RDATTO     */
                    _UWORD RBSYTO:1;                   /*   RBSYTO     */
                    _UWORD RSPTO:1;                    /*   RSPTO      */
                    } BIT;                             /*              */
             } CE_INT;                                 /*              */
       union {                                         /* CE_INT_EN    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD MCCSDE:1;                   /*   MCCSDE     */
                    _UWORD :2;                         /*              */
                    _UWORD MCMD12DRE:1;                /*   MCMD12DRE  */
                    _UWORD MCMD12RBE:1;                /*   MCMD12RBE  */
                    _UWORD MCMD12CRE:1;                /*   MCMD12CRE  */
                    _UWORD MDTRANE:1;                  /*   MDTRANE    */
                    _UWORD MBUFRE:1;                   /*   MBUFRE     */
                    _UWORD MBUFWEN:1;                  /*   MBUFWEN    */
                    _UWORD MBUFREN:1;                  /*   MBUFREN    */
                    _UWORD MCCSRCV:1;                  /*   MCCSRCV    */
                    _UWORD :1;                         /*              */
                    _UWORD MRBSYE:1;                   /*   MRBSYE     */
                    _UWORD MCRSPE:1;                   /*   MCRSPE     */
                    _UWORD MCMDVIO:1;                  /*   MCMDVIO    */
                    _UWORD MBUFVIO:1;                  /*   MBUFVIO    */
                    _UWORD :2;                         /*              */
                    _UWORD MWDATERR:1;                 /*   MWDATERR   */
                    _UWORD MRDATERR:1;                 /*   MRDATERR   */
                    _UWORD MRIDXERR:1;                 /*   MRIDXERR   */
                    _UWORD MRSPERR:1;                  /*   MRSPERR    */
                    _UWORD :2;                         /*              */
                    _UWORD MCCSTO:1;                   /*   MCCSTO     */
                    _UWORD MCRCSTO:1;                  /*   MCRCSTO    */
                    _UWORD MWDATTO:1;                  /*   MWDATTO    */
                    _UWORD MRDATTO:1;                  /*   MRDATTO    */
                    _UWORD MRBSYTO:1;                  /*   MRBSYTO    */
                    _UWORD MRSPTO:1;                   /*   MRSPTO     */
                    } BIT;                             /*              */
             } CE_INT_EN;                              /*              */
       union {                                         /* CE_HOST_STS1 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD CMDSEQ:1;                   /*   CMDSEQ     */
                    _UWORD CMDSIG:1;                   /*   CMDSIG     */
                    _UWORD RSPIDX:6;                   /*   RSPIDX     */
                    _UWORD DATSIG:8;                   /*   DATSIG     */
                    _UWORD RCVBLK:16;                  /*   RCVBLK     */
                    } BIT;                             /*              */
             } CE_HOST_STS1;                           /*              */
       union {                                         /* CE_HOST_STS2 */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD CRCSTE:1;                   /*   CRCSTE     */
                    _UWORD CRC16E:1;                   /*   CRC16E     */
                    _UWORD AC12CRCE:1;                 /*   AC12CRCE   */
                    _UWORD RSPCRC7E:1;                 /*   RSPCRC7E   */
                    _UWORD CRCSTEBE:1;                 /*   CRCSTEBE   */
                    _UWORD RDATEBE:1;                  /*   RDATEBE    */
                    _UWORD AC12REBE:1;                 /*   AC12REBE   */
                    _UWORD RSPEBE:1;                   /*   RSPEBE     */
                    _UWORD AC12IDXE:1;                 /*   AC12IDXE   */
                    _UWORD RSPIDXE:1;                  /*   RSPIDXE    */
                    _UWORD BTACKPATE:1;                /*   BTACKPATE  */
                    _UWORD BTACKEBE:1;                 /*   BTACKEBE   */
                    _UWORD :1;                         /*              */
                    _UWORD CRCST:3;                    /*   CRCST      */
                    _UWORD STCCSTO:1;                  /*   STCCSTO    */
                    _UWORD STRDATTO:1;                 /*   STRDATTO   */
                    _UWORD DATBSYTO:1;                 /*   DATBSYTO   */
                    _UWORD CRCSTTO:1;                  /*   CRCSTTO    */
                    _UWORD AC12BSYTO:1;                /*   AC12BSYTO  */
                    _UWORD RSPBSYTO:1;                 /*   RSPBSYTO   */
                    _UWORD AC12RSPTO:1;                /*   AC12RSPTO  */
                    _UWORD STRSPTO:1;                  /*   STRSPTO    */
                    _UWORD BTACKTO:1;                  /*   BTACKTO    */
                    _UWORD FSTBTDATTO:1;               /*   FSTBTDATTO */
                    _UWORD BTDATTO:1;                  /*   BTDATTO    */
                    _UWORD :5;                         /*              */
                    } BIT;                             /*              */
             } CE_HOST_STS2;                           /*              */
       _UBYTE wk2_0[12];                               /*              */
       union {                                         /* CE_DMA_MODE  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD DMASEL:1;                  /*   DMASEL     */
                    } BIT;                             /*              */
             } CE_DMA_MODE;                            /*              */
       _UBYTE wk2_1[16];                               /*              */
       union {                                         /* CE_DETECT    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :17;                       /*              */
                    _UDWORD CDSIG:1;                   /*   CDSIG      */
                    _UDWORD CDRISE:1;                  /*   CDRISE     */
                    _UDWORD CDFALL:1;                  /*   CDFALL     */
                    _UDWORD :6;                        /*              */
                    _UDWORD MCDRISE:1;                 /*   MCDRISE    */
                    _UDWORD MCDFALL:1;                 /*   MCDFALL    */
                    _UDWORD :4;                        /*              */
                    } BIT;                             /*              */
             } CE_DETECT;                              /*              */
       union {                                         /* CE_ADD_MODE  */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD :12;                       /*              */
                    _UDWORD CLKMAIN:1;                 /*   CLKMAIN    */
                    _UDWORD :19;                       /*              */
                    } BIT;                             /*              */
             } CE_ADD_MODE;                            /*              */
       _UBYTE wk3[4];                                  /*              */
       union {                                         /* CE_VERSION   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UWORD SWRST:1;                    /*   SWRST      */
                    _UWORD :15;                        /*              */
                    _UWORD VERSION:16;                 /*   VERSION    */
                    } BIT;                             /*              */
             } CE_VERSION;                             /*              */
};                                                     /*              */
struct st_dvdec {                                      /* struct DVDEC */
       union {                                         /* ADCCR        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD AGCMODE:1;                  /*   AGCMODE    */
                    _UWORD :8;                         /*              */
                    } BIT;                             /*              */
             } ADCCR1;                                 /*              */
       _UBYTE wk0[4];                                  /*              */
       union {                                         /* TGCR1        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD SRCLEFT:9;                  /*   SRCLEFT    */
                    } BIT;                             /*              */
             } TGCR1;                                  /*              */
       union {                                         /* TGCR2        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD SRCTOP:6;                   /*   SRCTOP     */
                    _UWORD SRCHEIGHT:10;               /*   SRCHEIGHT  */
                    } BIT;                             /*              */
             } TGCR2;                                  /*              */
       union {                                         /* TGCR3        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD SRCWIDTH:11;                /*   SRCWIDTH   */
                    } BIT;                             /*              */
             } TGCR3;                                  /*              */
       _UBYTE wk1[6];                                  /*              */
       union {                                         /* SYNSCR1      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD LPFVSYNC:3;                 /*   LPFVSYNC   */
                    _UWORD LPFHSYNC:3;                 /*   LPFHSYNC   */
                    _UWORD :2;                         /*              */
                    _UWORD VELOCITYSHIFT_H:4;          /*   VELOCITYSHIFT_H */
                    _UWORD SLICERMODE_H:2;             /*   SLICERMODE_H */
                    _UWORD SLICERMODE_V:2;             /*   SLICERMODE_V */
                    } BIT;                             /*              */
             } SYNSCR1;                                /*              */
       union {                                         /* SYNSCR2      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :4;                         /*              */
                    _UWORD SYNCMAXDUTY_H:6;            /*   SYNCMAXDUTY_H */
                    _UWORD SYNCMINDUTY_H:6;            /*   SYNCMINDUTY_H */
                    } BIT;                             /*              */
             } SYNSCR2;                                /*              */
       union {                                         /* SYNSCR3      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD SSCLIPSEL:4;                /*   SSCLIPSEL  */
                    _UWORD CSYNCSLICE_H:10;            /*   CSYNCSLICE_H */
                    } BIT;                             /*              */
             } SYNSCR3;                                /*              */
       union {                                         /* SYNSCR4      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :4;                         /*              */
                    _UWORD SYNCMAXDUTY_V:6;            /*   SYNCMAXDUTY_V */
                    _UWORD SYNCMINDUTY_V:6;            /*   SYNCMINDUTY_V */
                    } BIT;                             /*              */
             } SYNSCR4;                                /*              */
       union {                                         /* SYNSCR5      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD VSYNCDELAY:1;               /*   VSYNCDELAY */
                    _UWORD VSYNCSLICE:5;               /*   VSYNCSLICE */
                    _UWORD CSYNCSLICE_V:10;            /*   CSYNCSLICE_V */
                    } BIT;                             /*              */
             } SYNSCR5;                                /*              */
       union {                                         /* HAFCCR1      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD HAFCGAIN:4;                 /*   HAFCGAIN   */
                    _UWORD :1;                         /*              */
                    _UWORD HAFCFREERUN:1;              /*   HAFCFREERUN */
                    _UWORD HAFCTYP:10;                 /*   HAFCTYP    */
                    } BIT;                             /*              */
             } HAFCCR1;                                /*              */
       union {                                         /* HAFCCR2      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD HAFCSTART:4;                /*   HAFCSTART  */
                    _UWORD NOX2HOSC:1;                 /*   NOX2HOSC   */
                    _UWORD DOX2HOSC:1;                 /*   DOX2HOSC   */
                    _UWORD HAFCMAX:10;                 /*   HAFCMAX    */
                    } BIT;                             /*              */
             } HAFCCR2;                                /*              */
       union {                                         /* HAFCCR3      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD HAFCEND:4;                  /*   HAFCEND    */
                    _UWORD HAFCMODE:2;                 /*   HAFCMODE   */
                    _UWORD HAFCMIN:10;                 /*   HAFCMIN    */
                    } BIT;                             /*              */
             } HAFCCR3;                                /*              */
       union {                                         /* VCDWCR1      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD VCDFREERUN:1;               /*   VCDFREERUN */
                    _UWORD NOVCD50:1;                  /*   NOVCD50    */
                    _UWORD NOVCD60:1;                  /*   NOVCD60    */
                    _UWORD VCDDEFAULT:2;               /*   VCDDEFAULT */
                    _UWORD VCDWINDOW:6;                /*   VCDWINDOW  */
                    _UWORD VCDOFFSET:5;                /*   VCDOFFSET  */
                    } BIT;                             /*              */
             } VCDWCR1;                                /*              */
       _UBYTE wk2[4];                                  /*              */
       union {                                         /* DCPCR1       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DCPMODE_Y:1;                /*   DCPMODE_Y  */
                    _UWORD :3;                         /*              */
                    _UWORD DCPCHECK:1;                 /*   DCPCHECK   */
                    _UWORD :1;                         /*              */
                    _UWORD BLANKLEVEL_Y:10;            /*   BLANKLEVEL_Y */
                    } BIT;                             /*              */
             } DCPCR1;                                 /*              */
       union {                                         /* DCPCR2       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DCPMODE_C:1;                /*   DCPMODE_C  */
                    _UWORD :3;                         /*              */
                    _UWORD BLANKLEVEL_CB:6;            /*   BLANKLEVEL_CB */
                    _UWORD BLANKLEVEL_CR:6;            /*   BLANKLEVEL_CR */
                    } BIT;                             /*              */
             } DCPCR2;                                 /*              */
       union {                                         /* DCPCR3       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD DCPRESPONSE:3;              /*   DCPRESPONSE */
                    _UWORD :12;                        /*              */
                    } BIT;                             /*              */
             } DCPCR3;                                 /*              */
       union {                                         /* DCPCR4       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DCPSTART:6;                 /*   DCPSTART   */
                    _UWORD :10;                        /*              */
                    } BIT;                             /*              */
             } DCPCR4;                                 /*              */
       union {                                         /* DCPCR5       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DCPEND:6;                   /*   DCPEND     */
                    _UWORD :10;                        /*              */
                    } BIT;                             /*              */
             } DCPCR5;                                 /*              */
       union {                                         /* DCPCR6       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD DCPWIDTH:7;                 /*   DCPWIDTH   */
                    _UWORD :8;                         /*              */
                    } BIT;                             /*              */
             } DCPCR6;                                 /*              */
       union {                                         /* DCPCR7       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DCPPOS_Y:8;                 /*   DCPPOS_Y   */
                    _UWORD :8;                         /*              */
                    } BIT;                             /*              */
             } DCPCR7;                                 /*              */
       union {                                         /* DCPCR8       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DCPPOS_C:8;                 /*   DCPPOS_C   */
                    _UWORD :8;                         /*              */
                    } BIT;                             /*              */
             } DCPCR8;                                 /*              */
       union {                                         /* NSDCR        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD ACFINPUT:2;                 /*   ACFINPUT   */
                    _UWORD :3;                         /*              */
                    _UWORD ACFLAGTIME:5;               /*   ACFLAGTIME */
                    _UWORD :2;                         /*              */
                    _UWORD ACFFILTER:2;                /*   ACFFILTER  */
                    } BIT;                             /*              */
             } NSDCR;                                  /*              */
       union {                                         /* BTLCR        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD LOCKRANGE:2;                /*   LOCKRANGE  */
                    _UWORD LOOPGAIN:2;                 /*   LOOPGAIN   */
                    _UWORD LOCKLIMIT:2;                /*   LOCKLIMIT  */
                    _UWORD BCOFREERUN:1;               /*   BCOFREERUN */
                    _UWORD :1;                         /*              */
                    _UWORD DEFAULTSYS:2;               /*   DEFAULTSYS */
                    _UWORD NONTSC358:1;                /*   NONTSC358  */
                    _UWORD NONTSC443:1;                /*   NONTSC443  */
                    _UWORD NOPALM:1;                   /*   NOPALM     */
                    _UWORD NOPALN:1;                   /*   NOPALN     */
                    _UWORD NOPAL443:1;                 /*   NOPAL443   */
                    _UWORD NOSECAM:1;                  /*   NOSECAM    */
                    } BIT;                             /*              */
             } BTLCR;                                  /*              */
       union {                                         /* BTGPCR       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD BGPCHECK:1;                 /*   BGPCHECK   */
                    _UWORD BGPWIDTH:7;                 /*   BGPWIDTH   */
                    _UWORD BGPSTART:8;                 /*   BGPSTART   */
                    } BIT;                             /*              */
             } BTGPCR;                                 /*              */
       union {                                         /* ACCCR1       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD KILLEROFFSET:4;             /*   KILLEROFFSET */
                    _UWORD ACCMODE:1;                  /*   ACCMODE    */
                    _UWORD ACCMAXGAIN:2;               /*   ACCMAXGAIN */
                    _UWORD ACCLEVEL:9;                 /*   ACCLEVEL   */
                    } BIT;                             /*              */
             } ACCCR1;                                 /*              */
       union {                                         /* ACCCR2       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :5;                         /*              */
                    _UWORD CHROMASUBGAIN:2;            /*   CHROMASUBGAIN */
                    _UWORD CHROMAMAINGAIN:9;           /*   CHROMAMAINGAIN */
                    } BIT;                             /*              */
             } ACCCR2;                                 /*              */
       union {                                         /* ACCCR3       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD ACCRESPONSE:2;              /*   ACCRESPONSE */
                    _UWORD ACCPRECIS:6;                /*   ACCPRECIS  */
                    _UWORD KILLERMODE:1;               /*   KILLERMODE */
                    _UWORD KILLERLEVEL:6;              /*   KILLERLEVEL */
                    _UWORD :1;                         /*              */
                    } BIT;                             /*              */
             } ACCCR3;                                 /*              */
       union {                                         /* TINTCR       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD TINTSUB:6;                  /*   TINTSUB    */
                    _UWORD TINTMAIN:10;                /*   TINTMAIN   */
                    } BIT;                             /*              */
             } TINTCR;                                 /*              */
       union {                                         /* YCDCR        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD LUMADELAY:5;                /*   LUMADELAY  */
                    _UWORD :1;                         /*              */
                    _UWORD CHROMALPF:1;                /*   CHROMALPF  */
                    _UWORD DEMODMODE:2;                /*   DEMODMODE  */
                    } BIT;                             /*              */
             } YCDCR;                                  /*              */
       union {                                         /* AGCCR1       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD DOREDUCE:1;                 /*   DOREDUCE   */
                    _UWORD NOREDUCE:1;                 /*   NOREDUCE   */
                    _UWORD AGCRESPONSE:3;              /*   AGCRESPONSE */
                    _UWORD AGCLEVEL:9;                 /*   AGCLEVEL   */
                    } BIT;                             /*              */
             } AGCCR1;                                 /*              */
       union {                                         /* AGCCR2       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD AGCPRECIS:6;                /*   AGCPRECIS  */
                    _UWORD :8;                         /*              */
                    } BIT;                             /*              */
             } AGCCR2;                                 /*              */
       union {                                         /* PKLIMITCR    */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD PEAKLEVEL:2;                /*   PEAKLEVEL  */
                    _UWORD PEAKATTACK:2;               /*   PEAKATTACK */
                    _UWORD PEAKRELEASE:2;              /*   PEAKRELEASE */
                    _UWORD PEAKRATIO:2;                /*   PEAKRATIO  */
                    _UWORD MAXPEAKSAMPLES:8;           /*   MAXPEAKSAMPLES */
                    } BIT;                             /*              */
             } PKLIMITCR;                              /*              */
       union {                                         /* RGORCR1      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD RADJ_O_LEVEL0:10;           /*   RADJ_O_LEVEL0 */
                    } BIT;                             /*              */
             } RGORCR1;                                /*              */
       union {                                         /* RGORCR2      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD RADJ_U_LEVEL0:10;           /*   RADJ_U_LEVEL0 */
                    } BIT;                             /*              */
             } RGORCR2;                                /*              */
       union {                                         /* RGORCR3      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD RADJ_O_LEVEL1:10;           /*   RADJ_O_LEVEL1 */
                    } BIT;                             /*              */
             } RGORCR3;                                /*              */
       union {                                         /* RGORCR4      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD RADJ_U_LEVEL1:10;           /*   RADJ_U_LEVEL1 */
                    } BIT;                             /*              */
             } RGORCR4;                                /*              */
       union {                                         /* RGORCR5      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD RADJ_O_LEVEL2:10;           /*   RADJ_O_LEVEL2 */
                    } BIT;                             /*              */
             } RGORCR5;                                /*              */
       union {                                         /* RGORCR6      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD RADJ_U_LEVEL2:10;           /*   RADJ_U_LEVEL2 */
                    } BIT;                             /*              */
             } RGORCR6;                                /*              */
       union {                                         /* RGORCR7      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD TEST_MONI:3;                /*   TEST_MONI  */
                    _UWORD RADJ_MIX_K_FIX:3;           /*   RADJ_MIX_K_FIX */
                    _UWORD :6;                         /*              */
                    _UWORD UCMP_SW:1;                  /*   UCMP_SW    */
                    _UWORD DCMP_SW:1;                  /*   DCMP_SW    */
                    _UWORD HWIDE_SW:1;                 /*   HWIDE_SW   */
                    } BIT;                             /*              */
             } RGORCR7;                                /*              */
       _UBYTE wk3[24];                                 /*              */
       union {                                         /* AFCPFCR      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :11;                        /*              */
                    _UWORD PHDET_FIX:1;                /*   PHDET_FIX  */
                    _UWORD :1;                         /*              */
                    _UWORD PHDET_DIV:3;                /*   PHDET_DIV  */
                    } BIT;                             /*              */
             } AFCPFCR;                                /*              */
       union {                                         /* RUPDCR       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD NEWSETTING:1;               /*   NEWSETTING */
                    _UWORD :15;                        /*              */
                    } BIT;                             /*              */
             } RUPDCR;                                 /*              */
       union {                                         /* VSYNCSR      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD FHCOUNT_L:1;                /*   FHCOUNT_L  */
                    _UWORD FHLOCK:1;                   /*   FHLOCK     */
                    _UWORD ISNOISY:1;                  /*   ISNOISY    */
                    _UWORD FHMODE:1;                   /*   FHMODE     */
                    _UWORD NOSIGNAL:1;                 /*   NOSIGNAL   */
                    _UWORD FVLOCK:1;                   /*   FVLOCK     */
                    _UWORD FVMODE:1;                   /*   FVMODE     */
                    _UWORD INTERLACED:1;               /*   INTERLACED */
                    _UWORD FVCOUNT:8;                  /*   FVCOUNT    */
                    } BIT;                             /*              */
             } VSYNCSR;                                /*              */
       union {                                         /* HSYNCSR      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD FHCOUNT_H:16;               /*   FHCOUNT_H  */
                    } BIT;                             /*              */
             } HSYNCSR;                                /*              */
       union {                                         /* DCPSR1       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD CLAMPLEVEL_CB:6;            /*   CLAMPLEVEL_CB */
                    _UWORD CLAMPLEVEL_Y:10;            /*   CLAMPLEVEL_Y */
                    } BIT;                             /*              */
             } DCPSR1;                                 /*              */
       union {                                         /* DCPSR2       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD CLAMPLEVEL_CR:6;            /*   CLAMPLEVEL_CR */
                    _UWORD :10;                        /*              */
                    } BIT;                             /*              */
             } DCPSR2;                                 /*              */
       _UBYTE wk4[4];                                  /*              */
       union {                                         /* NSDSR        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD ACFSTRENGTH:16;             /*   ACFSTRENGTH */
                    } BIT;                             /*              */
             } NSDSR;                                  /*              */
       union {                                         /* CROMASR1     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD COLORSYS:2;                 /*   COLORSYS   */
                    _UWORD FSCMODE:1;                  /*   FSCMODE    */
                    _UWORD FSCLOCK:1;                  /*   FSCLOCK    */
                    _UWORD NOBURST:1;                  /*   NOBURST    */
                    _UWORD ACCSUBGAIN:2;               /*   ACCSUBGAIN */
                    _UWORD ACCMAINGAIN:9;              /*   ACCMAINGAIN */
                    } BIT;                             /*              */
             } CROMASR1;                               /*              */
       union {                                         /* CROMASR2     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD ISSECAM:1;                  /*   ISSECAM    */
                    _UWORD ISPAL:1;                    /*   ISPAL      */
                    _UWORD ISNTSC:1;                   /*   ISNTSC     */
                    _UWORD :2;                         /*              */
                    _UWORD LOCKLEVEL:8;                /*   LOCKLEVEL  */
                    } BIT;                             /*              */
             } CROMASR2;                               /*              */
       union {                                         /* SYNCSSR      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD ISREDUCED:1;                /*   ISREDUCED  */
                    _UWORD :2;                         /*              */
                    _UWORD SYNCDEPTH:10;               /*   SYNCDEPTH  */
                    } BIT;                             /*              */
             } SYNCSSR;                                /*              */
       union {                                         /* AGCCSR1      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD HIGHSAMPLES:8;              /*   HIGHSAMPLES */
                    _UWORD PEAKSAMPLES:8;              /*   PEAKSAMPLES */
                    } BIT;                             /*              */
             } AGCCSR1;                                /*              */
       union {                                         /* AGCCSR2      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD AGCCONVERGE:1;              /*   AGCCONVERGE */
                    _UWORD AGCGAIN:8;                  /*   AGCGAIN    */
                    } BIT;                             /*              */
             } AGCCSR2;                                /*              */
       _UBYTE wk5[14];                                 /*              */
       _UBYTE wk6[90];                                 /*              */
       _UBYTE wk7[4];                                  /*              */
       union {                                         /* YCSCR3       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD K15:4;                      /*   K15        */
                    _UWORD K13:6;                      /*   K13        */
                    _UWORD K11:6;                      /*   K11        */
                    } BIT;                             /*              */
             } YCSCR3;                                 /*              */
       union {                                         /* YCSCR4       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD K16:4;                      /*   K16        */
                    _UWORD K14:6;                      /*   K14        */
                    _UWORD K12:6;                      /*   K12        */
                    } BIT;                             /*              */
             } YCSCR4;                                 /*              */
       union {                                         /* YCSCR5       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD K22A:8;                     /*   K22A       */
                    _UWORD :2;                         /*              */
                    _UWORD K21A:6;                     /*   K21A       */
                    } BIT;                             /*              */
             } YCSCR5;                                 /*              */
       union {                                         /* YCSCR6       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD K22B:8;                     /*   K22B       */
                    _UWORD :2;                         /*              */
                    _UWORD K21B:6;                     /*   K21B       */
                    } BIT;                             /*              */
             } YCSCR6;                                 /*              */
       union {                                         /* YCSCR7       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD K23B:4;                     /*   K23B       */
                    _UWORD K23A:4;                     /*   K23A       */
                    _UWORD :3;                         /*              */
                    _UWORD K24:5;                      /*   K24        */
                    } BIT;                             /*              */
             } YCSCR7;                                 /*              */
       union {                                         /* YCSCR8       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD HBPF_NARROW:1;              /*   HBPF_NARROW */
                    _UWORD HVBPF_NARROW:1;             /*   HVBPF_NARROW */
                    _UWORD HBPF1_9TAP_ON:1;            /*   HBPF1_9TAP_ON */
                    _UWORD HVBPF1_9TAP_ON:1;           /*   HVBPF1_9TAP_ON */
                    _UWORD HFIL_TAP_SEL:1;             /*   HFIL_TAP_SEL */
                    _UWORD :11;                        /*              */
                    } BIT;                             /*              */
             } YCSCR8;                                 /*              */
       union {                                         /* YCSCR9       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DET2_ON:1;                  /*   DET2_ON    */
                    _UWORD :3;                         /*              */
                    _UWORD HSEL_MIX_Y:4;               /*   HSEL_MIX_Y */
                    _UWORD VSEL_MIX_Y:4;               /*   VSEL_MIX_Y */
                    _UWORD HVSEL_MIX_Y:4;              /*   HVSEL_MIX_Y */
                    } BIT;                             /*              */
             } YCSCR9;                                 /*              */
       _UBYTE wk8[2];                                  /*              */
       union {                                         /* YCSCR11      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :7;                         /*              */
                    _UWORD V_Y_LEVEL:9;                /*   V_Y_LEVEL */
                    } BIT;                             /*              */
             } YCSCR11;                                /*              */
       union {                                         /* YCSCR12      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD DET2_MIX_C:4;               /*   DET2_MIX_C */
                    _UWORD DET2_MIX_Y:4;               /*   DET2_MIX_Y */
                    _UWORD :4;                        /*              */
                    _UWORD FIL2_MODE_2D:2;             /*   FIL2_MODE_2D */
                    _UWORD :1;                         /*              */
                    _UWORD FIL2_NARROW_2D:1;           /*   FIL2_NARROW_2D */
                    } BIT;                             /*              */
             } YCSCR12;                                /*              */
       _UBYTE wk9[104];                                /*              */
       union {                                         /* DCPCR9       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD CLP_HOLD_ON_Y:1;            /*   CLP_HOLD_ON_Y */
                    _UWORD CLP_HOLD_ON_CB:1;           /*   CLP_HOLD_ON_CB */
                    _UWORD CLP_HOLD_ON_CR:1;           /*   CLP_HOLD_ON_CR */
                    _UWORD :10;                        /*              */
                    } BIT;                             /*              */
             } DCPCR9;                                 /*              */
       _UBYTE wk10[12];                                /*              */
       _UBYTE wk11[4];                                 /*              */
       union {                                         /* YCTWA_F0     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F0:13;           /*   FIL2_2D_WA_F0 */
                    } BIT;                             /*              */
             } YCTWA_F0;                               /*              */
       union {                                         /* YCTWA_F1     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F1:13;           /*   FIL2_2D_WA_F1 */
                    } BIT;                             /*              */
             } YCTWA_F1;                               /*              */
       union {                                         /* YCTWA_F2     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F2:13;           /*   FIL2_2D_WA_F2 */
                    } BIT;                             /*              */
             } YCTWA_F2;                               /*              */
       union {                                         /* YCTWA_F3     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F3:13;           /*   FIL2_2D_WA_F3 */
                    } BIT;                             /*              */
             } YCTWA_F3;                               /*              */
       union {                                         /* YCTWA_F4     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F4:13;           /*   FIL2_2D_WA_F4 */
                    } BIT;                             /*              */
             } YCTWA_F4;                               /*              */
       union {                                         /* YCTWA_F5     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F5:13;           /*   FIL2_2D_WA_F5 */
                    } BIT;                             /*              */
             } YCTWA_F5;                               /*              */
       union {                                         /* YCTWA_F6     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F6:13;           /*   FIL2_2D_WA_F6 */
                    } BIT;                             /*              */
             } YCTWA_F6;                               /*              */
       union {                                         /* YCTWA_F7     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F7:13;           /*   FIL2_2D_WA_F7 */
                    } BIT;                             /*              */
             } YCTWA_F7;                               /*              */
       union {                                         /* YCTWA_F8     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WA_F8:13;           /*   FIL2_2D_WA_F8 */
                    } BIT;                             /*              */
             } YCTWA_F8;                               /*              */
       union {                                         /* YCTWB_F0     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F0:13;           /*   FIL2_2D_WB_F0 */
                    } BIT;                             /*              */
             } YCTWB_F0;                               /*              */
       union {                                         /* YCTWB_F1     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F1:13;           /*   FIL2_2D_WB_F1 */
                    } BIT;                             /*              */
             } YCTWB_F1;                               /*              */
       union {                                         /* YCTWB_F2     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F2:13;           /*   FIL2_2D_WB_F2 */
                    } BIT;                             /*              */
             } YCTWB_F2;                               /*              */
       union {                                         /* YCTWB_F3     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F3:13;           /*   FIL2_2D_WB_F3 */
                    } BIT;                             /*              */
             } YCTWB_F3;                               /*              */
       union {                                         /* YCTWB_F4     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F4:13;           /*   FIL2_2D_WB_F4 */
                    } BIT;                             /*              */
             } YCTWB_F4;                               /*              */
       union {                                         /* YCTWB_F5     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F5:13;           /*   FIL2_2D_WB_F5 */
                    } BIT;                             /*              */
             } YCTWB_F5;                               /*              */
       union {                                         /* YCTWB_F6     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F6:13;           /*   FIL2_2D_WB_F6 */
                    } BIT;                             /*              */
             } YCTWB_F6;                               /*              */
       union {                                         /* YCTWB_F7     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F7:13;           /*   FIL2_2D_WB_F7 */
                    } BIT;                             /*              */
             } YCTWB_F7;                               /*              */
       union {                                         /* YCTWB_F8     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_WB_F8:13;           /*   FIL2_2D_WB_F8 */
                    } BIT;                             /*              */
             } YCTWB_F8;                               /*              */
       union {                                         /* YCTNA_F0     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F0:13;           /*   FIL2_2D_NA_F0 */
                    } BIT;                             /*              */
             } YCTNA_F0;                               /*              */
       union {                                         /* YCTNA_F1     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F1:13;           /*   FIL2_2D_NA_F1 */
                    } BIT;                             /*              */
             } YCTNA_F1;                               /*              */
       union {                                         /* YCTNA_F2     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F2:13;           /*   FIL2_2D_NA_F2 */
                    } BIT;                             /*              */
             } YCTNA_F2;                               /*              */
       union {                                         /* YCTNA_F3     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F3:13;           /*   FIL2_2D_NA_F3 */
                    } BIT;                             /*              */
             } YCTNA_F3;                               /*              */
       union {                                         /* YCTNA_F4     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F4:13;           /*   FIL2_2D_NA_F4 */
                    } BIT;                             /*              */
             } YCTNA_F4;                               /*              */
       union {                                         /* YCTNA_F5     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F5:13;           /*   FIL2_2D_NA_F5 */
                    } BIT;                             /*              */
             } YCTNA_F5;                               /*              */
       union {                                         /* YCTNA_F6     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F6:13;           /*   FIL2_2D_NA_F6 */
                    } BIT;                             /*              */
             } YCTNA_F6;                               /*              */
       union {                                         /* YCTNA_F7     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F7:13;           /*   FIL2_2D_NA_F7 */
                    } BIT;                             /*              */
             } YCTNA_F7;                               /*              */
       union {                                         /* YCTNA_F8     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NA_F8:13;           /*   FIL2_2D_NA_F8 */
                    } BIT;                             /*              */
             } YCTNA_F8;                               /*              */
       union {                                         /* YCTNB_F0     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F0:13;           /*   FIL2_2D_NB_F0 */
                    } BIT;                             /*              */
             } YCTNB_F0;                               /*              */
       union {                                         /* YCTNB_F1     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F1:13;           /*   FIL2_2D_NB_F1 */
                    } BIT;                             /*              */
             } YCTNB_F1;                               /*              */
       union {                                         /* YCTNB_F2     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F2:13;           /*   FIL2_2D_NB_F2 */
                    } BIT;                             /*              */
             } YCTNB_F2;                               /*              */
       union {                                         /* YCTNB_F3     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F3:13;           /*   FIL2_2D_NB_F3 */
                    } BIT;                             /*              */
             } YCTNB_F3;                               /*              */
       union {                                         /* YCTNB_F4     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F4:13;           /*   FIL2_2D_NB_F4 */
                    } BIT;                             /*              */
             } YCTNB_F4;                               /*              */
       union {                                         /* YCTNB_F5     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F5:13;           /*   FIL2_2D_NB_F5 */
                    } BIT;                             /*              */
             } YCTNB_F5;                               /*              */
       union {                                         /* YCTNB_F6     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F6:13;           /*   FIL2_2D_NB_F6 */
                    } BIT;                             /*              */
             } YCTNB_F6;                               /*              */
       union {                                         /* YCTNB_F7     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F7:13;           /*   FIL2_2D_NB_F7 */
                    } BIT;                             /*              */
             } YCTNB_F7;                               /*              */
       union {                                         /* YCTNB_F8     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :3;                         /*              */
                    _UWORD FIL2_2D_NB_F8:13;           /*   FIL2_2D_NB_F8 */
                    } BIT;                             /*              */
             } YCTNB_F8;                               /*              */
       _UBYTE wk12[38];                                /*              */
       union {                                         /* YGAINCR      */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD Y_GAIN2:10;                 /*   Y_GAIN2    */
                    } BIT;                             /*              */
             } YGAINCR;                                /*              */
       union {                                         /* CBGAINCR     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD CB_GAIN2:10;                /*   CB_GAIN2   */
                    } BIT;                             /*              */
             } CBGAINCR;                               /*              */
       union {                                         /* CRGAINCR     */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :6;                         /*              */
                    _UWORD CR_GAIN2:10;                /*   CR_GAIN2   */
                    } BIT;                             /*              */
             } CRGAINCR;                               /*              */
       _UBYTE wk13[122];                               /*              */
       union {                                         /* PGA_UPDATE   */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD PGA_VEN:1;                  /*   PGA_VEN    */
                    } BIT;                             /*              */
             } PGA_UPDATE;                             /*              */
       union {                                         /* PGACR        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :2;                         /*              */
                    _UWORD PGA_GAIN_SEL:1;             /*   PGA_GAIN_SEL */
                    _UWORD PGA_GAIN:5;                 /*   PGA_GAIN   */
                    _UWORD :8;                         /*              */
                    } BIT;                             /*              */
             } PGACR;                                  /*              */
       union {                                         /* ADCCR2       */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :15;                        /*              */
                    _UWORD ADC_VINSEL:1;               /*   ADC_VINSEL */
                    } BIT;                             /*              */
             } ADCCR2;                                 /*              */
};                                                     /*              */
struct st_ubc {								/* struct UBC   */
	union {									/* BAR0         */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BA0_:32;				/*   BA0_       */
		} BIT;								/*              */
	} BAR0;									/*              */
	union {									/* BAMR0        */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BAM0_:32;				/*   BAM0_      */
		} BIT;
	} BAMR0;
	union {									/* BDR0         */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BD0_:32;				/*   BD0_       */
		} BIT;
	} BDR0;
	union {									/* BDMR0        */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BDM0_:32;				/*   BDM0_      */
		} BIT;
	} BDMR0;
	union {									/* BAR1         */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BA1_:32;				/*   BA1_       */
		} BIT;
	} BAR1;
	union {									/* BAMR1        */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BAM1_:32;				/*   BAM1_      */
		} BIT;
	} BAMR1;
	union {									/* BDR1         */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BD1_:32;				/*   BD1_       */
		} BIT;
	} BDR1;
	union {									/* BDMR1        */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD BDM1_:32;				/*   BDM1_      */
		} BIT;
	} BDMR1;
	_UBYTE wk0[128];
	union {									/* BBR0         */
		_UWORD WORD;						/*  Word Access */
		struct {							/*  Bit Access  */
			_UWORD :2;
			_UWORD UBID0:1;					/*   UBID0      */
			_UWORD DBE0:1;					/*   DBE0       */
			_UWORD :2;						/*              */
			_UWORD CP0_:2;					/*   CP0_       */
			_UWORD CD0_:2;					/*   CD0_       */
			_UWORD ID0_:2;					/*   ID0_       */
			_UWORD RW0_:2;					/*   RW0_       */
			_UWORD SZ0_:2;					/*   SZ0_       */
		} BIT;
	} BBR0;
	_UBYTE wk1[14];
	union {									/* BBR1         */
		_UWORD WORD;						/*  Word Access */
		struct {							/*  Bit Access  */
			_UWORD :2;						/*              */
			_UWORD UBID1:1;					/*   UBID1      */
			_UWORD DBE1:1;					/*   DBE1       */
			_UWORD :2;						/*              */
			_UWORD CP1_:2;					/*   CP1_       */
			_UWORD CD1_:2;					/*   CD1_       */
			_UWORD ID1_:2;					/*   ID1_       */
			_UWORD RW1_:2;					/*   RW1_       */
			_UWORD SZ1_:2;					/*   SZ1_       */
		} BIT;
	} BBR1;
	_UBYTE wk2[14];
	union {									/* BRCR         */
		_UDWORD LONG;						/*  Long Access */
		struct {							/*  Bit Access  */
			_UDWORD :12;					/*              */
			_UDWORD UTOD1:1;				/*   UTOD1       */
			_UDWORD UTOD0:1;				/*   UTOD0       */
			_UDWORD CKS:2;					/*   CKS        */
			_UDWORD SCMFC0:1;				/*   SCMFC0     */
			_UDWORD SCMFC1:1;				/*   SCMFC1     */
			_UDWORD SCMFD0:1;				/*   SCMFD0     */
			_UDWORD SCMFD1:1;				/*   SCMFD1     */
			_UDWORD :5;						/*              */
			_UDWORD PCB1:1;					/*   PCB1       */
			_UDWORD PCB0:1;					/*   PCB0       */
			_UDWORD :5;						/*              */
		} BIT;
	} BRCR;
};
struct st_disc {                                       /* struct DISC  */
       union {                                         /* DOCMCR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :15;                       /*              */
                    _UDWORD CMPRU:1;                   /*   CMPRU      */
                    _UDWORD :15;                       /*              */
                    _UDWORD CMPR:1;                    /*   CMPR       */
                    } BIT;                             /*              */
             } DOCMCR;                                 /*              */
       union {                                         /* DOCMSTR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD CMPST:1;                   /*   CMPST      */
                    } BIT;                             /*              */
             } DOCMSTR;                                /*              */
       union {                                         /* DOCMCLSTR    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD CMPCLST:1;                 /*   CMPCLST    */
                    } BIT;                             /*              */
             } DOCMCLSTR;                              /*              */
       union {                                         /* DOCMIENR     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :31;                       /*              */
                    _UDWORD CMPIEN:1;                  /*   CMPIEN     */
                    } BIT;                             /*              */
             } DOCMIENR;                               /*              */
	   _UBYTE wk0[4];                                  /*              */
       union {                                         /* DOCMPMR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :15;                       /*              */
                    _UDWORD CMPBT:1;                   /*   CMPBT      */
                    _UDWORD CMPDFA:8;                  /*   CMPDFA     */
                    _UDWORD CMPDAUF:1;                 /*   CMPDAUF    */
                    _UDWORD :3;                        /*              */
                    _UDWORD CMPSELP:4;                 /*   CMPSELP    */
                    } BIT;                             /*              */
             } DOCMPMR;                                /*              */
       union {                                         /* DOCMECRCR    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMPECRC:32;                /*   CMPECRC    */
                    } BIT;                             /*              */
             } DOCMECRCR;                              /*              */
       union {                                         /* DOCMCCRCR    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMPCCRC:32;                /*   CMPCCRC    */
                    } BIT;                             /*              */
             } DOCMCCRCR;                              /*              */
       union {                                         /* DOCMSPXR     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :21;                       /*              */
                    _UDWORD CMPSPX:11;                 /*   CMPSPX     */
                    } BIT;                             /*              */
             } DOCMSPXR;                               /*              */
       union {                                         /* DOCMSPYR     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :21;                       /*              */
                    _UDWORD CMPSPY:11;                 /*   CMPSPY     */
                    } BIT;                             /*              */
             } DOCMSPYR;                               /*              */
       union {                                         /* DOCMSZXR     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :21;                       /*              */
                    _UDWORD CMPSZX:11;                 /*   CMPSZX     */
                    } BIT;                             /*              */
             } DOCMSZXR;                               /*              */
       union {                                         /* DOCMSZYR     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :21;                       /*              */
                    _UDWORD CMPSZY:11;                 /*   CMPSZY     */
                    } BIT;                             /*              */
             } DOCMSZYR;                               /*              */
       union {                                         /* DOCMCRCIR    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CRCINI:32;                 /*   CRCINI     */
                    } BIT;                             /*              */
             } DOCMCRCIR;                              /*              */
};                                                     /*              */
struct st_jcu {                                        /* struct JCU   */
       union {                                         /* JCMOD        */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :4;                         /*              */
                    _UBYTE DSP:1;                      /*   DSP        */
                    _UBYTE REDU:3;                     /*   REDU       */
                    } BIT;                             /*              */
             } JCMOD;                                  /*              */
       union {                                         /* JCCMD        */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE BRST:1;                     /*   BRST       */
                    _UBYTE :4;                         /*              */
                    _UBYTE JEND:1;                     /*   JEND       */
                    _UBYTE JRST:1;                     /*   JRST       */
                    _UBYTE JSRT:1;                     /*   JSRT       */
                    } BIT;                             /*              */
             } JCCMD;                                  /*              */
       _UBYTE wk0_0[1];                                /*              */
       union {                                         /* JCQTN        */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :2;                         /*              */
                    _UBYTE QT3:2;                      /*   QT3        */
                    _UBYTE QT2:2;                      /*   QT2        */
                    _UBYTE QT1:2;                      /*   QT1        */
                    } BIT;                             /*              */
             } JCQTN;                                  /*              */
       union {                                         /* JCHTN        */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :2;                         /*              */
                    _UBYTE HTA3:1;                     /*   HTA3       */
                    _UBYTE HTD3:1;                     /*   HTD3       */
                    _UBYTE HTA2:1;                     /*   HTA2       */
                    _UBYTE HTD2:1;                     /*   HTD2       */
                    _UBYTE HTA1:1;                     /*   HTA1       */
                    _UBYTE HTD1:1;                     /*   HTD1       */
                    } BIT;                             /*              */
             } JCHTN;                                  /*              */
       union {                                         /* JCDRIU       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE DRIU:8;                     /*   DRIU       */
                    } BIT;                             /*              */
             } JCDRIU;                                 /*              */
       union {                                         /* JCDRID       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE DRID:8;                     /*   DRID       */
                    } BIT;                             /*              */
             } JCDRID;                                 /*              */
       union {                                         /* JCVSZU       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE VSZU:8;                     /*   VSZU       */
                    } BIT;                             /*              */
             } JCVSZU;                                 /*              */
       union {                                         /* JCVSZD       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE VSZD:8;                     /*   VSZD       */
                    } BIT;                             /*              */
             } JCVSZD;                                 /*              */
       union {                                         /* JCHSZU       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE HSZU:8;                     /*   HSZU       */
                    } BIT;                             /*              */
             } JCHSZU;                                 /*              */
       union {                                         /* JCHSZD       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE HSZD:8;                     /*   HSZD       */
                    } BIT;                             /*              */
             } JCHSZD;                                 /*              */
       union {                                         /* JCDTCU       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE DCU:8;                      /*   DCU        */
                    } BIT;                             /*              */
             } JCDTCU;                                 /*              */
       union {                                         /* JCDTCM       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE DCM:8;                      /*   DCM        */
                    } BIT;                             /*              */
             } JCDTCM;                                 /*              */
       union {                                         /* JCDTCD       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE DCD:8;                      /*   DCD        */
                    } BIT;                             /*              */
             } JCDTCD;                                 /*              */
       union {                                         /* JINTE0       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE INT7:1;                     /*   INT7       */
                    _UBYTE INT6:1;                     /*   INT6       */
                    _UBYTE INT5:1;                     /*   INT5       */
                    _UBYTE :1;                         /*              */
                    _UBYTE INT3:1;                     /*   INT3       */
                    _UBYTE :3;                         /*              */
                    } BIT;                             /*              */
             } JINTE0;                                 /*              */
       union {                                         /* JINTS0       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :1;                         /*              */
                    _UBYTE INS6:1;                     /*   INS6       */
                    _UBYTE INS5:1;                     /*   INS5       */
                    _UBYTE :1;                         /*              */
                    _UBYTE INS3:1;                     /*   INS3       */
                    _UBYTE :3;                         /*              */
                    } BIT;                             /*              */
             } JINTS0;                                 /*              */
       union {                                         /* JCDERR       */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :4;                         /*              */
                    _UBYTE ERR:4;                      /*   ERR        */
                    } BIT;                             /*              */
             } JCDERR;                                 /*              */
       union {                                         /* JCRST        */
             _UBYTE BYTE;                              /*  Byte Access */
             struct {                                  /*  Bit Access  */
                    _UBYTE :7;                         /*              */
                    _UBYTE RST:1;                      /*   RST        */
                    } BIT;                             /*              */
             } JCRST;                                  /*              */
       _UBYTE wk0[46];                                 /*              */
       union {                                         /* JIFECNT      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :17;                       /*              */
                    _UDWORD JOUTRINI:1;                /*   JOUTRINI   */
                    _UDWORD JOUTRCMD:1;                /*   JOUTRCMD   */
                    _UDWORD JOUTC:1;                   /*   JOUTC      */
                    _UDWORD :1;                        /*              */
                    _UDWORD JOUTSWAP:3;                /*   JOUTSWAP   */
                    _UDWORD :1;                        /*              */
                    _UDWORD DINRINI:1;                 /*   DINRINI    */
                    _UDWORD DINRCMD:1;                 /*   DINRCMD    */
                    _UDWORD DINLC:1;                   /*   DINLC      */
                    _UDWORD :1;                        /*              */
                    _UDWORD DINSWAP:3;                 /*   DINSWAP    */
                    } BIT;                             /*              */
             } JIFECNT;                                /*              */
       union {                                         /* JIFESA       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ESA:32;                    /*   ESA        */
                    } BIT;                             /*              */
             } JIFESA;                                 /*              */
       union {                                         /* JIFESOFST    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :17;                       /*              */
                    _UDWORD ESMW:15;                   /*   ESMW       */
                    } BIT;                             /*              */
             } JIFESOFST;                              /*              */
       union {                                         /* JIFEDA       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD EDA:32;                    /*   EDA        */
                    } BIT;                             /*              */
             } JIFEDA;                                 /*              */
       union {                                         /* JIFESLC      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :16;                       /*              */
                    _UDWORD LINES:16;                  /*   LINES      */
                    } BIT;                             /*              */
             } JIFESLC;                                /*              */
       union {                                         /* JIFEDDC      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :16;                       /*              */
                    _UDWORD JDATAS:16;                 /*   JDATAS     */
                    } BIT;                             /*              */
             } JIFEDDC;                                /*              */
       union {                                         /* JIFDCNT      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :2;                        /*              */
                    _UDWORD VINTER:2;                  /*   VINTER     */
                    _UDWORD HINTER:2;                  /*   HINTER     */
                    _UDWORD OPF:2;                     /*   OPF        */
                    _UDWORD :9;                        /*              */
                    _UDWORD JINRINI:1;                 /*   JINRINI    */
                    _UDWORD JINRCMD:1;                 /*   JINRCMD    */
                    _UDWORD JINC:1;                    /*   JINC       */
                    _UDWORD :1;                        /*              */
                    _UDWORD JINSWAP:3;                 /*   JINSWAP    */
                    _UDWORD :1;                        /*              */
                    _UDWORD DOUTRINI:1;                /*   DOUTRINI   */
                    _UDWORD DOUTRCMD:1;                /*   DOUTRCMD   */
                    _UDWORD DOUTLC:1;                  /*   DOUTLC     */
                    _UDWORD :1;                        /*              */
                    _UDWORD DOUTSWAP:3;                /*   DOUTSWAP   */
                    } BIT;                             /*              */
             } JIFDCNT;                                /*              */
       union {                                         /* JIFDSA       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DSA:32;                    /*   DSA        */
                    } BIT;                             /*              */
             } JIFDSA;                                 /*              */
       union {                                         /* JIFDDOFST    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :17;                       /*              */
                    _UDWORD DDMW:15;                   /*   DDMW       */
                    } BIT;                             /*              */
             } JIFDDOFST;                              /*              */
       union {                                         /* JIFDDA       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DDA:32;                    /*   DDA        */
                    } BIT;                             /*              */
             } JIFDDA;                                 /*              */
       union {                                         /* JIFDSDC      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :16;                       /*              */
                    _UDWORD JDATAS:16;                 /*   JDATAS     */
                    } BIT;                             /*              */
             } JIFDSDC;                                /*              */
       union {                                         /* JIFDDLC      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :16;                       /*              */
                    _UDWORD LINES:16;                  /*   LINES      */
                    } BIT;                             /*              */
             } JIFDDLC;                                /*              */
       union {                                         /* JIFDADT      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :24;                       /*              */
                    _UDWORD ALPHA:8;                   /*   ALPHA      */
                    } BIT;                             /*              */
             } JIFDADT;                                /*              */
       _UBYTE wk1[24];                                 /*              */
       union {                                         /* JINTE1       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD CBTEN:1;                   /*   CBTEN      */
                    _UDWORD DINLEN:1;                  /*   DINLEN     */
                    _UDWORD JOUTEN:1;                  /*   JOUTEN     */
                    _UDWORD :1;                        /*              */
                    _UDWORD DBTEN:1;                   /*   DBTEN      */
                    _UDWORD JINEN:1;                   /*   JINEN      */
                    _UDWORD DOUTLEN:1;                 /*   DOUTLEN    */
                    } BIT;                             /*              */
             } JINTE1;                                 /*              */
       union {                                         /* JINTS1       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :25;                       /*              */
                    _UDWORD CBTF:1;                    /*   CBTF       */
                    _UDWORD DINLF:1;                   /*   DINLF      */
                    _UDWORD JOUTF:1;                   /*   JOUTF      */
                    _UDWORD :1;                        /*              */
                    _UDWORD DBTF:1;                    /*   DBTF       */
                    _UDWORD JINF:1;                    /*   JINF       */
                    _UDWORD DOUTLF:1;                  /*   DOUTLF     */
                    } BIT;                             /*              */
             } JINTS1;                                 /*              */
       _UBYTE wk2[108];                                /*              */
       _UBYTE JCQTBL0[64];                             /* JCQTBL0      */
       _UBYTE JCQTBL1[64];                             /* JCQTBL1      */
       _UBYTE JCQTBL2[64];                             /* JCQTBL2      */
       _UBYTE JCQTBL3[64];                             /* JCQTBL3      */
       _UBYTE JCHTBD0[28];                             /* JCHTBD0      */
       _UBYTE wk7[4];                                  /*              */
       _UBYTE JCHTBA0[178];                            /* JCHTBA0      */
       _UBYTE wk8[46];                                 /*              */
       _UBYTE JCHTBD1[28];                             /* JCHTBD1      */
       _UBYTE wk9[4];                                  /*              */
       _UBYTE JCHTBA1[178];                            /* JCHTBA1      */
};                                                     /*              */
struct st_spibsc {                                     /* struct SPIBSC */
       union {                                         /* CMNCR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD MD:1;                      /*   MD         */
                    _UDWORD :7;                        /*              */
                    _UDWORD MOIIO3:2;                  /*   MOIIO3     */
                    _UDWORD MOIIO2:2;                  /*   MOIIO2     */
                    _UDWORD MOIIO1:2;                  /*   MOIIO1     */
                    _UDWORD MOIIO0:2;                  /*   MOIIO0     */
                    _UDWORD IO3FV:2;                   /*   IO3FV      */
                    _UDWORD IO2FV:2;                   /*   IO2FV      */
                    _UDWORD :2;                        /*              */
                    _UDWORD IO0FV:2;                   /*   IO0FV      */
                    _UDWORD :1;                        /*              */
                    _UDWORD CPHAT:1;                   /*   CPHAT      */
                    _UDWORD CPHAR:1;                   /*   CPHAR      */
                    _UDWORD SSLP:1;                    /*   SSLP       */
                    _UDWORD CPOL:1;                    /*   CPOL       */
                    _UDWORD :1;                        /*              */
                    _UDWORD BSZ:2;                     /*   BSZ        */
                    } BIT;                             /*              */
             } CMNCR;                                  /*              */
       union {                                         /* SSLDR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :13;                       /*              */
                    _UDWORD SPNDL:3;                   /*   SPNDL      */
                    _UDWORD :5;                        /*              */
                    _UDWORD SLNDL:3;                   /*   SLNDL      */
                    _UDWORD :5;                        /*              */
                    _UDWORD SCKDL:3;                   /*   SCKDL      */
                    } BIT;                             /*              */
             } SSLDR;                                  /*              */
       union {                                         /* SPBCR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :16;                       /*              */
                    _UDWORD SPBR:8;                    /*   SPBR       */
                    _UDWORD :6;                        /*              */
                    _UDWORD BRDV:2;                    /*   BRDV       */
                    } BIT;                             /*              */
             } SPBCR;                                  /*              */
       union {                                         /* DRCR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :12;                       /*              */
                    _UDWORD RBURST:4;                  /*   RBURST     */
                    _UDWORD :6;                        /*              */
                    _UDWORD RCF:1;                     /*   RCF        */
                    _UDWORD RBE:1;                     /*   RBE        */
                    _UDWORD :7;                        /*              */
                    _UDWORD SSLE:1;                    /*   SSLE       */
                    } BIT;                             /*              */
             } DRCR;                                   /*              */
       union {                                         /* DRCMR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :8;                        /*              */
                    _UDWORD CMD:8;                     /*   CMD        */
                    _UDWORD :8;                        /*              */
                    _UDWORD OCMD:8;                    /*   OCMD       */
                    } BIT;                             /*              */
             } DRCMR;                                  /*              */
       union {                                         /* DREAR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :8;                        /*              */
                    _UDWORD EAV:8;                     /*   EAV        */
                    _UDWORD :13;                       /*              */
                    _UDWORD EAC:3;                     /*   EAC        */
                    } BIT;                             /*              */
             } DREAR;                                  /*              */
       union {                                         /* DROPR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD OPD3:8;                    /*   OPD3       */
                    _UDWORD OPD2:8;                    /*   OPD2       */
                    _UDWORD OPD1:8;                    /*   OPD1       */
                    _UDWORD OPD0:8;                    /*   OPD0       */
                    } BIT;                             /*              */
             } DROPR;                                  /*              */
       union {                                         /* DRENR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CDB:2;                     /*   CDB        */
                    _UDWORD OCDB:2;                    /*   OCDB       */
                    _UDWORD :2;                        /*              */
                    _UDWORD ADB:2;                     /*   ADB        */
                    _UDWORD :2;                        /*              */
                    _UDWORD OPDB:2;                    /*   OPDB       */
                    _UDWORD :2;                        /*              */
                    _UDWORD DRDB:2;                    /*   DRDB       */
                    _UDWORD :1;                        /*              */
                    _UDWORD CDE:1;                     /*   CDE        */
                    _UDWORD :1;                        /*              */
                    _UDWORD OCDE:1;                    /*   OCDE       */
                    _UDWORD ADE:4;                     /*   ADE        */
                    _UDWORD OPDE:4;                    /*   OPDE       */
                    _UDWORD :4;                        /*              */
                    } BIT;                             /*              */
             } DRENR;                                  /*              */
       union {                                         /* SMCR         */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :23;                       /*              */
                    _UDWORD SSLKP:1;                   /*   SSLKP      */
                    _UDWORD :5;                        /*              */
                    _UDWORD SPIRE:1;                   /*   SPIRE      */
                    _UDWORD SPIWE:1;                   /*   SPIWE      */
                    _UDWORD SPIE:1;                    /*   SPIE       */
                    } BIT;                             /*              */
             } SMCR;                                   /*              */
       union {                                         /* SMCMR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :8;                        /*              */
                    _UDWORD CMD:8;                     /*   CMD        */
                    _UDWORD :8;                        /*              */
                    _UDWORD OCMD:8;                    /*   OCMD       */
                    } BIT;                             /*              */
             } SMCMR;                                  /*              */
       union {                                         /* SMADR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ADR:32;                    /*   ADR        */
                    } BIT;                             /*              */
             } SMADR;                                  /*              */
       union {                                         /* SMOPR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD OPD3:8;                    /*   OPD3       */
                    _UDWORD OPD2:8;                    /*   OPD2       */
                    _UDWORD OPD1:8;                    /*   OPD1       */
                    _UDWORD OPD0:8;                    /*   OPD0       */
                    } BIT;                             /*              */
             } SMOPR;                                  /*              */
       union {                                         /* SMENR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CDB:2;                     /*   CDB        */
                    _UDWORD OCDB:2;                    /*   OCDB       */
                    _UDWORD :2;                        /*              */
                    _UDWORD ADB:2;                     /*   ADB        */
                    _UDWORD :2;                        /*              */
                    _UDWORD OPDB:2;                    /*   OPDB       */
                    _UDWORD :2;                        /*              */
                    _UDWORD SPIDB:2;                   /*   SPIDB      */
                    _UDWORD :1;                        /*              */
                    _UDWORD CDE:1;                     /*   CDE        */
                    _UDWORD :1;                        /*              */
                    _UDWORD OCDE:1;                    /*   OCDE       */
                    _UDWORD ADE:4;                     /*   ADE        */
                    _UDWORD OPDE:4;                    /*   OPDE       */
                    _UDWORD SPIDE:4;                   /*   SPIDE      */
                    } BIT;                             /*              */
             } SMENR;                                  /*              */
       _UBYTE wk0[4];                                  /*              */
       union {                                         /* SMRDR0       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Byte Access */
                    _UBYTE HH;                         /*   High, High */
                    _UBYTE HL;                         /*   High, Low  */
                    _UBYTE LH;                         /*   Low, High  */
                    _UBYTE LL;                         /*   Low, Low   */
                    } BYTE;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RDATA0:32;                 /*   RDATA0     */
                    } BIT;                             /*              */
             } SMRDR0;                                 /*              */
       union {                                         /* SMRDR1       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Byte Access */
                    _UBYTE HH;                         /*   High, High */
                    _UBYTE HL;                         /*   High, Low  */
                    _UBYTE LH;                         /*   Low, High  */
                    _UBYTE LL;                         /*   Low, Low   */
                    } BYTE;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD RDATA1:32;                 /*   RDATA1     */
                    } BIT;                             /*              */
             } SMRDR1;                                 /*              */
       union {                                         /* SMWDR0       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Byte Access */
                    _UBYTE HH;                         /*   High, High */
                    _UBYTE HL;                         /*   High, Low  */
                    _UBYTE LH;                         /*   Low, High  */
                    _UBYTE LL;                         /*   Low, Low   */
                    } BYTE;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD WDATA0:32;                 /*   WDATA0     */
                    } BIT;                             /*              */
             } SMWDR0;                                 /*              */
       union {                                         /* SMWDR1       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Word Access */
                    _UWORD H;                          /*   High       */
                    _UWORD L;                          /*   Low        */
                    } WORD;                            /*              */
             struct {                                  /*  Byte Access */
                    _UBYTE HH;                         /*   High, High */
                    _UBYTE HL;                         /*   High, Low  */
                    _UBYTE LH;                         /*   Low, High  */
                    _UBYTE LL;                         /*   Low, Low   */
                    } BYTE;                            /*              */
             struct {                                  /*  Bit Access  */
                    _UDWORD WDATA1:32;                 /*   WDATA1     */
                    } BIT;                             /*              */
             } SMWDR1;                                 /*              */
       union {                                         /* CMNSR        */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :30;                       /*              */
                    _UDWORD SSLF:1;                    /*   SSLF       */
                    _UDWORD TEND:1;                    /*   TEND       */
                    } BIT;                             /*              */
             } CMNSR;                                  /*              */
};                                                     /*              */

	#if	0
#define CPG (*(volatile struct st_cpg *)0xFFFE0010)    /* CPG Address  */
#define INTC (*(volatile struct st_intc *)0xFFFE0800)  /* INTC Address */
	#endif
#define CCNT (*(volatile struct st_ccnt *)0xFFFC1000)  /* CCNT Address */
	#if	0
#define BSC (*(volatile struct st_bsc *)0xFFFC0000)    /* BSC Address  */
#define DMAC (*(volatile struct st_dmac *)0xFFFE1000)  /* DMAC Address */
	#endif
	#if	0
#define MTU2 (*(volatile struct st_mtu2 *)0xFFFE4000)  /* MTU2 Address */
	#endif
#define CMT (*(volatile struct st_cmt *)0xFFFEC000)    /* CMT Address  */
#define WDT (*(volatile union  un_wdt *)0xFFFE0000)    /* WDT Address  */
#define RTC (*(volatile struct st_rtc *)0xFFFE6000)    /* RTC Address  */
	#if	0
#define SCIF0 (*(volatile struct st_scif02346 *)0xE8007000)/* SCIF0 Address */
#define SCIF1 (*(volatile struct st_scif157 *)0xE8007800)/* SCIF1 Address */
#define SCIF2 (*(volatile struct st_scif02346 *)0xE8008000)/* SCIF2 Address */
#define SCIF3 (*(volatile struct st_scif02346 *)0xE8008800)/* SCIF3 Address */
#define SCIF4 (*(volatile struct st_scif02346 *)0xE8009000)/* SCIF4 Address */
#define SCIF5 (*(volatile struct st_scif157 *)0xE8009800)/* SCIF5 Address */
#define SCIF6 (*(volatile struct st_scif02346 *)0xE800A000)/* SCIF6 Address */
#define SCIF7 (*(volatile struct st_scif157 *)0xE800A800)/* SCIF7 Address */
	#endif
#define RSPI0 (*(volatile struct st_rspi *)0xE800E000)  /* RSPI0 Address */
#define RSPI1 (*(volatile struct st_rspi *)0xE800E800)  /* RSPI1 Address */
	#if	0
#define IIC3_0 (*(volatile struct st_iic3 *)0xFFFEE000)/* IIC3_0 Address */
#define IIC3_1 (*(volatile struct st_iic3 *)0xFFFEE400)/* IIC3_1 Address */
#define IIC3_2 (*(volatile struct st_iic3 *)0xFFFEE800)/* IIC3_2 Address */
#define IIC3_3 (*(volatile struct st_iic3 *)0xFFFEEC00)/* IIC3_3 Address */
	#endif
#define SSIF0 (*(volatile struct st_ssif *)0xFFFF0000)/* SSIF0 Address */
#define SSIF1 (*(volatile struct st_ssif *)0xFFFF0800)/* SSIF1 Address */
#define SSIF2 (*(volatile struct st_ssif *)0xFFFF1000)/* SSIF2 Address */
#define SSIF3 (*(volatile struct st_ssif *)0xFFFF1800)/* SSIF3 Address */
#define SSIF4 (*(volatile struct st_ssif *)0xFFFF2000)/* SSIF4 Address */
#define SSIF5 (*(volatile struct st_ssif *)0xFFFF2800)/* SSIF5 Address */
#define SIOF (*(volatile struct st_siof *)0xFFFF4800)  /* SIOF Address */
#define RCAN0 (*(volatile struct st_rcan *)0xFFFE5000) /* RCAN0 Address */
#define RCAN1 (*(volatile struct st_rcan *)0xFFFE5800) /* RCAN1 Address */
#define RCAN2 (*(volatile struct st_rcan *)0xFFFED800) /* RCAN2 Address */
#define IEB (*(volatile struct st_ieb *)0xFFFEF000)    /* IEB Address  */
#define SPDIF (*(volatile struct st_spdif *)0xE8012000)/* SPDIF Address */
#define ROMDEC (*(volatile struct st_romdec *)0xE8005000)/* ROMDEC Address */
	#if 0 /* Old ADC iodefine */
#define ADC (*(volatile struct st_adc *)0xE8005800)    /* ADC Address  */
	#endif/* Old ADC iodefine */
#define FLCTL (*(volatile struct st_flctl *)0xFFFF4000)/* FLCTL Address */
	#if	0
#define USB (*(volatile struct st_usb *)0xE8010000)    /* USB Address  */
	#endif
#define VDC4 (*(volatile struct st_vdc4 *)0xFFFF7400)  /* VDC4 Address */
#define SRC0 (*(volatile struct st_src *)0xFFFE7000)  /* SRC0 Address */
#define SRC1 (*(volatile struct st_src *)0xFFFE7800)  /* SRC1 Address */
#define SRC2 (*(volatile struct st_src *)0xFFFE8000)  /* SRC2 Address */
	#if	0
#define PORT (*(volatile struct st_gpio *)0xFFFE3810)  /* GPIO Address */
	#endif
#define HUDI (*(volatile struct st_hudi *)0xFFFE2000)  /* HUDI Address */
#define PWM (*(volatile struct st_pwm *)0xFFFEF406)    /* PWM Address  */
#define QSPI0 (*(volatile struct st_rqspi *)0xE8033800)  /* RQSPI0 Address */
#define QSPI1 (*(volatile struct st_rqspi *)0xE8034000)  /* RQSPI1 Address */
#define IMRLS (*(volatile struct st_imrls *)0xFFFF3008)/* IMRLS Address */
#define SDG0 (*(volatile struct st_sdg0 *)0xFFFEC800)  /* SDG0 Address */
#define SDG1 (*(volatile struct st_sdg1 *)0xFFFECA00)  /* SDG1 Address */
#define SDG2 (*(volatile struct st_sdg2 *)0xFFFECC00)  /* SDG2 Address */
#define SDG3 (*(volatile struct st_sdg3 *)0xFFFECE00)  /* SDG3 Address */
#define MMC (*(volatile struct st_mmc *)0xE8030800)    /* MMC Address  */
#define DVDEC (*(volatile struct st_dvdec *)0xFFFFA008)/* DVDEC Address */
#define UBC (*(volatile struct st_ubc *)0xFFFC0400)    /* UBC Address  */
#define DISC (*(volatile struct st_disc *)0xFFFFA800)  /* DISC Address */
#define JCU (*(volatile struct st_jcu *)0xE8017000)    /* JCU Address  */
#define SPIBSC (*(volatile struct st_spibsc *)0xFFFC1C00)/* SPIBSC Address */


/* ==== includes each iodefine ==== */
#include "usb_iodefine.h"			/* for USB module */
#include "scif_iodefine.h"			/* for SCIF module */
#include "pfc_iodefine.h"			/* for PFC module */
#include "bsc_iodefine.h"			/* for BSC module */
#include "cpg_iodefine.h"			/* for CPG module */
//#include "dmac_iodefine.h"			/* for DMAC module */
#include "intc_iodefine.h"			/* for INTC module */
#include "ostm_iodefine.h"			/* for OSTM module */
#include "riic_iodefine.h"			/* for RIIC module */
#include "prr_iodefine.h"			/* for 製品バージョンレジスタ */
#include "spibsc_iodefine.h"		/* for SPIBSC module */
#include "mtu2_iodefine.h"			/* for MTU2 module */

#endif /* _IODEFINE_H_ */
