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
* File Name     : cpg_iodefine.h
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
*         : 27.07.2012 0.01		éQçléëóøÅFRZ_A1H_05J_121010_11.pdf
*******************************************************************************/
#ifndef __CPG_IODEFINE_H__
#define __CPG_IODEFINE_H__

#include "typedefine.h"

struct st_cpg {                                 /* struct CPG   */
       union {                                  /* FRQCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD IFC:2;               /*   IFC        */
                    _UWORD :2;                  /*              */
                    _UWORD CKOEN:2;             /*   CKOEN      */
                    _UWORD CKOEN2:1;            /*   CKOEN2     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } FRQCR;                           /*              */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* FRQCR2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD GFC:2;               /*   GFC        */
                    _UWORD :14;                 /*              */
                    } BIT;                      /*              */
             } FRQCR2;                          /*              */
       _UBYTE wk1[2];                           /*              */
       union {                                  /* CPUSTS       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :4;                  /*              */
                    _UBYTE ISBUSY0:1;           /*   ISBUSY0    */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } CPUSTS;                          /*              */
       _UBYTE wk2[7];                           /*              */
       union {                                  /* STBCR1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE DEEP:1;              /*   DEEP       */
                    _UBYTE STBY:1;              /*   STBY       */
                    } BIT;                      /*              */
             } STBCR1;                          /*              */
       _UBYTE wk3[3];                           /*              */
       union {                                  /* STBCR2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP20:1;            /*   MSTP20     */
                    _UBYTE :6;                  /*              */
                    _UBYTE HIZ:1;               /*   HIZ        */
                    } BIT;                      /*              */
             } STBCR2;                          /*              */
       _UBYTE wk4[11];                          /*              */
       union {                                  /* STBREQ1      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE STBRQ10:1;           /*   STBRQ10    */
                    _UBYTE :2;                  /*              */
                    _UBYTE STBRQ13:1;           /*   STBRQ13    */
                    _UBYTE :1;                  /*              */
                    _UBYTE STBRQ15:1;           /*   STBRQ15    */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } STBREQ1;                         /*              */
       _UBYTE wk5[3];                           /*              */
       union {                                  /* STBREQ2      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE STBRQ20:1;           /*   STBRQ20    */
                    _UBYTE STBRQ21:1;           /*   STBRQ21    */
                    _UBYTE STBRQ22:1;           /*   STBRQ22    */
                    _UBYTE STBRQ23:1;           /*   STBRQ23    */
                    _UBYTE STBRQ24:1;           /*   STBRQ24    */
                    _UBYTE STBRQ25:1;           /*   STBRQ25    */
                    _UBYTE STBRQ26:1;           /*   STBRQ26    */
                    _UBYTE STBRQ27:1;           /*   STBRQ27    */
                    } BIT;                      /*              */
             } STBREQ2;                         /*              */
       _UBYTE wk6[11];                          /*              */
       union {                                  /* STBACK1      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE STBAK10:1;           /*   STBAK10    */
                    _UBYTE :2;                  /*              */
                    _UBYTE STBAK13:1;           /*   STBAK13    */
                    _UBYTE :1;                  /*              */
                    _UBYTE STBAK15:1;           /*   STBAK15    */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } STBACK1;                         /*              */
       _UBYTE wk7[3];                           /*              */
       union {                                  /* STBACK2      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE STBAK20:1;           /*   STBAK20    */
                    _UBYTE STBAK21:1;           /*   STBAK21    */
                    _UBYTE STBAK22:1;           /*   STBAK22    */
                    _UBYTE STBAK23:1;           /*   STBAK23    */
                    _UBYTE STBAK24:1;           /*   STBAK24    */
                    _UBYTE STBAK25:1;           /*   STBAK25    */
                    _UBYTE STBAK26:1;           /*   STBAK26    */
                    _UBYTE STBAK27:1;           /*   STBAK27    */
                    } BIT;                      /*              */
             } STBACK2;                         /*              */
       _UBYTE wk8[955];                         /*              */
       union {                                  /* SYSCR1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE VRAME0:1;            /*   VRAME0     */
                    _UBYTE VRAME1:1;            /*   VRAME1     */
                    _UBYTE VRAME2:1;            /*   VRAME2     */
                    _UBYTE VRAME3:1;            /*   VRAME3     */
                    _UBYTE VRAME4:1;            /*   VRAME4     */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } SYSCR1;                          /*              */
       _UBYTE wk9[3];                           /*              */
       union {                                  /* SYSCR2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE VRAMWE0:1;           /*   VRAMWE0    */
                    _UBYTE VRAMWE1:1;           /*   VRAMWE1    */
                    _UBYTE VRAMWE2:1;           /*   VRAMWE2    */
                    _UBYTE VRAMWE3:1;           /*   VRAMWE3    */
                    _UBYTE VRAMWE4:1;           /*   VRAMWE4    */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } SYSCR2;                          /*              */
       _UBYTE wk10[3];                          /*              */
       union {                                  /* SYSCR3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE RRAMWE0:1;           /*   RRAMWE0    */
                    _UBYTE RRAMWE1:1;           /*   RRAMWE1    */
                    _UBYTE RRAMWE2:1;           /*   RRAMWE2    */
                    _UBYTE RRAMWE3:1;           /*   RRAMWE3    */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } SYSCR3;                          /*              */
       _UBYTE wk11[23];                         /*              */
       union {                                  /* STBCR3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP30:1;            /*   MSTP30     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP32:1;            /*   MSTP32     */
                    _UBYTE MSTP33:1;            /*   MSTP33     */
                    _UBYTE MSTP34:1;            /*   MSTP34     */
                    _UBYTE MSTP35:1;            /*   MSTP35     */
                    _UBYTE MSTP36:1;            /*   MSTP36     */
                    _UBYTE MSTP37:1;            /*   MSTP37     */
                    } BIT;                      /*              */
             } STBCR3;                          /*              */
       _UBYTE wk12[3];                          /*              */
       union {                                  /* STBCR4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP40:1;            /*   MSTP40     */
                    _UBYTE MSTP41:1;            /*   MSTP41     */
                    _UBYTE MSTP42:1;            /*   MSTP42     */
                    _UBYTE MSTP43:1;            /*   MSTP43     */
                    _UBYTE MSTP44:1;            /*   MSTP44     */
                    _UBYTE MSTP45:1;            /*   MSTP45     */
                    _UBYTE MSTP46:1;            /*   MSTP46     */
                    _UBYTE MSTP47:1;            /*   MSTP47     */
                    } BIT;                      /*              */
             } STBCR4;                          /*              */
       _UBYTE wk13[3];                          /*              */
       union {                                  /* STBCR5       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP50:1;            /*   MSTP50     */
                    _UBYTE MSTP51:1;            /*   MSTP51     */
                    _UBYTE MSTP52:1;            /*   MSTP52     */
                    _UBYTE MSTP53:1;            /*   MSTP53     */
                    _UBYTE MSTP54:1;            /*   MSTP54     */
                    _UBYTE MSTP55:1;            /*   MSTP55     */
                    _UBYTE MSTP56:1;            /*   MSTP56     */
                    _UBYTE MSTP57:1;            /*   MSTP57     */
                    } BIT;                      /*              */
             } STBCR5;                          /*              */
       _UBYTE wk14[3];                          /*              */
       union {                                  /* STBCR6       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP60:1;            /*   MSTP60     */
                    _UBYTE MSTP61:1;            /*   MSTP61     */
                    _UBYTE MSTP62:1;            /*   MSTP62     */
                    _UBYTE MSTP63:1;            /*   MSTP63     */
                    _UBYTE MSTP64:1;            /*   MSTP64     */
                    _UBYTE MSTP65:1;            /*   MSTP65     */
                    _UBYTE MSTP66:1;            /*   MSTP66     */
                    _UBYTE MSTP67:1;            /*   MSTP67     */
                    } BIT;                      /*              */
             } STBCR6;                          /*              */
       _UBYTE wk15[3];                          /*              */
       union {                                  /* STBCR7       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP70:1;            /*   MSTP70     */
                    _UBYTE MSTP71:1;            /*   MSTP71     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP73:1;            /*   MSTP73     */
                    _UBYTE MSTP74:1;            /*   MSTP74     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP76:1;            /*   MSTP76     */
                    _UBYTE MSTP77:1;            /*   MSTP77     */
                    } BIT;                      /*              */
             } STBCR7;                          /*              */
       _UBYTE wk16[3];                          /*              */
       union {                                  /* STBCR8       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP81:1;            /*   MSTP81     */
                    _UBYTE :1;                  /*              */
                    _UBYTE MSTP83:1;            /*   MSTP83     */
                    _UBYTE MSTP84:1;            /*   MSTP84     */
                    _UBYTE MSTP85:1;            /*   MSTP85     */
                    _UBYTE MSTP86:1;            /*   MSTP86     */
                    _UBYTE MSTP87:1;            /*   MSTP87     */
                    } BIT;                      /*              */
             } STBCR8;                          /*              */
       _UBYTE wk17[3];                          /*              */
       union {                                  /* STBCR9       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP90:1;            /*   MSTP60     */
                    _UBYTE MSTP91:1;            /*   MSTP61     */
                    _UBYTE MSTP92:1;            /*   MSTP62     */
                    _UBYTE MSTP93:1;            /*   MSTP63     */
                    _UBYTE MSTP94:1;            /*   MSTP64     */
                    _UBYTE MSTP95:1;            /*   MSTP65     */
                    _UBYTE MSTP96:1;            /*   MSTP66     */
                    _UBYTE MSTP97:1;            /*   MSTP67     */
                    } BIT;                      /*              */
             } STBCR9;                          /*              */
       _UBYTE wk18[3];                          /*              */
       union {                                  /* STBCR10      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP100:1;           /*   MSTP100    */
                    _UBYTE MSTP101:1;           /*   MSTP101    */
                    _UBYTE MSTP102:1;           /*   MSTP102    */
                    _UBYTE MSTP103:1;           /*   MSTP103    */
                    _UBYTE MSTP104:1;           /*   MSTP104    */
                    _UBYTE MSTP105:1;           /*   MSTP105    */
                    _UBYTE MSTP106:1;           /*   MSTP106    */
                    _UBYTE MSTP107:1;           /*   MSTP107    */
                    } BIT;                      /*              */
             } STBCR10;                         /*              */
       _UBYTE wk19[3];                          /*              */
       union {                                  /* STBCR11      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP110:1;           /*   MSTP110    */
                    _UBYTE MSTP111:1;           /*   MSTP111    */
                    _UBYTE MSTP112:1;           /*   MSTP112    */
                    _UBYTE MSTP113:1;           /*   MSTP113    */
                    _UBYTE MSTP114:1;           /*   MSTP114    */
                    _UBYTE MSTP115:1;           /*   MSTP115    */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } STBCR11;                         /*              */
       _UBYTE wk20[3];                          /*              */
       union {                                  /* STBCR12      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MSTP120:1;           /*   MSTP120    */
                    _UBYTE MSTP121:1;           /*   MSTP121    */
                    _UBYTE MSTP122:1;           /*   MSTP122    */
                    _UBYTE MSTP123:1;           /*   MSTP123    */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } STBCR12;                         /*              */
       _UBYTE wk21[27];                         /*              */
       union {                                  /* SWRSTCR1     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE SRST11:1;            /*   SRST11     */
                    _UBYTE SRST12:1;            /*   SRST12     */
                    _UBYTE SRST13:1;            /*   SRST13     */
                    _UBYTE SRST14:1;            /*   SRST14     */
                    _UBYTE SRST15:1;            /*   SRST15     */
                    _UBYTE SRST16:1;            /*   SRST16     */
                    _UBYTE AXTALE:1;            /*   AXTALE     */
                    } BIT;                      /*              */
             } SWRSTCR1;                        /*              */
       _UBYTE wk22[3];                          /*              */
       union {                                  /* SWRSTCR2     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE SRST21:1;            /*   SRST21     */
                    _UBYTE SRST22:1;            /*   SRST22     */
                    _UBYTE SRST23:1;            /*   SRST23     */
                    _UBYTE SRST24:1;            /*   SRST24     */
                    _UBYTE SRST25:1;            /*   SRST25     */
                    _UBYTE SRST26:1;            /*   SRST26     */
                    _UBYTE SRST27:1;            /*   SRST27     */
                    } BIT;                      /*              */
             } SWRSTCR2;                        /*              */
       _UBYTE wk23[3];                          /*              */
       union {                                  /* SWRSTCR3     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :1;                  /*              */
                    _UBYTE SRST31:1;            /*   SRST31     */
                    _UBYTE SRST32:1;            /*   SRST32     */
                    _UBYTE SRST33:1;            /*   SRST33     */
                    _UBYTE SRST34:1;            /*   SRST34     */
                    _UBYTE SRST35:1;            /*   SRST35     */
                    _UBYTE SRST36:1;            /*   SRST36     */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } SWRSTCR3;                        /*              */
       _UBYTE wk24[3];                          /*              */
       union {                                  /* SWRSTCR4     */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SRST40:1;            /*   SRST40     */
                    _UBYTE SRST41:1;            /*   SRST41     */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } SWRSTCR4;                        /*              */
       _UBYTE wk25[70547];                      /*              */
       union {                                  /* RRAMKP       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE RRAMKP0:1;           /*   RRAMKP0    */
                    _UBYTE RRAMKP1:1;           /*   RRAMKP1    */
                    _UBYTE RRAMKP2:1;           /*   RRAMKP2    */
                    _UBYTE RRAMKP3:1;           /*   RRAMKP3    */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } RRAMKP;                          /*              */
       _UBYTE wk26[1];                          /*              */
       union {                                  /* DSCTR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE :6;                  /*              */
                    _UBYTE RAMBOOT:1;           /*   RAMBOOT    */
                    _UBYTE EBUSKEEPE:1;         /*   EBUSKEEPE  */
                    } BIT;                      /*              */
             } DSCTR;                           /*              */
       _UBYTE wk27[1];                          /*              */
       union {                                  /* DSSSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD P8_2:1;              /*   P8_2       */
                    _UWORD P9_1:1;              /*   P9_1       */
                    _UWORD P2_15:1;             /*   P2_15      */
                    _UWORD P7_8:1;              /*   P7_8       */
                    _UWORD P5_9:1;              /*   P5_9       */
                    _UWORD P6_4:1;              /*   P6_4       */
                    _UWORD RTCAR:1;             /*   RTCAR      */
                    _UWORD :1;                  /*              */
                    _UWORD NMI:1;               /*   NMI        */
                    _UWORD P3_3:1;              /*   P3_3       */
                    _UWORD P8_7:1;              /*   P8_7       */
                    _UWORD P2_12:1;             /*   P2_12      */
                    _UWORD P3_1:1;              /*   P3_1       */
                    _UWORD P3_9:1;              /*   P3_9       */
                    _UWORD P6_2:1;              /*   P6_2       */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DSSSR;                           /*              */
       union {                                  /* DSESR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD P8_2E:1;             /*   P8_2E      */
                    _UWORD P9_1E:1;             /*   P9_1E      */
                    _UWORD P2_15E:1;            /*   P2_15E     */
                    _UWORD P7_8E:1;             /*   P7_8E      */
                    _UWORD P5_9E:1;             /*   P5_9E      */
                    _UWORD P6_4E:1;             /*   P6_4E      */
                    _UWORD :2;                  /*              */
                    _UWORD NMIE:1;              /*   NMIE       */
                    _UWORD P3_3E:1;             /*   P3_3E      */
                    _UWORD P8_7E:1;             /*   P8_7E      */
                    _UWORD P2_12E:1;            /*   P2_12E     */
                    _UWORD P3_1E:1;             /*   P3_1E      */
                    _UWORD P3_9E:1;             /*   P3_9E      */
                    _UWORD P6_2E:1;             /*   P6_2E      */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DSESR;                           /*              */
       union {                                  /* DSFR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD P8_2F:1;             /*   P8_2F      */
                    _UWORD P9_1F:1;             /*   P9_1F      */
                    _UWORD P2_15F:1;            /*   P2_15F     */
                    _UWORD P7_8F:1;             /*   P7_8F      */
                    _UWORD P5_9F:1;             /*   P5_9F      */
                    _UWORD P6_4F:1;             /*   P6_4F      */
                    _UWORD RTCARF:1;            /*   RTCARF     */
                    _UWORD :1;                  /*              */
                    _UWORD NMIF:1;              /*   NMIF       */
                    _UWORD P3_3F:1;             /*   P3_3F      */
                    _UWORD P8_7F:1;             /*   P8_7F      */
                    _UWORD P2_12F:1;            /*   P2_12F     */
                    _UWORD P3_1F:1;             /*   P3_1F      */
                    _UWORD P3_9F:1;             /*   P3_9F      */
                    _UWORD P6_2F:1;             /*   P6_2F      */
                    _UWORD IOKEEP:1;            /*   IOKEEP     */
                    } BIT;                      /*              */
             } DSFR;                            /*              */
       _UBYTE wk28[6];                          /*              */
       union {                                  /* XTALCTR      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE GAIN0:1;             /*   GAIN0      */
                    _UBYTE GAIN1:1;             /*   GAIN1      */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } XTALCTR;                         /*              */
};                                              /*              */

#define CPG (*(volatile struct st_cpg *)0xFCFE0010)    /* CPG Address  */


#endif /* __CPG_IODEFINE_H__ */

/* End of File */
