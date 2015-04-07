/******************************************************************************
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
*   Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
**************************** Technical reference data **************************
*   System Name : 
*   File Name   : usb_iodefine.h
*   Abstract    : 
*   Version     : 1.00.00
*   Device      : ARM
*   Tool-Chain  : 
*   OS          : None
*   H/W Platform: 
*   Description : 
********************************************************************************
*   History     : Mar.06,2012 Ver.1.00.00
*******************************************************************************/
#ifndef __USB_IODEFINE_H__
#define __USB_IODEFINE_H__

#include "typedefine.h"

struct st_usb_n {                               /* struct USB   */
       union {                                  /* SYSCFG       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD USBE:1;              /*   USBE       */
                    _UWORD UPLLE:1;             /*   UPLLE      */
                    _UWORD UCKSEL:1;            /*   UCKSEL     */
                    _UWORD :1;                  /*              */
                    _UWORD DPRPU:1;             /*   DPRPU      */
                    _UWORD DRPD:1;              /*   DRPD       */
                    _UWORD DCFM:1;              /*   DCFM       */
                    _UWORD HSE:1;               /*   HSE        */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } SYSCFG;                          /*              */
       union {                                  /* BUSWAIT      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BWAIT:6;             /*   BWAIT      */
                    _UWORD :10;                 /*              */
                    } BIT;                      /*              */
             } BUSWAIT;                         /*              */
       union {                                  /* SYSSTS0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD LNST:2;              /*   LNST       */
                    _UWORD :14;                 /*              */
                    } BIT;                      /*              */
             } SYSSTS0;                         /*              */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* DVSTCTR0     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD RHST:3;              /*   RHST       */
                    _UWORD :1;                  /*              */
                    _UWORD UACT:1;              /*   UACT       */
                    _UWORD RESUME:1;            /*   RESUME     */
                    _UWORD USBRST:1;            /*   USBRST     */
                    _UWORD RWUPE:1;             /*   RWUPE      */
                    _UWORD WKUP:1;              /*   WKUP       */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DVSTCTR0;                        /*              */
       _UBYTE wk1[2];                           /*              */
       union {                                  /* UTEST        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD UTST:4;              /*   UTST       */
                    _UWORD :12;                 /*              */
                    } BIT;                      /*              */
             } UTEST;                           /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* D0FBCFG      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :4;                  /*              */
                    _UWORD TENDE:1;             /*   TENDE      */
                    _UWORD :7;                  /*              */
                    _UWORD DFACC:2;             /*   DFACC      */
                    _UWORD :2;                  /*              */
                    } BIT;                      /*              */
             } D0FBCFG;                         /*              */
       union {                                  /* D1FBCFG      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :4;                  /*              */
                    _UWORD TENDE:1;             /*   TENDE      */
                    _UWORD :7;                  /*              */
                    _UWORD DFACC:2;             /*   DFACC      */
                    _UWORD :2;                  /*              */
                    } BIT;                      /*              */
             } D1FBCFG;                         /*              */
       union {                                  /* CFIFO        */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD[2];                    /*  Word Access */
             _UBYTE BYTE[4];                    /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } CFIFO;                           /*              */
       union {                                  /* D0FIFO       */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD[2];                    /*  Word Access */
             _UBYTE BYTE[4];                    /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFO;                          /*              */
       union {                                  /* D1FIFO       */
             _UDWORD LONG;                      /*  Long Access */
             _UWORD WORD[2];                    /*  Word Access */
             _UBYTE BYTE[4];                    /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFO;                          /*              */
       union {                                  /* CFIFOSEL     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD CURPIPE:4;           /*   CURPIPE    */
                    _UWORD :1;                  /*              */
                    _UWORD ISEL:1;              /*   ISEL       */
                    _UWORD :2;                  /*              */
                    _UWORD BIGEND:1;            /*   BIGEND     */
                    _UWORD :1;                  /*              */
                    _UWORD MBW:2;               /*   MBW        */
                    _UWORD :2;                  /*              */
                    _UWORD REW:1;               /*   REW        */
                    _UWORD RCNT:1;              /*   RCNT       */
                    } BIT;                      /*              */
             } CFIFOSEL;                        /*              */
       union {                                  /* CFIFOCTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD DTLN:12;             /*   DTLN       */
                    _UWORD :1;                  /*              */
                    _UWORD FRDY:1;              /*   FRDY       */
                    _UWORD BCLR:1;              /*   BCLR       */
                    _UWORD BVAL:1;              /*   BVAL       */
                    } BIT;                      /*              */
             } CFIFOCTR;                        /*              */
       _UBYTE wk3[4];                           /*              */
       union {                                  /* D0FIFOSEL    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD CURPIPE:4;           /*   CURPIPE    */
                    _UWORD :4;                  /*              */
                    _UWORD BIGEND:1;            /*   BIGEND     */
                    _UWORD :1;                  /*              */
                    _UWORD MBW:2;               /*   MBW        */
                    _UWORD DREQE:1;             /*   DREQE      */
                    _UWORD DCLRM:1;             /*   DCLRM      */
                    _UWORD REW:1;               /*   REW        */
                    _UWORD RCNT:1;              /*   RCNT       */
                    } BIT;                      /*              */
             } D0FIFOSEL;                       /*              */
       union {                                  /* D0FIFOCTR    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD DTLN:12;             /*   DTLN       */
                    _UWORD :1;                  /*              */
                    _UWORD FRDY:1;              /*   FRDY       */
                    _UWORD BCLR:1;              /*   BCLR       */
                    _UWORD BVAL:1;              /*   BVAL       */
                    } BIT;                      /*              */
             } D0FIFOCTR;                       /*              */
       union {                                  /* D1FIFOSEL    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD CURPIPE:4;           /*   CURPIPE    */
                    _UWORD :4;                  /*              */
                    _UWORD BIGEND:1;            /*   BIGEND     */
                    _UWORD :1;                  /*              */
                    _UWORD MBW:2;               /*   MBW        */
                    _UWORD DREQE:1;             /*   DREQE      */
                    _UWORD DCLRM:1;             /*   DCLRM      */
                    _UWORD REW:1;               /*   REW        */
                    _UWORD RCNT:1;              /*   RCNT       */
                    } BIT;                      /*              */
             } D1FIFOSEL;                       /*              */
       union {                                  /* D1FIFOCTR    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD DTLN:12;             /*   DTLN       */
                    _UWORD :1;                  /*              */
                    _UWORD FRDY:1;              /*   FRDY       */
                    _UWORD BCLR:1;              /*   BCLR       */
                    _UWORD BVAL:1;              /*   BVAL       */
                    } BIT;                      /*              */
             } D1FIFOCTR;                       /*              */
       union {                                  /* INTENB0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD BRDYE:1;             /*   BRDYE      */
                    _UWORD NRDYE:1;             /*   NRDYE      */
                    _UWORD BEMPE:1;             /*   BEMPE      */
                    _UWORD CTRE:1;              /*   CTRE       */
                    _UWORD DVSE:1;              /*   DVSE       */
                    _UWORD SOFE:1;              /*   SOFE       */
                    _UWORD RSME:1;              /*   RSME       */
                    _UWORD VBSE:1;              /*   VBSE       */
                    } BIT;                      /*              */
             } INTENB0;                         /*              */
       union {                                  /* INTENB1      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :4;                  /*              */
                    _UWORD SACKE:1;             /*   SACKE      */
                    _UWORD SIGNE:1;             /*   SIGNE      */
                    _UWORD EOFERRE:1;           /*   EOFERRE    */
                    _UWORD :4;                  /*              */
                    _UWORD ATTCHE:1;            /*   ATTCHE     */
                    _UWORD DTCHE:1;             /*   DTCHE      */
                    _UWORD :1;                  /*              */
                    _UWORD BCHGE:1;             /*   BCHGE      */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } INTENB1;                         /*              */
       _UBYTE wk4[2];                           /*              */
       union {                                  /* BRDYENB      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPE0BRDYE:1;        /*   PIPE0BRDYE */
                    _UWORD PIPE1BRDYE:1;        /*   PIPE1BRDYE */
                    _UWORD PIPE2BRDYE:1;        /*   PIPE2BRDYE */
                    _UWORD PIPE3BRDYE:1;        /*   PIPE3BRDYE */
                    _UWORD PIPE4BRDYE:1;        /*   PIPE4BRDYE */
                    _UWORD PIPE5BRDYE:1;        /*   PIPE5BRDYE */
                    _UWORD PIPE6BRDYE:1;        /*   PIPE6BRDYE */
                    _UWORD PIPE7BRDYE:1;        /*   PIPE7BRDYE */
                    _UWORD PIPE8BRDYE:1;        /*   PIPE8BRDYE */
                    _UWORD PIPE9BRDYE:1;        /*   PIPE9BRDYE */
                    _UWORD PIPEABRDYE:1;        /*   PIPEABRDYE */
                    _UWORD PIPEBBRDYE:1;        /*   PIPEBBRDYE */
                    _UWORD PIPECBRDYE:1;        /*   PIPECBRDYE */
                    _UWORD PIPEDBRDYE:1;        /*   PIPEDBRDYE */
                    _UWORD PIPEEBRDYE:1;        /*   PIPEEBRDYE */
                    _UWORD PIPEFBRDYE:1;        /*   PIPEFBRDYE */
                    } BIT;                      /*              */
             } BRDYENB;                         /*              */
       union {                                  /* NRDYENB      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPE0NRDYE:1;        /*   PIPE0NRDYE */
                    _UWORD PIPE1NRDYE:1;        /*   PIPE1NRDYE */
                    _UWORD PIPE2NRDYE:1;        /*   PIPE2NRDYE */
                    _UWORD PIPE3NRDYE:1;        /*   PIPE3NRDYE */
                    _UWORD PIPE4NRDYE:1;        /*   PIPE4NRDYE */
                    _UWORD PIPE5NRDYE:1;        /*   PIPE5NRDYE */
                    _UWORD PIPE6NRDYE:1;        /*   PIPE6NRDYE */
                    _UWORD PIPE7NRDYE:1;        /*   PIPE7NRDYE */
                    _UWORD PIPE8NRDYE:1;        /*   PIPE8NRDYE */
                    _UWORD PIPE9NRDYE:1;        /*   PIPE9NRDYE */
                    _UWORD PIPEANRDYE:1;        /*   PIPEANRDYE */
                    _UWORD PIPEBNRDYE:1;        /*   PIPEBNRDYE */
                    _UWORD PIPECNRDYE:1;        /*   PIPECNRDYE */
                    _UWORD PIPEDNRDYE:1;        /*   PIPEDNRDYE */
                    _UWORD PIPEENRDYE:1;        /*   PIPEENRDYE */
                    _UWORD PIPEFNRDYE:1;        /*   PIPEFNRDYE */
                    } BIT;                      /*              */
             } NRDYENB;                         /*              */
       union {                                  /* BEMPENB      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPE0BEMPE:1;        /*   PIPE0BEMPE */
                    _UWORD PIPE1BEMPE:1;        /*   PIPE1BEMPE */
                    _UWORD PIPE2BEMPE:1;        /*   PIPE2BEMPE */
                    _UWORD PIPE3BEMPE:1;        /*   PIPE3BEMPE */
                    _UWORD PIPE4BEMPE:1;        /*   PIPE4BEMPE */
                    _UWORD PIPE5BEMPE:1;        /*   PIPE5BEMPE */
                    _UWORD PIPE6BEMPE:1;        /*   PIPE6BEMPE */
                    _UWORD PIPE7BEMPE:1;        /*   PIPE7BEMPE */
                    _UWORD PIPE8BEMPE:1;        /*   PIPE8BEMPE */
                    _UWORD PIPE9BEMPE:1;        /*   PIPE9BEMPE */
                    _UWORD PIPEABEMPE:1;        /*   PIPEABEMPE */
                    _UWORD PIPEBBEMPE:1;        /*   PIPEBBEMPE */
                    _UWORD PIPECBEMPE:1;        /*   PIPECBEMPE */
                    _UWORD PIPEDBEMPE:1;        /*   PIPEDBEMPE */
                    _UWORD PIPEEBEMPE:1;        /*   PIPEEBEMPE */
                    _UWORD PIPEFBEMPE:1;        /*   PIPEFBEMPE */
                    } BIT;                      /*              */
             } BEMPENB;                         /*              */
       union {                                  /* SOFCFG       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD BRDYM:1;             /*   BRDYM      */
                    _UWORD :1;                  /*              */
                    _UWORD TRNENSEL:1;          /*   TRNENSEL   */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } SOFCFG;                          /*              */
       _UBYTE wk5[2];                           /*              */
       union {                                  /* INTSTS0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD CTSQ:3;              /*   CTSQ       */
                    _UWORD VALID:1;             /*   VALID      */
                    _UWORD DVSQ:3;              /*   DVSQ       */
                    _UWORD VBSTS:1;             /*   VBSTS      */
                    _UWORD BRDY:1;              /*   BRDY       */
                    _UWORD NRDY:1;              /*   NRDY       */
                    _UWORD BEMP:1;              /*   BEMP       */
                    _UWORD CTRT:1;              /*   CTRT       */
                    _UWORD DVST:1;              /*   DVST       */
                    _UWORD SOFR:1;              /*   SOFR       */
                    _UWORD RESM:1;              /*   RESM       */
                    _UWORD VBINT:1;             /*   VBINT      */
                    } BIT;                      /*              */
             } INTSTS0;                         /*              */
       union {                                  /* INTSTS1      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :4;                  /*              */
                    _UWORD SACK:1;              /*   SACK       */
                    _UWORD SIGN:1;              /*   SIGN       */
                    _UWORD EOFERR:1;            /*   EOFERR     */
                    _UWORD :4;                  /*              */
                    _UWORD ATTCH:1;             /*   ATTCH      */
                    _UWORD DTCH:1;              /*   DTCH       */
                    _UWORD :1;                  /*              */
                    _UWORD BCHG:1;              /*   BCHG       */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } INTSTS1;                         /*              */
       _UBYTE wk6[2];                           /*              */
       union {                                  /* BRDYSTS      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPE0BRDY:1;         /*   PIPE0BRDY  */
                    _UWORD PIPE1BRDY:1;         /*   PIPE1BRDY  */
                    _UWORD PIPE2BRDY:1;         /*   PIPE2BRDY  */
                    _UWORD PIPE3BRDY:1;         /*   PIPE3BRDY  */
                    _UWORD PIPE4BRDY:1;         /*   PIPE4BRDY  */
                    _UWORD PIPE5BRDY:1;         /*   PIPE5BRDY  */
                    _UWORD PIPE6BRDY:1;         /*   PIPE6BRDY  */
                    _UWORD PIPE7BRDY:1;         /*   PIPE7BRDY  */
                    _UWORD PIPE8BRDY:1;         /*   PIPE8BRDY  */
                    _UWORD PIPE9BRDY:1;         /*   PIPE9BRDY  */
                    _UWORD PIPEABRDY:1;         /*   PIPEABRDY  */
                    _UWORD PIPEBBRDY:1;         /*   PIPEBBRDY  */
                    _UWORD PIPECBRDY:1;         /*   PIPECBRDY  */
                    _UWORD PIPEDBRDY:1;         /*   PIPEDBRDY  */
                    _UWORD PIPEEBRDY:1;         /*   PIPEEBRDY  */
                    _UWORD PIPEFBRDY:1;         /*   PIPEFBRDY  */
                    } BIT;                      /*              */
             } BRDYSTS;                         /*              */
       union {                                  /* NRDYSTS      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPE0NRDY:1;         /*   PIPE0NRDY  */
                    _UWORD PIPE1NRDY:1;         /*   PIPE1NRDY  */
                    _UWORD PIPE2NRDY:1;         /*   PIPE2NRDY  */
                    _UWORD PIPE3NRDY:1;         /*   PIPE3NRDY  */
                    _UWORD PIPE4NRDY:1;         /*   PIPE4NRDY  */
                    _UWORD PIPE5NRDY:1;         /*   PIPE5NRDY  */
                    _UWORD PIPE6NRDY:1;         /*   PIPE6NRDY  */
                    _UWORD PIPE7NRDY:1;         /*   PIPE7NRDY  */
                    _UWORD PIPE8NRDY:1;         /*   PIPE8NRDY  */
                    _UWORD PIPE9NRDY:1;         /*   PIPE9NRDY  */
                    _UWORD PIPEANRDY:1;         /*   PIPEANRDY  */
                    _UWORD PIPEBNRDY:1;         /*   PIPEBNRDY  */
                    _UWORD PIPECNRDY:1;         /*   PIPECNRDY  */
                    _UWORD PIPEDNRDY:1;         /*   PIPEDNRDY  */
                    _UWORD PIPEENRDY:1;         /*   PIPEENRDY  */
                    _UWORD PIPEFNRDY:1;         /*   PIPEFNRDY  */
                    } BIT;                      /*              */
             } NRDYSTS;                         /*              */
       union {                                  /* BEMPSTS      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPE0BEMP:1;         /*   PIPE0BEMP  */
                    _UWORD PIPE1BEMP:1;         /*   PIPE1BEMP  */
                    _UWORD PIPE2BEMP:1;         /*   PIPE2BEMP  */
                    _UWORD PIPE3BEMP:1;         /*   PIPE3BEMP  */
                    _UWORD PIPE4BEMP:1;         /*   PIPE4BEMP  */
                    _UWORD PIPE5BEMP:1;         /*   PIPE5BEMP  */
                    _UWORD PIPE6BEMP:1;         /*   PIPE6BEMP  */
                    _UWORD PIPE7BEMP:1;         /*   PIPE7BEMP  */
                    _UWORD PIPE8BEMP:1;         /*   PIPE8BEMP  */
                    _UWORD PIPE9BEMP:1;         /*   PIPE9BEMP  */
                    _UWORD PIPEABEMP:1;         /*   PIPEABEMP  */
                    _UWORD PIPEBBEMP:1;         /*   PIPEBBEMP  */
                    _UWORD PIPECBEMP:1;         /*   PIPECBEMP  */
                    _UWORD PIPEDBEMP:1;         /*   PIPEDBEMP  */
                    _UWORD PIPEEBEMP:1;         /*   PIPEEBEMP  */
                    _UWORD PIPEFBEMP:1;         /*   PIPEFBEMP  */
                    } BIT;                      /*              */
             } BEMPSTS;                         /*              */
       union {                                  /* FRMNUM       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD FRNM:11;             /*   FRNM       */
                    _UWORD :3;                  /*              */
                    _UWORD CRCE:1;              /*   CRCE       */
                    _UWORD OVRN:1;              /*   OVRN       */
                    } BIT;                      /*              */
             } FRMNUM;                          /*              */
       union {                                  /* UFRMNUM      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD UFRNM:3;             /*   UFRNM      */
                    _UWORD :13;                 /*              */
                    } BIT;                      /*              */
             } UFRMNUM;                         /*              */
       union {                                  /* USBADDR      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD USBADDR:7;           /*   USBADDR    */
                    _UWORD :9;                  /*              */
                    } BIT;                      /*              */
             } USBADDR;                         /*              */
       _UBYTE wk7[2];                           /*              */
       union {                                  /* USBREQ       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BMREQUESTTYPE:8;     /*   BMREQUESTTYPE */
                    _UWORD BREQUEST:8;          /*   BREQUEST   */
                    } BIT;                      /*              */
             } USBREQ;                          /*              */
       _UWORD USBVAL;                           /* USBVAL       */
       _UWORD USBINDX;                          /* USBINDX      */
       _UWORD USBLENG;                          /* USBLENG      */
       union {                                  /* DCPCFG       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :4;                  /*              */
                    _UWORD DIR:1;               /*   DIR        */
                    _UWORD :11;                 /*              */
                    } BIT;                      /*              */
             } DCPCFG;                          /*              */
       union {                                  /* DCPMAXP      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD MXPS:7;              /*   MXPS       */
                    _UWORD :5;                  /*              */
                    _UWORD DEVSEL:4;            /*   DEVSEL     */
                    } BIT;                      /*              */
             } DCPMAXP;                         /*              */
       union {                                  /* DCPCTR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD CCPL:1;              /*   CCPL       */
                    _UWORD :1;                  /*              */
                    _UWORD PINGE:1;             /*   PINGE      */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD :2;                  /*              */
                    _UWORD SUREQCLR:1;          /*   SUREQCLR   */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD SUREQ:1;             /*   SUREQ      */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } DCPCTR;                          /*              */
       _UBYTE wk8[2];                           /*              */
       union {                                  /* PIPESEL      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPESEL:4;           /*   PIPESEL    */
                    _UWORD :12;                 /*              */
                    } BIT;                      /*              */
             } PIPESEL;                         /*              */
       _UBYTE wk9[2];                           /*              */
       union {                                  /* PIPECFG      */
             _UWORD WORD;                       /*  Word Access */
              struct {                          /*  Bit Access  */
                    _UWORD EPNUM:4;             /*   EPNUM      */
                    _UWORD DIR:1;               /*   DIR        */
                    _UWORD :2;                  /*              */
                    _UWORD SHTNAK:1;            /*   SHTNAK     */
                    _UWORD CNTMD:1;             /*   CNTMD      */
                    _UWORD DBLB:1;              /*   DBLB       */
                    _UWORD BFRE:1;              /*   BFRE       */
                    _UWORD :3;                  /*              */
                    _UWORD TYPE:2;              /*   TYPE       */
                    } BIT;                      /*              */
             } PIPECFG;                         /*              */
       union {                                  /* PIPEBUF      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD BUFNMB:8;            /*   BUFNMB     */
                    _UWORD :2;                  /*              */
                    _UWORD BUFSIZE:5;           /*   BUFSIZE    */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } PIPEBUF;                         /*              */
       union {                                  /* PIPEMAXP     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD MXPS:11;             /*   MXPS       */
                    _UWORD :1;                  /*              */
                    _UWORD DEVSEL:4;            /*   DEVSEL     */
                    } BIT;                      /*              */
             } PIPEMAXP;                        /*              */
       union {                                  /* PIPEPERI     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD IITV:3;              /*   IITV       */
                    _UWORD :9;                  /*              */
                    _UWORD IFIS:1;              /*   IFIS       */
                    _UWORD :3;                  /*              */
                    } BIT;                      /*              */
             } PIPEPERI;                        /*              */
       union {                                  /* PIPE1CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :1;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE1CTR;                        /*              */
       union {                                  /* PIPE2CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :1;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE2CTR;                        /*              */
       union {                                  /* PIPE3CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :1;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE3CTR;                        /*              */
       union {                                  /* PIPE4CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :1;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE4CTR;                        /*              */
       union {                                  /* PIPE5CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :1;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE5CTR;                        /*              */
       union {                                  /* PIPE6CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD :2;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD :1;                  /*              */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE6CTR;                        /*              */
       union {                                  /* PIPE7CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD :2;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD :1;                  /*              */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE7CTR;                        /*              */
       union {                                  /* PIPE8CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD :2;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD :1;                  /*              */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE8CTR;                        /*              */
       union {                                  /* PIPE9CTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :1;                  /*              */
                    _UWORD CSSTS:1;             /*   CSSTS      */
                    _UWORD CSCLR:1;             /*   CSCLR      */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPE9CTR;                        /*              */
       union {                                  /* PIPEACTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :3;                  /*              */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPEACTR;                        /*              */
       union {                                  /* PIPEBCTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :3;                  /*              */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPEBCTR;                        /*              */
       union {                                  /* PIPECCTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :3;                  /*              */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPECCTR;                        /*              */
       union {                                  /* PIPEDCTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :3;                  /*              */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPEDCTR;                        /*              */
       union {                                  /* PIPEECTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :3;                  /*              */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPEECTR;                        /*              */
       union {                                  /* PIPEFCTR     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PID:2;               /*   PID        */
                    _UWORD :3;                  /*              */
                    _UWORD PBUSY:1;             /*   PBUSY      */
                    _UWORD SQMON:1;             /*   SQMON      */
                    _UWORD SQSET:1;             /*   SQSET      */
                    _UWORD SQCLR:1;             /*   SQCLR      */
                    _UWORD ACLRM:1;             /*   ACLRM      */
                    _UWORD ATREPM:1;            /*   ATREPM     */
                    _UWORD :3;                  /*              */
                    _UWORD INBUFM:1;            /*   INBUFM     */
                    _UWORD BSTS:1;              /*   BSTS       */
                    } BIT;                      /*              */
             } PIPEFCTR;                        /*              */
       _UBYTE wk10[2];                          /*              */
       union {                                  /* PIPE1TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPE1TRE;                        /*              */
       _UWORD PIPE1TRN;                         /* PIPE1TRN     */
       union {                                  /* PIPE2TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPE2TRE;                        /*              */
       _UWORD PIPE2TRN;                         /* PIPE2TRN     */
       union {                                  /* PIPE3TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPE3TRE;                        /*              */
       _UWORD PIPE3TRN;                         /* PIPE3TRN     */
       union {                                  /* PIPE4TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPE4TRE;                        /*              */
       _UWORD PIPE4TRN;                         /* PIPE4TRN     */
       union {                                  /* PIPE5TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPE5TRE;                        /*              */
       _UWORD PIPE5TRN;                         /* PIPE5TRN     */
       union {                                  /* PIPEBTRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPEBTRE;                        /*              */
       _UWORD PIPEBTRN;                         /* PIPEBTRN     */
       union {                                  /* PIPECTRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPECTRE;                        /*              */
       _UWORD PIPECTRN;                         /* PIPECTRN     */
       union {                                  /* PIPEDTRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPEDTRE;                        /*              */
       _UWORD PIPEDTRN;                         /* PIPEDTRN     */
       union {                                  /* PIPEETRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPEETRE;                        /*              */
       _UWORD PIPEETRN;                         /* PIPEETRN     */
       union {                                  /* PIPEFTRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPEFTRE;                        /*              */
       _UWORD PIPEFTRN;                         /* PIPEFTRN     */
       union {                                  /* PIPE9TRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPE9TRE;                        /*              */
       _UWORD PIPE9TRN;                         /* PIPE9TRN     */
       union {                                  /* PIPEATRE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :8;                  /*              */
                    _UWORD TRCLR:1;             /*   TRCLR      */
                    _UWORD TRENB:1;             /*   TRENB      */
                    _UWORD :6;                  /*              */
                    } BIT;                      /*              */
             } PIPEATRE;                        /*              */
       _UWORD PIPEATRN;                         /* PIPEATRN     */
       _UBYTE wk11[16];                         /*              */
       union {                                  /* DEVADD0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD0;                         /*              */
       union {                                  /* DEVADD1      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD1;                         /*              */
       union {                                  /* DEVADD2      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD2;                         /*              */
       union {                                  /* DEVADD3      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD3;                         /*              */
       union {                                  /* DEVADD4      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD4;                         /*              */
       union {                                  /* DEVADD5      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD5;                         /*              */
       union {                                  /* DEVADD6      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD6;                         /*              */
       union {                                  /* DEVADD7      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD7;                         /*              */
       union {                                  /* DEVADD8      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD8;                         /*              */
       union {                                  /* DEVADD9      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADD9;                         /*              */
       union {                                  /* DEVADDA      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :6;                  /*              */
                    _UWORD USBSPD:2;            /*   USBSPD     */
                    _UWORD HUBPORT:3;           /*   HUBPORT    */
                    _UWORD UPPHUB:4;            /*   UPPHUB     */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } DEVADDA;                         /*              */
       _UBYTE wk12[28];                         /*              */
       union {                                  /* SUSPMODE     */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD :14;                 /*              */
                    _UWORD SUSPM:1;             /*   SUSPM      */
                    _UWORD :1;                  /*              */
                    } BIT;                      /*              */
             } SUSPMODE;                        /*              */
       _UBYTE wk13[92];                         /*              */
       union {                                  /* D0FIFOB0     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB0;                        /*              */
       union {                                  /* D0FIFOB1     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB1;                        /*              */
       union {                                  /* D0FIFOB2     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB2;                        /*              */
       union {                                  /* D0FIFOB3     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB3;                        /*              */
       union {                                  /* D0FIFOB4     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB4;                        /*              */
       union {                                  /* D0FIFOB5     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB5;                        /*              */
       union {                                  /* D0FIFOB6     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB6;                        /*              */
       union {                                  /* D0FIFOB7     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D0FIFOB7;                        /*              */
       union {                                  /* D1FIFOB0     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB0;                        /*              */
       union {                                  /* D1FIFOB1     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB1;                        /*              */
       union {                                  /* D1FIFOB2     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB2;                        /*              */
       union {                                  /* D1FIFOB3     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB3;                        /*              */
       union {                                  /* D1FIFOB4     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB4;                        /*              */
       union {                                  /* D1FIFOB5     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB5;                        /*              */
       union {                                  /* D1FIFOB6     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB6;                        /*              */
       union {                                  /* D1FIFOB7     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD FIFOPORT:32;        /*   FIFOPORT   */
                    } BIT;                      /*              */
             } D1FIFOB7;                        /*              */
};                                              /*              */

#define USB0 (*(volatile struct st_usb_n *)0xE8010000)    /* USB0 Address  */
#define USB1 (*(volatile struct st_usb_n *)0xE8207000)    /* USB1 Address  */


#endif /* __USB_IODEFINE_H__ */

/* End of File */
