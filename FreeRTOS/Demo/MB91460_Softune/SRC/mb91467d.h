/*  FR IO-MAP HEADER FILE      */
/*  =====================      */
/* CREATED BY IO-WIZARD V2.27    */
/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU     */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR     */
/* ELIGIBILITY FOR ANY PURPOSES.                                                 */
/*                 (C) Fujitsu Microelectronics Europe GmbH                      */
/*  */
/* ************************************************************************* */
/*                   Fujitsu Microelectronics Europe GmbH                        */
/*                 http://emea.fujitsu.com/microelectronics  */
/*                                                                           */
/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES                                              */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/* ************************************************************************* */
/* ---------------------------------------------------------------------- */
/* $Id: mb91467D.h,v 1.13 2007/08/08 10:56:26 mwilla Exp $ */
/* ---------------------------------------------------------------------- */
/*                      */
/* Id: mb91467D.iow,v 1.1 2005/10/14 11:25:42 umarke Exp  */
/*      - Initial Version based on mb91V460A, v1.1 */
/* Id: mb91467D.iow,v 1.2 2005/10/14 09:47:18 umarke Exp   */
/*      - Littel Endian IFxDTA_SWP_yz added     */
/* Id: mb91467D.iow,v 1.3 2005/11/18 06:55:29 umarke Exp   */
/*      - No. of port register reduced to the no. of registers in MB91467D */
/*      - Registers added: FMWT2, FMCR */
/*      - Addapted Bit Names of Register FMCS     */
/* Id: mb91467D.iow,v 1.4 2005/11/18 06:55:29 umarke Exp   */
/*      - OCS01 and OCS23 added         */
/* Id: mb91467D.iow,v 1.6 2006/01/13 08:58:51 umarke Exp  */
/*      - Bitnames of  CLKR changed                                                    */
/* Id: mb91467D.iow,v 1.7 2006/01/26 15:42:05 umarke Exp   */
/*      - REGSEL, BRPERx added */
/*      - REGCTR added   */
/*      - LVSEL added  */
/*      - Old Bitname of CLKR added                             */
/* Id: mb91467D.iow,v 1.8 2006/02/27 10:31:28 umarke Exp   */
/*      - BGR10x und BGR00x added  */
/*      - PCNx, ITBAx, ITMKx, IDARx_D7 added    */
/*      - SGCRH, SGCRL added */
/*      - Bit ACSR_MD added */
/*      - Bit CSCFG_PLLLOCK and CSCFG_RCSEL          */
/*      - CUCR: Bits shifted to correct position    */
/*      - CUTR1 & CUTR2 bits renamed to TDR14 instead of TR14     */
/*      - CMCR_RUN renamed to CMCR_FMODRUN and shifted               */
/*      - Bitnames of OSCCx and OSCRx added */
/*      - FSVx, BSVx and FSCRx added */
/*      - RBSYNC, CBSYNCx  */
/* Id: mb91467D.iow,v 1.9 2006/02/27 11:56:23 umarke Exp  */
/*      - changed Adress of REGSEL */
/* $Id: mb91467D.h,v 1.13 2007/08/08 10:56:26 mwilla Exp $  */
/*      - Grouped CANPRE_CPCKS */
/*      - Bitdescription of HLRC added */

/* ASSEMBLER DEFINITIONS : */

#ifdef  __IO_DEFINE
#define __IO_EXTERN
#else
#define __IO_EXTERN	extern volatile
#endif
#ifdef __IO_DEFINE
#pragma asm
 .GLOBAL _pdr00,    _pdr01,    _pdr02,    _pdr03,    _pdr04,    _pdr05
 .GLOBAL _pdr06,    _pdr07,    _pdr08,    _pdr09,    _pdr10,    _pdr13
 .GLOBAL _pdr14,    _pdr15,    _pdr16,    _pdr17,    _pdr18,    _pdr19
 .GLOBAL _pdr20,    _pdr22,    _pdr23,    _pdr24,    _pdr25,    _pdr26
 .GLOBAL _pdr27,    _pdr29,    _eirr0,    _enir0,    _elvr0,    _eirr1
 .GLOBAL _enir1,    _elvr1,    _dicr,     _hrcl,     _rbsync,   _scr02
 .GLOBAL _smr02,    _ssr02,    _rdr02,    _tdr02,    _escr02,   _eccr02
 .GLOBAL _scr04,    _smr04,    _ssr04,    _rdr04,    _tdr04,    _escr04
 .GLOBAL _eccr04,   _fsr04,    _fcr04,    _scr05,    _smr05,    _ssr05
 .GLOBAL _rdr05,    _tdr05,    _escr05,   _eccr05,   _fsr05,    _fcr05
 .GLOBAL _scr06,    _smr06,    _ssr06,    _rdr06,    _tdr06,    _escr06
 .GLOBAL _eccr06,   _fsr06,    _fcr06,    _scr07,    _smr07,    _ssr07
 .GLOBAL _rdr07,    _tdr07,    _escr07,   _eccr07,   _fsr07,    _fcr07
 .GLOBAL _bgr02,    _bgr102,   _bgr002,   _bgr04,    _bgr104,   _bgr004
 .GLOBAL _bgr05,    _bgr105,   _bgr005,   _bgr06,    _bgr106,   _bgr006
 .GLOBAL _bgr07,    _bgr107,   _bgr007,   _pwc20,    _pwc10,    _pws20
 .GLOBAL _pws10,    _pwc21,    _pwc11,    _pws21,    _pws11,    _pwc22
 .GLOBAL _pwc12,    _pws22,    _pws12,    _pwc23,    _pwc13,    _pws23
 .GLOBAL _pws13,    _pwc24,    _pwc14,    _pws24,    _pws14,    _pwc25
 .GLOBAL _pwc15,    _pws25,    _pws15,    _pwc0,     _pwc1,     _pwc2
 .GLOBAL _pwc3,     _pwc4,     _pwc5,     _ibcr0,    _ibsr0,    _itba0
 .GLOBAL _itbah0,   _itbal0,   _itmk0,    _itmkh0,   _itmkl0,   _ismk0
 .GLOBAL _isba0,    _idar0,    _iccr0,    _gcn11,    _gcn21,    _gcn12
 .GLOBAL _gcn22,    _ptmr04,   _pcsr04,   _pdut04,   _pcn04,    _pcnh04
 .GLOBAL _pcnl04,   _ptmr05,   _pcsr05,   _pdut05,   _pcn05,    _pcnh05
 .GLOBAL _pcnl05,   _ptmr06,   _pcsr06,   _pdut06,   _pcn06,    _pcnh06
 .GLOBAL _pcnl06,   _ptmr07,   _pcsr07,   _pdut07,   _pcn07,    _pcnh07
 .GLOBAL _pcnl07,   _ptmr08,   _pcsr08,   _pdut08,   _pcn08,    _pcnh08
 .GLOBAL _pcnl08,   _ptmr09,   _pcsr09,   _pdut09,   _pcn09,    _pcnh09
 .GLOBAL _pcnl09,   _ptmr10,   _pcsr10,   _pdut10,   _pcn10,    _pcnh10
 .GLOBAL _pcnl10,   _ptmr11,   _pcsr11,   _pdut11,   _pcn11,    _pcnh11
 .GLOBAL _pcnl11,   _p0tmcsr,  _p0tmcsrh, _p0tmcsrl, _p1tmcsr,  _p1tmcsrh
 .GLOBAL _p1tmcsrl, _p0tmrlr,  _p0tmr,    _p1tmrlr,  _p1tmr,    _ics01
 .GLOBAL _ics23,    _ipcp0,    _ipcp1,    _ipcp2,    _ipcp3,    _ocs01
 .GLOBAL _ocs23,    _occp0,    _occp1,    _occp2,    _occp3,    _sgcr
 .GLOBAL _sgcrh,    _sgcrl,    _sgfr,     _sgar,     _sgtr,     _sgdr
 .GLOBAL _aderh,    _aderl,    _ader,     _adcs1,    _adcs0,    _adcs
 .GLOBAL _adcr1,    _adcr0,    _adcr,     _adct1,    _adct0,    _adct
 .GLOBAL _adsch,    _adech,    _acsr0,    _tmrlr0,   _tmr0,     _tmcsr0
 .GLOBAL _tmcsrh0,  _tmcsrl0,  _tmrlr1,   _tmr1,     _tmcsr1,   _tmcsrh1
 .GLOBAL _tmcsrl1,  _tmrlr2,   _tmr2,     _tmcsr2,   _tmcsrh2,  _tmcsrl2
 .GLOBAL _tmrlr3,   _tmr3,     _tmcsr3,   _tmcsrh3,  _tmcsrl3,  _tmrlr4
 .GLOBAL _tmr4,     _tmcsr4,   _tmcsrh4,  _tmcsrl4,  _tmrlr5,   _tmr5
 .GLOBAL _tmcsr5,   _tmcsrh5,  _tmcsrl5,  _tmrlr6,   _tmr6,     _tmcsr6
 .GLOBAL _tmcsrh6,  _tmcsrl6,  _tmrlr7,   _tmr7,     _tmcsr7,   _tmcsrh7
 .GLOBAL _tmcsrl7,  _tcdt0,    _tccs0,    _tcdt1,    _tccs1,    _tcdt2
 .GLOBAL _tccs2,    _tcdt3,    _tccs3,    _dmaca0,   _dmacb0,   _dmaca1
 .GLOBAL _dmacb1,   _dmaca2,   _dmacb2,   _dmaca3,   _dmacb3,   _dmaca4
 .GLOBAL _dmacb4,   _dmacr,    _ics45,    _ics67,    _ipcp4,    _ipcp5
 .GLOBAL _ipcp6,    _ipcp7,    _tcdt4,    _tccs4,    _tcdt5,    _tccs5
 .GLOBAL _tcdt6,    _tccs6,    _tcdt7,    _tccs7,    _udrc10,   _udrc1
 .GLOBAL _udrc0,    _udcr10,   _udcr1,    _udcr0,    _udcc0,    _udcch0
 .GLOBAL _udccl0,   _udcs0,    _udcc1,    _udcch1,   _udccl1,   _udcs1
 .GLOBAL _udrc32,   _udrc3,    _udrc2,    _udcr32,   _udcr3,    _udcr2
 .GLOBAL _udcc2,    _udcch2,   _udccl2,   _udcs2,    _udcc3,    _udcch3
 .GLOBAL _udccl3,   _udcs3,    _gcn13,    _gcn23,    _ptmr12,   _pcsr12
 .GLOBAL _pdut12,   _pcn12,    _pcnh12,   _pcnl12,   _ptmr13,   _pcsr13
 .GLOBAL _pdut13,   _pcn13,    _pcnh13,   _pcnl13,   _ptmr14,   _pcsr14
 .GLOBAL _pdut14,   _pcn14,    _pcnh14,   _pcnl14,   _ptmr15,   _pcsr15
 .GLOBAL _pdut15,   _pcn15,    _pcnh15,   _pcnl15,   _ibcr2,    _ibsr2
 .GLOBAL _itba2,    _itbah2,   _itbal2,   _itmk2,    _itmkh2,   _itmkl2
 .GLOBAL _ismk2,    _isba2,    _idar2,    _iccr2,    _ibcr3,    _ibsr3
 .GLOBAL _itba3,    _itbah3,   _itbal3,   _itmk3,    _itmkh3,   _itmkl3
 .GLOBAL _ismk3,    _isba3,    _idar3,    _iccr3,    _roms,     _bsd0
 .GLOBAL _bsd1,     _bsdc,     _bsrr,     _icr00,    _icr01,    _icr02
 .GLOBAL _icr03,    _icr04,    _icr05,    _icr06,    _icr07,    _icr08
 .GLOBAL _icr09,    _icr10,    _icr11,    _icr12,    _icr13,    _icr14
 .GLOBAL _icr15,    _icr16,    _icr17,    _icr18,    _icr19,    _icr20
 .GLOBAL _icr21,    _icr22,    _icr23,    _icr24,    _icr25,    _icr26
 .GLOBAL _icr27,    _icr28,    _icr29,    _icr30,    _icr31,    _icr32
 .GLOBAL _icr33,    _icr34,    _icr35,    _icr36,    _icr37,    _icr38
 .GLOBAL _icr39,    _icr40,    _icr41,    _icr42,    _icr43,    _icr44
 .GLOBAL _icr45,    _icr46,    _icr47,    _icr48,    _icr49,    _icr50
 .GLOBAL _icr51,    _icr52,    _icr53,    _icr54,    _icr55,    _icr56
 .GLOBAL _icr57,    _icr58,    _icr59,    _icr60,    _icr61,    _icr62
 .GLOBAL _icr63,    _rsrr,     _stcr,     _tbcr,     _ctbr,     _clkr
 .GLOBAL _wpr,      _divr0,    _divr1,    _plldivm,  _plldivn,  _plldivg
 .GLOBAL _pllmulg,  _pllctrl,  _oscc1,    _oscs1,    _oscc2,    _oscs2
 .GLOBAL _porten,   _wtcer,    _wtcr,     _wtbr,     _wthr,     _wtmr
 .GLOBAL _wtsr,     _csvtr,    _csvcr,    _cscfg,    _cmcfg,    _cucr
 .GLOBAL _cutd,     _cutr1,    _cutr2,    _cmpr,     _cmcr,     _cmt1
 .GLOBAL _cmt2,     _canpre,   _canckd,   _lvsel,    _lvdet,    _hwwde
 .GLOBAL _hwwd,     _oscrh,    _oscrl,    _wpcrh,    _wpcrl,    _osccr
 .GLOBAL _regsel,   _regctr,   _asr0,     _acr0,     _asr1,     _acr1
 .GLOBAL _asr2,     _acr2,     _asr3,     _acr3,     _asr4,     _acr4
 .GLOBAL _asr5,     _acr5,     _asr6,     _acr6,     _asr7,     _acr7
 .GLOBAL _awr0,     _awr1,     _awr2,     _awr3,     _awr4,     _awr5
 .GLOBAL _awr6,     _awr7,     _mcra,     _mcrb,     _iowr0,    _iowr1
 .GLOBAL _iowr2,    _iowr3,    _cser,     _cher,     _tcr,      _rcr
 .GLOBAL _modr,     _pdrd00,   _pdrd01,   _pdrd02,   _pdrd03,   _pdrd04
 .GLOBAL _pdrd05,   _pdrd06,   _pdrd07,   _pdrd08,   _pdrd09,   _pdrd10
 .GLOBAL _pdrd13,   _pdrd14,   _pdrd15,   _pdrd16,   _pdrd17,   _pdrd18
 .GLOBAL _pdrd19,   _pdrd20,   _pdrd22,   _pdrd23,   _pdrd24,   _pdrd25
 .GLOBAL _pdrd26,   _pdrd27,   _pdrd29,   _ddr00,    _ddr01,    _ddr02
 .GLOBAL _ddr03,    _ddr04,    _ddr05,    _ddr06,    _ddr07,    _ddr08
 .GLOBAL _ddr09,    _ddr10,    _ddr13,    _ddr14,    _ddr15,    _ddr16
 .GLOBAL _ddr17,    _ddr18,    _ddr19,    _ddr20,    _ddr22,    _ddr23
 .GLOBAL _ddr24,    _ddr25,    _ddr26,    _ddr27,    _ddr29,    _pfr00
 .GLOBAL _pfr01,    _pfr02,    _pfr03,    _pfr04,    _pfr05,    _pfr06
 .GLOBAL _pfr07,    _pfr08,    _pfr09,    _pfr10,    _pfr13,    _pfr14
 .GLOBAL _pfr15,    _pfr16,    _pfr17,    _pfr18,    _pfr19,    _pfr20
 .GLOBAL _pfr22,    _pfr23,    _pfr24,    _pfr25,    _pfr26,    _pfr27
 .GLOBAL _pfr29,    _epfr10,   _epfr13,   _epfr14,   _epfr15,   _epfr16
 .GLOBAL _epfr18,   _epfr19,   _epfr20,   _epfr26,   _epfr27,   _podr00
 .GLOBAL _podr01,   _podr02,   _podr03,   _podr04,   _podr05,   _podr06
 .GLOBAL _podr07,   _podr08,   _podr09,   _podr10,   _podr13,   _podr14
 .GLOBAL _podr15,   _podr16,   _podr17,   _podr18,   _podr19,   _podr20
 .GLOBAL _podr22,   _podr23,   _podr24,   _podr25,   _podr26,   _podr27
 .GLOBAL _podr29,   _pilr00,   _pilr01,   _pilr02,   _pilr03,   _pilr04
 .GLOBAL _pilr05,   _pilr06,   _pilr07,   _pilr08,   _pilr09,   _pilr10
 .GLOBAL _pilr13,   _pilr14,   _pilr15,   _pilr16,   _pilr17,   _pilr18
 .GLOBAL _pilr19,   _pilr20,   _pilr22,   _pilr23,   _pilr24,   _pilr25
 .GLOBAL _pilr26,   _pilr27,   _pilr29,   _epilr00,  _epilr01,  _epilr02
 .GLOBAL _epilr03,  _epilr04,  _epilr05,  _epilr06,  _epilr07,  _epilr08
 .GLOBAL _epilr09,  _epilr10,  _epilr13,  _epilr14,  _epilr15,  _epilr16
 .GLOBAL _epilr17,  _epilr18,  _epilr19,  _epilr20,  _epilr22,  _epilr23
 .GLOBAL _epilr24,  _epilr25,  _epilr26,  _epilr27,  _epilr29,  _pper00
 .GLOBAL _pper01,   _pper02,   _pper03,   _pper04,   _pper05,   _pper06
 .GLOBAL _pper07,   _pper08,   _pper09,   _pper10,   _pper13,   _pper14
 .GLOBAL _pper15,   _pper16,   _pper17,   _pper18,   _pper19,   _pper20
 .GLOBAL _pper22,   _pper23,   _pper24,   _pper25,   _pper26,   _pper27
 .GLOBAL _pper29,   _ppcr00,   _ppcr01,   _ppcr02,   _ppcr03,   _ppcr04
 .GLOBAL _ppcr05,   _ppcr06,   _ppcr07,   _ppcr08,   _ppcr09,   _ppcr10
 .GLOBAL _ppcr13,   _ppcr14,   _ppcr15,   _ppcr16,   _ppcr17,   _ppcr18
 .GLOBAL _ppcr19,   _ppcr20,   _ppcr22,   _ppcr23,   _ppcr24,   _ppcr25
 .GLOBAL _ppcr26,   _ppcr27,   _ppcr29,   _dmasa0,   _dmada0,   _dmasa1
 .GLOBAL _dmada1,   _dmasa2,   _dmada2,   _dmasa3,   _dmada3,   _dmasa4
 .GLOBAL _dmada4,   _fmcs,     _fmcr,     _fchcr,    _fmwt,     _fmwt2
 .GLOBAL _fmps,     _fmac,     _fcha0,    _fcha1,    _fscr0,    _fscr1
 .GLOBAL _ctrlr0,   _statr0,   _errcnt0,  _btr0,     _intr0,    _testr0
 .GLOBAL _brper0,   _brpe0,    _cbsync0,  _if1creq0, _if1cmsk0, _if1msk120
 .GLOBAL _if1msk20, _if1msk10, _if1arb120, _if1arb20, _if1arb10, _if1mctr0
 .GLOBAL _if1dta120, _if1dta10, _if1dta20, _if1dtb120, _if1dtb10, _if1dtb20
 .GLOBAL _if1dta_swp120, _if1dta_swp20, _if1dta_swp10, _if1dtb_swp120, _if1dtb_swp20, _if1dtb_swp10
 .GLOBAL _if2creq0, _if2cmsk0, _if2msk120, _if2msk20, _if2msk10, _if2arb120
 .GLOBAL _if2arb20, _if2arb10, _if2mctr0, _if2dta120, _if2dta10, _if2dta20
 .GLOBAL _if2dtb120, _if2dtb10, _if2dtb20, _if2dta_swp120, _if2dta_swp20, _if2dta_swp10
 .GLOBAL _if2dtb_swp120, _if2dtb_swp20, _if2dtb_swp10, _treqr120, _treqr20,  _treqr10
 .GLOBAL _newdt120, _newdt20,  _newdt10,  _intpnd120, _intpnd20, _intpnd10
 .GLOBAL _msgval120, _msgval20, _msgval10, _msgval340, _ctrlr1,   _statr1
 .GLOBAL _errcnt1,  _btr1,     _intr1,    _testr1,   _brper1,   _brpe1
 .GLOBAL _cbsync1,  _if1creq1, _if1cmsk1, _if1msk121, _if1msk21, _if1msk11
 .GLOBAL _if1arb121, _if1arb21, _if1arb11, _if1mctr1, _if1dta121, _if1dta11
 .GLOBAL _if1dta21, _if1dtb121, _if1dtb11, _if1dtb21, _if1dta_swp121, _if1dta_swp21
 .GLOBAL _if1dta_swp11, _if1dtb_swp121, _if1dtb_swp21, _if1dtb_swp11, _if2creq1, _if2cmsk1
 .GLOBAL _if2msk121, _if2msk21, _if2msk11, _if2arb121, _if2arb21, _if2arb11
 .GLOBAL _if2mctr1, _if2dta121, _if2dta11, _if2dta21, _if2dtb121, _if2dtb11
 .GLOBAL _if2dtb21, _if2dta_swp121, _if2dta_swp21, _if2dta_swp11, _if2dtb_swp121, _if2dtb_swp21
 .GLOBAL _if2dtb_swp11, _treqr121, _treqr21,  _treqr11,  _newdt121, _newdt21
 .GLOBAL _newdt11,  _intpnd121, _intpnd21, _intpnd11, _msgval121, _msgval21
 .GLOBAL _msgval11, _ctrlr2,   _statr2,   _errcnt2,  _btr2,     _intr2
 .GLOBAL _testr2,   _brper2,   _brpe2,    _cbsync2,  _if1creq2, _if1cmsk2
 .GLOBAL _if1msk122, _if1msk22, _if1msk12, _if1arb122, _if1arb22, _if1arb12
 .GLOBAL _if1mctr2, _if1dta122, _if1dta12, _if1dta22, _if1dtb122, _if1dtb12
 .GLOBAL _if1dtb22, _if1dta_swp122, _if1dta_swp22, _if1dta_swp12, _if1dtb_swp122, _if1dtb_swp22
 .GLOBAL _if1dtb_swp12, _if2creq2, _if2cmsk2, _if2msk122, _if2msk22, _if2msk12
 .GLOBAL _if2arb122, _if2arb22, _if2arb12, _if2mctr2, _if2dta122, _if2dta12
 .GLOBAL _if2dta22, _if2dtb122, _if2dtb12, _if2dtb22, _if2dta_swp122, _if2dta_swp22
 .GLOBAL _if2dta_swp12, _if2dtb_swp122, _if2dtb_swp22, _if2dtb_swp12, _treqr122, _treqr22
 .GLOBAL _treqr12,  _newdt122, _newdt22,  _newdt12,  _intpnd122, _intpnd22
 .GLOBAL _intpnd12, _msgval122, _msgval22, _msgval12, _bctrl,    _bstat
 .GLOBAL _biac,     _boac,     _birq,     _bcr0,     _bcr1,     _bcr2
 .GLOBAL _bcr3,     _bcr4,     _bcr5,     _bcr6,     _bcr7,     _bad0
 .GLOBAL _bad1,     _bad2,     _bad3,     _bad4,     _bad5,     _bad6
 .GLOBAL _bad7,     _bad8,     _bad9,     _bad10,    _bad11,    _bad12
 .GLOBAL _bad13,    _bad14,    _bad15,    _fsv1,     _bsv1,     _fsv2
 .GLOBAL _bsv2

_pdr00     .EQU 0x000000
PDR00      .EQU 0x000000 /* Port Data Register */
_pdr01     .EQU 0x000001
PDR01      .EQU 0x000001
_pdr02     .EQU 0x000002
PDR02      .EQU 0x000002
_pdr03     .EQU 0x000003
PDR03      .EQU 0x000003
_pdr04     .EQU 0x000004
PDR04      .EQU 0x000004
_pdr05     .EQU 0x000005
PDR05      .EQU 0x000005
_pdr06     .EQU 0x000006
PDR06      .EQU 0x000006
_pdr07     .EQU 0x000007
PDR07      .EQU 0x000007
_pdr08     .EQU 0x000008
PDR08      .EQU 0x000008
_pdr09     .EQU 0x000009
PDR09      .EQU 0x000009
_pdr10     .EQU 0x00000A
PDR10      .EQU 0x00000A
_pdr13     .EQU 0x00000D
PDR13      .EQU 0x00000D
_pdr14     .EQU 0x00000E
PDR14      .EQU 0x00000E
_pdr15     .EQU 0x00000F
PDR15      .EQU 0x00000F
_pdr16     .EQU 0x000010
PDR16      .EQU 0x000010
_pdr17     .EQU 0x000011
PDR17      .EQU 0x000011
_pdr18     .EQU 0x000012
PDR18      .EQU 0x000012
_pdr19     .EQU 0x000013
PDR19      .EQU 0x000013
_pdr20     .EQU 0x000014
PDR20      .EQU 0x000014
_pdr22     .EQU 0x000016
PDR22      .EQU 0x000016
_pdr23     .EQU 0x000017
PDR23      .EQU 0x000017
_pdr24     .EQU 0x000018
PDR24      .EQU 0x000018
_pdr25     .EQU 0x000019
PDR25      .EQU 0x000019
_pdr26     .EQU 0x00001A
PDR26      .EQU 0x00001A
_pdr27     .EQU 0x00001B
PDR27      .EQU 0x00001B
_pdr29     .EQU 0x00001D
PDR29      .EQU 0x00001D
_eirr0     .EQU 0x000030
EIRR0      .EQU 0x000030 /* External Interrupt 0-7 */
_enir0     .EQU 0x000031
ENIR0      .EQU 0x000031
_elvr0     .EQU 0x000032
ELVR0      .EQU 0x000032
_eirr1     .EQU 0x000034
EIRR1      .EQU 0x000034 /* External Interrupt 8-15 */
_enir1     .EQU 0x000035
ENIR1      .EQU 0x000035
_elvr1     .EQU 0x000036
ELVR1      .EQU 0x000036
_dicr      .EQU 0x000038
DICR       .EQU 0x000038 /* DLYI/I-unit */
_hrcl      .EQU 0x000039
HRCL       .EQU 0x000039
_rbsync    .EQU 0x00003A
RBSYNC     .EQU 0x00003A /* R-Bus Sync */
_scr02     .EQU 0x000050
SCR02      .EQU 0x000050 /* USART (LIN) 2 */
_smr02     .EQU 0x000051
SMR02      .EQU 0x000051
_ssr02     .EQU 0x000052
SSR02      .EQU 0x000052
_rdr02     .EQU 0x000053
RDR02      .EQU 0x000053
_tdr02     .EQU 0x000053
TDR02      .EQU 0x000053
_escr02    .EQU 0x000054
ESCR02     .EQU 0x000054
_eccr02    .EQU 0x000055
ECCR02     .EQU 0x000055
_scr04     .EQU 0x000060
SCR04      .EQU 0x000060 /* USART (LIN) 4 with FIFO */
_smr04     .EQU 0x000061
SMR04      .EQU 0x000061
_ssr04     .EQU 0x000062
SSR04      .EQU 0x000062
_rdr04     .EQU 0x000063
RDR04      .EQU 0x000063
_tdr04     .EQU 0x000063
TDR04      .EQU 0x000063
_escr04    .EQU 0x000064
ESCR04     .EQU 0x000064
_eccr04    .EQU 0x000065
ECCR04     .EQU 0x000065
_fsr04     .EQU 0x000066
FSR04      .EQU 0x000066
_fcr04     .EQU 0x000067
FCR04      .EQU 0x000067
_scr05     .EQU 0x000068
SCR05      .EQU 0x000068 /* USART (LIN) 5 with FIFO */
_smr05     .EQU 0x000069
SMR05      .EQU 0x000069
_ssr05     .EQU 0x00006A
SSR05      .EQU 0x00006A
_rdr05     .EQU 0x00006B
RDR05      .EQU 0x00006B
_tdr05     .EQU 0x00006B
TDR05      .EQU 0x00006B
_escr05    .EQU 0x00006C
ESCR05     .EQU 0x00006C
_eccr05    .EQU 0x00006D
ECCR05     .EQU 0x00006D
_fsr05     .EQU 0x00006E
FSR05      .EQU 0x00006E
_fcr05     .EQU 0x00006F
FCR05      .EQU 0x00006F
_scr06     .EQU 0x000070
SCR06      .EQU 0x000070 /* USART (LIN) 6 with FIFO */
_smr06     .EQU 0x000071
SMR06      .EQU 0x000071
_ssr06     .EQU 0x000072
SSR06      .EQU 0x000072
_rdr06     .EQU 0x000073
RDR06      .EQU 0x000073
_tdr06     .EQU 0x000073
TDR06      .EQU 0x000073
_escr06    .EQU 0x000074
ESCR06     .EQU 0x000074
_eccr06    .EQU 0x000075
ECCR06     .EQU 0x000075
_fsr06     .EQU 0x000076
FSR06      .EQU 0x000076
_fcr06     .EQU 0x000077
FCR06      .EQU 0x000077
_scr07     .EQU 0x000078
SCR07      .EQU 0x000078 /* USART (LIN) 7 with FIFO */
_smr07     .EQU 0x000079
SMR07      .EQU 0x000079
_ssr07     .EQU 0x00007A
SSR07      .EQU 0x00007A
_rdr07     .EQU 0x00007B
RDR07      .EQU 0x00007B
_tdr07     .EQU 0x00007B
TDR07      .EQU 0x00007B
_escr07    .EQU 0x00007C
ESCR07     .EQU 0x00007C
_eccr07    .EQU 0x00007D
ECCR07     .EQU 0x00007D
_fsr07     .EQU 0x00007E
FSR07      .EQU 0x00007E
_fcr07     .EQU 0x00007F
FCR07      .EQU 0x00007F
_bgr02     .EQU 0x000084
BGR02      .EQU 0x000084 /* Bauderate Generator USART (LIN) 2,4-7 */
_bgr102    .EQU 0x000084
BGR102     .EQU 0x000084
_bgr002    .EQU 0x000085
BGR002     .EQU 0x000085
_bgr04     .EQU 0x000088
BGR04      .EQU 0x000088
_bgr104    .EQU 0x000088
BGR104     .EQU 0x000088
_bgr004    .EQU 0x000089
BGR004     .EQU 0x000089
_bgr05     .EQU 0x00008A
BGR05      .EQU 0x00008A
_bgr105    .EQU 0x00008A
BGR105     .EQU 0x00008A
_bgr005    .EQU 0x00008B
BGR005     .EQU 0x00008B
_bgr06     .EQU 0x00008C
BGR06      .EQU 0x00008C
_bgr106    .EQU 0x00008C
BGR106     .EQU 0x00008C
_bgr006    .EQU 0x00008D
BGR006     .EQU 0x00008D
_bgr07     .EQU 0x00008E
BGR07      .EQU 0x00008E
_bgr107    .EQU 0x00008E
BGR107     .EQU 0x00008E
_bgr007    .EQU 0x00008F
BGR007     .EQU 0x00008F
_pwc20     .EQU 0x000090
PWC20      .EQU 0x000090 /* Stepper Motor 0 */
_pwc10     .EQU 0x000092
PWC10      .EQU 0x000092
_pws20     .EQU 0x000096
PWS20      .EQU 0x000096
_pws10     .EQU 0x000097
PWS10      .EQU 0x000097
_pwc21     .EQU 0x000098
PWC21      .EQU 0x000098 /* Stepper Motor 1 */
_pwc11     .EQU 0x00009A
PWC11      .EQU 0x00009A
_pws21     .EQU 0x00009E
PWS21      .EQU 0x00009E
_pws11     .EQU 0x00009F
PWS11      .EQU 0x00009F
_pwc22     .EQU 0x0000A0
PWC22      .EQU 0x0000A0 /* Stepper Motor 2 */
_pwc12     .EQU 0x0000A2
PWC12      .EQU 0x0000A2
_pws22     .EQU 0x0000A6
PWS22      .EQU 0x0000A6
_pws12     .EQU 0x0000A7
PWS12      .EQU 0x0000A7
_pwc23     .EQU 0x0000A8
PWC23      .EQU 0x0000A8 /* Stepper Motor 3 */
_pwc13     .EQU 0x0000AA
PWC13      .EQU 0x0000AA
_pws23     .EQU 0x0000AE
PWS23      .EQU 0x0000AE
_pws13     .EQU 0x0000AF
PWS13      .EQU 0x0000AF
_pwc24     .EQU 0x0000B0
PWC24      .EQU 0x0000B0 /* Stepper Motor 4 */
_pwc14     .EQU 0x0000B2
PWC14      .EQU 0x0000B2
_pws24     .EQU 0x0000B6
PWS24      .EQU 0x0000B6
_pws14     .EQU 0x0000B7
PWS14      .EQU 0x0000B7
_pwc25     .EQU 0x0000B8
PWC25      .EQU 0x0000B8 /* Stepper Motor 5 */
_pwc15     .EQU 0x0000BA
PWC15      .EQU 0x0000BA
_pws25     .EQU 0x0000BE
PWS25      .EQU 0x0000BE
_pws15     .EQU 0x0000BF
PWS15      .EQU 0x0000BF
_pwc0      .EQU 0x0000C1
PWC0       .EQU 0x0000C1 /* Stepper Motor Control 0-5 */
_pwc1      .EQU 0x0000C3
PWC1       .EQU 0x0000C3
_pwc2      .EQU 0x0000C5
PWC2       .EQU 0x0000C5
_pwc3      .EQU 0x0000C7
PWC3       .EQU 0x0000C7
_pwc4      .EQU 0x0000C9
PWC4       .EQU 0x0000C9
_pwc5      .EQU 0x0000CB
PWC5       .EQU 0x0000CB
_ibcr0     .EQU 0x0000D0
IBCR0      .EQU 0x0000D0 /* I2C 0 */
_ibsr0     .EQU 0x0000D1
IBSR0      .EQU 0x0000D1
_itba0     .EQU 0x0000D2
ITBA0      .EQU 0x0000D2
_itbah0    .EQU 0x0000D2
ITBAH0     .EQU 0x0000D2
_itbal0    .EQU 0x0000D3
ITBAL0     .EQU 0x0000D3
_itmk0     .EQU 0x0000D4
ITMK0      .EQU 0x0000D4
_itmkh0    .EQU 0x0000D4
ITMKH0     .EQU 0x0000D4
_itmkl0    .EQU 0x0000D5
ITMKL0     .EQU 0x0000D5
_ismk0     .EQU 0x0000D6
ISMK0      .EQU 0x0000D6
_isba0     .EQU 0x0000D7
ISBA0      .EQU 0x0000D7
_idar0     .EQU 0x0000D9
IDAR0      .EQU 0x0000D9
_iccr0     .EQU 0x0000DA
ICCR0      .EQU 0x0000DA
_gcn11     .EQU 0x000104
GCN11      .EQU 0x000104 /* PPG Control 4-7 */
_gcn21     .EQU 0x000107
GCN21      .EQU 0x000107
_gcn12     .EQU 0x000108
GCN12      .EQU 0x000108 /* PPG Control 8-11 */
_gcn22     .EQU 0x00010B
GCN22      .EQU 0x00010B
_ptmr04    .EQU 0x000130
PTMR04     .EQU 0x000130 /* PPG 4 */
_pcsr04    .EQU 0x000132
PCSR04     .EQU 0x000132
_pdut04    .EQU 0x000134
PDUT04     .EQU 0x000134
_pcn04     .EQU 0x000136
PCN04      .EQU 0x000136
_pcnh04    .EQU 0x000136
PCNH04     .EQU 0x000136
_pcnl04    .EQU 0x000137
PCNL04     .EQU 0x000137
_ptmr05    .EQU 0x000138
PTMR05     .EQU 0x000138 /* PPG 5 */
_pcsr05    .EQU 0x00013A
PCSR05     .EQU 0x00013A
_pdut05    .EQU 0x00013C
PDUT05     .EQU 0x00013C
_pcn05     .EQU 0x00013E
PCN05      .EQU 0x00013E
_pcnh05    .EQU 0x00013E
PCNH05     .EQU 0x00013E
_pcnl05    .EQU 0x00013F
PCNL05     .EQU 0x00013F
_ptmr06    .EQU 0x000140
PTMR06     .EQU 0x000140 /* PPG 6 */
_pcsr06    .EQU 0x000142
PCSR06     .EQU 0x000142
_pdut06    .EQU 0x000144
PDUT06     .EQU 0x000144
_pcn06     .EQU 0x000146
PCN06      .EQU 0x000146
_pcnh06    .EQU 0x000146
PCNH06     .EQU 0x000146
_pcnl06    .EQU 0x000147
PCNL06     .EQU 0x000147
_ptmr07    .EQU 0x000148
PTMR07     .EQU 0x000148 /* PPG 7 */
_pcsr07    .EQU 0x00014A
PCSR07     .EQU 0x00014A
_pdut07    .EQU 0x00014C
PDUT07     .EQU 0x00014C
_pcn07     .EQU 0x00014E
PCN07      .EQU 0x00014E
_pcnh07    .EQU 0x00014E
PCNH07     .EQU 0x00014E
_pcnl07    .EQU 0x00014F
PCNL07     .EQU 0x00014F
_ptmr08    .EQU 0x000150
PTMR08     .EQU 0x000150 /* PPG 8 */
_pcsr08    .EQU 0x000152
PCSR08     .EQU 0x000152
_pdut08    .EQU 0x000154
PDUT08     .EQU 0x000154
_pcn08     .EQU 0x000156
PCN08      .EQU 0x000156
_pcnh08    .EQU 0x000156
PCNH08     .EQU 0x000156
_pcnl08    .EQU 0x000157
PCNL08     .EQU 0x000157
_ptmr09    .EQU 0x000158
PTMR09     .EQU 0x000158 /* PPG 9 */
_pcsr09    .EQU 0x00015A
PCSR09     .EQU 0x00015A
_pdut09    .EQU 0x00015C
PDUT09     .EQU 0x00015C
_pcn09     .EQU 0x00015E
PCN09      .EQU 0x00015E
_pcnh09    .EQU 0x00015E
PCNH09     .EQU 0x00015E
_pcnl09    .EQU 0x00015F
PCNL09     .EQU 0x00015F
_ptmr10    .EQU 0x000160
PTMR10     .EQU 0x000160 /* PPG 10 */
_pcsr10    .EQU 0x000162
PCSR10     .EQU 0x000162
_pdut10    .EQU 0x000164
PDUT10     .EQU 0x000164
_pcn10     .EQU 0x000166
PCN10      .EQU 0x000166
_pcnh10    .EQU 0x000166
PCNH10     .EQU 0x000166
_pcnl10    .EQU 0x000167
PCNL10     .EQU 0x000167
_ptmr11    .EQU 0x000168
PTMR11     .EQU 0x000168 /* PPG 11 */
_pcsr11    .EQU 0x00016A
PCSR11     .EQU 0x00016A
_pdut11    .EQU 0x00016C
PDUT11     .EQU 0x00016C
_pcn11     .EQU 0x00016E
PCN11      .EQU 0x00016E
_pcnh11    .EQU 0x00016E
PCNH11     .EQU 0x00016E
_pcnl11    .EQU 0x00016F
PCNL11     .EQU 0x00016F
_p0tmcsr   .EQU 0x000170
P0TMCSR    .EQU 0x000170 /* Pulse Frequency Modulator (PFM) */
_p0tmcsrh  .EQU 0x000170
P0TMCSRH   .EQU 0x000170
_p0tmcsrl  .EQU 0x000171
P0TMCSRL   .EQU 0x000171
_p1tmcsr   .EQU 0x000172
P1TMCSR    .EQU 0x000172
_p1tmcsrh  .EQU 0x000172
P1TMCSRH   .EQU 0x000172
_p1tmcsrl  .EQU 0x000173
P1TMCSRL   .EQU 0x000173
_p0tmrlr   .EQU 0x000174
P0TMRLR    .EQU 0x000174
_p0tmr     .EQU 0x000176
P0TMR      .EQU 0x000176
_p1tmrlr   .EQU 0x000178
P1TMRLR    .EQU 0x000178
_p1tmr     .EQU 0x00017A
P1TMR      .EQU 0x00017A
_ics01     .EQU 0x000181
ICS01      .EQU 0x000181 /* Input Capture 0-3 */
_ics23     .EQU 0x000183
ICS23      .EQU 0x000183
_ipcp0     .EQU 0x000184
IPCP0      .EQU 0x000184
_ipcp1     .EQU 0x000186
IPCP1      .EQU 0x000186
_ipcp2     .EQU 0x000188
IPCP2      .EQU 0x000188
_ipcp3     .EQU 0x00018A
IPCP3      .EQU 0x00018A
_ocs01     .EQU 0x00018C
OCS01      .EQU 0x00018C /* Output Compare 0-3 */
_ocs23     .EQU 0x00018E
OCS23      .EQU 0x00018E
_occp0     .EQU 0x000190
OCCP0      .EQU 0x000190
_occp1     .EQU 0x000192
OCCP1      .EQU 0x000192
_occp2     .EQU 0x000194
OCCP2      .EQU 0x000194
_occp3     .EQU 0x000196
OCCP3      .EQU 0x000196
_sgcr      .EQU 0x000198
SGCR       .EQU 0x000198 /* Sound Generator */
_sgcrh     .EQU 0x000198
SGCRH      .EQU 0x000198
_sgcrl     .EQU 0x000199
SGCRL      .EQU 0x000199
_sgfr      .EQU 0x00019A
SGFR       .EQU 0x00019A
_sgar      .EQU 0x00019C
SGAR       .EQU 0x00019C
_sgtr      .EQU 0x00019E
SGTR       .EQU 0x00019E
_sgdr      .EQU 0x00019F
SGDR       .EQU 0x00019F
_aderh     .EQU 0x0001A0
ADERH      .EQU 0x0001A0 /* ADC */
_aderl     .EQU 0x0001A2
ADERL      .EQU 0x0001A2
_ader  .EQU 0x0001A0
ADER   .EQU 0x0001A0
_adcs1     .EQU 0x0001A4
ADCS1      .EQU 0x0001A4
_adcs0     .EQU 0x0001A5
ADCS0      .EQU 0x0001A5
_adcs  .EQU 0x0001A4
ADCS   .EQU 0x0001A4
_adcr1     .EQU 0x0001A6
ADCR1      .EQU 0x0001A6
_adcr0     .EQU 0x0001A7
ADCR0      .EQU 0x0001A7
_adcr  .EQU 0x0001A6
ADCR   .EQU 0x0001A6
_adct1     .EQU 0x0001A8
ADCT1      .EQU 0x0001A8
_adct0     .EQU 0x0001A9
ADCT0      .EQU 0x0001A9
_adct  .EQU 0x0001A8
ADCT   .EQU 0x0001A8
_adsch     .EQU 0x0001AA
ADSCH      .EQU 0x0001AA
_adech     .EQU 0x0001AB
ADECH      .EQU 0x0001AB
_acsr0     .EQU 0x0001AD
ACSR0      .EQU 0x0001AD /* Alarm Comparator 0-1 */
_tmrlr0    .EQU 0x0001B0
TMRLR0     .EQU 0x0001B0 /* Reload Timer 0 */
_tmr0      .EQU 0x0001B2
TMR0       .EQU 0x0001B2
_tmcsr0    .EQU 0x0001B6
TMCSR0     .EQU 0x0001B6
_tmcsrh0  .EQU 0x0001B6
TMCSRH0   .EQU 0x0001B6
_tmcsrl0  .EQU 0x0001B7
TMCSRL0   .EQU 0x0001B7
_tmrlr1    .EQU 0x0001B8
TMRLR1     .EQU 0x0001B8 /* Reload Timer 1 */
_tmr1      .EQU 0x0001BA
TMR1       .EQU 0x0001BA
_tmcsr1    .EQU 0x0001BE
TMCSR1     .EQU 0x0001BE
_tmcsrh1  .EQU 0x0001BE
TMCSRH1   .EQU 0x0001BE
_tmcsrl1  .EQU 0x0001BF
TMCSRL1   .EQU 0x0001BF
_tmrlr2    .EQU 0x0001C0
TMRLR2     .EQU 0x0001C0 /* Reload Timer 2 */
_tmr2      .EQU 0x0001C2
TMR2       .EQU 0x0001C2
_tmcsr2    .EQU 0x0001C6
TMCSR2     .EQU 0x0001C6
_tmcsrh2  .EQU 0x0001C6
TMCSRH2   .EQU 0x0001C6
_tmcsrl2  .EQU 0x0001C7
TMCSRL2   .EQU 0x0001C7
_tmrlr3    .EQU 0x0001C8
TMRLR3     .EQU 0x0001C8 /* Reload Timer 3 */
_tmr3      .EQU 0x0001CA
TMR3       .EQU 0x0001CA
_tmcsr3    .EQU 0x0001CE
TMCSR3     .EQU 0x0001CE
_tmcsrh3  .EQU 0x0001CE
TMCSRH3   .EQU 0x0001CE
_tmcsrl3  .EQU 0x0001CF
TMCSRL3   .EQU 0x0001CF
_tmrlr4    .EQU 0x0001D0
TMRLR4     .EQU 0x0001D0 /* Reload Timer 4 */
_tmr4      .EQU 0x0001D2
TMR4       .EQU 0x0001D2
_tmcsr4    .EQU 0x0001D6
TMCSR4     .EQU 0x0001D6
_tmcsrh4  .EQU 0x0001D6
TMCSRH4   .EQU 0x0001D6
_tmcsrl4  .EQU 0x0001D7
TMCSRL4   .EQU 0x0001D7
_tmrlr5    .EQU 0x0001D8
TMRLR5     .EQU 0x0001D8 /* Reload Timer 5 */
_tmr5      .EQU 0x0001DA
TMR5       .EQU 0x0001DA
_tmcsr5    .EQU 0x0001DE
TMCSR5     .EQU 0x0001DE
_tmcsrh5  .EQU 0x0001DE
TMCSRH5   .EQU 0x0001DE
_tmcsrl5  .EQU 0x0001DF
TMCSRL5   .EQU 0x0001DF
_tmrlr6    .EQU 0x0001E0
TMRLR6     .EQU 0x0001E0 /* Reload Timer 6 */
_tmr6      .EQU 0x0001E2
TMR6       .EQU 0x0001E2
_tmcsr6    .EQU 0x0001E6
TMCSR6     .EQU 0x0001E6
_tmcsrh6  .EQU 0x0001E6
TMCSRH6   .EQU 0x0001E6
_tmcsrl6  .EQU 0x0001E7
TMCSRL6   .EQU 0x0001E7
_tmrlr7    .EQU 0x0001E8
TMRLR7     .EQU 0x0001E8 /* Reload Timer 7 */
_tmr7      .EQU 0x0001EA
TMR7       .EQU 0x0001EA
_tmcsr7    .EQU 0x0001EE
TMCSR7     .EQU 0x0001EE
_tmcsrh7  .EQU 0x0001EE
TMCSRH7   .EQU 0x0001EE
_tmcsrl7  .EQU 0x0001EF
TMCSRL7   .EQU 0x0001EF
_tcdt0     .EQU 0x0001F0
TCDT0      .EQU 0x0001F0 /* Free Running Timer0 */
_tccs0     .EQU 0x0001F3
TCCS0      .EQU 0x0001F3
_tcdt1     .EQU 0x0001F4
TCDT1      .EQU 0x0001F4 /* Free Running Timer1 */
_tccs1     .EQU 0x0001F7
TCCS1      .EQU 0x0001F7
_tcdt2     .EQU 0x0001F8
TCDT2      .EQU 0x0001F8 /* Free Running Timer2 */
_tccs2     .EQU 0x0001FB
TCCS2      .EQU 0x0001FB
_tcdt3     .EQU 0x0001FC
TCDT3      .EQU 0x0001FC /* Free Running Timer3 */
_tccs3     .EQU 0x0001FF
TCCS3      .EQU 0x0001FF
_dmaca0    .EQU 0x000200
DMACA0     .EQU 0x000200 /* DMAC */
_dmacb0    .EQU 0x000204
DMACB0     .EQU 0x000204
_dmaca1    .EQU 0x000208
DMACA1     .EQU 0x000208
_dmacb1    .EQU 0x00020C
DMACB1     .EQU 0x00020C
_dmaca2    .EQU 0x000210
DMACA2     .EQU 0x000210
_dmacb2    .EQU 0x000214
DMACB2     .EQU 0x000214
_dmaca3    .EQU 0x000218
DMACA3     .EQU 0x000218
_dmacb3    .EQU 0x00021C
DMACB3     .EQU 0x00021C
_dmaca4    .EQU 0x000220
DMACA4     .EQU 0x000220
_dmacb4    .EQU 0x000224
DMACB4     .EQU 0x000224
_dmacr     .EQU 0x000240
DMACR      .EQU 0x000240
_ics45     .EQU 0x0002D1
ICS45      .EQU 0x0002D1 /* Input Capture 4-7 */
_ics67     .EQU 0x0002D3
ICS67      .EQU 0x0002D3
_ipcp4     .EQU 0x0002D4
IPCP4      .EQU 0x0002D4
_ipcp5     .EQU 0x0002D6
IPCP5      .EQU 0x0002D6
_ipcp6     .EQU 0x0002D8
IPCP6      .EQU 0x0002D8
_ipcp7     .EQU 0x0002DA
IPCP7      .EQU 0x0002DA
_tcdt4     .EQU 0x0002F0
TCDT4      .EQU 0x0002F0 /* Free Running Timer4 */
_tccs4     .EQU 0x0002F3
TCCS4      .EQU 0x0002F3
_tcdt5     .EQU 0x0002F4
TCDT5      .EQU 0x0002F4 /* Free Running Timer5 */
_tccs5     .EQU 0x0002F7
TCCS5      .EQU 0x0002F7
_tcdt6     .EQU 0x0002F8
TCDT6      .EQU 0x0002F8 /* Free Running Timer6 */
_tccs6     .EQU 0x0002FB
TCCS6      .EQU 0x0002FB
_tcdt7     .EQU 0x0002FC
TCDT7      .EQU 0x0002FC /* Free Running Timer7 */
_tccs7     .EQU 0x0002FF
TCCS7      .EQU 0x0002FF
_udrc10    .EQU 0x000300
UDRC10     .EQU 0x000300 /* Up/Down Counter 0-1 */
_udrc1     .EQU 0x000300
UDRC1      .EQU 0x000300
_udrc0     .EQU 0x000301
UDRC0      .EQU 0x000301
_udcr10    .EQU 0x000302
UDCR10     .EQU 0x000302
_udcr1     .EQU 0x000302
UDCR1      .EQU 0x000302
_udcr0     .EQU 0x000303
UDCR0      .EQU 0x000303
_udcc0     .EQU 0x000304
UDCC0      .EQU 0x000304
_udcch0  .EQU 0x000304
UDCCH0   .EQU 0x000304
_udccl0  .EQU 0x000305
UDCCL0   .EQU 0x000305
_udcs0     .EQU 0x000307
UDCS0      .EQU 0x000307
_udcc1     .EQU 0x000308
UDCC1      .EQU 0x000308
_udcch1  .EQU 0x000308
UDCCH1   .EQU 0x000308
_udccl1  .EQU 0x000309
UDCCL1   .EQU 0x000309
_udcs1     .EQU 0x00030B
UDCS1      .EQU 0x00030B
_udrc32    .EQU 0x000310
UDRC32     .EQU 0x000310 /* Up/Down Counter 2-3 */
_udrc3     .EQU 0x000310
UDRC3      .EQU 0x000310
_udrc2     .EQU 0x000311
UDRC2      .EQU 0x000311
_udcr32    .EQU 0x000312
UDCR32     .EQU 0x000312
_udcr3     .EQU 0x000312
UDCR3      .EQU 0x000312
_udcr2     .EQU 0x000313
UDCR2      .EQU 0x000313
_udcc2     .EQU 0x000314
UDCC2      .EQU 0x000314
_udcch2  .EQU 0x000314
UDCCH2   .EQU 0x000314
_udccl2  .EQU 0x000315
UDCCL2   .EQU 0x000315
_udcs2     .EQU 0x000317
UDCS2      .EQU 0x000317
_udcc3     .EQU 0x000318
UDCC3      .EQU 0x000318
_udcch3  .EQU 0x000318
UDCCH3   .EQU 0x000318
_udccl3  .EQU 0x000319
UDCCL3   .EQU 0x000319
_udcs3     .EQU 0x00031B
UDCS3      .EQU 0x00031B
_gcn13     .EQU 0x000320
GCN13      .EQU 0x000320 /* PPG Control 12-15 */
_gcn23     .EQU 0x000323
GCN23      .EQU 0x000323
_ptmr12    .EQU 0x000330
PTMR12     .EQU 0x000330 /* PPG 12 */
_pcsr12    .EQU 0x000332
PCSR12     .EQU 0x000332
_pdut12    .EQU 0x000334
PDUT12     .EQU 0x000334
_pcn12     .EQU 0x000336
PCN12      .EQU 0x000336
_pcnh12    .EQU 0x000336
PCNH12     .EQU 0x000336
_pcnl12    .EQU 0x000337
PCNL12     .EQU 0x000337
_ptmr13    .EQU 0x000338
PTMR13     .EQU 0x000338 /* PPG 13 */
_pcsr13    .EQU 0x00033A
PCSR13     .EQU 0x00033A
_pdut13    .EQU 0x00033C
PDUT13     .EQU 0x00033C
_pcn13     .EQU 0x00033E
PCN13      .EQU 0x00033E
_pcnh13    .EQU 0x00033E
PCNH13     .EQU 0x00033E
_pcnl13    .EQU 0x00033F
PCNL13     .EQU 0x00033F
_ptmr14    .EQU 0x000340
PTMR14     .EQU 0x000340 /* PPG 14 */
_pcsr14    .EQU 0x000342
PCSR14     .EQU 0x000342
_pdut14    .EQU 0x000344
PDUT14     .EQU 0x000344
_pcn14     .EQU 0x000346
PCN14      .EQU 0x000346
_pcnh14    .EQU 0x000346
PCNH14     .EQU 0x000346
_pcnl14    .EQU 0x000347
PCNL14     .EQU 0x000347
_ptmr15    .EQU 0x000348
PTMR15     .EQU 0x000348 /* PPG 15 */
_pcsr15    .EQU 0x00034A
PCSR15     .EQU 0x00034A
_pdut15    .EQU 0x00034C
PDUT15     .EQU 0x00034C
_pcn15     .EQU 0x00034E
PCN15      .EQU 0x00034E
_pcnh15    .EQU 0x00034E
PCNH15     .EQU 0x00034E
_pcnl15    .EQU 0x00034F
PCNL15     .EQU 0x00034F
_ibcr2     .EQU 0x000368
IBCR2      .EQU 0x000368 /* I2C 2 */
_ibsr2     .EQU 0x000369
IBSR2      .EQU 0x000369
_itba2     .EQU 0x00036A
ITBA2      .EQU 0x00036A
_itbah2    .EQU 0x00036A
ITBAH2     .EQU 0x00036A
_itbal2    .EQU 0x00036B
ITBAL2     .EQU 0x00036B
_itmk2     .EQU 0x00036C
ITMK2      .EQU 0x00036C
_itmkh2    .EQU 0x00036C
ITMKH2     .EQU 0x00036C
_itmkl2    .EQU 0x00036D
ITMKL2     .EQU 0x00036D
_ismk2     .EQU 0x00036E
ISMK2      .EQU 0x00036E
_isba2     .EQU 0x00036F
ISBA2      .EQU 0x00036F
_idar2     .EQU 0x000371
IDAR2      .EQU 0x000371
_iccr2     .EQU 0x000372
ICCR2      .EQU 0x000372
_ibcr3     .EQU 0x000374
IBCR3      .EQU 0x000374 /* I2C 3 */
_ibsr3     .EQU 0x000375
IBSR3      .EQU 0x000375
_itba3     .EQU 0x000376
ITBA3      .EQU 0x000376
_itbah3    .EQU 0x000376
ITBAH3     .EQU 0x000376
_itbal3    .EQU 0x000377
ITBAL3     .EQU 0x000377
_itmk3     .EQU 0x000378
ITMK3      .EQU 0x000378
_itmkh3    .EQU 0x000378
ITMKH3     .EQU 0x000378
_itmkl3    .EQU 0x000379
ITMKL3     .EQU 0x000379
_ismk3     .EQU 0x00037A
ISMK3      .EQU 0x00037A
_isba3     .EQU 0x00037B
ISBA3      .EQU 0x00037B
_idar3     .EQU 0x00037D
IDAR3      .EQU 0x00037D
_iccr3     .EQU 0x00037E
ICCR3      .EQU 0x00037E
_roms      .EQU 0x000390
ROMS       .EQU 0x000390 /* ROM Select Register */
_bsd0      .EQU 0x0003F0
BSD0       .EQU 0x0003F0 /* Bit Search Module */
_bsd1      .EQU 0x0003F4
BSD1       .EQU 0x0003F4
_bsdc      .EQU 0x0003F8
BSDC       .EQU 0x0003F8
_bsrr      .EQU 0x0003FC
BSRR       .EQU 0x0003FC
_icr00     .EQU 0x000440
ICR00      .EQU 0x000440 /* Interrupt Control Unit */
_icr01     .EQU 0x000441
ICR01      .EQU 0x000441
_icr02     .EQU 0x000442
ICR02      .EQU 0x000442
_icr03     .EQU 0x000443
ICR03      .EQU 0x000443
_icr04     .EQU 0x000444
ICR04      .EQU 0x000444
_icr05     .EQU 0x000445
ICR05      .EQU 0x000445
_icr06     .EQU 0x000446
ICR06      .EQU 0x000446
_icr07     .EQU 0x000447
ICR07      .EQU 0x000447
_icr08     .EQU 0x000448
ICR08      .EQU 0x000448
_icr09     .EQU 0x000449
ICR09      .EQU 0x000449
_icr10     .EQU 0x00044A
ICR10      .EQU 0x00044A
_icr11     .EQU 0x00044B
ICR11      .EQU 0x00044B
_icr12     .EQU 0x00044C
ICR12      .EQU 0x00044C
_icr13     .EQU 0x00044D
ICR13      .EQU 0x00044D
_icr14     .EQU 0x00044E
ICR14      .EQU 0x00044E
_icr15     .EQU 0x00044F
ICR15      .EQU 0x00044F
_icr16     .EQU 0x000450
ICR16      .EQU 0x000450
_icr17     .EQU 0x000451
ICR17      .EQU 0x000451
_icr18     .EQU 0x000452
ICR18      .EQU 0x000452
_icr19     .EQU 0x000453
ICR19      .EQU 0x000453
_icr20     .EQU 0x000454
ICR20      .EQU 0x000454
_icr21     .EQU 0x000455
ICR21      .EQU 0x000455
_icr22     .EQU 0x000456
ICR22      .EQU 0x000456
_icr23     .EQU 0x000457
ICR23      .EQU 0x000457
_icr24     .EQU 0x000458
ICR24      .EQU 0x000458
_icr25     .EQU 0x000459
ICR25      .EQU 0x000459
_icr26     .EQU 0x00045A
ICR26      .EQU 0x00045A
_icr27     .EQU 0x00045B
ICR27      .EQU 0x00045B
_icr28     .EQU 0x00045C
ICR28      .EQU 0x00045C
_icr29     .EQU 0x00045D
ICR29      .EQU 0x00045D
_icr30     .EQU 0x00045E
ICR30      .EQU 0x00045E
_icr31     .EQU 0x00045F
ICR31      .EQU 0x00045F
_icr32     .EQU 0x000460
ICR32      .EQU 0x000460
_icr33     .EQU 0x000461
ICR33      .EQU 0x000461
_icr34     .EQU 0x000462
ICR34      .EQU 0x000462
_icr35     .EQU 0x000463
ICR35      .EQU 0x000463
_icr36     .EQU 0x000464
ICR36      .EQU 0x000464
_icr37     .EQU 0x000465
ICR37      .EQU 0x000465
_icr38     .EQU 0x000466
ICR38      .EQU 0x000466
_icr39     .EQU 0x000467
ICR39      .EQU 0x000467
_icr40     .EQU 0x000468
ICR40      .EQU 0x000468
_icr41     .EQU 0x000469
ICR41      .EQU 0x000469
_icr42     .EQU 0x00046A
ICR42      .EQU 0x00046A
_icr43     .EQU 0x00046B
ICR43      .EQU 0x00046B
_icr44     .EQU 0x00046C
ICR44      .EQU 0x00046C
_icr45     .EQU 0x00046D
ICR45      .EQU 0x00046D
_icr46     .EQU 0x00046E
ICR46      .EQU 0x00046E
_icr47     .EQU 0x00046F
ICR47      .EQU 0x00046F
_icr48     .EQU 0x000470
ICR48      .EQU 0x000470
_icr49     .EQU 0x000471
ICR49      .EQU 0x000471
_icr50     .EQU 0x000472
ICR50      .EQU 0x000472
_icr51     .EQU 0x000473
ICR51      .EQU 0x000473
_icr52     .EQU 0x000474
ICR52      .EQU 0x000474
_icr53     .EQU 0x000475
ICR53      .EQU 0x000475
_icr54     .EQU 0x000476
ICR54      .EQU 0x000476
_icr55     .EQU 0x000477
ICR55      .EQU 0x000477
_icr56     .EQU 0x000478
ICR56      .EQU 0x000478
_icr57     .EQU 0x000479
ICR57      .EQU 0x000479
_icr58     .EQU 0x00047A
ICR58      .EQU 0x00047A
_icr59     .EQU 0x00047B
ICR59      .EQU 0x00047B
_icr60     .EQU 0x00047C
ICR60      .EQU 0x00047C
_icr61     .EQU 0x00047D
ICR61      .EQU 0x00047D
_icr62     .EQU 0x00047E
ICR62      .EQU 0x00047E
_icr63     .EQU 0x00047F
ICR63      .EQU 0x00047F
_rsrr      .EQU 0x000480
RSRR       .EQU 0x000480 /* Clock Control Unit */
_stcr      .EQU 0x000481
STCR       .EQU 0x000481
_tbcr      .EQU 0x000482
TBCR       .EQU 0x000482
_ctbr      .EQU 0x000483
CTBR       .EQU 0x000483
_clkr      .EQU 0x000484
CLKR       .EQU 0x000484
_wpr       .EQU 0x000485
WPR        .EQU 0x000485
_divr0     .EQU 0x000486
DIVR0      .EQU 0x000486
_divr1     .EQU 0x000487
DIVR1      .EQU 0x000487
_plldivm   .EQU 0x00048C
PLLDIVM    .EQU 0x00048C /* PLL - Clock Gear Unit: */
_plldivn   .EQU 0x00048D
PLLDIVN    .EQU 0x00048D
_plldivg   .EQU 0x00048E
PLLDIVG    .EQU 0x00048E
_pllmulg   .EQU 0x00048F
PLLMULG    .EQU 0x00048F
_pllctrl   .EQU 0x000490
PLLCTRL    .EQU 0x000490
_oscc1     .EQU 0x000494
OSCC1      .EQU 0x000494 /* Main/Sub Oscillator Control */
_oscs1     .EQU 0x000495
OSCS1      .EQU 0x000495
_oscc2     .EQU 0x000496
OSCC2      .EQU 0x000496
_oscs2     .EQU 0x000497
OSCS2      .EQU 0x000497
_porten  .EQU 0x000498
PORTEN   .EQU 0x000498 /* Port Input Enable Control */
_wtcer     .EQU 0x0004A1
WTCER      .EQU 0x0004A1 /* Real Time Clock (Watch Timer) */
_wtcr      .EQU 0x0004A2
WTCR       .EQU 0x0004A2
_wtbr      .EQU 0x0004A4
WTBR       .EQU 0x0004A4
_wthr      .EQU 0x0004A8
WTHR       .EQU 0x0004A8
_wtmr      .EQU 0x0004A9
WTMR       .EQU 0x0004A9
_wtsr      .EQU 0x0004AA
WTSR       .EQU 0x0004AA
_csvtr     .EQU 0x0004AC
CSVTR      .EQU 0x0004AC /* Clock-Supervisor / Selecor / Monitor */
_csvcr     .EQU 0x0004AD
CSVCR      .EQU 0x0004AD
_cscfg  .EQU 0x0004AE
CSCFG   .EQU 0x0004AE
_cmcfg  .EQU 0x0004AF
CMCFG   .EQU 0x0004AF
_cucr      .EQU 0x0004B0
CUCR       .EQU 0x0004B0 /* Calibration Unit of Sub Oszillation */
_cutd      .EQU 0x0004B2
CUTD       .EQU 0x0004B2
_cutr1     .EQU 0x0004B4
CUTR1      .EQU 0x0004B4
_cutr2     .EQU 0x0004B6
CUTR2      .EQU 0x0004B6
_cmpr      .EQU 0x0004B8
CMPR       .EQU 0x0004B8 /* Clock Modulator */
_cmcr  .EQU 0x0004BB
CMCR   .EQU 0x0004BB
_cmt1      .EQU 0x0004BC
CMT1       .EQU 0x0004BC
_cmt2      .EQU 0x0004BE
CMT2       .EQU 0x0004BE
_canpre  .EQU 0x0004C0
CANPRE   .EQU 0x0004C0 /* CAN clock control */
_canckd  .EQU 0x0004C1
CANCKD   .EQU 0x0004C1
_lvsel  .EQU 0x0004C4
LVSEL   .EQU 0x0004C4 /* LV Detection / Hardware-Watchdog */
_lvdet     .EQU 0x0004C5
LVDET      .EQU 0x0004C5
_hwwde     .EQU 0x0004C6
HWWDE      .EQU 0x0004C6
_hwwd      .EQU 0x0004C7
HWWD       .EQU 0x0004C7
_oscrh     .EQU 0x0004C8
OSCRH      .EQU 0x0004C8 /* Main-/Sub-Oscillatio Stabilization Timer */
_oscrl     .EQU 0x0004C9
OSCRL      .EQU 0x0004C9
_wpcrh     .EQU 0x0004CA
WPCRH      .EQU 0x0004CA
_wpcrl     .EQU 0x0004CB
WPCRL      .EQU 0x0004CB
_osccr     .EQU 0x0004CC
OSCCR      .EQU 0x0004CC /* Main-/Sub-Oscillatio Standby Control */
_regsel  .EQU 0x0004CE
REGSEL   .EQU 0x0004CE
_regctr  .EQU 0x0004CF
REGCTR   .EQU 0x0004CF
_asr0      .EQU 0x000640
ASR0       .EQU 0x000640 /* External Bus/Chip Select Registers */
_acr0      .EQU 0x000642
ACR0       .EQU 0x000642
_asr1      .EQU 0x000644
ASR1       .EQU 0x000644
_acr1      .EQU 0x000646
ACR1       .EQU 0x000646
_asr2      .EQU 0x000648
ASR2       .EQU 0x000648
_acr2      .EQU 0x00064A
ACR2       .EQU 0x00064A
_asr3      .EQU 0x00064C
ASR3       .EQU 0x00064C
_acr3      .EQU 0x00064E
ACR3       .EQU 0x00064E
_asr4      .EQU 0x000650
ASR4       .EQU 0x000650
_acr4      .EQU 0x000652
ACR4       .EQU 0x000652
_asr5      .EQU 0x000654
ASR5       .EQU 0x000654
_acr5      .EQU 0x000656
ACR5       .EQU 0x000656
_asr6      .EQU 0x000658
ASR6       .EQU 0x000658
_acr6      .EQU 0x00065A
ACR6       .EQU 0x00065A
_asr7      .EQU 0x00065C
ASR7       .EQU 0x00065C
_acr7      .EQU 0x00065E
ACR7       .EQU 0x00065E
_awr0      .EQU 0x000660
AWR0       .EQU 0x000660
_awr1      .EQU 0x000662
AWR1       .EQU 0x000662
_awr2      .EQU 0x000664
AWR2       .EQU 0x000664
_awr3      .EQU 0x000666
AWR3       .EQU 0x000666
_awr4      .EQU 0x000668
AWR4       .EQU 0x000668
_awr5      .EQU 0x00066A
AWR5       .EQU 0x00066A
_awr6      .EQU 0x00066C
AWR6       .EQU 0x00066C
_awr7      .EQU 0x00066E
AWR7       .EQU 0x00066E
_mcra      .EQU 0x000670
MCRA       .EQU 0x000670
_mcrb      .EQU 0x000671
MCRB       .EQU 0x000671
_iowr0     .EQU 0x000678
IOWR0      .EQU 0x000678
_iowr1     .EQU 0x000679
IOWR1      .EQU 0x000679
_iowr2     .EQU 0x00067A
IOWR2      .EQU 0x00067A
_iowr3     .EQU 0x00067B
IOWR3      .EQU 0x00067B
_cser      .EQU 0x000680
CSER       .EQU 0x000680
_cher      .EQU 0x000681
CHER       .EQU 0x000681
_tcr       .EQU 0x000683
TCR        .EQU 0x000683
_rcr  .EQU 0x000684
RCR   .EQU 0x000684
_modr      .EQU 0x0007FD
MODR       .EQU 0x0007FD /* Mode Register */
_pdrd00    .EQU 0x000D00
PDRD00     .EQU 0x000D00 /* R-bus Port Data Direct Read Register */
_pdrd01    .EQU 0x000D01
PDRD01     .EQU 0x000D01
_pdrd02    .EQU 0x000D02
PDRD02     .EQU 0x000D02
_pdrd03    .EQU 0x000D03
PDRD03     .EQU 0x000D03
_pdrd04    .EQU 0x000D04
PDRD04     .EQU 0x000D04
_pdrd05    .EQU 0x000D05
PDRD05     .EQU 0x000D05
_pdrd06    .EQU 0x000D06
PDRD06     .EQU 0x000D06
_pdrd07    .EQU 0x000D07
PDRD07     .EQU 0x000D07
_pdrd08    .EQU 0x000D08
PDRD08     .EQU 0x000D08
_pdrd09    .EQU 0x000D09
PDRD09     .EQU 0x000D09
_pdrd10    .EQU 0x000D0A
PDRD10     .EQU 0x000D0A
_pdrd13    .EQU 0x000D0D
PDRD13     .EQU 0x000D0D
_pdrd14    .EQU 0x000D0E
PDRD14     .EQU 0x000D0E
_pdrd15    .EQU 0x000D0F
PDRD15     .EQU 0x000D0F
_pdrd16    .EQU 0x000D10
PDRD16     .EQU 0x000D10
_pdrd17    .EQU 0x000D11
PDRD17     .EQU 0x000D11
_pdrd18    .EQU 0x000D12
PDRD18     .EQU 0x000D12
_pdrd19    .EQU 0x000D13
PDRD19     .EQU 0x000D13
_pdrd20    .EQU 0x000D14
PDRD20     .EQU 0x000D14
_pdrd22    .EQU 0x000D16
PDRD22     .EQU 0x000D16
_pdrd23    .EQU 0x000D17
PDRD23     .EQU 0x000D17
_pdrd24    .EQU 0x000D18
PDRD24     .EQU 0x000D18
_pdrd25    .EQU 0x000D19
PDRD25     .EQU 0x000D19
_pdrd26    .EQU 0x000D1A
PDRD26     .EQU 0x000D1A
_pdrd27    .EQU 0x000D1B
PDRD27     .EQU 0x000D1B
_pdrd29    .EQU 0x000D1D
PDRD29     .EQU 0x000D1D
_ddr00     .EQU 0x000D40
DDR00      .EQU 0x000D40 /* R-bus Port Direction Register */
_ddr01     .EQU 0x000D41
DDR01      .EQU 0x000D41
_ddr02     .EQU 0x000D42
DDR02      .EQU 0x000D42
_ddr03     .EQU 0x000D43
DDR03      .EQU 0x000D43
_ddr04     .EQU 0x000D44
DDR04      .EQU 0x000D44
_ddr05     .EQU 0x000D45
DDR05      .EQU 0x000D45
_ddr06     .EQU 0x000D46
DDR06      .EQU 0x000D46
_ddr07     .EQU 0x000D47
DDR07      .EQU 0x000D47
_ddr08     .EQU 0x000D48
DDR08      .EQU 0x000D48
_ddr09     .EQU 0x000D49
DDR09      .EQU 0x000D49
_ddr10     .EQU 0x000D4A
DDR10      .EQU 0x000D4A
_ddr13     .EQU 0x000D4D
DDR13      .EQU 0x000D4D
_ddr14     .EQU 0x000D4E
DDR14      .EQU 0x000D4E
_ddr15     .EQU 0x000D4F
DDR15      .EQU 0x000D4F
_ddr16     .EQU 0x000D50
DDR16      .EQU 0x000D50
_ddr17     .EQU 0x000D51
DDR17      .EQU 0x000D51
_ddr18     .EQU 0x000D52
DDR18      .EQU 0x000D52
_ddr19     .EQU 0x000D53
DDR19      .EQU 0x000D53
_ddr20     .EQU 0x000D54
DDR20      .EQU 0x000D54
_ddr22     .EQU 0x000D56
DDR22      .EQU 0x000D56
_ddr23     .EQU 0x000D57
DDR23      .EQU 0x000D57
_ddr24     .EQU 0x000D58
DDR24      .EQU 0x000D58
_ddr25     .EQU 0x000D59
DDR25      .EQU 0x000D59
_ddr26     .EQU 0x000D5A
DDR26      .EQU 0x000D5A
_ddr27     .EQU 0x000D5B
DDR27      .EQU 0x000D5B
_ddr29     .EQU 0x000D5D
DDR29      .EQU 0x000D5D
_pfr00     .EQU 0x000D80
PFR00      .EQU 0x000D80 /* R-bus Port Function Register */
_pfr01     .EQU 0x000D81
PFR01      .EQU 0x000D81
_pfr02     .EQU 0x000D82
PFR02      .EQU 0x000D82
_pfr03     .EQU 0x000D83
PFR03      .EQU 0x000D83
_pfr04     .EQU 0x000D84
PFR04      .EQU 0x000D84
_pfr05     .EQU 0x000D85
PFR05      .EQU 0x000D85
_pfr06     .EQU 0x000D86
PFR06      .EQU 0x000D86
_pfr07     .EQU 0x000D87
PFR07      .EQU 0x000D87
_pfr08     .EQU 0x000D88
PFR08      .EQU 0x000D88
_pfr09     .EQU 0x000D89
PFR09      .EQU 0x000D89
_pfr10     .EQU 0x000D8A
PFR10      .EQU 0x000D8A
_pfr13     .EQU 0x000D8D
PFR13      .EQU 0x000D8D
_pfr14     .EQU 0x000D8E
PFR14      .EQU 0x000D8E
_pfr15     .EQU 0x000D8F
PFR15      .EQU 0x000D8F
_pfr16     .EQU 0x000D90
PFR16      .EQU 0x000D90
_pfr17     .EQU 0x000D91
PFR17      .EQU 0x000D91
_pfr18     .EQU 0x000D92
PFR18      .EQU 0x000D92
_pfr19     .EQU 0x000D93
PFR19      .EQU 0x000D93
_pfr20     .EQU 0x000D94
PFR20      .EQU 0x000D94
_pfr22     .EQU 0x000D96
PFR22      .EQU 0x000D96
_pfr23     .EQU 0x000D97
PFR23      .EQU 0x000D97
_pfr24     .EQU 0x000D98
PFR24      .EQU 0x000D98
_pfr25     .EQU 0x000D99
PFR25      .EQU 0x000D99
_pfr26     .EQU 0x000D9A
PFR26      .EQU 0x000D9A
_pfr27     .EQU 0x000D9B
PFR27      .EQU 0x000D9B
_pfr29     .EQU 0x000D9D
PFR29      .EQU 0x000D9D
_epfr10    .EQU 0x000DCA
EPFR10     .EQU 0x000DCA /* R-bus Port Extra Function Register */
_epfr13    .EQU 0x000DCD
EPFR13     .EQU 0x000DCD
_epfr14    .EQU 0x000DCE
EPFR14     .EQU 0x000DCE
_epfr15    .EQU 0x000DCF
EPFR15     .EQU 0x000DCF
_epfr16    .EQU 0x000DD0
EPFR16     .EQU 0x000DD0
_epfr18    .EQU 0x000DD2
EPFR18     .EQU 0x000DD2
_epfr19    .EQU 0x000DD3
EPFR19     .EQU 0x000DD3
_epfr20    .EQU 0x000DD4
EPFR20     .EQU 0x000DD4
_epfr26    .EQU 0x000DDA
EPFR26     .EQU 0x000DDA
_epfr27    .EQU 0x000DDB
EPFR27     .EQU 0x000DDB
_podr00    .EQU 0x000E00
PODR00     .EQU 0x000E00 /* R-bus Port Output Drive Select Register */
_podr01    .EQU 0x000E01
PODR01     .EQU 0x000E01
_podr02    .EQU 0x000E02
PODR02     .EQU 0x000E02
_podr03    .EQU 0x000E03
PODR03     .EQU 0x000E03
_podr04    .EQU 0x000E04
PODR04     .EQU 0x000E04
_podr05    .EQU 0x000E05
PODR05     .EQU 0x000E05
_podr06    .EQU 0x000E06
PODR06     .EQU 0x000E06
_podr07    .EQU 0x000E07
PODR07     .EQU 0x000E07
_podr08    .EQU 0x000E08
PODR08     .EQU 0x000E08
_podr09    .EQU 0x000E09
PODR09     .EQU 0x000E09
_podr10    .EQU 0x000E0A
PODR10     .EQU 0x000E0A
_podr13    .EQU 0x000E0D
PODR13     .EQU 0x000E0D
_podr14    .EQU 0x000E0E
PODR14     .EQU 0x000E0E
_podr15    .EQU 0x000E0F
PODR15     .EQU 0x000E0F
_podr16    .EQU 0x000E10
PODR16     .EQU 0x000E10
_podr17    .EQU 0x000E11
PODR17     .EQU 0x000E11
_podr18    .EQU 0x000E12
PODR18     .EQU 0x000E12
_podr19    .EQU 0x000E13
PODR19     .EQU 0x000E13
_podr20    .EQU 0x000E14
PODR20     .EQU 0x000E14
_podr22    .EQU 0x000E16
PODR22     .EQU 0x000E16
_podr23    .EQU 0x000E17
PODR23     .EQU 0x000E17
_podr24    .EQU 0x000E18
PODR24     .EQU 0x000E18
_podr25    .EQU 0x000E19
PODR25     .EQU 0x000E19
_podr26    .EQU 0x000E1A
PODR26     .EQU 0x000E1A
_podr27    .EQU 0x000E1B
PODR27     .EQU 0x000E1B
_podr29    .EQU 0x000E1D
PODR29     .EQU 0x000E1D
_pilr00    .EQU 0x000E40
PILR00     .EQU 0x000E40 /* R-bus Port Input Level Select Register */
_pilr01    .EQU 0x000E41
PILR01     .EQU 0x000E41
_pilr02    .EQU 0x000E42
PILR02     .EQU 0x000E42
_pilr03    .EQU 0x000E43
PILR03     .EQU 0x000E43
_pilr04    .EQU 0x000E44
PILR04     .EQU 0x000E44
_pilr05    .EQU 0x000E45
PILR05     .EQU 0x000E45
_pilr06    .EQU 0x000E46
PILR06     .EQU 0x000E46
_pilr07    .EQU 0x000E47
PILR07     .EQU 0x000E47
_pilr08    .EQU 0x000E48
PILR08     .EQU 0x000E48
_pilr09    .EQU 0x000E49
PILR09     .EQU 0x000E49
_pilr10    .EQU 0x000E4A
PILR10     .EQU 0x000E4A
_pilr13    .EQU 0x000E4D
PILR13     .EQU 0x000E4D
_pilr14    .EQU 0x000E4E
PILR14     .EQU 0x000E4E
_pilr15    .EQU 0x000E4F
PILR15     .EQU 0x000E4F
_pilr16    .EQU 0x000E50
PILR16     .EQU 0x000E50
_pilr17    .EQU 0x000E51
PILR17     .EQU 0x000E51
_pilr18    .EQU 0x000E52
PILR18     .EQU 0x000E52
_pilr19    .EQU 0x000E53
PILR19     .EQU 0x000E53
_pilr20    .EQU 0x000E54
PILR20     .EQU 0x000E54
_pilr22    .EQU 0x000E56
PILR22     .EQU 0x000E56
_pilr23    .EQU 0x000E57
PILR23     .EQU 0x000E57
_pilr24    .EQU 0x000E58
PILR24     .EQU 0x000E58
_pilr25    .EQU 0x000E59
PILR25     .EQU 0x000E59
_pilr26    .EQU 0x000E5A
PILR26     .EQU 0x000E5A
_pilr27    .EQU 0x000E5B
PILR27     .EQU 0x000E5B
_pilr29    .EQU 0x000E5D
PILR29     .EQU 0x000E5D
_epilr00   .EQU 0x000E80
EPILR00    .EQU 0x000E80 /* R-bus Port Extra Input Level Select Register */
_epilr01   .EQU 0x000E81
EPILR01    .EQU 0x000E81
_epilr02   .EQU 0x000E82
EPILR02    .EQU 0x000E82
_epilr03   .EQU 0x000E83
EPILR03    .EQU 0x000E83
_epilr04   .EQU 0x000E84
EPILR04    .EQU 0x000E84
_epilr05   .EQU 0x000E85
EPILR05    .EQU 0x000E85
_epilr06   .EQU 0x000E86
EPILR06    .EQU 0x000E86
_epilr07   .EQU 0x000E87
EPILR07    .EQU 0x000E87
_epilr08   .EQU 0x000E88
EPILR08    .EQU 0x000E88
_epilr09   .EQU 0x000E89
EPILR09    .EQU 0x000E89
_epilr10   .EQU 0x000E8A
EPILR10    .EQU 0x000E8A
_epilr13   .EQU 0x000E8D
EPILR13    .EQU 0x000E8D
_epilr14   .EQU 0x000E8E
EPILR14    .EQU 0x000E8E
_epilr15   .EQU 0x000E8F
EPILR15    .EQU 0x000E8F
_epilr16   .EQU 0x000E80
EPILR16    .EQU 0x000E80
_epilr17   .EQU 0x000E81
EPILR17    .EQU 0x000E81
_epilr18   .EQU 0x000E82
EPILR18    .EQU 0x000E82
_epilr19   .EQU 0x000E83
EPILR19    .EQU 0x000E83
_epilr20   .EQU 0x000E84
EPILR20    .EQU 0x000E84
_epilr22   .EQU 0x000E86
EPILR22    .EQU 0x000E86
_epilr23   .EQU 0x000E87
EPILR23    .EQU 0x000E87
_epilr24   .EQU 0x000E88
EPILR24    .EQU 0x000E88
_epilr25   .EQU 0x000E89
EPILR25    .EQU 0x000E89
_epilr26   .EQU 0x000E8A
EPILR26    .EQU 0x000E8A
_epilr27   .EQU 0x000E8B
EPILR27    .EQU 0x000E8B
_epilr29   .EQU 0x000E8D
EPILR29    .EQU 0x000E8D
_pper00    .EQU 0x000EC0
PPER00     .EQU 0x000EC0 /* R-bus Port Pull-Up/Down  Enable Register */
_pper01    .EQU 0x000EC1
PPER01     .EQU 0x000EC1
_pper02    .EQU 0x000EC2
PPER02     .EQU 0x000EC2
_pper03    .EQU 0x000EC3
PPER03     .EQU 0x000EC3
_pper04    .EQU 0x000EC4
PPER04     .EQU 0x000EC4
_pper05    .EQU 0x000EC5
PPER05     .EQU 0x000EC5
_pper06    .EQU 0x000EC6
PPER06     .EQU 0x000EC6
_pper07    .EQU 0x000EC7
PPER07     .EQU 0x000EC7
_pper08    .EQU 0x000EC8
PPER08     .EQU 0x000EC8
_pper09    .EQU 0x000EC9
PPER09     .EQU 0x000EC9
_pper10    .EQU 0x000ECA
PPER10     .EQU 0x000ECA
_pper13    .EQU 0x000ECD
PPER13     .EQU 0x000ECD
_pper14    .EQU 0x000ECE
PPER14     .EQU 0x000ECE
_pper15    .EQU 0x000ECF
PPER15     .EQU 0x000ECF
_pper16    .EQU 0x000ED0
PPER16     .EQU 0x000ED0
_pper17    .EQU 0x000ED1
PPER17     .EQU 0x000ED1
_pper18    .EQU 0x000ED2
PPER18     .EQU 0x000ED2
_pper19    .EQU 0x000ED3
PPER19     .EQU 0x000ED3
_pper20    .EQU 0x000ED4
PPER20     .EQU 0x000ED4
_pper22    .EQU 0x000ED6
PPER22     .EQU 0x000ED6
_pper23    .EQU 0x000ED7
PPER23     .EQU 0x000ED7
_pper24    .EQU 0x000ED8
PPER24     .EQU 0x000ED8
_pper25    .EQU 0x000ED9
PPER25     .EQU 0x000ED9
_pper26    .EQU 0x000EDA
PPER26     .EQU 0x000EDA
_pper27    .EQU 0x000EDB
PPER27     .EQU 0x000EDB
_pper29    .EQU 0x000EDD
PPER29     .EQU 0x000EDD
_ppcr00    .EQU 0x000F00
PPCR00     .EQU 0x000F00 /* R-bus Port Pull-Up/Down Control Register */
_ppcr01    .EQU 0x000F01
PPCR01     .EQU 0x000F01
_ppcr02    .EQU 0x000F02
PPCR02     .EQU 0x000F02
_ppcr03    .EQU 0x000F03
PPCR03     .EQU 0x000F03
_ppcr04    .EQU 0x000F04
PPCR04     .EQU 0x000F04
_ppcr05    .EQU 0x000F05
PPCR05     .EQU 0x000F05
_ppcr06    .EQU 0x000F06
PPCR06     .EQU 0x000F06
_ppcr07    .EQU 0x000F07
PPCR07     .EQU 0x000F07
_ppcr08    .EQU 0x000F08
PPCR08     .EQU 0x000F08
_ppcr09    .EQU 0x000F09
PPCR09     .EQU 0x000F09
_ppcr10    .EQU 0x000F0A
PPCR10     .EQU 0x000F0A
_ppcr13    .EQU 0x000F0D
PPCR13     .EQU 0x000F0D
_ppcr14    .EQU 0x000F0E
PPCR14     .EQU 0x000F0E
_ppcr15    .EQU 0x000F0F
PPCR15     .EQU 0x000F0F
_ppcr16    .EQU 0x000F10
PPCR16     .EQU 0x000F10
_ppcr17    .EQU 0x000F11
PPCR17     .EQU 0x000F11
_ppcr18    .EQU 0x000F12
PPCR18     .EQU 0x000F12
_ppcr19    .EQU 0x000F13
PPCR19     .EQU 0x000F13
_ppcr20    .EQU 0x000F14
PPCR20     .EQU 0x000F14
_ppcr22    .EQU 0x000F16
PPCR22     .EQU 0x000F16
_ppcr23    .EQU 0x000F17
PPCR23     .EQU 0x000F17
_ppcr24    .EQU 0x000F18
PPCR24     .EQU 0x000F18
_ppcr25    .EQU 0x000F19
PPCR25     .EQU 0x000F19
_ppcr26    .EQU 0x000F1A
PPCR26     .EQU 0x000F1A
_ppcr27    .EQU 0x000F1B
PPCR27     .EQU 0x000F1B
_ppcr29    .EQU 0x000F1D
PPCR29     .EQU 0x000F1D
_dmasa0    .EQU 0x001000
DMASA0     .EQU 0x001000 /* DMAC */
_dmada0    .EQU 0x001004
DMADA0     .EQU 0x001004
_dmasa1    .EQU 0x001008
DMASA1     .EQU 0x001008
_dmada1    .EQU 0x00100C
DMADA1     .EQU 0x00100C
_dmasa2    .EQU 0x001010
DMASA2     .EQU 0x001010
_dmada2    .EQU 0x001014
DMADA2     .EQU 0x001014
_dmasa3    .EQU 0x001018
DMASA3     .EQU 0x001018
_dmada3    .EQU 0x00101C
DMADA3     .EQU 0x00101C
_dmasa4    .EQU 0x001020
DMASA4     .EQU 0x001020
_dmada4    .EQU 0x001024
DMADA4     .EQU 0x001024
_fmcs      .EQU 0x007000
FMCS       .EQU 0x007000 /* Flash Memory/I-Cache Control Register */
_fmcr      .EQU 0x007001
FMCR       .EQU 0x007001
_fchcr     .EQU 0x007002
FCHCR      .EQU 0x007002
_fmwt      .EQU 0x007004
FMWT       .EQU 0x007004
_fmwt2     .EQU 0x007006
FMWT2      .EQU 0x007006
_fmps      .EQU 0x007007
FMPS       .EQU 0x007007
_fmac      .EQU 0x007008
FMAC       .EQU 0x007008
_fcha0     .EQU 0x00700C
FCHA0      .EQU 0x00700C /* I_Cache Nonchachable area settings Register */
_fcha1     .EQU 0x007010
FCHA1      .EQU 0x007010
_fscr0     .EQU 0x007100
FSCR0      .EQU 0x007100 /* Flash Security Control Register */
_fscr1     .EQU 0x007104
FSCR1      .EQU 0x007104
_ctrlr0    .EQU 0x00C000
CTRLR0     .EQU 0x00C000 /* CAN 0 Control Register */
_statr0    .EQU 0x00C002
STATR0     .EQU 0x00C002
_errcnt0   .EQU 0x00C004
ERRCNT0    .EQU 0x00C004
_btr0  .EQU 0x00C006
BTR0   .EQU 0x00C006
_intr0     .EQU 0x00C008
INTR0      .EQU 0x00C008
_testr0    .EQU 0x00C00A
TESTR0     .EQU 0x00C00A
_brper0    .EQU 0x00C00C
BRPER0     .EQU 0x00C00C
_brpe0     .EQU 0x00C00C
BRPE0      .EQU 0x00C00C
_cbsync0   .EQU 0x00C00E
CBSYNC0    .EQU 0x00C00E
_if1creq0  .EQU 0x00C010
IF1CREQ0   .EQU 0x00C010 /* CAN 0 IF 1 */
_if1cmsk0  .EQU 0x00C012
IF1CMSK0   .EQU 0x00C012
_if1msk120  .EQU 0x00C014
IF1MSK120   .EQU 0x00C014
_if1msk20  .EQU 0x00C014
IF1MSK20   .EQU 0x00C014
_if1msk10  .EQU 0x00C016
IF1MSK10   .EQU 0x00C016
_if1arb120  .EQU 0x00C018
IF1ARB120   .EQU 0x00C018
_if1arb20  .EQU 0x00C018
IF1ARB20   .EQU 0x00C018
_if1arb10  .EQU 0x00C01A
IF1ARB10   .EQU 0x00C01A
_if1mctr0  .EQU 0x00C01C
IF1MCTR0   .EQU 0x00C01C
_if1dta120  .EQU 0x00C020
IF1DTA120   .EQU 0x00C020
_if1dta10  .EQU 0x00C020
IF1DTA10   .EQU 0x00C020
_if1dta20  .EQU 0x00C022
IF1DTA20   .EQU 0x00C022
_if1dtb120  .EQU 0x00C024
IF1DTB120   .EQU 0x00C024
_if1dtb10  .EQU 0x00C024
IF1DTB10   .EQU 0x00C024
_if1dtb20  .EQU 0x00C026
IF1DTB20   .EQU 0x00C026
_if1dta_swp120  .EQU 0x00C030
IF1DTA_SWP120   .EQU 0x00C030
_if1dta_swp20  .EQU 0x00C030
IF1DTA_SWP20   .EQU 0x00C030
_if1dta_swp10  .EQU 0x00C032
IF1DTA_SWP10   .EQU 0x00C032
_if1dtb_swp120  .EQU 0x00C034
IF1DTB_SWP120   .EQU 0x00C034
_if1dtb_swp20  .EQU 0x00C034
IF1DTB_SWP20   .EQU 0x00C034
_if1dtb_swp10  .EQU 0x00C036
IF1DTB_SWP10   .EQU 0x00C036
_if2creq0  .EQU 0x00C040
IF2CREQ0   .EQU 0x00C040 /* CAN 0 IF 2 */
_if2cmsk0  .EQU 0x00C042
IF2CMSK0   .EQU 0x00C042
_if2msk120  .EQU 0x00C044
IF2MSK120   .EQU 0x00C044
_if2msk20  .EQU 0x00C044
IF2MSK20   .EQU 0x00C044
_if2msk10  .EQU 0x00C046
IF2MSK10   .EQU 0x00C046
_if2arb120  .EQU 0x00C048
IF2ARB120   .EQU 0x00C048
_if2arb20  .EQU 0x00C048
IF2ARB20   .EQU 0x00C048
_if2arb10  .EQU 0x00C04A
IF2ARB10   .EQU 0x00C04A
_if2mctr0  .EQU 0x00C04C
IF2MCTR0   .EQU 0x00C04C
_if2dta120  .EQU 0x00C050
IF2DTA120   .EQU 0x00C050
_if2dta10  .EQU 0x00C050
IF2DTA10   .EQU 0x00C050
_if2dta20  .EQU 0x00C052
IF2DTA20   .EQU 0x00C052
_if2dtb120  .EQU 0x00C054
IF2DTB120   .EQU 0x00C054
_if2dtb10  .EQU 0x00C054
IF2DTB10   .EQU 0x00C054
_if2dtb20  .EQU 0x00C056
IF2DTB20   .EQU 0x00C056
_if2dta_swp120  .EQU 0x00C060
IF2DTA_SWP120   .EQU 0x00C060
_if2dta_swp20  .EQU 0x00C060
IF2DTA_SWP20   .EQU 0x00C060
_if2dta_swp10  .EQU 0x00C062
IF2DTA_SWP10   .EQU 0x00C062
_if2dtb_swp120  .EQU 0x00C064
IF2DTB_SWP120   .EQU 0x00C064
_if2dtb_swp20  .EQU 0x00C064
IF2DTB_SWP20   .EQU 0x00C064
_if2dtb_swp10  .EQU 0x00C066
IF2DTB_SWP10   .EQU 0x00C066
_treqr120  .EQU 0x00C080
TREQR120   .EQU 0x00C080 /* CAN 0 Status Flags */
_treqr20   .EQU 0x00C080
TREQR20    .EQU 0x00C080
_treqr10   .EQU 0x00C082
TREQR10    .EQU 0x00C082
_newdt120  .EQU 0x00C090
NEWDT120   .EQU 0x00C090
_newdt20   .EQU 0x00C090
NEWDT20    .EQU 0x00C090
_newdt10   .EQU 0x00C092
NEWDT10    .EQU 0x00C092
_intpnd120  .EQU 0x00C0A0
INTPND120   .EQU 0x00C0A0
_intpnd20  .EQU 0x00C0A0
INTPND20   .EQU 0x00C0A0
_intpnd10  .EQU 0x00C0A2
INTPND10   .EQU 0x00C0A2
_msgval120  .EQU 0x00C0B0
MSGVAL120   .EQU 0x00C0B0
_msgval20  .EQU 0x00C0B0
MSGVAL20   .EQU 0x00C0B0
_msgval10  .EQU 0x00C0B2
MSGVAL10   .EQU 0x00C0B2
_msgval340  .EQU 0x00C0B4
MSGVAL340   .EQU 0x00C0B4
_ctrlr1    .EQU 0x00C100
CTRLR1     .EQU 0x00C100 /* CAN 1 Control Register */
_statr1    .EQU 0x00C102
STATR1     .EQU 0x00C102
_errcnt1   .EQU 0x00C104
ERRCNT1    .EQU 0x00C104
_btr1  .EQU 0x00C106
BTR1   .EQU 0x00C106
_intr1     .EQU 0x00C108
INTR1      .EQU 0x00C108
_testr1    .EQU 0x00C10A
TESTR1     .EQU 0x00C10A
_brper1    .EQU 0x00C10C
BRPER1     .EQU 0x00C10C
_brpe1     .EQU 0x00C10C
BRPE1      .EQU 0x00C10C
_cbsync1   .EQU 0x00C10E
CBSYNC1    .EQU 0x00C10E
_if1creq1  .EQU 0x00C110
IF1CREQ1   .EQU 0x00C110 /* CAN 1 IF 1 */
_if1cmsk1  .EQU 0x00C112
IF1CMSK1   .EQU 0x00C112
_if1msk121  .EQU 0x00C114
IF1MSK121   .EQU 0x00C114
_if1msk21  .EQU 0x00C114
IF1MSK21   .EQU 0x00C114
_if1msk11  .EQU 0x00C116
IF1MSK11   .EQU 0x00C116
_if1arb121  .EQU 0x00C118
IF1ARB121   .EQU 0x00C118
_if1arb21  .EQU 0x00C118
IF1ARB21   .EQU 0x00C118
_if1arb11  .EQU 0x00C11A
IF1ARB11   .EQU 0x00C11A
_if1mctr1  .EQU 0x00C11C
IF1MCTR1   .EQU 0x00C11C
_if1dta121  .EQU 0x00C120
IF1DTA121   .EQU 0x00C120
_if1dta11  .EQU 0x00C120
IF1DTA11   .EQU 0x00C120
_if1dta21  .EQU 0x00C122
IF1DTA21   .EQU 0x00C122
_if1dtb121  .EQU 0x00C124
IF1DTB121   .EQU 0x00C124
_if1dtb11  .EQU 0x00C124
IF1DTB11   .EQU 0x00C124
_if1dtb21  .EQU 0x00C126
IF1DTB21   .EQU 0x00C126
_if1dta_swp121  .EQU 0x00C130
IF1DTA_SWP121   .EQU 0x00C130
_if1dta_swp21  .EQU 0x00C130
IF1DTA_SWP21   .EQU 0x00C130
_if1dta_swp11  .EQU 0x00C132
IF1DTA_SWP11   .EQU 0x00C132
_if1dtb_swp121  .EQU 0x00C134
IF1DTB_SWP121   .EQU 0x00C134
_if1dtb_swp21  .EQU 0x00C134
IF1DTB_SWP21   .EQU 0x00C134
_if1dtb_swp11  .EQU 0x00C136
IF1DTB_SWP11   .EQU 0x00C136
_if2creq1  .EQU 0x00C140
IF2CREQ1   .EQU 0x00C140 /* CAN 1 IF 2 */
_if2cmsk1  .EQU 0x00C142
IF2CMSK1   .EQU 0x00C142
_if2msk121  .EQU 0x00C144
IF2MSK121   .EQU 0x00C144
_if2msk21  .EQU 0x00C144
IF2MSK21   .EQU 0x00C144
_if2msk11  .EQU 0x00C146
IF2MSK11   .EQU 0x00C146
_if2arb121  .EQU 0x00C148
IF2ARB121   .EQU 0x00C148
_if2arb21  .EQU 0x00C148
IF2ARB21   .EQU 0x00C148
_if2arb11  .EQU 0x00C14A
IF2ARB11   .EQU 0x00C14A
_if2mctr1  .EQU 0x00C14C
IF2MCTR1   .EQU 0x00C14C
_if2dta121  .EQU 0x00C150
IF2DTA121   .EQU 0x00C150
_if2dta11  .EQU 0x00C150
IF2DTA11   .EQU 0x00C150
_if2dta21  .EQU 0x00C152
IF2DTA21   .EQU 0x00C152
_if2dtb121  .EQU 0x00C154
IF2DTB121   .EQU 0x00C154
_if2dtb11  .EQU 0x00C154
IF2DTB11   .EQU 0x00C154
_if2dtb21  .EQU 0x00C156
IF2DTB21   .EQU 0x00C156
_if2dta_swp121  .EQU 0x00C160
IF2DTA_SWP121   .EQU 0x00C160
_if2dta_swp21  .EQU 0x00C160
IF2DTA_SWP21   .EQU 0x00C160
_if2dta_swp11  .EQU 0x00C162
IF2DTA_SWP11   .EQU 0x00C162
_if2dtb_swp121  .EQU 0x00C164
IF2DTB_SWP121   .EQU 0x00C164
_if2dtb_swp21  .EQU 0x00C164
IF2DTB_SWP21   .EQU 0x00C164
_if2dtb_swp11  .EQU 0x00C166
IF2DTB_SWP11   .EQU 0x00C166
_treqr121  .EQU 0x00C180
TREQR121   .EQU 0x00C180 /* CAN 1 Status Flags */
_treqr21   .EQU 0x00C180
TREQR21    .EQU 0x00C180
_treqr11   .EQU 0x00C182
TREQR11    .EQU 0x00C182
_newdt121  .EQU 0x00C190
NEWDT121   .EQU 0x00C190
_newdt21   .EQU 0x00C190
NEWDT21    .EQU 0x00C190
_newdt11   .EQU 0x00C192
NEWDT11    .EQU 0x00C192
_intpnd121  .EQU 0x00C1A0
INTPND121   .EQU 0x00C1A0
_intpnd21  .EQU 0x00C1A0
INTPND21   .EQU 0x00C1A0
_intpnd11  .EQU 0x00C1A2
INTPND11   .EQU 0x00C1A2
_msgval121  .EQU 0x00C1B0
MSGVAL121   .EQU 0x00C1B0
_msgval21  .EQU 0x00C1B0
MSGVAL21   .EQU 0x00C1B0
_msgval11  .EQU 0x00C1B2
MSGVAL11   .EQU 0x00C1B2
_ctrlr2    .EQU 0x00C200
CTRLR2     .EQU 0x00C200 /* CAN 2 Control Register */
_statr2    .EQU 0x00C202
STATR2     .EQU 0x00C202
_errcnt2   .EQU 0x00C204
ERRCNT2    .EQU 0x00C204
_btr2  .EQU 0x00C206
BTR2   .EQU 0x00C206
_intr2     .EQU 0x00C208
INTR2      .EQU 0x00C208
_testr2    .EQU 0x00C20A
TESTR2     .EQU 0x00C20A
_brper2    .EQU 0x00C20C
BRPER2     .EQU 0x00C20C
_brpe2     .EQU 0x00C20C
BRPE2      .EQU 0x00C20C
_cbsync2   .EQU 0x00C20E
CBSYNC2    .EQU 0x00C20E
_if1creq2  .EQU 0x00C210
IF1CREQ2   .EQU 0x00C210 /* CAN 2 IF 1 */
_if1cmsk2  .EQU 0x00C212
IF1CMSK2   .EQU 0x00C212
_if1msk122  .EQU 0x00C214
IF1MSK122   .EQU 0x00C214
_if1msk22  .EQU 0x00C214
IF1MSK22   .EQU 0x00C214
_if1msk12  .EQU 0x00C216
IF1MSK12   .EQU 0x00C216
_if1arb122  .EQU 0x00C218
IF1ARB122   .EQU 0x00C218
_if1arb22  .EQU 0x00C218
IF1ARB22   .EQU 0x00C218
_if1arb12  .EQU 0x00C21A
IF1ARB12   .EQU 0x00C21A
_if1mctr2  .EQU 0x00C21C
IF1MCTR2   .EQU 0x00C21C
_if1dta122  .EQU 0x00C220
IF1DTA122   .EQU 0x00C220
_if1dta12  .EQU 0x00C220
IF1DTA12   .EQU 0x00C220
_if1dta22  .EQU 0x00C222
IF1DTA22   .EQU 0x00C222
_if1dtb122  .EQU 0x00C224
IF1DTB122   .EQU 0x00C224
_if1dtb12  .EQU 0x00C224
IF1DTB12   .EQU 0x00C224
_if1dtb22  .EQU 0x00C226
IF1DTB22   .EQU 0x00C226
_if1dta_swp122  .EQU 0x00C230
IF1DTA_SWP122   .EQU 0x00C230
_if1dta_swp22  .EQU 0x00C230
IF1DTA_SWP22   .EQU 0x00C230
_if1dta_swp12  .EQU 0x00C232
IF1DTA_SWP12   .EQU 0x00C232
_if1dtb_swp122  .EQU 0x00C234
IF1DTB_SWP122   .EQU 0x00C234
_if1dtb_swp22  .EQU 0x00C234
IF1DTB_SWP22   .EQU 0x00C234
_if1dtb_swp12  .EQU 0x00C236
IF1DTB_SWP12   .EQU 0x00C236
_if2creq2  .EQU 0x00C240
IF2CREQ2   .EQU 0x00C240 /* CAN 2 IF 2 */
_if2cmsk2  .EQU 0x00C242
IF2CMSK2   .EQU 0x00C242
_if2msk122  .EQU 0x00C244
IF2MSK122   .EQU 0x00C244
_if2msk22  .EQU 0x00C244
IF2MSK22   .EQU 0x00C244
_if2msk12  .EQU 0x00C246
IF2MSK12   .EQU 0x00C246
_if2arb122  .EQU 0x00C248
IF2ARB122   .EQU 0x00C248
_if2arb22  .EQU 0x00C248
IF2ARB22   .EQU 0x00C248
_if2arb12  .EQU 0x00C24A
IF2ARB12   .EQU 0x00C24A
_if2mctr2  .EQU 0x00C24C
IF2MCTR2   .EQU 0x00C24C
_if2dta122  .EQU 0x00C250
IF2DTA122   .EQU 0x00C250
_if2dta12  .EQU 0x00C250
IF2DTA12   .EQU 0x00C250
_if2dta22  .EQU 0x00C252
IF2DTA22   .EQU 0x00C252
_if2dtb122  .EQU 0x00C254
IF2DTB122   .EQU 0x00C254
_if2dtb12  .EQU 0x00C254
IF2DTB12   .EQU 0x00C254
_if2dtb22  .EQU 0x00C256
IF2DTB22   .EQU 0x00C256
_if2dta_swp122  .EQU 0x00C260
IF2DTA_SWP122   .EQU 0x00C260
_if2dta_swp22  .EQU 0x00C260
IF2DTA_SWP22   .EQU 0x00C260
_if2dta_swp12  .EQU 0x00C262
IF2DTA_SWP12   .EQU 0x00C262
_if2dtb_swp122  .EQU 0x00C264
IF2DTB_SWP122   .EQU 0x00C264
_if2dtb_swp22  .EQU 0x00C264
IF2DTB_SWP22   .EQU 0x00C264
_if2dtb_swp12  .EQU 0x00C266
IF2DTB_SWP12   .EQU 0x00C266
_treqr122  .EQU 0x00C280
TREQR122   .EQU 0x00C280 /* CAN 2 Status Flags */
_treqr22   .EQU 0x00C280
TREQR22    .EQU 0x00C280
_treqr12   .EQU 0x00C282
TREQR12    .EQU 0x00C282
_newdt122  .EQU 0x00C290
NEWDT122   .EQU 0x00C290
_newdt22   .EQU 0x00C290
NEWDT22    .EQU 0x00C290
_newdt12   .EQU 0x00C292
NEWDT12    .EQU 0x00C292
_intpnd122  .EQU 0x00C2A0
INTPND122   .EQU 0x00C2A0
_intpnd22  .EQU 0x00C2A0
INTPND22   .EQU 0x00C2A0
_intpnd12  .EQU 0x00C2A2
INTPND12   .EQU 0x00C2A2
_msgval122  .EQU 0x00C2B0
MSGVAL122   .EQU 0x00C2B0
_msgval22  .EQU 0x00C2B0
MSGVAL22   .EQU 0x00C2B0
_msgval12  .EQU 0x00C2B2
MSGVAL12   .EQU 0x00C2B2
_bctrl     .EQU 0x00F000
BCTRL      .EQU 0x00F000 /* EDSU/MPU Registers */
_bstat     .EQU 0x00F004
BSTAT      .EQU 0x00F004
_biac      .EQU 0x00F008
BIAC       .EQU 0x00F008
_boac      .EQU 0x00F00C
BOAC       .EQU 0x00F00C
_birq      .EQU 0x00F010
BIRQ       .EQU 0x00F010
_bcr0      .EQU 0x00F020
BCR0       .EQU 0x00F020
_bcr1      .EQU 0x00F024
BCR1       .EQU 0x00F024
_bcr2      .EQU 0x00F028
BCR2       .EQU 0x00F028
_bcr3      .EQU 0x00F02C
BCR3       .EQU 0x00F02C
_bcr4      .EQU 0x00F030
BCR4       .EQU 0x00F030
_bcr5      .EQU 0x00F034
BCR5       .EQU 0x00F034
_bcr6      .EQU 0x00F038
BCR6       .EQU 0x00F038
_bcr7      .EQU 0x00F03C
BCR7       .EQU 0x00F03C
_bad0      .EQU 0x00F080
BAD0       .EQU 0x00F080
_bad1      .EQU 0x00F084
BAD1       .EQU 0x00F084
_bad2      .EQU 0x00F088
BAD2       .EQU 0x00F088
_bad3      .EQU 0x00F08C
BAD3       .EQU 0x00F08C
_bad4      .EQU 0x00F090
BAD4       .EQU 0x00F090
_bad5      .EQU 0x00F094
BAD5       .EQU 0x00F094
_bad6      .EQU 0x00F098
BAD6       .EQU 0x00F098
_bad7      .EQU 0x00F09C
BAD7       .EQU 0x00F09C
_bad8      .EQU 0x00F0A0
BAD8       .EQU 0x00F0A0
_bad9      .EQU 0x00F0A4
BAD9       .EQU 0x00F0A4
_bad10     .EQU 0x00F0A8
BAD10      .EQU 0x00F0A8
_bad11     .EQU 0x00F0AC
BAD11      .EQU 0x00F0AC
_bad12     .EQU 0x00F0B0
BAD12      .EQU 0x00F0B0
_bad13     .EQU 0x00F0B4
BAD13      .EQU 0x00F0B4
_bad14     .EQU 0x00F0B8
BAD14      .EQU 0x00F0B8
_bad15     .EQU 0x00F0BC
BAD15      .EQU 0x00F0BC
_fsv1      .EQU 0x148000
FSV1       .EQU 0x148000 /* FSV & BSV Registers */
_bsv1      .EQU 0x148004
BSV1       .EQU 0x148004
_fsv2      .EQU 0x148008
FSV2       .EQU 0x148008
_bsv2      .EQU 0x14800C
BSV2       .EQU 0x14800C
#pragma endasm
#else

#ifndef _MB91XXX_H
#define _MB91XXX_H

#ifdef  __FASM__ 
#pragma asm
 .IMPORT _pdr00,    _pdr01,    _pdr02,    _pdr03,    _pdr04,    _pdr05
 .IMPORT _pdr06,    _pdr07,    _pdr08,    _pdr09,    _pdr10,    _pdr13
 .IMPORT _pdr14,    _pdr15,    _pdr16,    _pdr17,    _pdr18,    _pdr19
 .IMPORT _pdr20,    _pdr22,    _pdr23,    _pdr24,    _pdr25,    _pdr26
 .IMPORT _pdr27,    _pdr29,    _eirr0,    _enir0,    _elvr0,    _eirr1
 .IMPORT _enir1,    _elvr1,    _dicr,     _hrcl,     _rbsync,   _scr02
 .IMPORT _smr02,    _ssr02,    _rdr02,    _tdr02,    _escr02,   _eccr02
 .IMPORT _scr04,    _smr04,    _ssr04,    _rdr04,    _tdr04,    _escr04
 .IMPORT _eccr04,   _fsr04,    _fcr04,    _scr05,    _smr05,    _ssr05
 .IMPORT _rdr05,    _tdr05,    _escr05,   _eccr05,   _fsr05,    _fcr05
 .IMPORT _scr06,    _smr06,    _ssr06,    _rdr06,    _tdr06,    _escr06
 .IMPORT _eccr06,   _fsr06,    _fcr06,    _scr07,    _smr07,    _ssr07
 .IMPORT _rdr07,    _tdr07,    _escr07,   _eccr07,   _fsr07,    _fcr07
 .IMPORT _bgr02,    _bgr102,   _bgr002,   _bgr04,    _bgr104,   _bgr004
 .IMPORT _bgr05,    _bgr105,   _bgr005,   _bgr06,    _bgr106,   _bgr006
 .IMPORT _bgr07,    _bgr107,   _bgr007,   _pwc20,    _pwc10,    _pws20
 .IMPORT _pws10,    _pwc21,    _pwc11,    _pws21,    _pws11,    _pwc22
 .IMPORT _pwc12,    _pws22,    _pws12,    _pwc23,    _pwc13,    _pws23
 .IMPORT _pws13,    _pwc24,    _pwc14,    _pws24,    _pws14,    _pwc25
 .IMPORT _pwc15,    _pws25,    _pws15,    _pwc0,     _pwc1,     _pwc2
 .IMPORT _pwc3,     _pwc4,     _pwc5,     _ibcr0,    _ibsr0,    _itba0
 .IMPORT _itbah0,   _itbal0,   _itmk0,    _itmkh0,   _itmkl0,   _ismk0
 .IMPORT _isba0,    _idar0,    _iccr0,    _gcn11,    _gcn21,    _gcn12
 .IMPORT _gcn22,    _ptmr04,   _pcsr04,   _pdut04,   _pcn04,    _pcnh04
 .IMPORT _pcnl04,   _ptmr05,   _pcsr05,   _pdut05,   _pcn05,    _pcnh05
 .IMPORT _pcnl05,   _ptmr06,   _pcsr06,   _pdut06,   _pcn06,    _pcnh06
 .IMPORT _pcnl06,   _ptmr07,   _pcsr07,   _pdut07,   _pcn07,    _pcnh07
 .IMPORT _pcnl07,   _ptmr08,   _pcsr08,   _pdut08,   _pcn08,    _pcnh08
 .IMPORT _pcnl08,   _ptmr09,   _pcsr09,   _pdut09,   _pcn09,    _pcnh09
 .IMPORT _pcnl09,   _ptmr10,   _pcsr10,   _pdut10,   _pcn10,    _pcnh10
 .IMPORT _pcnl10,   _ptmr11,   _pcsr11,   _pdut11,   _pcn11,    _pcnh11
 .IMPORT _pcnl11,   _p0tmcsr,  _p0tmcsrh, _p0tmcsrl, _p1tmcsr,  _p1tmcsrh
 .IMPORT _p1tmcsrl, _p0tmrlr,  _p0tmr,    _p1tmrlr,  _p1tmr,    _ics01
 .IMPORT _ics23,    _ipcp0,    _ipcp1,    _ipcp2,    _ipcp3,    _ocs01
 .IMPORT _ocs23,    _occp0,    _occp1,    _occp2,    _occp3,    _sgcr
 .IMPORT _sgcrh,    _sgcrl,    _sgfr,     _sgar,     _sgtr,     _sgdr
 .IMPORT _aderh,    _aderl,    _ader,     _adcs1,    _adcs0,    _adcs
 .IMPORT _adcr1,    _adcr0,    _adcr,     _adct1,    _adct0,    _adct
 .IMPORT _adsch,    _adech,    _acsr0,    _tmrlr0,   _tmr0,     _tmcsr0
 .IMPORT _tmcsrh0,  _tmcsrl0,  _tmrlr1,   _tmr1,     _tmcsr1,   _tmcsrh1
 .IMPORT _tmcsrl1,  _tmrlr2,   _tmr2,     _tmcsr2,   _tmcsrh2,  _tmcsrl2
 .IMPORT _tmrlr3,   _tmr3,     _tmcsr3,   _tmcsrh3,  _tmcsrl3,  _tmrlr4
 .IMPORT _tmr4,     _tmcsr4,   _tmcsrh4,  _tmcsrl4,  _tmrlr5,   _tmr5
 .IMPORT _tmcsr5,   _tmcsrh5,  _tmcsrl5,  _tmrlr6,   _tmr6,     _tmcsr6
 .IMPORT _tmcsrh6,  _tmcsrl6,  _tmrlr7,   _tmr7,     _tmcsr7,   _tmcsrh7
 .IMPORT _tmcsrl7,  _tcdt0,    _tccs0,    _tcdt1,    _tccs1,    _tcdt2
 .IMPORT _tccs2,    _tcdt3,    _tccs3,    _dmaca0,   _dmacb0,   _dmaca1
 .IMPORT _dmacb1,   _dmaca2,   _dmacb2,   _dmaca3,   _dmacb3,   _dmaca4
 .IMPORT _dmacb4,   _dmacr,    _ics45,    _ics67,    _ipcp4,    _ipcp5
 .IMPORT _ipcp6,    _ipcp7,    _tcdt4,    _tccs4,    _tcdt5,    _tccs5
 .IMPORT _tcdt6,    _tccs6,    _tcdt7,    _tccs7,    _udrc10,   _udrc1
 .IMPORT _udrc0,    _udcr10,   _udcr1,    _udcr0,    _udcc0,    _udcch0
 .IMPORT _udccl0,   _udcs0,    _udcc1,    _udcch1,   _udccl1,   _udcs1
 .IMPORT _udrc32,   _udrc3,    _udrc2,    _udcr32,   _udcr3,    _udcr2
 .IMPORT _udcc2,    _udcch2,   _udccl2,   _udcs2,    _udcc3,    _udcch3
 .IMPORT _udccl3,   _udcs3,    _gcn13,    _gcn23,    _ptmr12,   _pcsr12
 .IMPORT _pdut12,   _pcn12,    _pcnh12,   _pcnl12,   _ptmr13,   _pcsr13
 .IMPORT _pdut13,   _pcn13,    _pcnh13,   _pcnl13,   _ptmr14,   _pcsr14
 .IMPORT _pdut14,   _pcn14,    _pcnh14,   _pcnl14,   _ptmr15,   _pcsr15
 .IMPORT _pdut15,   _pcn15,    _pcnh15,   _pcnl15,   _ibcr2,    _ibsr2
 .IMPORT _itba2,    _itbah2,   _itbal2,   _itmk2,    _itmkh2,   _itmkl2
 .IMPORT _ismk2,    _isba2,    _idar2,    _iccr2,    _ibcr3,    _ibsr3
 .IMPORT _itba3,    _itbah3,   _itbal3,   _itmk3,    _itmkh3,   _itmkl3
 .IMPORT _ismk3,    _isba3,    _idar3,    _iccr3,    _roms,     _bsd0
 .IMPORT _bsd1,     _bsdc,     _bsrr,     _icr00,    _icr01,    _icr02
 .IMPORT _icr03,    _icr04,    _icr05,    _icr06,    _icr07,    _icr08
 .IMPORT _icr09,    _icr10,    _icr11,    _icr12,    _icr13,    _icr14
 .IMPORT _icr15,    _icr16,    _icr17,    _icr18,    _icr19,    _icr20
 .IMPORT _icr21,    _icr22,    _icr23,    _icr24,    _icr25,    _icr26
 .IMPORT _icr27,    _icr28,    _icr29,    _icr30,    _icr31,    _icr32
 .IMPORT _icr33,    _icr34,    _icr35,    _icr36,    _icr37,    _icr38
 .IMPORT _icr39,    _icr40,    _icr41,    _icr42,    _icr43,    _icr44
 .IMPORT _icr45,    _icr46,    _icr47,    _icr48,    _icr49,    _icr50
 .IMPORT _icr51,    _icr52,    _icr53,    _icr54,    _icr55,    _icr56
 .IMPORT _icr57,    _icr58,    _icr59,    _icr60,    _icr61,    _icr62
 .IMPORT _icr63,    _rsrr,     _stcr,     _tbcr,     _ctbr,     _clkr
 .IMPORT _wpr,      _divr0,    _divr1,    _plldivm,  _plldivn,  _plldivg
 .IMPORT _pllmulg,  _pllctrl,  _oscc1,    _oscs1,    _oscc2,    _oscs2
 .IMPORT _porten,   _wtcer,    _wtcr,     _wtbr,     _wthr,     _wtmr
 .IMPORT _wtsr,     _csvtr,    _csvcr,    _cscfg,    _cmcfg,    _cucr
 .IMPORT _cutd,     _cutr1,    _cutr2,    _cmpr,     _cmcr,     _cmt1
 .IMPORT _cmt2,     _canpre,   _canckd,   _lvsel,    _lvdet,    _hwwde
 .IMPORT _hwwd,     _oscrh,    _oscrl,    _wpcrh,    _wpcrl,    _osccr
 .IMPORT _regsel,   _regctr,   _asr0,     _acr0,     _asr1,     _acr1
 .IMPORT _asr2,     _acr2,     _asr3,     _acr3,     _asr4,     _acr4
 .IMPORT _asr5,     _acr5,     _asr6,     _acr6,     _asr7,     _acr7
 .IMPORT _awr0,     _awr1,     _awr2,     _awr3,     _awr4,     _awr5
 .IMPORT _awr6,     _awr7,     _mcra,     _mcrb,     _iowr0,    _iowr1
 .IMPORT _iowr2,    _iowr3,    _cser,     _cher,     _tcr,      _rcr
 .IMPORT _modr,     _pdrd00,   _pdrd01,   _pdrd02,   _pdrd03,   _pdrd04
 .IMPORT _pdrd05,   _pdrd06,   _pdrd07,   _pdrd08,   _pdrd09,   _pdrd10
 .IMPORT _pdrd13,   _pdrd14,   _pdrd15,   _pdrd16,   _pdrd17,   _pdrd18
 .IMPORT _pdrd19,   _pdrd20,   _pdrd22,   _pdrd23,   _pdrd24,   _pdrd25
 .IMPORT _pdrd26,   _pdrd27,   _pdrd29,   _ddr00,    _ddr01,    _ddr02
 .IMPORT _ddr03,    _ddr04,    _ddr05,    _ddr06,    _ddr07,    _ddr08
 .IMPORT _ddr09,    _ddr10,    _ddr13,    _ddr14,    _ddr15,    _ddr16
 .IMPORT _ddr17,    _ddr18,    _ddr19,    _ddr20,    _ddr22,    _ddr23
 .IMPORT _ddr24,    _ddr25,    _ddr26,    _ddr27,    _ddr29,    _pfr00
 .IMPORT _pfr01,    _pfr02,    _pfr03,    _pfr04,    _pfr05,    _pfr06
 .IMPORT _pfr07,    _pfr08,    _pfr09,    _pfr10,    _pfr13,    _pfr14
 .IMPORT _pfr15,    _pfr16,    _pfr17,    _pfr18,    _pfr19,    _pfr20
 .IMPORT _pfr22,    _pfr23,    _pfr24,    _pfr25,    _pfr26,    _pfr27
 .IMPORT _pfr29,    _epfr10,   _epfr13,   _epfr14,   _epfr15,   _epfr16
 .IMPORT _epfr18,   _epfr19,   _epfr20,   _epfr26,   _epfr27,   _podr00
 .IMPORT _podr01,   _podr02,   _podr03,   _podr04,   _podr05,   _podr06
 .IMPORT _podr07,   _podr08,   _podr09,   _podr10,   _podr13,   _podr14
 .IMPORT _podr15,   _podr16,   _podr17,   _podr18,   _podr19,   _podr20
 .IMPORT _podr22,   _podr23,   _podr24,   _podr25,   _podr26,   _podr27
 .IMPORT _podr29,   _pilr00,   _pilr01,   _pilr02,   _pilr03,   _pilr04
 .IMPORT _pilr05,   _pilr06,   _pilr07,   _pilr08,   _pilr09,   _pilr10
 .IMPORT _pilr13,   _pilr14,   _pilr15,   _pilr16,   _pilr17,   _pilr18
 .IMPORT _pilr19,   _pilr20,   _pilr22,   _pilr23,   _pilr24,   _pilr25
 .IMPORT _pilr26,   _pilr27,   _pilr29,   _epilr00,  _epilr01,  _epilr02
 .IMPORT _epilr03,  _epilr04,  _epilr05,  _epilr06,  _epilr07,  _epilr08
 .IMPORT _epilr09,  _epilr10,  _epilr13,  _epilr14,  _epilr15,  _epilr16
 .IMPORT _epilr17,  _epilr18,  _epilr19,  _epilr20,  _epilr22,  _epilr23
 .IMPORT _epilr24,  _epilr25,  _epilr26,  _epilr27,  _epilr29,  _pper00
 .IMPORT _pper01,   _pper02,   _pper03,   _pper04,   _pper05,   _pper06
 .IMPORT _pper07,   _pper08,   _pper09,   _pper10,   _pper13,   _pper14
 .IMPORT _pper15,   _pper16,   _pper17,   _pper18,   _pper19,   _pper20
 .IMPORT _pper22,   _pper23,   _pper24,   _pper25,   _pper26,   _pper27
 .IMPORT _pper29,   _ppcr00,   _ppcr01,   _ppcr02,   _ppcr03,   _ppcr04
 .IMPORT _ppcr05,   _ppcr06,   _ppcr07,   _ppcr08,   _ppcr09,   _ppcr10
 .IMPORT _ppcr13,   _ppcr14,   _ppcr15,   _ppcr16,   _ppcr17,   _ppcr18
 .IMPORT _ppcr19,   _ppcr20,   _ppcr22,   _ppcr23,   _ppcr24,   _ppcr25
 .IMPORT _ppcr26,   _ppcr27,   _ppcr29,   _dmasa0,   _dmada0,   _dmasa1
 .IMPORT _dmada1,   _dmasa2,   _dmada2,   _dmasa3,   _dmada3,   _dmasa4
 .IMPORT _dmada4,   _fmcs,     _fmcr,     _fchcr,    _fmwt,     _fmwt2
 .IMPORT _fmps,     _fmac,     _fcha0,    _fcha1,    _fscr0,    _fscr1
 .IMPORT _ctrlr0,   _statr0,   _errcnt0,  _btr0,     _intr0,    _testr0
 .IMPORT _brper0,   _brpe0,    _cbsync0,  _if1creq0, _if1cmsk0, _if1msk120
 .IMPORT _if1msk20, _if1msk10, _if1arb120, _if1arb20, _if1arb10, _if1mctr0
 .IMPORT _if1dta120, _if1dta10, _if1dta20, _if1dtb120, _if1dtb10, _if1dtb20
 .IMPORT _if1dta_swp120, _if1dta_swp20, _if1dta_swp10, _if1dtb_swp120, _if1dtb_swp20, _if1dtb_swp10
 .IMPORT _if2creq0, _if2cmsk0, _if2msk120, _if2msk20, _if2msk10, _if2arb120
 .IMPORT _if2arb20, _if2arb10, _if2mctr0, _if2dta120, _if2dta10, _if2dta20
 .IMPORT _if2dtb120, _if2dtb10, _if2dtb20, _if2dta_swp120, _if2dta_swp20, _if2dta_swp10
 .IMPORT _if2dtb_swp120, _if2dtb_swp20, _if2dtb_swp10, _treqr120, _treqr20,  _treqr10
 .IMPORT _newdt120, _newdt20,  _newdt10,  _intpnd120, _intpnd20, _intpnd10
 .IMPORT _msgval120, _msgval20, _msgval10, _msgval340, _ctrlr1,   _statr1
 .IMPORT _errcnt1,  _btr1,     _intr1,    _testr1,   _brper1,   _brpe1
 .IMPORT _cbsync1,  _if1creq1, _if1cmsk1, _if1msk121, _if1msk21, _if1msk11
 .IMPORT _if1arb121, _if1arb21, _if1arb11, _if1mctr1, _if1dta121, _if1dta11
 .IMPORT _if1dta21, _if1dtb121, _if1dtb11, _if1dtb21, _if1dta_swp121, _if1dta_swp21
 .IMPORT _if1dta_swp11, _if1dtb_swp121, _if1dtb_swp21, _if1dtb_swp11, _if2creq1, _if2cmsk1
 .IMPORT _if2msk121, _if2msk21, _if2msk11, _if2arb121, _if2arb21, _if2arb11
 .IMPORT _if2mctr1, _if2dta121, _if2dta11, _if2dta21, _if2dtb121, _if2dtb11
 .IMPORT _if2dtb21, _if2dta_swp121, _if2dta_swp21, _if2dta_swp11, _if2dtb_swp121, _if2dtb_swp21
 .IMPORT _if2dtb_swp11, _treqr121, _treqr21,  _treqr11,  _newdt121, _newdt21
 .IMPORT _newdt11,  _intpnd121, _intpnd21, _intpnd11, _msgval121, _msgval21
 .IMPORT _msgval11, _ctrlr2,   _statr2,   _errcnt2,  _btr2,     _intr2
 .IMPORT _testr2,   _brper2,   _brpe2,    _cbsync2,  _if1creq2, _if1cmsk2
 .IMPORT _if1msk122, _if1msk22, _if1msk12, _if1arb122, _if1arb22, _if1arb12
 .IMPORT _if1mctr2, _if1dta122, _if1dta12, _if1dta22, _if1dtb122, _if1dtb12
 .IMPORT _if1dtb22, _if1dta_swp122, _if1dta_swp22, _if1dta_swp12, _if1dtb_swp122, _if1dtb_swp22
 .IMPORT _if1dtb_swp12, _if2creq2, _if2cmsk2, _if2msk122, _if2msk22, _if2msk12
 .IMPORT _if2arb122, _if2arb22, _if2arb12, _if2mctr2, _if2dta122, _if2dta12
 .IMPORT _if2dta22, _if2dtb122, _if2dtb12, _if2dtb22, _if2dta_swp122, _if2dta_swp22
 .IMPORT _if2dta_swp12, _if2dtb_swp122, _if2dtb_swp22, _if2dtb_swp12, _treqr122, _treqr22
 .IMPORT _treqr12,  _newdt122, _newdt22,  _newdt12,  _intpnd122, _intpnd22
 .IMPORT _intpnd12, _msgval122, _msgval22, _msgval12, _bctrl,    _bstat
 .IMPORT _biac,     _boac,     _birq,     _bcr0,     _bcr1,     _bcr2
 .IMPORT _bcr3,     _bcr4,     _bcr5,     _bcr6,     _bcr7,     _bad0
 .IMPORT _bad1,     _bad2,     _bad3,     _bad4,     _bad5,     _bad6
 .IMPORT _bad7,     _bad8,     _bad9,     _bad10,    _bad11,    _bad12
 .IMPORT _bad13,    _bad14,    _bad15,    _fsv1,     _bsv1,     _fsv2
 .IMPORT _bsv2
#pragma endasm
#else  /* __FASM__  */ 
/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU     */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR     */
/* ELIGIBILITY FOR ANY PURPOSES.                                                 */
/*                 (C) Fujitsu Microelectronics Europe GmbH                      */
/*  */
/* ************************************************************************* */
/*                   Fujitsu Microelectronics Europe GmbH                        */
/*                 http://emea.fujitsu.com/microelectronics  */
/*                                                                           */
/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES                                              */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/* ************************************************************************* */
/* ---------------------------------------------------------------------- */
/* $Id: mb91467D.h,v 1.13 2007/08/08 10:56:26 mwilla Exp $ */
/* ---------------------------------------------------------------------- */
/*                      */
/* Id: mb91467D.iow,v 1.1 2005/10/14 11:25:42 umarke Exp  */
/*      - Initial Version based on mb91V460A, v1.1 */
/* Id: mb91467D.iow,v 1.2 2005/10/14 09:47:18 umarke Exp   */
/*      - Littel Endian IFxDTA_SWP_yz added     */
/* Id: mb91467D.iow,v 1.3 2005/11/18 06:55:29 umarke Exp   */
/*      - No. of port register reduced to the no. of registers in MB91467D */
/*      - Registers added: FMWT2, FMCR */
/*      - Addapted Bit Names of Register FMCS     */
/* Id: mb91467D.iow,v 1.4 2005/11/18 06:55:29 umarke Exp   */
/*      - OCS01 and OCS23 added         */
/* Id: mb91467D.iow,v 1.6 2006/01/13 08:58:51 umarke Exp  */
/*      - Bitnames of  CLKR changed                                                    */
/* Id: mb91467D.iow,v 1.7 2006/01/26 15:42:05 umarke Exp   */
/*      - REGSEL, BRPERx added */
/*      - REGCTR added   */
/*      - LVSEL added  */
/*      - Old Bitname of CLKR added                             */
/* Id: mb91467D.iow,v 1.8 2006/02/27 10:31:28 umarke Exp   */
/*      - BGR10x und BGR00x added  */
/*      - PCNx, ITBAx, ITMKx, IDARx_D7 added    */
/*      - SGCRH, SGCRL added */
/*      - Bit ACSR_MD added */
/*      - Bit CSCFG_PLLLOCK and CSCFG_RCSEL          */
/*      - CUCR: Bits shifted to correct position    */
/*      - CUTR1 & CUTR2 bits renamed to TDR14 instead of TR14     */
/*      - CMCR_RUN renamed to CMCR_FMODRUN and shifted               */
/*      - Bitnames of OSCCx and OSCRx added */
/*      - FSVx, BSVx and FSCRx added */
/*      - RBSYNC, CBSYNCx  */
/* Id: mb91467D.iow,v 1.9 2006/02/27 11:56:23 umarke Exp  */
/*      - changed Adress of REGSEL */
/* $Id: mb91467D.h,v 1.13 2007/08/08 10:56:26 mwilla Exp $  */
/*      - Grouped CANPRE_CPCKS */
/*      - Bitdescription of HLRC added */
/* BIT-STRUCTURE-DEFINITIONS */

typedef unsigned char		IO_BYTE;
typedef unsigned short		IO_WORD;
typedef unsigned long		IO_LWORD;
typedef const unsigned short	IO_WORD_READ;

typedef union{   /* Port Data Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }PDR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PDR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDR29STR;
typedef union{   /* External Interrupt 0-7 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ER7 :1;
    IO_BYTE _ER6 :1;
    IO_BYTE _ER5 :1;
    IO_BYTE _ER4 :1;
    IO_BYTE _ER3 :1;
    IO_BYTE _ER2 :1;
    IO_BYTE _ER1 :1;
    IO_BYTE _ER0 :1;
  }bit;
 }EIRR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EN7 :1;
    IO_BYTE _EN6 :1;
    IO_BYTE _EN5 :1;
    IO_BYTE _EN4 :1;
    IO_BYTE _EN3 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN0 :1;
  }bit;
 }ENIR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _LB7 :1;
    IO_WORD _LA7 :1;
    IO_WORD _LB6 :1;
    IO_WORD _LA6 :1;
    IO_WORD _LB5 :1;
    IO_WORD _LA5 :1;
    IO_WORD _LB4 :1;
    IO_WORD _LA4 :1;
    IO_WORD _LB3 :1;
    IO_WORD _LA3 :1;
    IO_WORD _LB2 :1;
    IO_WORD _LA2 :1;
    IO_WORD _LB1 :1;
    IO_WORD _LA1 :1;
    IO_WORD _LB0 :1;
    IO_WORD _LA0 :1;
  }bit;
 }ELVR0STR;
typedef union{   /* External Interrupt 8-15 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ER15 :1;
    IO_BYTE _ER14 :1;
    IO_BYTE _ER13 :1;
    IO_BYTE _ER12 :1;
    IO_BYTE _ER11 :1;
    IO_BYTE _ER10 :1;
    IO_BYTE _ER9 :1;
    IO_BYTE _ER8 :1;
  }bit;
 }EIRR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EN15 :1;
    IO_BYTE _EN14 :1;
    IO_BYTE _EN13 :1;
    IO_BYTE _EN12 :1;
    IO_BYTE _EN11 :1;
    IO_BYTE _EN10 :1;
    IO_BYTE _EN9 :1;
    IO_BYTE _EN8 :1;
  }bit;
 }ENIR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _LB15 :1;
    IO_WORD _LA15 :1;
    IO_WORD _LB14 :1;
    IO_WORD _LA14 :1;
    IO_WORD _LB13 :1;
    IO_WORD _LA13 :1;
    IO_WORD _LB12 :1;
    IO_WORD _LA12 :1;
    IO_WORD _LB11 :1;
    IO_WORD _LA11 :1;
    IO_WORD _LB10 :1;
    IO_WORD _LA10 :1;
    IO_WORD _LB9 :1;
    IO_WORD _LA9 :1;
    IO_WORD _LB8 :1;
    IO_WORD _LA8 :1;
  }bit;
 }ELVR1STR;
typedef union{   /* DLYI/I-unit */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _DLYI :1;
  }bit;
 }DICRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MHALTI :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _LVL4 :1;
    IO_BYTE _LVL3 :1;
    IO_BYTE _LVL2 :1;
    IO_BYTE _LVL1 :1;
    IO_BYTE _LVL0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _LVL :5;
  }bitc;
 }HRCLSTR;
typedef union{   /* USART (LIN) 2 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PEN :1;
    IO_BYTE _P :1;
    IO_BYTE _SBL :1;
    IO_BYTE _CL :1;
    IO_BYTE _AD :1;
    IO_BYTE _CRE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _TXE :1;
  }bit;
 }SCR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MD1 :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _OTO :1;
    IO_BYTE _EXT :1;
    IO_BYTE _REST :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _SOE :1;
  }bit;
  struct{
    IO_BYTE _MD :2;
  }bitc;
 }SMR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _FRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _RIE :1;
    IO_BYTE _TIE :1;
  }bit;
 }SSR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _LBIE :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SCES :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _INV :1;
    IO_BYTE _LBR :1;
    IO_BYTE _MS :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _BIE :1;
    IO_BYTE _RBI :1;
    IO_BYTE _TBI :1;
  }bit;
 }ECCR02STR;
typedef union{   /* USART (LIN) 4 with FIFO */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PEN :1;
    IO_BYTE _P :1;
    IO_BYTE _SBL :1;
    IO_BYTE _CL :1;
    IO_BYTE _AD :1;
    IO_BYTE _CRE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _TXE :1;
  }bit;
 }SCR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MD1 :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _OTO :1;
    IO_BYTE _EXT :1;
    IO_BYTE _REST :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _SOE :1;
  }bit;
  struct{
    IO_BYTE _MD :2;
  }bitc;
 }SMR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _FRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _RIE :1;
    IO_BYTE _TIE :1;
  }bit;
 }SSR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _LBIE :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SCES :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _INV :1;
    IO_BYTE _LBR :1;
    IO_BYTE _MS :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _BIE :1;
    IO_BYTE _RBI :1;
    IO_BYTE _TBI :1;
  }bit;
 }ECCR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RXL3 :1;
    IO_BYTE _RXL2 :1;
    IO_BYTE _RXL1 :1;
    IO_BYTE _RXL0 :1;
    IO_BYTE  :1;
    IO_BYTE _ERX :1;
    IO_BYTE _ETX :1;
    IO_BYTE _SVD :1;
  }bit;
  struct{
    IO_BYTE _RXL :4;
  }bitc;
 }FCR04STR;
typedef union{   /* USART (LIN) 5 with FIFO */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PEN :1;
    IO_BYTE _P :1;
    IO_BYTE _SBL :1;
    IO_BYTE _CL :1;
    IO_BYTE _AD :1;
    IO_BYTE _CRE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _TXE :1;
  }bit;
 }SCR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MD1 :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _OTO :1;
    IO_BYTE _EXT :1;
    IO_BYTE _REST :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _SOE :1;
  }bit;
  struct{
    IO_BYTE _MD :2;
  }bitc;
 }SMR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _FRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _RIE :1;
    IO_BYTE _TIE :1;
  }bit;
 }SSR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _LBIE :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SCES :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _INV :1;
    IO_BYTE _LBR :1;
    IO_BYTE _MS :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _BIE :1;
    IO_BYTE _RBI :1;
    IO_BYTE _TBI :1;
  }bit;
 }ECCR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RXL3 :1;
    IO_BYTE _RXL2 :1;
    IO_BYTE _RXL1 :1;
    IO_BYTE _RXL0 :1;
    IO_BYTE  :1;
    IO_BYTE _ERX :1;
    IO_BYTE _ETX :1;
    IO_BYTE _SVD :1;
  }bit;
  struct{
    IO_BYTE _RXL :4;
  }bitc;
 }FCR05STR;
typedef union{   /* USART (LIN) 6 with FIFO */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PEN :1;
    IO_BYTE _P :1;
    IO_BYTE _SBL :1;
    IO_BYTE _CL :1;
    IO_BYTE _AD :1;
    IO_BYTE _CRE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _TXE :1;
  }bit;
 }SCR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MD1 :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _OTO :1;
    IO_BYTE _EXT :1;
    IO_BYTE _REST :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _SOE :1;
  }bit;
  struct{
    IO_BYTE _MD :2;
  }bitc;
 }SMR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _FRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _RIE :1;
    IO_BYTE _TIE :1;
  }bit;
 }SSR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _LBIE :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SCES :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _INV :1;
    IO_BYTE _LBR :1;
    IO_BYTE _MS :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _BIE :1;
    IO_BYTE _RBI :1;
    IO_BYTE _TBI :1;
  }bit;
 }ECCR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RXL3 :1;
    IO_BYTE _RXL2 :1;
    IO_BYTE _RXL1 :1;
    IO_BYTE _RXL0 :1;
    IO_BYTE  :1;
    IO_BYTE _ERX :1;
    IO_BYTE _ETX :1;
    IO_BYTE _SVD :1;
  }bit;
  struct{
    IO_BYTE _RXL :4;
  }bitc;
 }FCR06STR;
typedef union{   /* USART (LIN) 7 with FIFO */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PEN :1;
    IO_BYTE _P :1;
    IO_BYTE _SBL :1;
    IO_BYTE _CL :1;
    IO_BYTE _AD :1;
    IO_BYTE _CRE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _TXE :1;
  }bit;
 }SCR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MD1 :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _OTO :1;
    IO_BYTE _EXT :1;
    IO_BYTE _REST :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _SOE :1;
  }bit;
  struct{
    IO_BYTE _MD :2;
  }bitc;
 }SMR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _PE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _FRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _RIE :1;
    IO_BYTE _TIE :1;
  }bit;
 }SSR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _LBIE :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SCES :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _INV :1;
    IO_BYTE _LBR :1;
    IO_BYTE _MS :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _BIE :1;
    IO_BYTE _RBI :1;
    IO_BYTE _TBI :1;
  }bit;
 }ECCR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RXL3 :1;
    IO_BYTE _RXL2 :1;
    IO_BYTE _RXL1 :1;
    IO_BYTE _RXL0 :1;
    IO_BYTE  :1;
    IO_BYTE _ERX :1;
    IO_BYTE _ETX :1;
    IO_BYTE _SVD :1;
  }bit;
  struct{
    IO_BYTE _RXL :4;
  }bitc;
 }FCR07STR;
typedef union{   /* Stepper Motor 0 */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC20STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _BS :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS10STR;
typedef union{   /* Stepper Motor 1 */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC21STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC11STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _BS :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS21STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS11STR;
typedef union{   /* Stepper Motor 2 */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC22STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC12STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _BS :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS12STR;
typedef union{   /* Stepper Motor 3 */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC23STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _BS :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS13STR;
typedef union{   /* Stepper Motor 4 */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC24STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _BS :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS14STR;
typedef union{   /* Stepper Motor 5 */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC25STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }PWC15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _BS :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _P :3;
    IO_BYTE _M :3;
  }bitc;
 }PWS15STR;
typedef union{   /* Stepper Motor Control 0-5 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _S2 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _CE :1;
    IO_BYTE _SC :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _P :3;
  }bitc;
 }PWC0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _S2 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _CE :1;
    IO_BYTE _SC :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _P :3;
  }bitc;
 }PWC1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _S2 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _CE :1;
    IO_BYTE _SC :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _P :3;
  }bitc;
 }PWC2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _S2 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _CE :1;
    IO_BYTE _SC :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _P :3;
  }bitc;
 }PWC3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _S2 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _CE :1;
    IO_BYTE _SC :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _P :3;
  }bitc;
 }PWC4STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _S2 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
    IO_BYTE _CE :1;
    IO_BYTE _SC :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _P :3;
  }bitc;
 }PWC5STR;
typedef union{   /* I2C 0 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BER :1;
    IO_BYTE _BEIE :1;
    IO_BYTE _SCC :1;
    IO_BYTE _MSS :1;
    IO_BYTE _ACK :1;
    IO_BYTE _GCAA :1;
    IO_BYTE _INTE :1;
    IO_BYTE _INT :1;
  }bit;
 }IBCR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BB :1;
    IO_BYTE _RSC :1;
    IO_BYTE _AL :1;
    IO_BYTE _LRB :1;
    IO_BYTE _TRX :1;
    IO_BYTE _AAS :1;
    IO_BYTE _GCA :1;
    IO_BYTE _ADT :1;
  }bit;
 }IBSR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TA9 :1;
    IO_WORD _TA8 :1;
    IO_WORD _TA7 :1;
    IO_WORD _TA6 :1;
    IO_WORD _TA5 :1;
    IO_WORD _TA4 :1;
    IO_WORD _TA3 :1;
    IO_WORD _TA2 :1;
    IO_WORD _TA1 :1;
    IO_WORD _TA0 :1;
  }bit;
 }ITBA0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TA9 :1;
    IO_BYTE _TA8 :1;
  }bit;
 }ITBAH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TA7 :1;
    IO_BYTE _TA6 :1;
    IO_BYTE _TA5 :1;
    IO_BYTE _TA4 :1;
    IO_BYTE _TA3 :1;
    IO_BYTE _TA2 :1;
    IO_BYTE _TA1 :1;
    IO_BYTE _TA0 :1;
  }bit;
 }ITBAL0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ENTB :1;
    IO_WORD _RAL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TM9 :1;
    IO_WORD _TM8 :1;
    IO_WORD _TM7 :1;
    IO_WORD _TM6 :1;
    IO_WORD _TM5 :1;
    IO_WORD _TM4 :1;
    IO_WORD _TM3 :1;
    IO_WORD _TM2 :1;
    IO_WORD _TM1 :1;
    IO_WORD _TM0 :1;
  }bit;
 }ITMK0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ENTB :1;
    IO_BYTE _RAL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TM9 :1;
    IO_BYTE _TM8 :1;
  }bit;
 }ITMKH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TM7 :1;
    IO_BYTE _TM6 :1;
    IO_BYTE _TM5 :1;
    IO_BYTE _TM4 :1;
    IO_BYTE _TM3 :1;
    IO_BYTE _TM2 :1;
    IO_BYTE _TM1 :1;
    IO_BYTE _TM0 :1;
  }bit;
 }ITMKL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ENSB :1;
    IO_BYTE _SM6 :1;
    IO_BYTE _SM5 :1;
    IO_BYTE _SM4 :1;
    IO_BYTE _SM3 :1;
    IO_BYTE _SM2 :1;
    IO_BYTE _SM1 :1;
    IO_BYTE _SM0 :1;
  }bit;
 }ISMK0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _SA6 :1;
    IO_BYTE _SA5 :1;
    IO_BYTE _SA4 :1;
    IO_BYTE _SA3 :1;
    IO_BYTE _SA2 :1;
    IO_BYTE _SA1 :1;
    IO_BYTE _SA0 :1;
  }bit;
 }ISBA0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }IDAR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _NSF :1;
    IO_BYTE _EN :1;
    IO_BYTE _CS4 :1;
    IO_BYTE _CS3 :1;
    IO_BYTE _CS2 :1;
    IO_BYTE _CS1 :1;
    IO_BYTE _CS0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CS :5;
  }bitc;
 }ICCR0STR;
typedef union{   /* PPG Control 4-7 */
    IO_WORD	word;
    struct{   
    IO_WORD _TSEL33 :1;
    IO_WORD _TSEL32 :1;
    IO_WORD _TSEL31 :1;
    IO_WORD _TSEL30 :1;
    IO_WORD _TSEL23 :1;
    IO_WORD _TSEL22 :1;
    IO_WORD _TSEL21 :1;
    IO_WORD _TSEL20 :1;
    IO_WORD _TSEL13 :1;
    IO_WORD _TSEL12 :1;
    IO_WORD _TSEL11 :1;
    IO_WORD _TSEL10 :1;
    IO_WORD _TSEL03 :1;
    IO_WORD _TSEL02 :1;
    IO_WORD _TSEL01 :1;
    IO_WORD _TSEL00 :1;
  }bit;
 }GCN11STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _EN3 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN0 :1;
  }bit;
 }GCN21STR;
typedef union{   /* PPG Control 8-11 */
    IO_WORD	word;
    struct{   
    IO_WORD _TSEL33 :1;
    IO_WORD _TSEL32 :1;
    IO_WORD _TSEL31 :1;
    IO_WORD _TSEL30 :1;
    IO_WORD _TSEL23 :1;
    IO_WORD _TSEL22 :1;
    IO_WORD _TSEL21 :1;
    IO_WORD _TSEL20 :1;
    IO_WORD _TSEL13 :1;
    IO_WORD _TSEL12 :1;
    IO_WORD _TSEL11 :1;
    IO_WORD _TSEL10 :1;
    IO_WORD _TSEL03 :1;
    IO_WORD _TSEL02 :1;
    IO_WORD _TSEL01 :1;
    IO_WORD _TSEL00 :1;
  }bit;
 }GCN12STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _EN3 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN0 :1;
  }bit;
 }GCN22STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL04STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL05STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL06STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL07STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL08STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL09STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL10STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN11STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH11STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL11STR;
typedef union{   /* Pulse Frequency Modulator (PFM) */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD _INV :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD  :1;
    IO_WORD _MOD1 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
  }bitc;
 }P0TMCSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _INV :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE  :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }P0TMCSRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }P0TMCSRLSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD _INV :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD  :1;
    IO_WORD _MOD1 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
  }bitc;
 }P1TMCSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _INV :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE  :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }P1TMCSRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }P1TMCSRLSTR;
typedef union{   /* Input Capture 0-3 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ICP1 :1;
    IO_BYTE _ICP0 :1;
    IO_BYTE _ICE1 :1;
    IO_BYTE _ICE0 :1;
    IO_BYTE _EG11 :1;
    IO_BYTE _EG10 :1;
    IO_BYTE _EG01 :1;
    IO_BYTE _EG00 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _EG1 :2;
    IO_BYTE _EG0 :2;
  }bitc;
 }ICS01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ICP3 :1;
    IO_BYTE _ICP2 :1;
    IO_BYTE _ICE3 :1;
    IO_BYTE _ICE2 :1;
    IO_BYTE _EG31 :1;
    IO_BYTE _EG30 :1;
    IO_BYTE _EG21 :1;
    IO_BYTE _EG20 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _EG3 :2;
    IO_BYTE _EG2 :2;
  }bitc;
 }ICS23STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP3STR;
typedef union{   /* Output Compare 0-3 */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CMOD :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _OTD1 :1;
    IO_WORD _OTD0 :1;
    IO_WORD _ICP1 :1;
    IO_WORD _ICP0 :1;
    IO_WORD _ICE1 :1;
    IO_WORD _ICE0 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CST1 :1;
    IO_WORD _CST0 :1;
  }bit;
 }OCS01STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CMOD :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _OTD3 :1;
    IO_WORD _OTD2 :1;
    IO_WORD _ICP3 :1;
    IO_WORD _ICP2 :1;
    IO_WORD _ICE3 :1;
    IO_WORD _ICE2 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CST3 :1;
    IO_WORD _CST2 :1;
  }bit;
 }OCS23STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _C15 :1;
    IO_WORD _C14 :1;
    IO_WORD _C13 :1;
    IO_WORD _C12 :1;
    IO_WORD _C11 :1;
    IO_WORD _C10 :1;
    IO_WORD _C9 :1;
    IO_WORD _C8 :1;
    IO_WORD _C7 :1;
    IO_WORD _C6 :1;
    IO_WORD _C5 :1;
    IO_WORD _C4 :1;
    IO_WORD _C3 :1;
    IO_WORD _C2 :1;
    IO_WORD _C1 :1;
    IO_WORD _C0 :1;
  }bit;
 }OCCP0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _C15 :1;
    IO_WORD _C14 :1;
    IO_WORD _C13 :1;
    IO_WORD _C12 :1;
    IO_WORD _C11 :1;
    IO_WORD _C10 :1;
    IO_WORD _C9 :1;
    IO_WORD _C8 :1;
    IO_WORD _C7 :1;
    IO_WORD _C6 :1;
    IO_WORD _C5 :1;
    IO_WORD _C4 :1;
    IO_WORD _C3 :1;
    IO_WORD _C2 :1;
    IO_WORD _C1 :1;
    IO_WORD _C0 :1;
  }bit;
 }OCCP1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _C15 :1;
    IO_WORD _C14 :1;
    IO_WORD _C13 :1;
    IO_WORD _C12 :1;
    IO_WORD _C11 :1;
    IO_WORD _C10 :1;
    IO_WORD _C9 :1;
    IO_WORD _C8 :1;
    IO_WORD _C7 :1;
    IO_WORD _C6 :1;
    IO_WORD _C5 :1;
    IO_WORD _C4 :1;
    IO_WORD _C3 :1;
    IO_WORD _C2 :1;
    IO_WORD _C1 :1;
    IO_WORD _C0 :1;
  }bit;
 }OCCP2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _C15 :1;
    IO_WORD _C14 :1;
    IO_WORD _C13 :1;
    IO_WORD _C12 :1;
    IO_WORD _C11 :1;
    IO_WORD _C10 :1;
    IO_WORD _C9 :1;
    IO_WORD _C8 :1;
    IO_WORD _C7 :1;
    IO_WORD _C6 :1;
    IO_WORD _C5 :1;
    IO_WORD _C4 :1;
    IO_WORD _C3 :1;
    IO_WORD _C2 :1;
    IO_WORD _C1 :1;
    IO_WORD _C0 :1;
  }bit;
 }OCCP3STR;
typedef union{   /* Sound Generator */
    IO_WORD	word;
    struct{   
    IO_WORD _TST :1;
    IO_WORD _S2 :1;
    IO_WORD _S1 :1;
    IO_WORD _S0 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BUSY :1;
    IO_WORD _DEC :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TONE :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _INTE :1;
    IO_WORD _INT :1;
    IO_WORD _ST :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD _S :3;
  }bitc;
 }SGCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TST :1;
    IO_BYTE _S2 :1;
    IO_BYTE _S1 :1;
    IO_BYTE _S0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BUSY :1;
    IO_BYTE _DEC :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _S :3;
  }bitc;
 }SGCRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TONE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _INTE :1;
    IO_BYTE _INT :1;
    IO_BYTE _ST :1;
  }bit;
 }SGCRLSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }SGFRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }SGARSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }SGTRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }SGDRSTR;
typedef union{   /* ADC */
    IO_WORD	word;
    struct{   
    IO_WORD _ADE31 :1;
    IO_WORD _ADE30 :1;
    IO_WORD _ADE29 :1;
    IO_WORD _ADE28 :1;
    IO_WORD _ADE27 :1;
    IO_WORD _ADE26 :1;
    IO_WORD _ADE25 :1;
    IO_WORD _ADE24 :1;
    IO_WORD _ADE23 :1;
    IO_WORD _ADE22 :1;
    IO_WORD _ADE21 :1;
    IO_WORD _ADE20 :1;
    IO_WORD _ADE19 :1;
    IO_WORD _ADE18 :1;
    IO_WORD _ADE17 :1;
    IO_WORD _ADE16 :1;
  }bit;
 }ADERHSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ADE15 :1;
    IO_WORD _ADE14 :1;
    IO_WORD _ADE13 :1;
    IO_WORD _ADE12 :1;
    IO_WORD _ADE11 :1;
    IO_WORD _ADE10 :1;
    IO_WORD _ADE9 :1;
    IO_WORD _ADE8 :1;
    IO_WORD _ADE7 :1;
    IO_WORD _ADE6 :1;
    IO_WORD _ADE5 :1;
    IO_WORD _ADE4 :1;
    IO_WORD _ADE3 :1;
    IO_WORD _ADE2 :1;
    IO_WORD _ADE1 :1;
    IO_WORD _ADE0 :1;
  }bit;
 }ADERLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BUSY :1;
    IO_BYTE _INT :1;
    IO_BYTE _INTE :1;
    IO_BYTE _PAUS :1;
    IO_BYTE _STS1 :1;
    IO_BYTE _STS0 :1;
    IO_BYTE _STRT :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _STS :2;
  }bitc;
 }ADCS1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MD1 :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _S10 :1;
    IO_BYTE _ACH4 :1;
    IO_BYTE _ACH3 :1;
    IO_BYTE _ACH2 :1;
    IO_BYTE _ACH1 :1;
    IO_BYTE _ACH0 :1;
  }bit;
  struct{
    IO_BYTE _MD :2;
    IO_BYTE :1;
    IO_BYTE _ACH :5;
  }bitc;
 }ADCS0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D9 :1;
    IO_BYTE _D8 :1;
  }bit;
 }ADCR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }ADCR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CT5 :1;
    IO_BYTE _CT4 :1;
    IO_BYTE _CT3 :1;
    IO_BYTE _CT2 :1;
    IO_BYTE _CT1 :1;
    IO_BYTE _CT0 :1;
    IO_BYTE _ST9 :1;
    IO_BYTE _ST8 :1;
  }bit;
 }ADCT1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ST7 :1;
    IO_BYTE _ST6 :1;
    IO_BYTE _ST5 :1;
    IO_BYTE _ST4 :1;
    IO_BYTE _ST3 :1;
    IO_BYTE _ST2 :1;
    IO_BYTE _ST1 :1;
    IO_BYTE _ST0 :1;
  }bit;
 }ADCT0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ANS4 :1;
    IO_BYTE _ANS3 :1;
    IO_BYTE _ANS2 :1;
    IO_BYTE _ANS1 :1;
    IO_BYTE _ASN0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _ANS :5;
  }bitc;
 }ADSCHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ANE4 :1;
    IO_BYTE _ANE3 :1;
    IO_BYTE _ANE2 :1;
    IO_BYTE _ANE1 :1;
    IO_BYTE _ANE0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _ANE :5;
  }bitc;
 }ADECHSTR;
typedef union{   /* Alarm Comparator 0-1 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MD :1;
    IO_BYTE _OV_EN :1;
    IO_BYTE _UV_EN :1;
    IO_BYTE _OUT2 :1;
    IO_BYTE _OUT1 :1;
    IO_BYTE _IRQ :1;
    IO_BYTE _IEN :1;
    IO_BYTE _PD :1;
  }bit;
 }ACSR0STR;
typedef union{   /* Reload Timer 0 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL0STR;
typedef union{   /* Reload Timer 1 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL1STR;
typedef union{   /* Reload Timer 2 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL2STR;
typedef union{   /* Reload Timer 3 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR3STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR3STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL3STR;
typedef union{   /* Reload Timer 4 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR4STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR4STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR4STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH4STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL4STR;
typedef union{   /* Reload Timer 5 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR5STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR5STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR5STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH5STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL5STR;
typedef union{   /* Reload Timer 6 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR6STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR6STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR6STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH6STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL6STR;
typedef union{   /* Reload Timer 7 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMRLR7STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }TMR7STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSL2 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD0 :1;
    IO_WORD  :1;
    IO_WORD _OUTL :1;
    IO_WORD _RELD :1;
    IO_WORD _INTE :1;
    IO_WORD _UF :1;
    IO_WORD _CNTE :1;
    IO_WORD _TRG :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CSL :3;
    IO_WORD _MOD :3;
  }bitc;
 }TMCSR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSL2 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _MOD1 :1;
  }bit;
  struct{
    IO_BYTE :3;
    IO_BYTE _CSL :3;
  }bitc;
 }TMCSRH7STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MOD0 :1;
    IO_BYTE  :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _RELD :1;
    IO_BYTE _INTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _TRG :1;
  }bit;
 }TMCSRL7STR;
typedef union{   /* Free Running Timer0 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS0STR;
typedef union{   /* Free Running Timer1 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS1STR;
typedef union{   /* Free Running Timer2 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS2STR;
typedef union{   /* Free Running Timer3 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS3STR;
typedef union{   /* DMAC */
    IO_LWORD	lword;
    struct{   
    IO_LWORD _DENB :1;
    IO_LWORD _PAUS :1;
    IO_LWORD _STRG :1;
    IO_LWORD _IS4 :1;
    IO_LWORD _IS3 :1;
    IO_LWORD _IS2 :1;
    IO_LWORD _IS1 :1;
    IO_LWORD _IS0 :1;
    IO_LWORD _EIS3 :1;
    IO_LWORD _EIS2 :1;
    IO_LWORD _EIS1 :1;
    IO_LWORD _EIS0 :1;
    IO_LWORD _BLK3 :1;
    IO_LWORD _BLK2 :1;
    IO_LWORD _BLK1 :1;
    IO_LWORD _BLK0 :1;
    IO_LWORD _DTCF :1;
    IO_LWORD _DTCE :1;
    IO_LWORD _DTCD :1;
    IO_LWORD _DTCC :1;
    IO_LWORD _DTCB :1;
    IO_LWORD _DTCA :1;
    IO_LWORD _DTC9 :1;
    IO_LWORD _DTC8 :1;
    IO_LWORD _DTC7 :1;
    IO_LWORD _DTC6 :1;
    IO_LWORD _DTC5 :1;
    IO_LWORD _DTC4 :1;
    IO_LWORD _DTC3 :1;
    IO_LWORD _DTC2 :1;
    IO_LWORD _DTC1 :1;
    IO_LWORD _DTC0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _IS :5;
    IO_LWORD _EIS :4;
    IO_LWORD _BLK :4;
    IO_LWORD _DTC :16;
  }bitc;
 }DMACA0STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _TYPE1 :1;
    IO_LWORD _TYPE0 :1;
    IO_LWORD _MOD1 :1;
    IO_LWORD _MOD0 :1;
    IO_LWORD _WS1 :1;
    IO_LWORD _WS0 :1;
    IO_LWORD _SADM :1;
    IO_LWORD _DADM :1;
    IO_LWORD _DTCR :1;
    IO_LWORD _SADR :1;
    IO_LWORD _DADR :1;
    IO_LWORD _ERIE :1;
    IO_LWORD _EDIE :1;
    IO_LWORD _DSS2 :1;
    IO_LWORD _DSS1 :1;
    IO_LWORD _DSS0 :1;
    IO_LWORD _SASZ7 :1;
    IO_LWORD _SASZ6 :1;
    IO_LWORD _SASZ5 :1;
    IO_LWORD _SASZ4 :1;
    IO_LWORD _SASZ3 :1;
    IO_LWORD _SASZ2 :1;
    IO_LWORD _SASZ1 :1;
    IO_LWORD _SASZ0 :1;
    IO_LWORD _DASZ7 :1;
    IO_LWORD _DASZ6 :1;
    IO_LWORD _DASZ5 :1;
    IO_LWORD _DASZ4 :1;
    IO_LWORD _DASZ3 :1;
    IO_LWORD _DASZ2 :1;
    IO_LWORD _DASZ1 :1;
    IO_LWORD _DASZ0 :1;
  }bit;
  struct{
    IO_LWORD _TYPE :2;
    IO_LWORD _MOD :2;
    IO_LWORD _WS :2;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _DSS :3;
    IO_LWORD _SASZ :8;
    IO_LWORD _DASZ :8;
  }bitc;
 }DMACB0STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _DENB :1;
    IO_LWORD _PAUS :1;
    IO_LWORD _STRG :1;
    IO_LWORD _IS4 :1;
    IO_LWORD _IS3 :1;
    IO_LWORD _IS2 :1;
    IO_LWORD _IS1 :1;
    IO_LWORD _IS0 :1;
    IO_LWORD _EIS3 :1;
    IO_LWORD _EIS2 :1;
    IO_LWORD _EIS1 :1;
    IO_LWORD _EIS0 :1;
    IO_LWORD _BLK3 :1;
    IO_LWORD _BLK2 :1;
    IO_LWORD _BLK1 :1;
    IO_LWORD _BLK0 :1;
    IO_LWORD _DTCF :1;
    IO_LWORD _DTCE :1;
    IO_LWORD _DTCD :1;
    IO_LWORD _DTCC :1;
    IO_LWORD _DTCB :1;
    IO_LWORD _DTCA :1;
    IO_LWORD _DTC9 :1;
    IO_LWORD _DTC8 :1;
    IO_LWORD _DTC7 :1;
    IO_LWORD _DTC6 :1;
    IO_LWORD _DTC5 :1;
    IO_LWORD _DTC4 :1;
    IO_LWORD _DTC3 :1;
    IO_LWORD _DTC2 :1;
    IO_LWORD _DTC1 :1;
    IO_LWORD _DTC0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _IS :5;
    IO_LWORD _EIS :4;
    IO_LWORD _BLK :4;
    IO_LWORD _DTC :16;
  }bitc;
 }DMACA1STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _TYPE1 :1;
    IO_LWORD _TYPE0 :1;
    IO_LWORD _MOD1 :1;
    IO_LWORD _MOD0 :1;
    IO_LWORD _WS1 :1;
    IO_LWORD _WS0 :1;
    IO_LWORD _SADM :1;
    IO_LWORD _DADM :1;
    IO_LWORD _DTCR :1;
    IO_LWORD _SADR :1;
    IO_LWORD _DADR :1;
    IO_LWORD _ERIE :1;
    IO_LWORD _EDIE :1;
    IO_LWORD _DSS2 :1;
    IO_LWORD _DSS1 :1;
    IO_LWORD _DSS0 :1;
    IO_LWORD _SASZ7 :1;
    IO_LWORD _SASZ6 :1;
    IO_LWORD _SASZ5 :1;
    IO_LWORD _SASZ4 :1;
    IO_LWORD _SASZ3 :1;
    IO_LWORD _SASZ2 :1;
    IO_LWORD _SASZ1 :1;
    IO_LWORD _SASZ0 :1;
    IO_LWORD _DASZ7 :1;
    IO_LWORD _DASZ6 :1;
    IO_LWORD _DASZ5 :1;
    IO_LWORD _DASZ4 :1;
    IO_LWORD _DASZ3 :1;
    IO_LWORD _DASZ2 :1;
    IO_LWORD _DASZ1 :1;
    IO_LWORD _DASZ0 :1;
  }bit;
  struct{
    IO_LWORD _TYPE :2;
    IO_LWORD _MOD :2;
    IO_LWORD _WS :2;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _DSS :3;
    IO_LWORD _SASZ :8;
    IO_LWORD _DASZ :8;
  }bitc;
 }DMACB1STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _DENB :1;
    IO_LWORD _PAUS :1;
    IO_LWORD _STRG :1;
    IO_LWORD _IS4 :1;
    IO_LWORD _IS3 :1;
    IO_LWORD _IS2 :1;
    IO_LWORD _IS1 :1;
    IO_LWORD _IS0 :1;
    IO_LWORD _EIS3 :1;
    IO_LWORD _EIS2 :1;
    IO_LWORD _EIS1 :1;
    IO_LWORD _EIS0 :1;
    IO_LWORD _BLK3 :1;
    IO_LWORD _BLK2 :1;
    IO_LWORD _BLK1 :1;
    IO_LWORD _BLK0 :1;
    IO_LWORD _DTCF :1;
    IO_LWORD _DTCE :1;
    IO_LWORD _DTCD :1;
    IO_LWORD _DTCC :1;
    IO_LWORD _DTCB :1;
    IO_LWORD _DTCA :1;
    IO_LWORD _DTC9 :1;
    IO_LWORD _DTC8 :1;
    IO_LWORD _DTC7 :1;
    IO_LWORD _DTC6 :1;
    IO_LWORD _DTC5 :1;
    IO_LWORD _DTC4 :1;
    IO_LWORD _DTC3 :1;
    IO_LWORD _DTC2 :1;
    IO_LWORD _DTC1 :1;
    IO_LWORD _DTC0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _IS :5;
    IO_LWORD _EIS :4;
    IO_LWORD _BLK :4;
    IO_LWORD _DTC :16;
  }bitc;
 }DMACA2STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _TYPE1 :1;
    IO_LWORD _TYPE0 :1;
    IO_LWORD _MOD1 :1;
    IO_LWORD _MOD0 :1;
    IO_LWORD _WS1 :1;
    IO_LWORD _WS0 :1;
    IO_LWORD _SADM :1;
    IO_LWORD _DADM :1;
    IO_LWORD _DTCR :1;
    IO_LWORD _SADR :1;
    IO_LWORD _DADR :1;
    IO_LWORD _ERIE :1;
    IO_LWORD _EDIE :1;
    IO_LWORD _DSS2 :1;
    IO_LWORD _DSS1 :1;
    IO_LWORD _DSS0 :1;
    IO_LWORD _SASZ7 :1;
    IO_LWORD _SASZ6 :1;
    IO_LWORD _SASZ5 :1;
    IO_LWORD _SASZ4 :1;
    IO_LWORD _SASZ3 :1;
    IO_LWORD _SASZ2 :1;
    IO_LWORD _SASZ1 :1;
    IO_LWORD _SASZ0 :1;
    IO_LWORD _DASZ7 :1;
    IO_LWORD _DASZ6 :1;
    IO_LWORD _DASZ5 :1;
    IO_LWORD _DASZ4 :1;
    IO_LWORD _DASZ3 :1;
    IO_LWORD _DASZ2 :1;
    IO_LWORD _DASZ1 :1;
    IO_LWORD _DASZ0 :1;
  }bit;
  struct{
    IO_LWORD _TYPE :2;
    IO_LWORD _MOD :2;
    IO_LWORD _WS :2;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _DSS :3;
    IO_LWORD _SASZ :8;
    IO_LWORD _DASZ :8;
  }bitc;
 }DMACB2STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _DENB :1;
    IO_LWORD _PAUS :1;
    IO_LWORD _STRG :1;
    IO_LWORD _IS4 :1;
    IO_LWORD _IS3 :1;
    IO_LWORD _IS2 :1;
    IO_LWORD _IS1 :1;
    IO_LWORD _IS0 :1;
    IO_LWORD _EIS3 :1;
    IO_LWORD _EIS2 :1;
    IO_LWORD _EIS1 :1;
    IO_LWORD _EIS0 :1;
    IO_LWORD _BLK3 :1;
    IO_LWORD _BLK2 :1;
    IO_LWORD _BLK1 :1;
    IO_LWORD _BLK0 :1;
    IO_LWORD _DTCF :1;
    IO_LWORD _DTCE :1;
    IO_LWORD _DTCD :1;
    IO_LWORD _DTCC :1;
    IO_LWORD _DTCB :1;
    IO_LWORD _DTCA :1;
    IO_LWORD _DTC9 :1;
    IO_LWORD _DTC8 :1;
    IO_LWORD _DTC7 :1;
    IO_LWORD _DTC6 :1;
    IO_LWORD _DTC5 :1;
    IO_LWORD _DTC4 :1;
    IO_LWORD _DTC3 :1;
    IO_LWORD _DTC2 :1;
    IO_LWORD _DTC1 :1;
    IO_LWORD _DTC0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _IS :5;
    IO_LWORD _EIS :4;
    IO_LWORD _BLK :4;
    IO_LWORD _DTC :16;
  }bitc;
 }DMACA3STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _TYPE1 :1;
    IO_LWORD _TYPE0 :1;
    IO_LWORD _MOD1 :1;
    IO_LWORD _MOD0 :1;
    IO_LWORD _WS1 :1;
    IO_LWORD _WS0 :1;
    IO_LWORD _SADM :1;
    IO_LWORD _DADM :1;
    IO_LWORD _DTCR :1;
    IO_LWORD _SADR :1;
    IO_LWORD _DADR :1;
    IO_LWORD _ERIE :1;
    IO_LWORD _EDIE :1;
    IO_LWORD _DSS2 :1;
    IO_LWORD _DSS1 :1;
    IO_LWORD _DSS0 :1;
    IO_LWORD _SASZ7 :1;
    IO_LWORD _SASZ6 :1;
    IO_LWORD _SASZ5 :1;
    IO_LWORD _SASZ4 :1;
    IO_LWORD _SASZ3 :1;
    IO_LWORD _SASZ2 :1;
    IO_LWORD _SASZ1 :1;
    IO_LWORD _SASZ0 :1;
    IO_LWORD _DASZ7 :1;
    IO_LWORD _DASZ6 :1;
    IO_LWORD _DASZ5 :1;
    IO_LWORD _DASZ4 :1;
    IO_LWORD _DASZ3 :1;
    IO_LWORD _DASZ2 :1;
    IO_LWORD _DASZ1 :1;
    IO_LWORD _DASZ0 :1;
  }bit;
  struct{
    IO_LWORD _TYPE :2;
    IO_LWORD _MOD :2;
    IO_LWORD _WS :2;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _DSS :3;
    IO_LWORD _SASZ :8;
    IO_LWORD _DASZ :8;
  }bitc;
 }DMACB3STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _DENB :1;
    IO_LWORD _PAUS :1;
    IO_LWORD _STRG :1;
    IO_LWORD _IS4 :1;
    IO_LWORD _IS3 :1;
    IO_LWORD _IS2 :1;
    IO_LWORD _IS1 :1;
    IO_LWORD _IS0 :1;
    IO_LWORD _EIS3 :1;
    IO_LWORD _EIS2 :1;
    IO_LWORD _EIS1 :1;
    IO_LWORD _EIS0 :1;
    IO_LWORD _BLK3 :1;
    IO_LWORD _BLK2 :1;
    IO_LWORD _BLK1 :1;
    IO_LWORD _BLK0 :1;
    IO_LWORD _DTCF :1;
    IO_LWORD _DTCE :1;
    IO_LWORD _DTCD :1;
    IO_LWORD _DTCC :1;
    IO_LWORD _DTCB :1;
    IO_LWORD _DTCA :1;
    IO_LWORD _DTC9 :1;
    IO_LWORD _DTC8 :1;
    IO_LWORD _DTC7 :1;
    IO_LWORD _DTC6 :1;
    IO_LWORD _DTC5 :1;
    IO_LWORD _DTC4 :1;
    IO_LWORD _DTC3 :1;
    IO_LWORD _DTC2 :1;
    IO_LWORD _DTC1 :1;
    IO_LWORD _DTC0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _IS :5;
    IO_LWORD _EIS :4;
    IO_LWORD _BLK :4;
    IO_LWORD _DTC :16;
  }bitc;
 }DMACA4STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _TYPE1 :1;
    IO_LWORD _TYPE0 :1;
    IO_LWORD _MOD1 :1;
    IO_LWORD _MOD0 :1;
    IO_LWORD _WS1 :1;
    IO_LWORD _WS0 :1;
    IO_LWORD _SADM :1;
    IO_LWORD _DADM :1;
    IO_LWORD _DTCR :1;
    IO_LWORD _SADR :1;
    IO_LWORD _DADR :1;
    IO_LWORD _ERIE :1;
    IO_LWORD _EDIE :1;
    IO_LWORD _DSS2 :1;
    IO_LWORD _DSS1 :1;
    IO_LWORD _DSS0 :1;
    IO_LWORD _SASZ7 :1;
    IO_LWORD _SASZ6 :1;
    IO_LWORD _SASZ5 :1;
    IO_LWORD _SASZ4 :1;
    IO_LWORD _SASZ3 :1;
    IO_LWORD _SASZ2 :1;
    IO_LWORD _SASZ1 :1;
    IO_LWORD _SASZ0 :1;
    IO_LWORD _DASZ7 :1;
    IO_LWORD _DASZ6 :1;
    IO_LWORD _DASZ5 :1;
    IO_LWORD _DASZ4 :1;
    IO_LWORD _DASZ3 :1;
    IO_LWORD _DASZ2 :1;
    IO_LWORD _DASZ1 :1;
    IO_LWORD _DASZ0 :1;
  }bit;
  struct{
    IO_LWORD _TYPE :2;
    IO_LWORD _MOD :2;
    IO_LWORD _WS :2;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _DSS :3;
    IO_LWORD _SASZ :8;
    IO_LWORD _DASZ :8;
  }bitc;
 }DMACB4STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _DMAE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _PM01 :1;
    IO_BYTE _DMAH3 :1;
    IO_BYTE _DMAH2 :1;
    IO_BYTE _DMAH1 :1;
    IO_BYTE _DMAH0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _DMAH :4;
  }bitc;
 }DMACRSTR;
typedef union{   /* Input Capture 4-7 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ICP5 :1;
    IO_BYTE _ICP4 :1;
    IO_BYTE _ICE5 :1;
    IO_BYTE _ICE4 :1;
    IO_BYTE _EG51 :1;
    IO_BYTE _EG50 :1;
    IO_BYTE _EG41 :1;
    IO_BYTE _EG40 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _EG5 :2;
    IO_BYTE _EG4 :2;
  }bitc;
 }ICS45STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ICP7 :1;
    IO_BYTE _ICP6 :1;
    IO_BYTE _ICE7 :1;
    IO_BYTE _ICE6 :1;
    IO_BYTE _EG71 :1;
    IO_BYTE _EG70 :1;
    IO_BYTE _EG61 :1;
    IO_BYTE _EG60 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _EG7 :2;
    IO_BYTE _EG6 :2;
  }bitc;
 }ICS67STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP4STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP5STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP6STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CP15 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP9 :1;
    IO_WORD _CP8 :1;
    IO_WORD _CP7 :1;
    IO_WORD _CP6 :1;
    IO_WORD _CP5 :1;
    IO_WORD _CP4 :1;
    IO_WORD _CP3 :1;
    IO_WORD _CP2 :1;
    IO_WORD _CP1 :1;
    IO_WORD _CP0 :1;
  }bit;
 }IPCP7STR;
typedef union{   /* Free Running Timer4 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT4STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS4STR;
typedef union{   /* Free Running Timer5 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT5STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS5STR;
typedef union{   /* Free Running Timer6 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT6STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS6STR;
typedef union{   /* Free Running Timer7 */
    IO_WORD	word;
    struct{   
    IO_WORD _T15 :1;
    IO_WORD _T14 :1;
    IO_WORD _T13 :1;
    IO_WORD _T12 :1;
    IO_WORD _T11 :1;
    IO_WORD _T10 :1;
    IO_WORD _T9 :1;
    IO_WORD _T8 :1;
    IO_WORD _T7 :1;
    IO_WORD _T6 :1;
    IO_WORD _T5 :1;
    IO_WORD _T4 :1;
    IO_WORD _T3 :1;
    IO_WORD _T2 :1;
    IO_WORD _T1 :1;
    IO_WORD _T0 :1;
  }bit;
 }TCDT7STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ECLK :1;
    IO_BYTE _IVF :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _MODE :1;
    IO_BYTE _CLR :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLK :2;
  }bitc;
 }TCCS7STR;
typedef union{   /* Up/Down Counter 0-1 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }UDRC10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDRC1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDRC0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }UDCR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDCR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDCR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _M16E :1;
    IO_WORD _CDCF :1;
    IO_WORD _CFIE :1;
    IO_WORD _CLKS :1;
    IO_WORD _CMS1 :1;
    IO_WORD _CMS0 :1;
    IO_WORD _CES1 :1;
    IO_WORD _CES0 :1;
    IO_WORD  :1;
    IO_WORD _CTUT :1;
    IO_WORD _UCRE :1;
    IO_WORD _RLDE :1;
    IO_WORD _UDCLR :1;
    IO_WORD _CGSC :1;
    IO_WORD _CGE1 :1;
    IO_WORD _CGE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CMS :2;
    IO_WORD _CES :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CGE :2;
  }bitc;
 }UDCC0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _M16E :1;
    IO_BYTE _CDCF :1;
    IO_BYTE _CFIE :1;
    IO_BYTE _CLKS :1;
    IO_BYTE _CMS1 :1;
    IO_BYTE _CMS0 :1;
    IO_BYTE _CES1 :1;
    IO_BYTE _CES0 :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _CMS :2;
    IO_BYTE _CES :2;
  }bitc;
 }UDCCH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _CTUT :1;
    IO_BYTE _UCRE :1;
    IO_BYTE _RLDE :1;
    IO_BYTE _UDCLR :1;
    IO_BYTE _CGSC :1;
    IO_BYTE _CGE1 :1;
    IO_BYTE _CGE0 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _CGE :2;
  }bitc;
 }UDCCL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CSTR :1;
    IO_BYTE _CITE :1;
    IO_BYTE _UDIE :1;
    IO_BYTE _CMPF :1;
    IO_BYTE _OVFF :1;
    IO_BYTE _UDFF :1;
    IO_BYTE _UDF1 :1;
    IO_BYTE _UDF0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _UDF :2;
  }bitc;
 }UDCS0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _RESV15 :1;
    IO_WORD _CDCF :1;
    IO_WORD _CFIE :1;
    IO_WORD _CLKS :1;
    IO_WORD _CMS1 :1;
    IO_WORD _CMS0 :1;
    IO_WORD _CES1 :1;
    IO_WORD _CES0 :1;
    IO_WORD  :1;
    IO_WORD _CTUT :1;
    IO_WORD _UCRE :1;
    IO_WORD _RLDE :1;
    IO_WORD _UDCLR :1;
    IO_WORD _CGSC :1;
    IO_WORD _CGE1 :1;
    IO_WORD _CGE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CMS :2;
    IO_WORD _CES :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CGE :2;
  }bitc;
 }UDCC1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RESV15 :1;
    IO_BYTE _CDCF :1;
    IO_BYTE _CFIE :1;
    IO_BYTE _CLKS :1;
    IO_BYTE _CMS1 :1;
    IO_BYTE _CMS0 :1;
    IO_BYTE _CES1 :1;
    IO_BYTE _CES0 :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _CMS :2;
    IO_BYTE _CES :2;
  }bitc;
 }UDCCH1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _CTUT :1;
    IO_BYTE _UCRE :1;
    IO_BYTE _RLDE :1;
    IO_BYTE _UDCLR :1;
    IO_BYTE _CGSC :1;
    IO_BYTE _CGE1 :1;
    IO_BYTE _CGE0 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _CGE :2;
  }bitc;
 }UDCCL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CSTR :1;
    IO_BYTE _CITE :1;
    IO_BYTE _UDIE :1;
    IO_BYTE _CMPF :1;
    IO_BYTE _OVFF :1;
    IO_BYTE _UDFF :1;
    IO_BYTE _UDF1 :1;
    IO_BYTE _UDF0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _UDF :2;
  }bitc;
 }UDCS1STR;
typedef union{   /* Up/Down Counter 2-3 */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }UDRC32STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDRC3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDRC2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }UDCR32STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDCR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }UDCR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _M16E :1;
    IO_WORD _CDCF :1;
    IO_WORD _CFIE :1;
    IO_WORD _CLKS :1;
    IO_WORD _CMS1 :1;
    IO_WORD _CMS0 :1;
    IO_WORD _CES1 :1;
    IO_WORD _CES0 :1;
    IO_WORD  :1;
    IO_WORD _CTUT :1;
    IO_WORD _UCRE :1;
    IO_WORD _RLDE :1;
    IO_WORD _UDCLR :1;
    IO_WORD _CGSC :1;
    IO_WORD _CGE1 :1;
    IO_WORD _CGE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CMS :2;
    IO_WORD _CES :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CGE :2;
  }bitc;
 }UDCC2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _M16E :1;
    IO_BYTE _CDCF :1;
    IO_BYTE _CFIE :1;
    IO_BYTE _CLKS :1;
    IO_BYTE _CMS1 :1;
    IO_BYTE _CMS0 :1;
    IO_BYTE _CES1 :1;
    IO_BYTE _CES0 :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _CMS :2;
    IO_BYTE _CES :2;
  }bitc;
 }UDCCH2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _CTUT :1;
    IO_BYTE _UCRE :1;
    IO_BYTE _RLDE :1;
    IO_BYTE _UDCLR :1;
    IO_BYTE _CGSC :1;
    IO_BYTE _CGE1 :1;
    IO_BYTE _CGE0 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _CGE :2;
  }bitc;
 }UDCCL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CSTR :1;
    IO_BYTE _CITE :1;
    IO_BYTE _UDIE :1;
    IO_BYTE _CMPF :1;
    IO_BYTE _OVFF :1;
    IO_BYTE _UDFF :1;
    IO_BYTE _UDF1 :1;
    IO_BYTE _UDF0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _UDF :2;
  }bitc;
 }UDCS2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _RESV15 :1;
    IO_WORD _CDCF :1;
    IO_WORD _CFIE :1;
    IO_WORD _CLKS :1;
    IO_WORD _CMS1 :1;
    IO_WORD _CMS0 :1;
    IO_WORD _CES1 :1;
    IO_WORD _CES0 :1;
    IO_WORD  :1;
    IO_WORD _CTUT :1;
    IO_WORD _UCRE :1;
    IO_WORD _RLDE :1;
    IO_WORD _UDCLR :1;
    IO_WORD _CGSC :1;
    IO_WORD _CGE1 :1;
    IO_WORD _CGE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CMS :2;
    IO_WORD _CES :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CGE :2;
  }bitc;
 }UDCC3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RESV15 :1;
    IO_BYTE _CDCF :1;
    IO_BYTE _CFIE :1;
    IO_BYTE _CLKS :1;
    IO_BYTE _CMS1 :1;
    IO_BYTE _CMS0 :1;
    IO_BYTE _CES1 :1;
    IO_BYTE _CES0 :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _CMS :2;
    IO_BYTE _CES :2;
  }bitc;
 }UDCCH3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _CTUT :1;
    IO_BYTE _UCRE :1;
    IO_BYTE _RLDE :1;
    IO_BYTE _UDCLR :1;
    IO_BYTE _CGSC :1;
    IO_BYTE _CGE1 :1;
    IO_BYTE _CGE0 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _CGE :2;
  }bitc;
 }UDCCL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CSTR :1;
    IO_BYTE _CITE :1;
    IO_BYTE _UDIE :1;
    IO_BYTE _CMPF :1;
    IO_BYTE _OVFF :1;
    IO_BYTE _UDFF :1;
    IO_BYTE _UDF1 :1;
    IO_BYTE _UDF0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _UDF :2;
  }bitc;
 }UDCS3STR;
typedef union{   /* PPG Control 12-15 */
    IO_WORD	word;
    struct{   
    IO_WORD _TSEL33 :1;
    IO_WORD _TSEL32 :1;
    IO_WORD _TSEL31 :1;
    IO_WORD _TSEL30 :1;
    IO_WORD _TSEL23 :1;
    IO_WORD _TSEL22 :1;
    IO_WORD _TSEL21 :1;
    IO_WORD _TSEL20 :1;
    IO_WORD _TSEL13 :1;
    IO_WORD _TSEL12 :1;
    IO_WORD _TSEL11 :1;
    IO_WORD _TSEL10 :1;
    IO_WORD _TSEL03 :1;
    IO_WORD _TSEL02 :1;
    IO_WORD _TSEL01 :1;
    IO_WORD _TSEL00 :1;
  }bit;
 }GCN13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _EN3 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN0 :1;
  }bit;
 }GCN23STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN12STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH12STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL12STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL13STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL14STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _CNTE :1;
    IO_WORD _STGR :1;
    IO_WORD _MDSE :1;
    IO_WORD _RTRG :1;
    IO_WORD _CKS1 :1;
    IO_WORD _CKS0 :1;
    IO_WORD _PGMS :1;
    IO_WORD  :1;
    IO_WORD _EGS1 :1;
    IO_WORD _EGS0 :1;
    IO_WORD _IREN :1;
    IO_WORD _IRQF :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRS0 :1;
    IO_WORD  :1;
    IO_WORD _OSEL :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _CKS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _EGS :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _IRS :2;
  }bitc;
 }PCN15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CNTE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _PGMS :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EGS1 :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _IREN :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE  :1;
    IO_BYTE _OSEL :1;
  }bit;
  struct{
    IO_BYTE _EGS :2;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _IRS :2;
  }bitc;
 }PCNL15STR;
typedef union{   /* I2C 2 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BER :1;
    IO_BYTE _BEIE :1;
    IO_BYTE _SCC :1;
    IO_BYTE _MSS :1;
    IO_BYTE _ACK :1;
    IO_BYTE _GCAA :1;
    IO_BYTE _INTE :1;
    IO_BYTE _INT :1;
  }bit;
 }IBCR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BB :1;
    IO_BYTE _RSC :1;
    IO_BYTE _AL :1;
    IO_BYTE _LRB :1;
    IO_BYTE _TRX :1;
    IO_BYTE _AAS :1;
    IO_BYTE _GCA :1;
    IO_BYTE _ADT :1;
  }bit;
 }IBSR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TA9 :1;
    IO_WORD _TA8 :1;
    IO_WORD _TA7 :1;
    IO_WORD _TA6 :1;
    IO_WORD _TA5 :1;
    IO_WORD _TA4 :1;
    IO_WORD _TA3 :1;
    IO_WORD _TA2 :1;
    IO_WORD _TA1 :1;
    IO_WORD _TA0 :1;
  }bit;
 }ITBA2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TA9 :1;
    IO_BYTE _TA8 :1;
  }bit;
 }ITBAH2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TA7 :1;
    IO_BYTE _TA6 :1;
    IO_BYTE _TA5 :1;
    IO_BYTE _TA4 :1;
    IO_BYTE _TA3 :1;
    IO_BYTE _TA2 :1;
    IO_BYTE _TA1 :1;
    IO_BYTE _TA0 :1;
  }bit;
 }ITBAL2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ENTB :1;
    IO_WORD _RAL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TM9 :1;
    IO_WORD _TM8 :1;
    IO_WORD _TM7 :1;
    IO_WORD _TM6 :1;
    IO_WORD _TM5 :1;
    IO_WORD _TM4 :1;
    IO_WORD _TM3 :1;
    IO_WORD _TM2 :1;
    IO_WORD _TM1 :1;
    IO_WORD _TM0 :1;
  }bit;
 }ITMK2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ENTB :1;
    IO_BYTE _RAL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TM9 :1;
    IO_BYTE _TM8 :1;
  }bit;
 }ITMKH2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TM7 :1;
    IO_BYTE _TM6 :1;
    IO_BYTE _TM5 :1;
    IO_BYTE _TM4 :1;
    IO_BYTE _TM3 :1;
    IO_BYTE _TM2 :1;
    IO_BYTE _TM1 :1;
    IO_BYTE _TM0 :1;
  }bit;
 }ITMKL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ENSB :1;
    IO_BYTE _SM6 :1;
    IO_BYTE _SM5 :1;
    IO_BYTE _SM4 :1;
    IO_BYTE _SM3 :1;
    IO_BYTE _SM2 :1;
    IO_BYTE _SM1 :1;
    IO_BYTE _SM0 :1;
  }bit;
 }ISMK2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _SA6 :1;
    IO_BYTE _SA5 :1;
    IO_BYTE _SA4 :1;
    IO_BYTE _SA3 :1;
    IO_BYTE _SA2 :1;
    IO_BYTE _SA1 :1;
    IO_BYTE _SA0 :1;
  }bit;
 }ISBA2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }IDAR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _NSF :1;
    IO_BYTE _EN :1;
    IO_BYTE _CS4 :1;
    IO_BYTE _CS3 :1;
    IO_BYTE _CS2 :1;
    IO_BYTE _CS1 :1;
    IO_BYTE _CS0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CS :5;
  }bitc;
 }ICCR2STR;
typedef union{   /* I2C 3 */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BER :1;
    IO_BYTE _BEIE :1;
    IO_BYTE _SCC :1;
    IO_BYTE _MSS :1;
    IO_BYTE _ACK :1;
    IO_BYTE _GCAA :1;
    IO_BYTE _INTE :1;
    IO_BYTE _INT :1;
  }bit;
 }IBCR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BB :1;
    IO_BYTE _RSC :1;
    IO_BYTE _AL :1;
    IO_BYTE _LRB :1;
    IO_BYTE _TRX :1;
    IO_BYTE _AAS :1;
    IO_BYTE _GCA :1;
    IO_BYTE _ADT :1;
  }bit;
 }IBSR3STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TA9 :1;
    IO_WORD _TA8 :1;
    IO_WORD _TA7 :1;
    IO_WORD _TA6 :1;
    IO_WORD _TA5 :1;
    IO_WORD _TA4 :1;
    IO_WORD _TA3 :1;
    IO_WORD _TA2 :1;
    IO_WORD _TA1 :1;
    IO_WORD _TA0 :1;
  }bit;
 }ITBA3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TA9 :1;
    IO_BYTE _TA8 :1;
  }bit;
 }ITBAH3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TA7 :1;
    IO_BYTE _TA6 :1;
    IO_BYTE _TA5 :1;
    IO_BYTE _TA4 :1;
    IO_BYTE _TA3 :1;
    IO_BYTE _TA2 :1;
    IO_BYTE _TA1 :1;
    IO_BYTE _TA0 :1;
  }bit;
 }ITBAL3STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ENTB :1;
    IO_WORD _RAL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TM9 :1;
    IO_WORD _TM8 :1;
    IO_WORD _TM7 :1;
    IO_WORD _TM6 :1;
    IO_WORD _TM5 :1;
    IO_WORD _TM4 :1;
    IO_WORD _TM3 :1;
    IO_WORD _TM2 :1;
    IO_WORD _TM1 :1;
    IO_WORD _TM0 :1;
  }bit;
 }ITMK3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ENTB :1;
    IO_BYTE _RAL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TM9 :1;
    IO_BYTE _TM8 :1;
  }bit;
 }ITMKH3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TM7 :1;
    IO_BYTE _TM6 :1;
    IO_BYTE _TM5 :1;
    IO_BYTE _TM4 :1;
    IO_BYTE _TM3 :1;
    IO_BYTE _TM2 :1;
    IO_BYTE _TM1 :1;
    IO_BYTE _TM0 :1;
  }bit;
 }ITMKL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ENSB :1;
    IO_BYTE _SM6 :1;
    IO_BYTE _SM5 :1;
    IO_BYTE _SM4 :1;
    IO_BYTE _SM3 :1;
    IO_BYTE _SM2 :1;
    IO_BYTE _SM1 :1;
    IO_BYTE _SM0 :1;
  }bit;
 }ISMK3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _SA6 :1;
    IO_BYTE _SA5 :1;
    IO_BYTE _SA4 :1;
    IO_BYTE _SA3 :1;
    IO_BYTE _SA2 :1;
    IO_BYTE _SA1 :1;
    IO_BYTE _SA0 :1;
  }bit;
 }ISBA3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }IDAR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _NSF :1;
    IO_BYTE _EN :1;
    IO_BYTE _CS4 :1;
    IO_BYTE _CS3 :1;
    IO_BYTE _CS2 :1;
    IO_BYTE _CS1 :1;
    IO_BYTE _CS0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CS :5;
  }bitc;
 }ICCR3STR;
typedef union{   /* ROM Select Register */
    IO_WORD	word;
    struct{   
    IO_WORD _D15 :1;
    IO_WORD _D14 :1;
    IO_WORD _D13 :1;
    IO_WORD _D12 :1;
    IO_WORD _D11 :1;
    IO_WORD _D10 :1;
    IO_WORD _D9 :1;
    IO_WORD _D8 :1;
    IO_WORD _D7 :1;
    IO_WORD _D6 :1;
    IO_WORD _D5 :1;
    IO_WORD _D4 :1;
    IO_WORD _D3 :1;
    IO_WORD _D2 :1;
    IO_WORD _D1 :1;
    IO_WORD _D0 :1;
  }bit;
 }ROMSSTR;
typedef union{   /* Interrupt Control Unit */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR11STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR12STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR21STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR28STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR29STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR30STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR31STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR32STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR33STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR34STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR35STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR36STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR37STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR38STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR39STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR40STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR41STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR42STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR43STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR44STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR45STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR46STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR47STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR48STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR49STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR50STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR51STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR52STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR53STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR54STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR55STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR56STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR57STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR58STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR59STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR60STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR61STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR62STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICR4 :1;
    IO_BYTE _ICR3 :1;
    IO_BYTE _ICR2 :1;
    IO_BYTE _ICR1 :1;
    IO_BYTE _ICR0 :1;
  }bit;
 }ICR63STR;
typedef union{   /* Clock Control Unit */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _INIT :1;
    IO_BYTE _HSTB :1;
    IO_BYTE _WDOG :1;
    IO_BYTE _ERST :1;
    IO_BYTE _SRST :1;
    IO_BYTE _LINIT :1;
    IO_BYTE _WT1 :1;
    IO_BYTE _WT0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WT :2;
  }bitc;
 }RSRRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _STOP :1;
    IO_BYTE _SLEEP :1;
    IO_BYTE _HIZ :1;
    IO_BYTE _SRST :1;
    IO_BYTE _OS1 :1;
    IO_BYTE _OS0 :1;
    IO_BYTE _OSCD2 :1;
    IO_BYTE _OSCD1 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _OS :2;
    IO_BYTE _OSCD :2;
  }bitc;
 }STCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _TBIF :1;
    IO_BYTE _TBIE :1;
    IO_BYTE _TBC2 :1;
    IO_BYTE _TBC1 :1;
    IO_BYTE _TBC0 :1;
    IO_BYTE  :1;
    IO_BYTE _SYNCR :1;
    IO_BYTE _SYNCS :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _TBC :3;
  }bitc;
 }TBCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }CTBRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _SCKEN :1;
    IO_BYTE _PLL1EN :1;
    IO_BYTE _CLKS1 :1;
    IO_BYTE _CLKS0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _CLKS :2;
  }bitc;
 }CLKRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }WPRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _B3 :1;
    IO_BYTE _B2 :1;
    IO_BYTE _B1 :1;
    IO_BYTE _B0 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P0 :1;
  }bit;
  struct{
    IO_BYTE _B :4;
    IO_BYTE _P :4;
  }bitc;
 }DIVR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _T3 :1;
    IO_BYTE _T2 :1;
    IO_BYTE _T1 :1;
    IO_BYTE _T0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _T :4;
  }bitc;
 }DIVR1STR;
typedef union{   /* PLL - Clock Gear Unit: */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _DVM3 :1;
    IO_BYTE _DVM2 :1;
    IO_BYTE _DVM1 :1;
    IO_BYTE _DVM0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _DVM :4;
  }bitc;
 }PLLDIVMSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _DVN5 :1;
    IO_BYTE _DVN4 :1;
    IO_BYTE _DVN3 :1;
    IO_BYTE _DVN2 :1;
    IO_BYTE _DVN1 :1;
    IO_BYTE _DVN0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _DVN :6;
  }bitc;
 }PLLDIVNSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _DVG3 :1;
    IO_BYTE _DVG2 :1;
    IO_BYTE _DVG1 :1;
    IO_BYTE _DVG0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _DVG :4;
  }bitc;
 }PLLDIVGSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _MLG7 :1;
    IO_BYTE _MLG6 :1;
    IO_BYTE _MLG5 :1;
    IO_BYTE _MLG4 :1;
    IO_BYTE _MLG3 :1;
    IO_BYTE _MLG2 :1;
    IO_BYTE _MLG1 :1;
    IO_BYTE _MLG0 :1;
  }bit;
  struct{
    IO_BYTE _MLG :8;
  }bitc;
 }PLLMULGSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _IEDN :1;
    IO_BYTE _GRDN :1;
    IO_BYTE _IEUP :1;
    IO_BYTE _GRUP :1;
  }bit;
 }PLLCTRLSTR;
typedef union{   /* Main/Sub Oscillator Control */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _FCI :1;
    IO_BYTE _RFBEN :1;
    IO_BYTE _OSCR :1;
  }bit;
 }OSCC1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _OSCS7 :1;
    IO_BYTE _OSCS6 :1;
    IO_BYTE _OSCS5 :1;
    IO_BYTE _OSCS4 :1;
    IO_BYTE _OSCS3 :1;
    IO_BYTE _OSCS2 :1;
    IO_BYTE _OSCS1 :1;
    IO_BYTE _OSCS0 :1;
  }bit;
 }OSCS1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _FCI :1;
    IO_BYTE _RFBEN :1;
    IO_BYTE _OSCR :1;
  }bit;
 }OSCC2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _OSCS7 :1;
    IO_BYTE _OSCS6 :1;
    IO_BYTE _OSCS5 :1;
    IO_BYTE _OSCS4 :1;
    IO_BYTE _OSCS3 :1;
    IO_BYTE _OSCS2 :1;
    IO_BYTE _OSCS1 :1;
    IO_BYTE _OSCS0 :1;
  }bit;
 }OSCS2STR;
typedef union{   /* Port Input Enable Control */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CPORTEN :1;
    IO_BYTE _GPORTEN :1;
  }bit;
 }PORTENSTR;
typedef union{   /* Real Time Clock (Watch Timer) */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _INTE4 :1;
    IO_BYTE _INT4 :1;
  }bit;
 }WTCERSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _INTE3 :1;
    IO_WORD _INT3 :1;
    IO_WORD _INTE2 :1;
    IO_WORD _INT2 :1;
    IO_WORD _INTE1 :1;
    IO_WORD _INT1 :1;
    IO_WORD _INTE0 :1;
    IO_WORD _INT0 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _RUN :1;
    IO_WORD _UPDT :1;
    IO_WORD  :1;
    IO_WORD _ST :1;
  }bit;
 }WTCRSTR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _D20 :1;
    IO_LWORD _D19 :1;
    IO_LWORD _D18 :1;
    IO_LWORD _D17 :1;
    IO_LWORD _D16 :1;
    IO_LWORD _D15 :1;
    IO_LWORD _D14 :1;
    IO_LWORD _D13 :1;
    IO_LWORD _D12 :1;
    IO_LWORD _D11 :1;
    IO_LWORD _D10 :1;
    IO_LWORD _D9 :1;
    IO_LWORD _D8 :1;
    IO_LWORD _D7 :1;
    IO_LWORD _D6 :1;
    IO_LWORD _D5 :1;
    IO_LWORD _D4 :1;
    IO_LWORD _D3 :1;
    IO_LWORD _D2 :1;
    IO_LWORD _D1 :1;
    IO_LWORD _D0 :1;
  }bit;
 }WTBRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _H4 :1;
    IO_BYTE _H3 :1;
    IO_BYTE _H2 :1;
    IO_BYTE _H1 :1;
    IO_BYTE _H0 :1;
  }bit;
 }WTHRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _M5 :1;
    IO_BYTE _M4 :1;
    IO_BYTE _M3 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M0 :1;
  }bit;
 }WTMRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _S5 :1;
    IO_BYTE _S4 :1;
    IO_BYTE _S3 :1;
    IO_BYTE _S2 :1;
    IO_BYTE _S1 :1;
    IO_BYTE _S0 :1;
  }bit;
 }WTSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _SCKS :1;
    IO_BYTE _MM :1;
    IO_BYTE _SM :1;
    IO_BYTE _RCE :1;
    IO_BYTE _MSVE :1;
    IO_BYTE _SSVE :1;
    IO_BYTE _SRST :1;
    IO_BYTE _OUTE :1;
  }bit;
 }CSVCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _EDSUEN :1;
    IO_BYTE _PLLLOCK :1;
    IO_BYTE _RCSEL :1;
    IO_BYTE _MONCKI :1;
    IO_BYTE _CSC3 :1;
    IO_BYTE _CSC2 :1;
    IO_BYTE _CSC1 :1;
    IO_BYTE _CSC0 :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _CSC :4;
  }bitc;
 }CSCFGSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CMPRE3 :1;
    IO_BYTE _CMPRE2 :1;
    IO_BYTE _CMPRE1 :1;
    IO_BYTE _CMPRE0 :1;
    IO_BYTE _CMSEL3 :1;
    IO_BYTE _CMSEL2 :1;
    IO_BYTE _CMSEL1 :1;
    IO_BYTE _CMSEL0 :1;
  }bit;
  struct{
    IO_BYTE _CMPRE :4;
    IO_BYTE _CMSEL :4;
  }bitc;
 }CMCFGSTR;
typedef union{   /* Calibration Unit of Sub Oszillation */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _STRT :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _INT :1;
    IO_WORD _INTEN :1;
  }bit;
 }CUCRSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _TDD15 :1;
    IO_WORD _TDD14 :1;
    IO_WORD _TDD13 :1;
    IO_WORD _TDD12 :1;
    IO_WORD _TDD11 :1;
    IO_WORD _TDD10 :1;
    IO_WORD _TDD9 :1;
    IO_WORD _TDD8 :1;
    IO_WORD _TDD7 :1;
    IO_WORD _TDD6 :1;
    IO_WORD _TDD5 :1;
    IO_WORD _TDD4 :1;
    IO_WORD _TDD3 :1;
    IO_WORD _TDD2 :1;
    IO_WORD _TDD1 :1;
    IO_WORD _TDD0 :1;
  }bit;
 }CUTDSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TDR23 :1;
    IO_WORD _TDR22 :1;
    IO_WORD _TDR21 :1;
    IO_WORD _TDR20 :1;
    IO_WORD _TDR19 :1;
    IO_WORD _TDR18 :1;
    IO_WORD _TDR17 :1;
    IO_WORD _TDR16 :1;
  }bit;
 }CUTR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _TDR15 :1;
    IO_WORD _TDR14 :1;
    IO_WORD _TDR13 :1;
    IO_WORD _TDR12 :1;
    IO_WORD _TDR11 :1;
    IO_WORD _TDR10 :1;
    IO_WORD _TDR9 :1;
    IO_WORD _TDR8 :1;
    IO_WORD _TDR7 :1;
    IO_WORD _TDR6 :1;
    IO_WORD _TDR5 :1;
    IO_WORD _TDR4 :1;
    IO_WORD _TDR3 :1;
    IO_WORD _TDR2 :1;
    IO_WORD _TDR1 :1;
    IO_WORD _TDR0 :1;
  }bit;
 }CUTR2STR;
typedef union{   /* Clock Modulator */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MP13 :1;
    IO_WORD _MP12 :1;
    IO_WORD _MP11 :1;
    IO_WORD _MP10 :1;
    IO_WORD _MP9 :1;
    IO_WORD _MP8 :1;
    IO_WORD _MP7 :1;
    IO_WORD _MP6 :1;
    IO_WORD _MP5 :1;
    IO_WORD _MP4 :1;
    IO_WORD _MP3 :1;
    IO_WORD _MP2 :1;
    IO_WORD _MP1 :1;
    IO_WORD _MP0 :1;
  }bit;
 }CMPRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _FMODRUN :1;
    IO_BYTE  :1;
    IO_BYTE _FMOD :1;
    IO_BYTE _PDX :1;
  }bit;
 }CMCRSTR;
typedef union{   /* CAN clock control */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CPCKS1 :1;
    IO_BYTE _CPCKS0 :1;
    IO_BYTE _DVC3 :1;
    IO_BYTE _DVC2 :1;
    IO_BYTE _DVC1 :1;
    IO_BYTE _DVC0 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CPCKS :2;
    IO_BYTE _DVC :4;
  }bitc;
 }CANPRESTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CANCKD5 :1;
    IO_BYTE _CANCKD4 :1;
    IO_BYTE _CANCKD3 :1;
    IO_BYTE _CANCKD2 :1;
    IO_BYTE _CANCKD1 :1;
    IO_BYTE _CANCKD0 :1;
  }bit;
 }CANCKDSTR;
typedef union{   /* LV Detection / Hardware-Watchdog */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _LVESEL3 :1;
    IO_BYTE _LVESEL2 :1;
    IO_BYTE _LVESEL1 :1;
    IO_BYTE _LVESEL0 :1;
    IO_BYTE _LVISEL3 :1;
    IO_BYTE _LVISEL2 :1;
    IO_BYTE _LVISEL1 :1;
    IO_BYTE _LVISEL0 :1;
  }bit;
  struct{
    IO_BYTE _LVESEL :4;
    IO_BYTE _LVISEL :4;
  }bitc;
 }LVSELSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _LVSEL :1;
    IO_BYTE _LVEPD :1;
    IO_BYTE _LVIPD :1;
    IO_BYTE _LVREN :1;
    IO_BYTE  :1;
    IO_BYTE _LVIEN :1;
    IO_BYTE _LVIRQ :1;
  }bit;
 }LVDETSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ED1 :1;
    IO_BYTE _ED0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _ED :2;
  }bitc;
 }HWWDESTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CPUF :1;
  }bit;
 }HWWDSTR;
typedef union{   /* Main-/Sub-Oscillatio Stabilization Timer */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _WIF :1;
    IO_BYTE _WIE :1;
    IO_BYTE _WEN :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _WS1 :1;
    IO_BYTE _WS0 :1;
    IO_BYTE _WCL :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WS :2;
  }bitc;
 }OSCRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _WIF :1;
    IO_BYTE _WIE :1;
    IO_BYTE _WEN :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _WS1 :1;
    IO_BYTE _WS0 :1;
    IO_BYTE _WCL :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WS :2;
  }bitc;
 }WPCRHSTR;
typedef union{   /* Main-/Sub-Oscillatio Standby Control */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _OSCDS1 :1;
  }bit;
 }OSCCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _FLASHSEL :1;
    IO_BYTE _MAINSEL :1;
    IO_BYTE _SUBSEL3 :1;
    IO_BYTE _SUBSEL2 :1;
    IO_BYTE _SUBSEL1 :1;
    IO_BYTE _SUBSEL0 :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _SUBSEL :4;
  }bitc;
 }REGSELSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _MSTBO :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _MAINKPEN :1;
    IO_BYTE _MAINDSBL :1;
  }bit;
 }REGCTRSTR;
typedef union{   /* External Bus/Chip Select Registers */
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD  :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD _LEND :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD _LEND :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR3STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD _LEND :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR3STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR4STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD _LEND :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR4STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR5STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD _LEND :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR5STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR6STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD _LEND :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR6STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _A31 :1;
    IO_WORD _A30 :1;
    IO_WORD _A29 :1;
    IO_WORD _A28 :1;
    IO_WORD _A27 :1;
    IO_WORD _A26 :1;
    IO_WORD _A25 :1;
    IO_WORD _A24 :1;
    IO_WORD _A23 :1;
    IO_WORD _A22 :1;
    IO_WORD _A21 :1;
    IO_WORD _A20 :1;
    IO_WORD _A19 :1;
    IO_WORD _A18 :1;
    IO_WORD _A17 :1;
    IO_WORD _A16 :1;
  }bit;
 }ASR7STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _ASZ3 :1;
    IO_WORD _ASZ2 :1;
    IO_WORD _ASZ1 :1;
    IO_WORD _ASZ0 :1;
    IO_WORD _DBW1 :1;
    IO_WORD _DBW0 :1;
    IO_WORD _BST1 :1;
    IO_WORD _BST0 :1;
    IO_WORD _SREN :1;
    IO_WORD _PFEN :1;
    IO_WORD _WREN :1;
    IO_WORD _LEND :1;
    IO_WORD _TYP3 :1;
    IO_WORD _TYP2 :1;
    IO_WORD _TYP1 :1;
    IO_WORD _TYP0 :1;
  }bit;
  struct{
    IO_WORD _ASZ :4;
    IO_WORD _DBW :2;
    IO_WORD _BST :2;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _TYP :4;
  }bitc;
 }ACR7STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR3STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR4STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR5STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR6STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _W15 :1;
    IO_WORD _W14 :1;
    IO_WORD _W13 :1;
    IO_WORD _W12 :1;
    IO_WORD _W11 :1;
    IO_WORD _W10 :1;
    IO_WORD _W9 :1;
    IO_WORD _W8 :1;
    IO_WORD _W7 :1;
    IO_WORD _W6 :1;
    IO_WORD _W5 :1;
    IO_WORD _W4 :1;
    IO_WORD _W3 :1;
    IO_WORD _W2 :1;
    IO_WORD _W1 :1;
    IO_WORD _W0 :1;
  }bit;
 }AWR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _PSZ2 :1;
    IO_BYTE _PSZ1 :1;
    IO_BYTE _PSZ0 :1;
    IO_BYTE _WBST :1;
    IO_BYTE _BANK :1;
    IO_BYTE _ABS1 :1;
    IO_BYTE _ABS0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _PSZ :3;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _ABS :2;
  }bitc;
 }MCRASTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _PSZ2 :1;
    IO_BYTE _PSZ1 :1;
    IO_BYTE _PSZ0 :1;
    IO_BYTE _WBST :1;
    IO_BYTE _BANK :1;
    IO_BYTE _ABS1 :1;
    IO_BYTE _ABS0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _PSZ :3;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _ABS :2;
  }bitc;
 }MCRBSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RYE0 :1;
    IO_BYTE _HLD0 :1;
    IO_BYTE _WR01 :1;
    IO_BYTE _WR00 :1;
    IO_BYTE _IW03 :1;
    IO_BYTE _IW02 :1;
    IO_BYTE _IW01 :1;
    IO_BYTE _IW00 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WR0 :2;
    IO_BYTE _IW0 :4;
  }bitc;
 }IOWR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RYE1 :1;
    IO_BYTE _HLD1 :1;
    IO_BYTE _WR11 :1;
    IO_BYTE _WR10 :1;
    IO_BYTE _IW13 :1;
    IO_BYTE _IW12 :1;
    IO_BYTE _IW11 :1;
    IO_BYTE _IW10 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WR1 :2;
    IO_BYTE _IW1 :4;
  }bitc;
 }IOWR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RYE2 :1;
    IO_BYTE _HLD2 :1;
    IO_BYTE _WR21 :1;
    IO_BYTE _WR20 :1;
    IO_BYTE _IW23 :1;
    IO_BYTE _IW22 :1;
    IO_BYTE _IW21 :1;
    IO_BYTE _IW20 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WR2 :2;
    IO_BYTE _IW2 :4;
  }bitc;
 }IOWR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _RYE3 :1;
    IO_BYTE _HLD3 :1;
    IO_BYTE _WR31 :1;
    IO_BYTE _WR30 :1;
    IO_BYTE _IW33 :1;
    IO_BYTE _IW32 :1;
    IO_BYTE _IW31 :1;
    IO_BYTE _IW30 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WR3 :2;
    IO_BYTE _IW3 :4;
  }bitc;
 }IOWR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CSE7 :1;
    IO_BYTE _CSE6 :1;
    IO_BYTE _CSE5 :1;
    IO_BYTE _CSE4 :1;
    IO_BYTE _CSE3 :1;
    IO_BYTE _CSE2 :1;
    IO_BYTE _CSE1 :1;
    IO_BYTE _CSE0 :1;
  }bit;
 }CSERSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _CHE7 :1;
    IO_BYTE _CHE6 :1;
    IO_BYTE _CHE5 :1;
    IO_BYTE _CHE4 :1;
    IO_BYTE _CHE3 :1;
    IO_BYTE _CHE2 :1;
    IO_BYTE _CHE1 :1;
    IO_BYTE _CHE0 :1;
  }bit;
 }CHERSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _BREN :1;
    IO_BYTE _PSUS :1;
    IO_BYTE _PCLR :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _RDW1 :1;
    IO_BYTE _RDW0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _RDW :2;
  }bitc;
 }TCRSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _SELF :1;
    IO_WORD _RRLD :1;
    IO_WORD _RFINT5 :1;
    IO_WORD _RFINT4 :1;
    IO_WORD _RDINT3 :1;
    IO_WORD _RFINT2 :1;
    IO_WORD _RFINT1 :1;
    IO_WORD _RFINT0 :1;
    IO_WORD _BRST :1;
    IO_WORD _RFC2 :1;
    IO_WORD _RFC1 :1;
    IO_WORD _RFC0 :1;
    IO_WORD _PON :1;
    IO_WORD _TRC2 :1;
    IO_WORD _TRC1 :1;
    IO_WORD _TRC0 :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _RFINT :6;
    IO_WORD :1;
    IO_WORD _RFC :3;
    IO_WORD :1;
    IO_WORD _TRC :3;
  }bitc;
 }RCRSTR;
typedef union{   /* Mode Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ROMA :1;
    IO_BYTE _WTH1 :1;
    IO_BYTE _WTH0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _WTH :2;
  }bitc;
 }MODRSTR;
typedef union{   /* R-bus Port Data Direct Read Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }PDRD10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PDRD17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PDRD29STR;
typedef union{   /* R-bus Port Direction Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }DDR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DDR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }DDR29STR;
typedef union{   /* R-bus Port Function Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }PFR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PFR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PFR29STR;
typedef union{   /* R-bus Port Extra Function Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EPFR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EPFR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPFR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPFR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EPFR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPFR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EPFR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPFR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPFR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPFR27STR;
typedef union{   /* R-bus Port Output Drive Select Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }PODR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PODR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PODR29STR;
typedef union{   /* R-bus Port Input Level Select Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }PILR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PILR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PILR29STR;
typedef union{   /* R-bus Port Extra Input Level Select Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }EPILR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EPILR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }EPILR29STR;
typedef union{   /* R-bus Port Pull-Up/Down  Enable Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }PPER10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PPER17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPER29STR;
typedef union{   /* R-bus Port Pull-Up/Down Control Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
  }bit;
 }PPCR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR13STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR14STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR15STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR16STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PPCR17STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR18STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR19STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE  :1;
    IO_BYTE _D2 :1;
    IO_BYTE  :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR22STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR23STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR24STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR25STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR26STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR27STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE _D7 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D0 :1;
  }bit;
 }PPCR29STR;
typedef union{   /* Flash Memory/I-Cache Control Register */
    IO_BYTE	byte;
    struct{   
    IO_BYTE _ASYNC :1;
    IO_BYTE _FIXE :1;
    IO_BYTE _BIRE :1;
    IO_BYTE _RDYEG :1;
    IO_BYTE _RDY :1;
    IO_BYTE _RDYI :1;
    IO_BYTE _RW16 :1;
    IO_BYTE _LPM :1;
  }bit;
 }FMCSSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _LOCK :1;
    IO_BYTE _PHASE :1;
    IO_BYTE _PF2I :1;
    IO_BYTE _RD64 :1;
  }bit;
 }FMCRSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _REN :1;
    IO_WORD _TAGE :1;
    IO_WORD _FLUSH :1;
    IO_WORD _DBEN :1;
    IO_WORD _PFEN :1;
    IO_WORD _PFMC :1;
    IO_WORD _LOCK :1;
    IO_WORD _ENAB :1;
    IO_WORD _SIZE1 :1;
    IO_WORD _SIZE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _SIZE :2;
  }bitc;
 }FCHCRSTR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _WTP1 :1;
    IO_WORD _WTP0 :1;
    IO_WORD _WEXH1 :1;
    IO_WORD _WEXH0 :1;
    IO_WORD _WTC3 :1;
    IO_WORD _WTC2 :1;
    IO_WORD _WTC1 :1;
    IO_WORD _WTC0 :1;
    IO_WORD _FRAM :1;
    IO_WORD _ATD2 :1;
    IO_WORD _ATD1 :1;
    IO_WORD _ATD0 :1;
    IO_WORD _EQ3 :1;
    IO_WORD _EQ2 :1;
    IO_WORD _EQ1 :1;
    IO_WORD _EQ0 :1;
  }bit;
  struct{
    IO_WORD _WTP :2;
    IO_WORD _WEXH :2;
    IO_WORD _WTC :4;
    IO_WORD :1;
    IO_WORD _ATD :3;
    IO_WORD _EQ :4;
  }bitc;
 }FMWTSTR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE _ALEH2 :1;
    IO_BYTE _ALEH1 :1;
    IO_BYTE _ALEH0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _ALEH :3;
  }bitc;
 }FMWT2STR;
typedef union{  
    IO_BYTE	byte;
    struct{   
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS0 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE :1;
    IO_BYTE _PS :3;
  }bitc;
 }FMPSSTR;
typedef union{   /* Flash Security Control Register */
    IO_LWORD	lword;
    struct{   
    IO_LWORD _CRC31 :1;
    IO_LWORD _CRC30 :1;
    IO_LWORD _CRC29 :1;
    IO_LWORD _CRC28 :1;
    IO_LWORD _CRC27 :1;
    IO_LWORD _CRC26 :1;
    IO_LWORD _CRC25 :1;
    IO_LWORD _CRC24 :1;
    IO_LWORD _CRC23 :1;
    IO_LWORD _CRC22 :1;
    IO_LWORD _CRC21 :1;
    IO_LWORD _CRC20 :1;
    IO_LWORD _CRC19 :1;
    IO_LWORD _CRC18 :1;
    IO_LWORD _CRC17 :1;
    IO_LWORD _CRC16 :1;
    IO_LWORD _CRC15 :1;
    IO_LWORD _CRC14 :1;
    IO_LWORD _CRC13 :1;
    IO_LWORD _CRC12 :1;
    IO_LWORD _CRC11 :1;
    IO_LWORD _CRC10 :1;
    IO_LWORD _CRC9 :1;
    IO_LWORD _CRC8 :1;
    IO_LWORD _CRC7 :1;
    IO_LWORD _CRC6 :1;
    IO_LWORD _CRC5 :1;
    IO_LWORD _CRC4 :1;
    IO_LWORD _CRC3 :1;
    IO_LWORD _CRC2 :1;
    IO_LWORD _CRC1 :1;
    IO_LWORD _CRC0 :1;
  }bit;
 }FSCR0STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _RDY :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _CSZ3 :1;
    IO_LWORD _CSZ2 :1;
    IO_LWORD _CSZ1 :1;
    IO_LWORD _CSZ0 :1;
    IO_LWORD _CSA15 :1;
    IO_LWORD _CSA14 :1;
    IO_LWORD _CSA13 :1;
    IO_LWORD _CSA12 :1;
    IO_LWORD _CSA11 :1;
    IO_LWORD _CSA10 :1;
    IO_LWORD _CSA9 :1;
    IO_LWORD _CSA8 :1;
    IO_LWORD _CSA7 :1;
    IO_LWORD _CSA6 :1;
    IO_LWORD _CSA5 :1;
    IO_LWORD _CSA4 :1;
    IO_LWORD _CSA3 :1;
    IO_LWORD _CSA2 :1;
    IO_LWORD _CSA1 :1;
    IO_LWORD _CSA0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CSZ :4;
  }bitc;
 }FSCR1STR;
typedef union{   /* CAN 0 Control Register */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _Test :1;
    IO_WORD _CCE :1;
    IO_WORD _DAR :1;
    IO_WORD  :1;
    IO_WORD _EIE :1;
    IO_WORD _SIE :1;
    IO_WORD _IE :1;
    IO_WORD _Init :1;
  }bit;
 }CTRLR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BOff :1;
    IO_WORD _EWarn :1;
    IO_WORD _EPass :1;
    IO_WORD _RxOK :1;
    IO_WORD _TxOK :1;
    IO_WORD _LEC2 :1;
    IO_WORD _LEC1 :1;
    IO_WORD _LEC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _LEC :3;
  }bitc;
 }STATR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _RP :1;
    IO_WORD _REC6 :1;
    IO_WORD _REC5 :1;
    IO_WORD _REC4 :1;
    IO_WORD _REC3 :1;
    IO_WORD _REC2 :1;
    IO_WORD _REC1 :1;
    IO_WORD _REC0 :1;
    IO_WORD _TEC7 :1;
    IO_WORD _TEC6 :1;
    IO_WORD _TEC5 :1;
    IO_WORD _TEC4 :1;
    IO_WORD _TEC3 :1;
    IO_WORD _TEC2 :1;
    IO_WORD _TEC1 :1;
    IO_WORD _TEC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD _REC :7;
    IO_WORD _TEC :8;
  }bitc;
 }ERRCNT0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD _Tseg22 :1;
    IO_WORD _Tseg21 :1;
    IO_WORD _Tseg20 :1;
    IO_WORD _Tseg13 :1;
    IO_WORD _Tseg12 :1;
    IO_WORD _Tseg11 :1;
    IO_WORD _Tseg10 :1;
    IO_WORD _SJW1 :1;
    IO_WORD _SJW0 :1;
    IO_WORD _BRP5 :1;
    IO_WORD _BRP4 :1;
    IO_WORD _BRP3 :1;
    IO_WORD _BRP2 :1;
    IO_WORD _BRP1 :1;
    IO_WORD _BRP0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD _Tseg2 :3;
    IO_WORD _Tseg1 :4;
    IO_WORD _SJW :2;
    IO_WORD _BRP :6;
  }bitc;
 }BTR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _Rx :1;
    IO_WORD _Tx1 :1;
    IO_WORD _Tx0 :1;
    IO_WORD _LBack :1;
    IO_WORD _Silent :1;
    IO_WORD _Basic :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _Tx :2;
  }bitc;
 }TESTR0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BRPE3 :1;
    IO_WORD _BRPE2 :1;
    IO_WORD _BRPE1 :1;
    IO_WORD _BRPE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _BRPE :4;
  }bitc;
 }BRPER0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }BRPE0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }CBSYNC0STR;
typedef union{   /* CAN 0 IF 1 */
    IO_WORD	word;
    struct{   
    IO_WORD _Busy :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MN5 :1;
    IO_WORD _MN4 :1;
    IO_WORD _MN3 :1;
    IO_WORD _MN2 :1;
    IO_WORD _MN1 :1;
    IO_WORD _MN0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _MN :6;
  }bitc;
 }IF1CREQ0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _WR :1;
    IO_WORD _Mask :1;
    IO_WORD _Arb :1;
    IO_WORD _Control :1;
    IO_WORD _CIP :1;
    IO_WORD _TxReq :1;
    IO_WORD _DataA :1;
    IO_WORD _DataB :1;
  }bit;
 }IF1CMSK0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MXtd :1;
    IO_WORD _MDir :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1MSK20STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MsgVal :1;
    IO_WORD _Xtd :1;
    IO_WORD _DIR :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1ARB20STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _NewDat :1;
    IO_WORD _MsgLst :1;
    IO_WORD _IntPnd :1;
    IO_WORD _UMask :1;
    IO_WORD _TxIE :1;
    IO_WORD _RxIE :1;
    IO_WORD _RmtEn :1;
    IO_WORD _TxRqst :1;
    IO_WORD _EoB :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _DLC3 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _DLC :4;
  }bitc;
 }IF1MCTR0STR;
typedef union{   /* CAN 0 IF 2 */
    IO_WORD	word;
    struct{   
    IO_WORD _Busy :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MN5 :1;
    IO_WORD _MN4 :1;
    IO_WORD _MN3 :1;
    IO_WORD _MN2 :1;
    IO_WORD _MN1 :1;
    IO_WORD _MN0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _MN :6;
  }bitc;
 }IF2CREQ0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _WR :1;
    IO_WORD _Mask :1;
    IO_WORD _Arb :1;
    IO_WORD _Control :1;
    IO_WORD _CIP :1;
    IO_WORD _TxReq :1;
    IO_WORD _DataA :1;
    IO_WORD _DataB :1;
  }bit;
 }IF2CMSK0STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MXtd :1;
    IO_WORD _MDir :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2MSK20STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MsgVal :1;
    IO_WORD _Xtd :1;
    IO_WORD _DIR :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2ARB20STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _NewDat :1;
    IO_WORD _MsgLst :1;
    IO_WORD _IntPnd :1;
    IO_WORD _UMask :1;
    IO_WORD _TxIE :1;
    IO_WORD _RxIE :1;
    IO_WORD _RmtEn :1;
    IO_WORD _TxRqst :1;
    IO_WORD _EoB :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _DLC3 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _DLC :4;
  }bitc;
 }IF2MCTR0STR;
typedef union{   /* CAN 1 Control Register */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _Test :1;
    IO_WORD _CCE :1;
    IO_WORD _DAR :1;
    IO_WORD  :1;
    IO_WORD _EIE :1;
    IO_WORD _SIE :1;
    IO_WORD _IE :1;
    IO_WORD _Init :1;
  }bit;
 }CTRLR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BOff :1;
    IO_WORD _EWarn :1;
    IO_WORD _EPass :1;
    IO_WORD _RxOK :1;
    IO_WORD _TxOK :1;
    IO_WORD _LEC2 :1;
    IO_WORD _LEC1 :1;
    IO_WORD _LEC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _LEC :3;
  }bitc;
 }STATR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _RP :1;
    IO_WORD _REC6 :1;
    IO_WORD _REC5 :1;
    IO_WORD _REC4 :1;
    IO_WORD _REC3 :1;
    IO_WORD _REC2 :1;
    IO_WORD _REC1 :1;
    IO_WORD _REC0 :1;
    IO_WORD _TEC7 :1;
    IO_WORD _TEC6 :1;
    IO_WORD _TEC5 :1;
    IO_WORD _TEC4 :1;
    IO_WORD _TEC3 :1;
    IO_WORD _TEC2 :1;
    IO_WORD _TEC1 :1;
    IO_WORD _TEC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD _REC :7;
    IO_WORD _TEC :8;
  }bitc;
 }ERRCNT1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD _Tseg22 :1;
    IO_WORD _Tseg21 :1;
    IO_WORD _Tseg20 :1;
    IO_WORD _Tseg13 :1;
    IO_WORD _Tseg12 :1;
    IO_WORD _Tseg11 :1;
    IO_WORD _Tseg10 :1;
    IO_WORD _SJW1 :1;
    IO_WORD _SJW0 :1;
    IO_WORD _BRP5 :1;
    IO_WORD _BRP4 :1;
    IO_WORD _BRP3 :1;
    IO_WORD _BRP2 :1;
    IO_WORD _BRP1 :1;
    IO_WORD _BRP0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD _Tseg2 :3;
    IO_WORD _Tseg1 :4;
    IO_WORD _SJW :2;
    IO_WORD _BRP :6;
  }bitc;
 }BTR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _Rx :1;
    IO_WORD _Tx1 :1;
    IO_WORD _Tx0 :1;
    IO_WORD _LBack :1;
    IO_WORD _Silent :1;
    IO_WORD _Basic :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _Tx :2;
  }bitc;
 }TESTR1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BRPE3 :1;
    IO_WORD _BRPE2 :1;
    IO_WORD _BRPE1 :1;
    IO_WORD _BRPE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _BRPE :4;
  }bitc;
 }BRPER1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }BRPE1STR;
typedef union{   /* CAN 1 IF 1 */
    IO_WORD	word;
    struct{   
    IO_WORD _Busy :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MN5 :1;
    IO_WORD _MN4 :1;
    IO_WORD _MN3 :1;
    IO_WORD _MN2 :1;
    IO_WORD _MN1 :1;
    IO_WORD _MN0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _MN :6;
  }bitc;
 }IF1CREQ1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _WR :1;
    IO_WORD _Mask :1;
    IO_WORD _Arb :1;
    IO_WORD _Control :1;
    IO_WORD _CIP :1;
    IO_WORD _TxReq :1;
    IO_WORD _DataA :1;
    IO_WORD _DataB :1;
  }bit;
 }IF1CMSK1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MXtd :1;
    IO_WORD _MDir :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1MSK21STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MsgVal :1;
    IO_WORD _Xtd :1;
    IO_WORD _DIR :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1ARB21STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _NewDat :1;
    IO_WORD _MsgLst :1;
    IO_WORD _IntPnd :1;
    IO_WORD _UMask :1;
    IO_WORD _TxIE :1;
    IO_WORD _RxIE :1;
    IO_WORD _RmtEn :1;
    IO_WORD _TxRqst :1;
    IO_WORD _EoB :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _DLC3 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _DLC :4;
  }bitc;
 }IF1MCTR1STR;
typedef union{   /* CAN 1 IF 2 */
    IO_WORD	word;
    struct{   
    IO_WORD _Busy :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MN5 :1;
    IO_WORD _MN4 :1;
    IO_WORD _MN3 :1;
    IO_WORD _MN2 :1;
    IO_WORD _MN1 :1;
    IO_WORD _MN0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _MN :6;
  }bitc;
 }IF2CREQ1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _WR :1;
    IO_WORD _Mask :1;
    IO_WORD _Arb :1;
    IO_WORD _Control :1;
    IO_WORD _CIP :1;
    IO_WORD _TxReq :1;
    IO_WORD _DataA :1;
    IO_WORD _DataB :1;
  }bit;
 }IF2CMSK1STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MXtd :1;
    IO_WORD _MDir :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2MSK21STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MsgVal :1;
    IO_WORD _Xtd :1;
    IO_WORD _DIR :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2ARB21STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _NewDat :1;
    IO_WORD _MsgLst :1;
    IO_WORD _IntPnd :1;
    IO_WORD _UMask :1;
    IO_WORD _TxIE :1;
    IO_WORD _RxIE :1;
    IO_WORD _RmtEn :1;
    IO_WORD _TxRqst :1;
    IO_WORD _EoB :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _DLC3 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _DLC :4;
  }bitc;
 }IF2MCTR1STR;
typedef union{   /* CAN 2 Control Register */
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _Test :1;
    IO_WORD _CCE :1;
    IO_WORD _DAR :1;
    IO_WORD  :1;
    IO_WORD _EIE :1;
    IO_WORD _SIE :1;
    IO_WORD _IE :1;
    IO_WORD _Init :1;
  }bit;
 }CTRLR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BOff :1;
    IO_WORD _EWarn :1;
    IO_WORD _EPass :1;
    IO_WORD _RxOK :1;
    IO_WORD _TxOK :1;
    IO_WORD _LEC2 :1;
    IO_WORD _LEC1 :1;
    IO_WORD _LEC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _LEC :3;
  }bitc;
 }STATR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _RP :1;
    IO_WORD _REC6 :1;
    IO_WORD _REC5 :1;
    IO_WORD _REC4 :1;
    IO_WORD _REC3 :1;
    IO_WORD _REC2 :1;
    IO_WORD _REC1 :1;
    IO_WORD _REC0 :1;
    IO_WORD _TEC7 :1;
    IO_WORD _TEC6 :1;
    IO_WORD _TEC5 :1;
    IO_WORD _TEC4 :1;
    IO_WORD _TEC3 :1;
    IO_WORD _TEC2 :1;
    IO_WORD _TEC1 :1;
    IO_WORD _TEC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD _REC :7;
    IO_WORD _TEC :8;
  }bitc;
 }ERRCNT2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD _Tseg22 :1;
    IO_WORD _Tseg21 :1;
    IO_WORD _Tseg20 :1;
    IO_WORD _Tseg13 :1;
    IO_WORD _Tseg12 :1;
    IO_WORD _Tseg11 :1;
    IO_WORD _Tseg10 :1;
    IO_WORD _SJW1 :1;
    IO_WORD _SJW0 :1;
    IO_WORD _BRP5 :1;
    IO_WORD _BRP4 :1;
    IO_WORD _BRP3 :1;
    IO_WORD _BRP2 :1;
    IO_WORD _BRP1 :1;
    IO_WORD _BRP0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD _Tseg2 :3;
    IO_WORD _Tseg1 :4;
    IO_WORD _SJW :2;
    IO_WORD _BRP :6;
  }bitc;
 }BTR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _Rx :1;
    IO_WORD _Tx1 :1;
    IO_WORD _Tx0 :1;
    IO_WORD _LBack :1;
    IO_WORD _Silent :1;
    IO_WORD _Basic :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _Tx :2;
  }bitc;
 }TESTR2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BRPE3 :1;
    IO_WORD _BRPE2 :1;
    IO_WORD _BRPE1 :1;
    IO_WORD _BRPE0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _BRPE :4;
  }bitc;
 }BRPER2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }BRPE2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }CBSYNC2STR;
typedef union{   /* CAN 2 IF 1 */
    IO_WORD	word;
    struct{   
    IO_WORD _Busy :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MN5 :1;
    IO_WORD _MN4 :1;
    IO_WORD _MN3 :1;
    IO_WORD _MN2 :1;
    IO_WORD _MN1 :1;
    IO_WORD _MN0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _MN :6;
  }bitc;
 }IF1CREQ2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _WR :1;
    IO_WORD _Mask :1;
    IO_WORD _Arb :1;
    IO_WORD _Control :1;
    IO_WORD _CIP :1;
    IO_WORD _TxReq :1;
    IO_WORD _DataA :1;
    IO_WORD _DataB :1;
  }bit;
 }IF1CMSK2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MXtd :1;
    IO_WORD _MDir :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1MSK22STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MsgVal :1;
    IO_WORD _Xtd :1;
    IO_WORD _DIR :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1ARB22STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _NewDat :1;
    IO_WORD _MsgLst :1;
    IO_WORD _IntPnd :1;
    IO_WORD _UMask :1;
    IO_WORD _TxIE :1;
    IO_WORD _RxIE :1;
    IO_WORD _RmtEn :1;
    IO_WORD _TxRqst :1;
    IO_WORD _EoB :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _DLC3 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _DLC :4;
  }bitc;
 }IF1MCTR2STR;
typedef union{   /* CAN 2 IF 2 */
    IO_WORD	word;
    struct{   
    IO_WORD _Busy :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MN5 :1;
    IO_WORD _MN4 :1;
    IO_WORD _MN3 :1;
    IO_WORD _MN2 :1;
    IO_WORD _MN1 :1;
    IO_WORD _MN0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _MN :6;
  }bitc;
 }IF2CREQ2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _WR :1;
    IO_WORD _Mask :1;
    IO_WORD _Arb :1;
    IO_WORD _Control :1;
    IO_WORD _CIP :1;
    IO_WORD _TxReq :1;
    IO_WORD _DataA :1;
    IO_WORD _DataB :1;
  }bit;
 }IF2CMSK2STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MXtd :1;
    IO_WORD _MDir :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2MSK22STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _MsgVal :1;
    IO_WORD _Xtd :1;
    IO_WORD _DIR :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2ARB22STR;
typedef union{  
    IO_WORD	word;
    struct{   
    IO_WORD _NewDat :1;
    IO_WORD _MsgLst :1;
    IO_WORD _IntPnd :1;
    IO_WORD _UMask :1;
    IO_WORD _TxIE :1;
    IO_WORD _RxIE :1;
    IO_WORD _RmtEn :1;
    IO_WORD _TxRqst :1;
    IO_WORD _EoB :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _DLC3 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC0 :1;
  }bit;
  struct{
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD :1;
    IO_WORD _DLC :4;
  }bitc;
 }IF2MCTR2STR;
typedef union{   /* EDSU/MPU Registers */
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SR :1;
    IO_LWORD _SW :1;
    IO_LWORD _SX :1;
    IO_LWORD _UR :1;
    IO_LWORD _UW :1;
    IO_LWORD _UX :1;
    IO_LWORD _FCPU :1;
    IO_LWORD _FDMA :1;
    IO_LWORD _EEMM :1;
    IO_LWORD _PFD :1;
    IO_LWORD _SINT1 :1;
    IO_LWORD _SINT0 :1;
    IO_LWORD _EINT1 :1;
    IO_LWORD _EINT0 :1;
    IO_LWORD _EINTT :1;
    IO_LWORD _EINTR :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _SINT :2;
    IO_LWORD _EINT :2;
  }bitc;
 }BCTRLSTR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _IDX4 :1;
    IO_LWORD _IDX3 :1;
    IO_LWORD _IDX2 :1;
    IO_LWORD _IDX1 :1;
    IO_LWORD _IDX0 :1;
    IO_LWORD _CDMA :1;
    IO_LWORD _CSZ1 :1;
    IO_LWORD _CSZ0 :1;
    IO_LWORD _CRW1 :1;
    IO_LWORD _CRW0 :1;
    IO_LWORD _PV :1;
    IO_LWORD _RST :1;
    IO_LWORD _INT1 :1;
    IO_LWORD _INT0 :1;
    IO_LWORD _INTT :1;
    IO_LWORD _INTR :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _IDX :5;
    IO_LWORD :1;
    IO_LWORD _CSZ :2;
    IO_LWORD _CRW :2;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _INT :2;
  }bitc;
 }BSTATSTR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD _BD31 :1;
    IO_LWORD _BD30 :1;
    IO_LWORD _BD29 :1;
    IO_LWORD _BD28 :1;
    IO_LWORD _BD27 :1;
    IO_LWORD _BD26 :1;
    IO_LWORD _BD25 :1;
    IO_LWORD _BD24 :1;
    IO_LWORD _BD23 :1;
    IO_LWORD _BD22 :1;
    IO_LWORD _BD21 :1;
    IO_LWORD _BD20 :1;
    IO_LWORD _BD19 :1;
    IO_LWORD _BD18 :1;
    IO_LWORD _BD17 :1;
    IO_LWORD _BD16 :1;
    IO_LWORD _BD15 :1;
    IO_LWORD _BD14 :1;
    IO_LWORD _BD13 :1;
    IO_LWORD _BD12 :1;
    IO_LWORD _BD11 :1;
    IO_LWORD _BD10 :1;
    IO_LWORD _BD9 :1;
    IO_LWORD _BD8 :1;
    IO_LWORD _BD7 :1;
    IO_LWORD _BD6 :1;
    IO_LWORD _BD5 :1;
    IO_LWORD _BD4 :1;
    IO_LWORD _BD3 :1;
    IO_LWORD _BD2 :1;
    IO_LWORD _BD1 :1;
    IO_LWORD _BD0 :1;
  }bit;
 }BIRQSTR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR0STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR1STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR2STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR3STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR4STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR5STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR6STR;
typedef union{  
    IO_LWORD	lword;
    struct{   
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD _SRX1 :1;
    IO_LWORD _SW1 :1;
    IO_LWORD _SRX0 :1;
    IO_LWORD _SW0 :1;
    IO_LWORD _URX1 :1;
    IO_LWORD _UW1 :1;
    IO_LWORD _URX0 :1;
    IO_LWORD _UW0 :1;
    IO_LWORD _MPE :1;
    IO_LWORD _COMB :1;
    IO_LWORD _CTC1 :1;
    IO_LWORD _CTC0 :1;
    IO_LWORD _OBS1 :1;
    IO_LWORD _OBS0 :1;
    IO_LWORD _OBT1 :1;
    IO_LWORD _OBT0 :1;
    IO_LWORD _EP3 :1;
    IO_LWORD _EP2 :1;
    IO_LWORD _EP1 :1;
    IO_LWORD _EP0 :1;
    IO_LWORD _EM1 :1;
    IO_LWORD _EM0 :1;
    IO_LWORD _ER1 :1;
    IO_LWORD _ER0 :1;
  }bit;
  struct{
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD :1;
    IO_LWORD _CTC :2;
    IO_LWORD _OBS :2;
    IO_LWORD _OBT :2;
    IO_LWORD _EP :4;
    IO_LWORD _EM :2;
    IO_LWORD _ER :2;
  }bitc;
 }BCR7STR;

/* C-DECLARATIONS */

__IO_EXTERN __io PDR00STR pdr00;   /* Port Data Register */
#define PDR00 pdr00.byte
#define PDR00_D7 pdr00.bit._D7
#define PDR00_D6 pdr00.bit._D6
#define PDR00_D5 pdr00.bit._D5
#define PDR00_D4 pdr00.bit._D4
#define PDR00_D3 pdr00.bit._D3
#define PDR00_D2 pdr00.bit._D2
#define PDR00_D1 pdr00.bit._D1
#define PDR00_D0 pdr00.bit._D0
__IO_EXTERN __io PDR01STR pdr01;  
#define PDR01 pdr01.byte
#define PDR01_D7 pdr01.bit._D7
#define PDR01_D6 pdr01.bit._D6
#define PDR01_D5 pdr01.bit._D5
#define PDR01_D4 pdr01.bit._D4
#define PDR01_D3 pdr01.bit._D3
#define PDR01_D2 pdr01.bit._D2
#define PDR01_D1 pdr01.bit._D1
#define PDR01_D0 pdr01.bit._D0
__IO_EXTERN __io PDR02STR pdr02;  
#define PDR02 pdr02.byte
#define PDR02_D7 pdr02.bit._D7
#define PDR02_D6 pdr02.bit._D6
#define PDR02_D5 pdr02.bit._D5
#define PDR02_D4 pdr02.bit._D4
#define PDR02_D3 pdr02.bit._D3
#define PDR02_D2 pdr02.bit._D2
#define PDR02_D1 pdr02.bit._D1
#define PDR02_D0 pdr02.bit._D0
__IO_EXTERN __io PDR03STR pdr03;  
#define PDR03 pdr03.byte
#define PDR03_D7 pdr03.bit._D7
#define PDR03_D6 pdr03.bit._D6
#define PDR03_D5 pdr03.bit._D5
#define PDR03_D4 pdr03.bit._D4
#define PDR03_D3 pdr03.bit._D3
#define PDR03_D2 pdr03.bit._D2
#define PDR03_D1 pdr03.bit._D1
#define PDR03_D0 pdr03.bit._D0
__IO_EXTERN __io PDR04STR pdr04;  
#define PDR04 pdr04.byte
#define PDR04_D1 pdr04.bit._D1
#define PDR04_D0 pdr04.bit._D0
__IO_EXTERN __io PDR05STR pdr05;  
#define PDR05 pdr05.byte
#define PDR05_D7 pdr05.bit._D7
#define PDR05_D6 pdr05.bit._D6
#define PDR05_D5 pdr05.bit._D5
#define PDR05_D4 pdr05.bit._D4
#define PDR05_D3 pdr05.bit._D3
#define PDR05_D2 pdr05.bit._D2
#define PDR05_D1 pdr05.bit._D1
#define PDR05_D0 pdr05.bit._D0
__IO_EXTERN __io PDR06STR pdr06;  
#define PDR06 pdr06.byte
#define PDR06_D7 pdr06.bit._D7
#define PDR06_D6 pdr06.bit._D6
#define PDR06_D5 pdr06.bit._D5
#define PDR06_D4 pdr06.bit._D4
#define PDR06_D3 pdr06.bit._D3
#define PDR06_D2 pdr06.bit._D2
#define PDR06_D1 pdr06.bit._D1
#define PDR06_D0 pdr06.bit._D0
__IO_EXTERN __io PDR07STR pdr07;  
#define PDR07 pdr07.byte
#define PDR07_D7 pdr07.bit._D7
#define PDR07_D6 pdr07.bit._D6
#define PDR07_D5 pdr07.bit._D5
#define PDR07_D4 pdr07.bit._D4
#define PDR07_D3 pdr07.bit._D3
#define PDR07_D2 pdr07.bit._D2
#define PDR07_D1 pdr07.bit._D1
#define PDR07_D0 pdr07.bit._D0
__IO_EXTERN __io PDR08STR pdr08;  
#define PDR08 pdr08.byte
#define PDR08_D7 pdr08.bit._D7
#define PDR08_D6 pdr08.bit._D6
#define PDR08_D5 pdr08.bit._D5
#define PDR08_D4 pdr08.bit._D4
#define PDR08_D3 pdr08.bit._D3
#define PDR08_D2 pdr08.bit._D2
#define PDR08_D1 pdr08.bit._D1
#define PDR08_D0 pdr08.bit._D0
__IO_EXTERN __io PDR09STR pdr09;  
#define PDR09 pdr09.byte
#define PDR09_D7 pdr09.bit._D7
#define PDR09_D6 pdr09.bit._D6
#define PDR09_D3 pdr09.bit._D3
#define PDR09_D2 pdr09.bit._D2
#define PDR09_D1 pdr09.bit._D1
#define PDR09_D0 pdr09.bit._D0
__IO_EXTERN __io PDR10STR pdr10;  
#define PDR10 pdr10.byte
#define PDR10_D6 pdr10.bit._D6
#define PDR10_D5 pdr10.bit._D5
#define PDR10_D4 pdr10.bit._D4
#define PDR10_D3 pdr10.bit._D3
#define PDR10_D2 pdr10.bit._D2
#define PDR10_D1 pdr10.bit._D1
__IO_EXTERN __io PDR13STR pdr13;  
#define PDR13 pdr13.byte
#define PDR13_D2 pdr13.bit._D2
#define PDR13_D1 pdr13.bit._D1
#define PDR13_D0 pdr13.bit._D0
__IO_EXTERN __io PDR14STR pdr14;  
#define PDR14 pdr14.byte
#define PDR14_D7 pdr14.bit._D7
#define PDR14_D6 pdr14.bit._D6
#define PDR14_D5 pdr14.bit._D5
#define PDR14_D4 pdr14.bit._D4
#define PDR14_D3 pdr14.bit._D3
#define PDR14_D2 pdr14.bit._D2
#define PDR14_D1 pdr14.bit._D1
#define PDR14_D0 pdr14.bit._D0
__IO_EXTERN __io PDR15STR pdr15;  
#define PDR15 pdr15.byte
#define PDR15_D3 pdr15.bit._D3
#define PDR15_D2 pdr15.bit._D2
#define PDR15_D1 pdr15.bit._D1
#define PDR15_D0 pdr15.bit._D0
__IO_EXTERN __io PDR16STR pdr16;  
#define PDR16 pdr16.byte
#define PDR16_D7 pdr16.bit._D7
#define PDR16_D6 pdr16.bit._D6
#define PDR16_D5 pdr16.bit._D5
#define PDR16_D4 pdr16.bit._D4
#define PDR16_D3 pdr16.bit._D3
#define PDR16_D2 pdr16.bit._D2
#define PDR16_D1 pdr16.bit._D1
#define PDR16_D0 pdr16.bit._D0
__IO_EXTERN __io PDR17STR pdr17;  
#define PDR17 pdr17.byte
#define PDR17_D7 pdr17.bit._D7
#define PDR17_D6 pdr17.bit._D6
#define PDR17_D5 pdr17.bit._D5
#define PDR17_D4 pdr17.bit._D4
__IO_EXTERN __io PDR18STR pdr18;  
#define PDR18 pdr18.byte
#define PDR18_D6 pdr18.bit._D6
#define PDR18_D5 pdr18.bit._D5
#define PDR18_D4 pdr18.bit._D4
#define PDR18_D2 pdr18.bit._D2
#define PDR18_D1 pdr18.bit._D1
#define PDR18_D0 pdr18.bit._D0
__IO_EXTERN __io PDR19STR pdr19;  
#define PDR19 pdr19.byte
#define PDR19_D6 pdr19.bit._D6
#define PDR19_D5 pdr19.bit._D5
#define PDR19_D4 pdr19.bit._D4
#define PDR19_D2 pdr19.bit._D2
#define PDR19_D1 pdr19.bit._D1
#define PDR19_D0 pdr19.bit._D0
__IO_EXTERN __io PDR20STR pdr20;  
#define PDR20 pdr20.byte
#define PDR20_D2 pdr20.bit._D2
#define PDR20_D1 pdr20.bit._D1
#define PDR20_D0 pdr20.bit._D0
__IO_EXTERN __io PDR22STR pdr22;  
#define PDR22 pdr22.byte
#define PDR22_D5 pdr22.bit._D5
#define PDR22_D4 pdr22.bit._D4
#define PDR22_D2 pdr22.bit._D2
#define PDR22_D0 pdr22.bit._D0
__IO_EXTERN __io PDR23STR pdr23;  
#define PDR23 pdr23.byte
#define PDR23_D5 pdr23.bit._D5
#define PDR23_D4 pdr23.bit._D4
#define PDR23_D3 pdr23.bit._D3
#define PDR23_D2 pdr23.bit._D2
#define PDR23_D1 pdr23.bit._D1
#define PDR23_D0 pdr23.bit._D0
__IO_EXTERN __io PDR24STR pdr24;  
#define PDR24 pdr24.byte
#define PDR24_D7 pdr24.bit._D7
#define PDR24_D6 pdr24.bit._D6
#define PDR24_D5 pdr24.bit._D5
#define PDR24_D4 pdr24.bit._D4
#define PDR24_D3 pdr24.bit._D3
#define PDR24_D2 pdr24.bit._D2
#define PDR24_D1 pdr24.bit._D1
#define PDR24_D0 pdr24.bit._D0
__IO_EXTERN __io PDR25STR pdr25;  
#define PDR25 pdr25.byte
#define PDR25_D7 pdr25.bit._D7
#define PDR25_D6 pdr25.bit._D6
#define PDR25_D5 pdr25.bit._D5
#define PDR25_D4 pdr25.bit._D4
#define PDR25_D3 pdr25.bit._D3
#define PDR25_D2 pdr25.bit._D2
#define PDR25_D1 pdr25.bit._D1
#define PDR25_D0 pdr25.bit._D0
__IO_EXTERN __io PDR26STR pdr26;  
#define PDR26 pdr26.byte
#define PDR26_D7 pdr26.bit._D7
#define PDR26_D6 pdr26.bit._D6
#define PDR26_D5 pdr26.bit._D5
#define PDR26_D4 pdr26.bit._D4
#define PDR26_D3 pdr26.bit._D3
#define PDR26_D2 pdr26.bit._D2
#define PDR26_D1 pdr26.bit._D1
#define PDR26_D0 pdr26.bit._D0
__IO_EXTERN __io PDR27STR pdr27;  
#define PDR27 pdr27.byte
#define PDR27_D7 pdr27.bit._D7
#define PDR27_D6 pdr27.bit._D6
#define PDR27_D5 pdr27.bit._D5
#define PDR27_D4 pdr27.bit._D4
#define PDR27_D3 pdr27.bit._D3
#define PDR27_D2 pdr27.bit._D2
#define PDR27_D1 pdr27.bit._D1
#define PDR27_D0 pdr27.bit._D0
__IO_EXTERN __io PDR29STR pdr29;  
#define PDR29 pdr29.byte
#define PDR29_D7 pdr29.bit._D7
#define PDR29_D6 pdr29.bit._D6
#define PDR29_D5 pdr29.bit._D5
#define PDR29_D4 pdr29.bit._D4
#define PDR29_D3 pdr29.bit._D3
#define PDR29_D2 pdr29.bit._D2
#define PDR29_D1 pdr29.bit._D1
#define PDR29_D0 pdr29.bit._D0
__IO_EXTERN __io EIRR0STR eirr0;   /* External Interrupt 0-7 */
#define EIRR0 eirr0.byte
#define EIRR0_ER7 eirr0.bit._ER7
#define EIRR0_ER6 eirr0.bit._ER6
#define EIRR0_ER5 eirr0.bit._ER5
#define EIRR0_ER4 eirr0.bit._ER4
#define EIRR0_ER3 eirr0.bit._ER3
#define EIRR0_ER2 eirr0.bit._ER2
#define EIRR0_ER1 eirr0.bit._ER1
#define EIRR0_ER0 eirr0.bit._ER0
__IO_EXTERN __io ENIR0STR enir0;  
#define ENIR0 enir0.byte
#define ENIR0_EN7 enir0.bit._EN7
#define ENIR0_EN6 enir0.bit._EN6
#define ENIR0_EN5 enir0.bit._EN5
#define ENIR0_EN4 enir0.bit._EN4
#define ENIR0_EN3 enir0.bit._EN3
#define ENIR0_EN2 enir0.bit._EN2
#define ENIR0_EN1 enir0.bit._EN1
#define ENIR0_EN0 enir0.bit._EN0
__IO_EXTERN __io ELVR0STR elvr0;  
#define ELVR0 elvr0.word
#define ELVR0_LB7 elvr0.bit._LB7
#define ELVR0_LA7 elvr0.bit._LA7
#define ELVR0_LB6 elvr0.bit._LB6
#define ELVR0_LA6 elvr0.bit._LA6
#define ELVR0_LB5 elvr0.bit._LB5
#define ELVR0_LA5 elvr0.bit._LA5
#define ELVR0_LB4 elvr0.bit._LB4
#define ELVR0_LA4 elvr0.bit._LA4
#define ELVR0_LB3 elvr0.bit._LB3
#define ELVR0_LA3 elvr0.bit._LA3
#define ELVR0_LB2 elvr0.bit._LB2
#define ELVR0_LA2 elvr0.bit._LA2
#define ELVR0_LB1 elvr0.bit._LB1
#define ELVR0_LA1 elvr0.bit._LA1
#define ELVR0_LB0 elvr0.bit._LB0
#define ELVR0_LA0 elvr0.bit._LA0
__IO_EXTERN __io EIRR1STR eirr1;   /* External Interrupt 8-15 */
#define EIRR1 eirr1.byte
#define EIRR1_ER15 eirr1.bit._ER15
#define EIRR1_ER14 eirr1.bit._ER14
#define EIRR1_ER13 eirr1.bit._ER13
#define EIRR1_ER12 eirr1.bit._ER12
#define EIRR1_ER11 eirr1.bit._ER11
#define EIRR1_ER10 eirr1.bit._ER10
#define EIRR1_ER9 eirr1.bit._ER9
#define EIRR1_ER8 eirr1.bit._ER8
__IO_EXTERN __io ENIR1STR enir1;  
#define ENIR1 enir1.byte
#define ENIR1_EN15 enir1.bit._EN15
#define ENIR1_EN14 enir1.bit._EN14
#define ENIR1_EN13 enir1.bit._EN13
#define ENIR1_EN12 enir1.bit._EN12
#define ENIR1_EN11 enir1.bit._EN11
#define ENIR1_EN10 enir1.bit._EN10
#define ENIR1_EN9 enir1.bit._EN9
#define ENIR1_EN8 enir1.bit._EN8
__IO_EXTERN __io ELVR1STR elvr1;  
#define ELVR1 elvr1.word
#define ELVR1_LB15 elvr1.bit._LB15
#define ELVR1_LA15 elvr1.bit._LA15
#define ELVR1_LB14 elvr1.bit._LB14
#define ELVR1_LA14 elvr1.bit._LA14
#define ELVR1_LB13 elvr1.bit._LB13
#define ELVR1_LA13 elvr1.bit._LA13
#define ELVR1_LB12 elvr1.bit._LB12
#define ELVR1_LA12 elvr1.bit._LA12
#define ELVR1_LB11 elvr1.bit._LB11
#define ELVR1_LA11 elvr1.bit._LA11
#define ELVR1_LB10 elvr1.bit._LB10
#define ELVR1_LA10 elvr1.bit._LA10
#define ELVR1_LB9 elvr1.bit._LB9
#define ELVR1_LA9 elvr1.bit._LA9
#define ELVR1_LB8 elvr1.bit._LB8
#define ELVR1_LA8 elvr1.bit._LA8
__IO_EXTERN __io DICRSTR dicr;   /* DLYI/I-unit */
#define DICR dicr.byte
#define DICR_DLYI dicr.bit._DLYI
__IO_EXTERN __io HRCLSTR hrcl;  
#define HRCL hrcl.byte
#define HRCL_MHALTI hrcl.bit._MHALTI
#define HRCL_LVL4 hrcl.bit._LVL4
#define HRCL_LVL3 hrcl.bit._LVL3
#define HRCL_LVL2 hrcl.bit._LVL2
#define HRCL_LVL1 hrcl.bit._LVL1
#define HRCL_LVL0 hrcl.bit._LVL0
#define HRCL_LVL hrcl.bitc._LVL
__IO_EXTERN __io IO_WORD rbsync;   /* R-Bus Sync */
#define RBSYNC rbsync
__IO_EXTERN __io SCR02STR scr02;   /* USART (LIN) 2 */
#define SCR02 scr02.byte
#define SCR02_PEN scr02.bit._PEN
#define SCR02_P scr02.bit._P
#define SCR02_SBL scr02.bit._SBL
#define SCR02_CL scr02.bit._CL
#define SCR02_AD scr02.bit._AD
#define SCR02_CRE scr02.bit._CRE
#define SCR02_RXE scr02.bit._RXE
#define SCR02_TXE scr02.bit._TXE
__IO_EXTERN __io SMR02STR smr02;  
#define SMR02 smr02.byte
#define SMR02_MD1 smr02.bit._MD1
#define SMR02_MD0 smr02.bit._MD0
#define SMR02_OTO smr02.bit._OTO
#define SMR02_EXT smr02.bit._EXT
#define SMR02_REST smr02.bit._REST
#define SMR02_UPCL smr02.bit._UPCL
#define SMR02_SCKE smr02.bit._SCKE
#define SMR02_SOE smr02.bit._SOE
#define SMR02_MD smr02.bitc._MD
__IO_EXTERN __io SSR02STR ssr02;  
#define SSR02 ssr02.byte
#define SSR02_PE ssr02.bit._PE
#define SSR02_ORE ssr02.bit._ORE
#define SSR02_FRE ssr02.bit._FRE
#define SSR02_RDRF ssr02.bit._RDRF
#define SSR02_TDRE ssr02.bit._TDRE
#define SSR02_BDS ssr02.bit._BDS
#define SSR02_RIE ssr02.bit._RIE
#define SSR02_TIE ssr02.bit._TIE
__IO_EXTERN __io IO_BYTE rdr02;  
#define RDR02 rdr02
__IO_EXTERN __io IO_BYTE tdr02;  
#define TDR02 tdr02
__IO_EXTERN __io ESCR02STR escr02;  
#define ESCR02 escr02.byte
#define ESCR02_LBIE escr02.bit._LBIE
#define ESCR02_LBD escr02.bit._LBD
#define ESCR02_LBL1 escr02.bit._LBL1
#define ESCR02_LBL0 escr02.bit._LBL0
#define ESCR02_SOPE escr02.bit._SOPE
#define ESCR02_SIOP escr02.bit._SIOP
#define ESCR02_CCO escr02.bit._CCO
#define ESCR02_SCES escr02.bit._SCES
#define ESCR02_LBL escr02.bitc._LBL
__IO_EXTERN __io ECCR02STR eccr02;  
#define ECCR02 eccr02.byte
#define ECCR02_INV eccr02.bit._INV
#define ECCR02_LBR eccr02.bit._LBR
#define ECCR02_MS eccr02.bit._MS
#define ECCR02_SCDE eccr02.bit._SCDE
#define ECCR02_SSM eccr02.bit._SSM
#define ECCR02_BIE eccr02.bit._BIE
#define ECCR02_RBI eccr02.bit._RBI
#define ECCR02_TBI eccr02.bit._TBI
__IO_EXTERN __io SCR04STR scr04;   /* USART (LIN) 4 with FIFO */
#define SCR04 scr04.byte
#define SCR04_PEN scr04.bit._PEN
#define SCR04_P scr04.bit._P
#define SCR04_SBL scr04.bit._SBL
#define SCR04_CL scr04.bit._CL
#define SCR04_AD scr04.bit._AD
#define SCR04_CRE scr04.bit._CRE
#define SCR04_RXE scr04.bit._RXE
#define SCR04_TXE scr04.bit._TXE
__IO_EXTERN __io SMR04STR smr04;  
#define SMR04 smr04.byte
#define SMR04_MD1 smr04.bit._MD1
#define SMR04_MD0 smr04.bit._MD0
#define SMR04_OTO smr04.bit._OTO
#define SMR04_EXT smr04.bit._EXT
#define SMR04_REST smr04.bit._REST
#define SMR04_UPCL smr04.bit._UPCL
#define SMR04_SCKE smr04.bit._SCKE
#define SMR04_SOE smr04.bit._SOE
#define SMR04_MD smr04.bitc._MD
__IO_EXTERN __io SSR04STR ssr04;  
#define SSR04 ssr04.byte
#define SSR04_PE ssr04.bit._PE
#define SSR04_ORE ssr04.bit._ORE
#define SSR04_FRE ssr04.bit._FRE
#define SSR04_RDRF ssr04.bit._RDRF
#define SSR04_TDRE ssr04.bit._TDRE
#define SSR04_BDS ssr04.bit._BDS
#define SSR04_RIE ssr04.bit._RIE
#define SSR04_TIE ssr04.bit._TIE
__IO_EXTERN __io IO_BYTE rdr04;  
#define RDR04 rdr04
__IO_EXTERN __io IO_BYTE tdr04;  
#define TDR04 tdr04
__IO_EXTERN __io ESCR04STR escr04;  
#define ESCR04 escr04.byte
#define ESCR04_LBIE escr04.bit._LBIE
#define ESCR04_LBD escr04.bit._LBD
#define ESCR04_LBL1 escr04.bit._LBL1
#define ESCR04_LBL0 escr04.bit._LBL0
#define ESCR04_SOPE escr04.bit._SOPE
#define ESCR04_SIOP escr04.bit._SIOP
#define ESCR04_CCO escr04.bit._CCO
#define ESCR04_SCES escr04.bit._SCES
#define ESCR04_LBL escr04.bitc._LBL
__IO_EXTERN __io ECCR04STR eccr04;  
#define ECCR04 eccr04.byte
#define ECCR04_INV eccr04.bit._INV
#define ECCR04_LBR eccr04.bit._LBR
#define ECCR04_MS eccr04.bit._MS
#define ECCR04_SCDE eccr04.bit._SCDE
#define ECCR04_SSM eccr04.bit._SSM
#define ECCR04_BIE eccr04.bit._BIE
#define ECCR04_RBI eccr04.bit._RBI
#define ECCR04_TBI eccr04.bit._TBI
__IO_EXTERN __io IO_BYTE fsr04;  
#define FSR04 fsr04
__IO_EXTERN __io FCR04STR fcr04;  
#define FCR04 fcr04.byte
#define FCR04_RXL3 fcr04.bit._RXL3
#define FCR04_RXL2 fcr04.bit._RXL2
#define FCR04_RXL1 fcr04.bit._RXL1
#define FCR04_RXL0 fcr04.bit._RXL0
#define FCR04_ERX fcr04.bit._ERX
#define FCR04_ETX fcr04.bit._ETX
#define FCR04_SVD fcr04.bit._SVD
#define FCR04_RXL fcr04.bitc._RXL
__IO_EXTERN __io SCR05STR scr05;   /* USART (LIN) 5 with FIFO */
#define SCR05 scr05.byte
#define SCR05_PEN scr05.bit._PEN
#define SCR05_P scr05.bit._P
#define SCR05_SBL scr05.bit._SBL
#define SCR05_CL scr05.bit._CL
#define SCR05_AD scr05.bit._AD
#define SCR05_CRE scr05.bit._CRE
#define SCR05_RXE scr05.bit._RXE
#define SCR05_TXE scr05.bit._TXE
__IO_EXTERN __io SMR05STR smr05;  
#define SMR05 smr05.byte
#define SMR05_MD1 smr05.bit._MD1
#define SMR05_MD0 smr05.bit._MD0
#define SMR05_OTO smr05.bit._OTO
#define SMR05_EXT smr05.bit._EXT
#define SMR05_REST smr05.bit._REST
#define SMR05_UPCL smr05.bit._UPCL
#define SMR05_SCKE smr05.bit._SCKE
#define SMR05_SOE smr05.bit._SOE
#define SMR05_MD smr05.bitc._MD
__IO_EXTERN __io SSR05STR ssr05;  
#define SSR05 ssr05.byte
#define SSR05_PE ssr05.bit._PE
#define SSR05_ORE ssr05.bit._ORE
#define SSR05_FRE ssr05.bit._FRE
#define SSR05_RDRF ssr05.bit._RDRF
#define SSR05_TDRE ssr05.bit._TDRE
#define SSR05_BDS ssr05.bit._BDS
#define SSR05_RIE ssr05.bit._RIE
#define SSR05_TIE ssr05.bit._TIE
__IO_EXTERN __io IO_BYTE rdr05;  
#define RDR05 rdr05
__IO_EXTERN __io IO_BYTE tdr05;  
#define TDR05 tdr05
__IO_EXTERN __io ESCR05STR escr05;  
#define ESCR05 escr05.byte
#define ESCR05_LBIE escr05.bit._LBIE
#define ESCR05_LBD escr05.bit._LBD
#define ESCR05_LBL1 escr05.bit._LBL1
#define ESCR05_LBL0 escr05.bit._LBL0
#define ESCR05_SOPE escr05.bit._SOPE
#define ESCR05_SIOP escr05.bit._SIOP
#define ESCR05_CCO escr05.bit._CCO
#define ESCR05_SCES escr05.bit._SCES
#define ESCR05_LBL escr05.bitc._LBL
__IO_EXTERN __io ECCR05STR eccr05;  
#define ECCR05 eccr05.byte
#define ECCR05_INV eccr05.bit._INV
#define ECCR05_LBR eccr05.bit._LBR
#define ECCR05_MS eccr05.bit._MS
#define ECCR05_SCDE eccr05.bit._SCDE
#define ECCR05_SSM eccr05.bit._SSM
#define ECCR05_BIE eccr05.bit._BIE
#define ECCR05_RBI eccr05.bit._RBI
#define ECCR05_TBI eccr05.bit._TBI
__IO_EXTERN __io IO_BYTE fsr05;  
#define FSR05 fsr05
__IO_EXTERN __io FCR05STR fcr05;  
#define FCR05 fcr05.byte
#define FCR05_RXL3 fcr05.bit._RXL3
#define FCR05_RXL2 fcr05.bit._RXL2
#define FCR05_RXL1 fcr05.bit._RXL1
#define FCR05_RXL0 fcr05.bit._RXL0
#define FCR05_ERX fcr05.bit._ERX
#define FCR05_ETX fcr05.bit._ETX
#define FCR05_SVD fcr05.bit._SVD
#define FCR05_RXL fcr05.bitc._RXL
__IO_EXTERN __io SCR06STR scr06;   /* USART (LIN) 6 with FIFO */
#define SCR06 scr06.byte
#define SCR06_PEN scr06.bit._PEN
#define SCR06_P scr06.bit._P
#define SCR06_SBL scr06.bit._SBL
#define SCR06_CL scr06.bit._CL
#define SCR06_AD scr06.bit._AD
#define SCR06_CRE scr06.bit._CRE
#define SCR06_RXE scr06.bit._RXE
#define SCR06_TXE scr06.bit._TXE
__IO_EXTERN __io SMR06STR smr06;  
#define SMR06 smr06.byte
#define SMR06_MD1 smr06.bit._MD1
#define SMR06_MD0 smr06.bit._MD0
#define SMR06_OTO smr06.bit._OTO
#define SMR06_EXT smr06.bit._EXT
#define SMR06_REST smr06.bit._REST
#define SMR06_UPCL smr06.bit._UPCL
#define SMR06_SCKE smr06.bit._SCKE
#define SMR06_SOE smr06.bit._SOE
#define SMR06_MD smr06.bitc._MD
__IO_EXTERN __io SSR06STR ssr06;  
#define SSR06 ssr06.byte
#define SSR06_PE ssr06.bit._PE
#define SSR06_ORE ssr06.bit._ORE
#define SSR06_FRE ssr06.bit._FRE
#define SSR06_RDRF ssr06.bit._RDRF
#define SSR06_TDRE ssr06.bit._TDRE
#define SSR06_BDS ssr06.bit._BDS
#define SSR06_RIE ssr06.bit._RIE
#define SSR06_TIE ssr06.bit._TIE
__IO_EXTERN __io IO_BYTE rdr06;  
#define RDR06 rdr06
__IO_EXTERN __io IO_BYTE tdr06;  
#define TDR06 tdr06
__IO_EXTERN __io ESCR06STR escr06;  
#define ESCR06 escr06.byte
#define ESCR06_LBIE escr06.bit._LBIE
#define ESCR06_LBD escr06.bit._LBD
#define ESCR06_LBL1 escr06.bit._LBL1
#define ESCR06_LBL0 escr06.bit._LBL0
#define ESCR06_SOPE escr06.bit._SOPE
#define ESCR06_SIOP escr06.bit._SIOP
#define ESCR06_CCO escr06.bit._CCO
#define ESCR06_SCES escr06.bit._SCES
#define ESCR06_LBL escr06.bitc._LBL
__IO_EXTERN __io ECCR06STR eccr06;  
#define ECCR06 eccr06.byte
#define ECCR06_INV eccr06.bit._INV
#define ECCR06_LBR eccr06.bit._LBR
#define ECCR06_MS eccr06.bit._MS
#define ECCR06_SCDE eccr06.bit._SCDE
#define ECCR06_SSM eccr06.bit._SSM
#define ECCR06_BIE eccr06.bit._BIE
#define ECCR06_RBI eccr06.bit._RBI
#define ECCR06_TBI eccr06.bit._TBI
__IO_EXTERN __io IO_BYTE fsr06;  
#define FSR06 fsr06
__IO_EXTERN __io FCR06STR fcr06;  
#define FCR06 fcr06.byte
#define FCR06_RXL3 fcr06.bit._RXL3
#define FCR06_RXL2 fcr06.bit._RXL2
#define FCR06_RXL1 fcr06.bit._RXL1
#define FCR06_RXL0 fcr06.bit._RXL0
#define FCR06_ERX fcr06.bit._ERX
#define FCR06_ETX fcr06.bit._ETX
#define FCR06_SVD fcr06.bit._SVD
#define FCR06_RXL fcr06.bitc._RXL
__IO_EXTERN __io SCR07STR scr07;   /* USART (LIN) 7 with FIFO */
#define SCR07 scr07.byte
#define SCR07_PEN scr07.bit._PEN
#define SCR07_P scr07.bit._P
#define SCR07_SBL scr07.bit._SBL
#define SCR07_CL scr07.bit._CL
#define SCR07_AD scr07.bit._AD
#define SCR07_CRE scr07.bit._CRE
#define SCR07_RXE scr07.bit._RXE
#define SCR07_TXE scr07.bit._TXE
__IO_EXTERN __io SMR07STR smr07;  
#define SMR07 smr07.byte
#define SMR07_MD1 smr07.bit._MD1
#define SMR07_MD0 smr07.bit._MD0
#define SMR07_OTO smr07.bit._OTO
#define SMR07_EXT smr07.bit._EXT
#define SMR07_REST smr07.bit._REST
#define SMR07_UPCL smr07.bit._UPCL
#define SMR07_SCKE smr07.bit._SCKE
#define SMR07_SOE smr07.bit._SOE
#define SMR07_MD smr07.bitc._MD
__IO_EXTERN __io SSR07STR ssr07;  
#define SSR07 ssr07.byte
#define SSR07_PE ssr07.bit._PE
#define SSR07_ORE ssr07.bit._ORE
#define SSR07_FRE ssr07.bit._FRE
#define SSR07_RDRF ssr07.bit._RDRF
#define SSR07_TDRE ssr07.bit._TDRE
#define SSR07_BDS ssr07.bit._BDS
#define SSR07_RIE ssr07.bit._RIE
#define SSR07_TIE ssr07.bit._TIE
__IO_EXTERN __io IO_BYTE rdr07;  
#define RDR07 rdr07
__IO_EXTERN __io IO_BYTE tdr07;  
#define TDR07 tdr07
__IO_EXTERN __io ESCR07STR escr07;  
#define ESCR07 escr07.byte
#define ESCR07_LBIE escr07.bit._LBIE
#define ESCR07_LBD escr07.bit._LBD
#define ESCR07_LBL1 escr07.bit._LBL1
#define ESCR07_LBL0 escr07.bit._LBL0
#define ESCR07_SOPE escr07.bit._SOPE
#define ESCR07_SIOP escr07.bit._SIOP
#define ESCR07_CCO escr07.bit._CCO
#define ESCR07_SCES escr07.bit._SCES
#define ESCR07_LBL escr07.bitc._LBL
__IO_EXTERN __io ECCR07STR eccr07;  
#define ECCR07 eccr07.byte
#define ECCR07_INV eccr07.bit._INV
#define ECCR07_LBR eccr07.bit._LBR
#define ECCR07_MS eccr07.bit._MS
#define ECCR07_SCDE eccr07.bit._SCDE
#define ECCR07_SSM eccr07.bit._SSM
#define ECCR07_BIE eccr07.bit._BIE
#define ECCR07_RBI eccr07.bit._RBI
#define ECCR07_TBI eccr07.bit._TBI
__IO_EXTERN __io IO_BYTE fsr07;  
#define FSR07 fsr07
__IO_EXTERN __io FCR07STR fcr07;  
#define FCR07 fcr07.byte
#define FCR07_RXL3 fcr07.bit._RXL3
#define FCR07_RXL2 fcr07.bit._RXL2
#define FCR07_RXL1 fcr07.bit._RXL1
#define FCR07_RXL0 fcr07.bit._RXL0
#define FCR07_ERX fcr07.bit._ERX
#define FCR07_ETX fcr07.bit._ETX
#define FCR07_SVD fcr07.bit._SVD
#define FCR07_RXL fcr07.bitc._RXL
__IO_EXTERN __io IO_WORD bgr02;   /* Bauderate Generator USART (LIN) 2,4-7 */
#define BGR02 bgr02
__IO_EXTERN __io IO_BYTE bgr102;  
#define BGR102 bgr102
__IO_EXTERN __io IO_BYTE bgr002;  
#define BGR002 bgr002
__IO_EXTERN __io IO_WORD bgr04;  
#define BGR04 bgr04
__IO_EXTERN __io IO_BYTE bgr104;  
#define BGR104 bgr104
__IO_EXTERN __io IO_BYTE bgr004;  
#define BGR004 bgr004
__IO_EXTERN __io IO_WORD bgr05;  
#define BGR05 bgr05
__IO_EXTERN __io IO_BYTE bgr105;  
#define BGR105 bgr105
__IO_EXTERN __io IO_BYTE bgr005;  
#define BGR005 bgr005
__IO_EXTERN __io IO_WORD bgr06;  
#define BGR06 bgr06
__IO_EXTERN __io IO_BYTE bgr106;  
#define BGR106 bgr106
__IO_EXTERN __io IO_BYTE bgr006;  
#define BGR006 bgr006
__IO_EXTERN __io IO_WORD bgr07;  
#define BGR07 bgr07
__IO_EXTERN __io IO_BYTE bgr107;  
#define BGR107 bgr107
__IO_EXTERN __io IO_BYTE bgr007;  
#define BGR007 bgr007
__IO_EXTERN __io PWC20STR pwc20;   /* Stepper Motor 0 */
#define PWC20 pwc20.word
#define PWC20_D9 pwc20.bit._D9
#define PWC20_D8 pwc20.bit._D8
#define PWC20_D7 pwc20.bit._D7
#define PWC20_D6 pwc20.bit._D6
#define PWC20_D5 pwc20.bit._D5
#define PWC20_D4 pwc20.bit._D4
#define PWC20_D3 pwc20.bit._D3
#define PWC20_D2 pwc20.bit._D2
#define PWC20_D1 pwc20.bit._D1
#define PWC20_D0 pwc20.bit._D0
__IO_EXTERN __io PWC10STR pwc10;  
#define PWC10 pwc10.word
#define PWC10_D9 pwc10.bit._D9
#define PWC10_D8 pwc10.bit._D8
#define PWC10_D7 pwc10.bit._D7
#define PWC10_D6 pwc10.bit._D6
#define PWC10_D5 pwc10.bit._D5
#define PWC10_D4 pwc10.bit._D4
#define PWC10_D3 pwc10.bit._D3
#define PWC10_D2 pwc10.bit._D2
#define PWC10_D1 pwc10.bit._D1
#define PWC10_D0 pwc10.bit._D0
__IO_EXTERN __io PWS20STR pws20;  
#define PWS20 pws20.byte
#define PWS20_BS pws20.bit._BS
#define PWS20_P2 pws20.bit._P2
#define PWS20_P1 pws20.bit._P1
#define PWS20_P0 pws20.bit._P0
#define PWS20_M2 pws20.bit._M2
#define PWS20_M1 pws20.bit._M1
#define PWS20_M0 pws20.bit._M0
#define PWS20_P pws20.bitc._P
#define PWS20_M pws20.bitc._M
__IO_EXTERN __io PWS10STR pws10;  
#define PWS10 pws10.byte
#define PWS10_P2 pws10.bit._P2
#define PWS10_P1 pws10.bit._P1
#define PWS10_P0 pws10.bit._P0
#define PWS10_M2 pws10.bit._M2
#define PWS10_M1 pws10.bit._M1
#define PWS10_M0 pws10.bit._M0
#define PWS10_P pws10.bitc._P
#define PWS10_M pws10.bitc._M
__IO_EXTERN __io PWC21STR pwc21;   /* Stepper Motor 1 */
#define PWC21 pwc21.word
#define PWC21_D9 pwc21.bit._D9
#define PWC21_D8 pwc21.bit._D8
#define PWC21_D7 pwc21.bit._D7
#define PWC21_D6 pwc21.bit._D6
#define PWC21_D5 pwc21.bit._D5
#define PWC21_D4 pwc21.bit._D4
#define PWC21_D3 pwc21.bit._D3
#define PWC21_D2 pwc21.bit._D2
#define PWC21_D1 pwc21.bit._D1
#define PWC21_D0 pwc21.bit._D0
__IO_EXTERN __io PWC11STR pwc11;  
#define PWC11 pwc11.word
#define PWC11_D9 pwc11.bit._D9
#define PWC11_D8 pwc11.bit._D8
#define PWC11_D7 pwc11.bit._D7
#define PWC11_D6 pwc11.bit._D6
#define PWC11_D5 pwc11.bit._D5
#define PWC11_D4 pwc11.bit._D4
#define PWC11_D3 pwc11.bit._D3
#define PWC11_D2 pwc11.bit._D2
#define PWC11_D1 pwc11.bit._D1
#define PWC11_D0 pwc11.bit._D0
__IO_EXTERN __io PWS21STR pws21;  
#define PWS21 pws21.byte
#define PWS21_BS pws21.bit._BS
#define PWS21_P2 pws21.bit._P2
#define PWS21_P1 pws21.bit._P1
#define PWS21_P0 pws21.bit._P0
#define PWS21_M2 pws21.bit._M2
#define PWS21_M1 pws21.bit._M1
#define PWS21_M0 pws21.bit._M0
#define PWS21_P pws21.bitc._P
#define PWS21_M pws21.bitc._M
__IO_EXTERN __io PWS11STR pws11;  
#define PWS11 pws11.byte
#define PWS11_P2 pws11.bit._P2
#define PWS11_P1 pws11.bit._P1
#define PWS11_P0 pws11.bit._P0
#define PWS11_M2 pws11.bit._M2
#define PWS11_M1 pws11.bit._M1
#define PWS11_M0 pws11.bit._M0
#define PWS11_P pws11.bitc._P
#define PWS11_M pws11.bitc._M
__IO_EXTERN __io PWC22STR pwc22;   /* Stepper Motor 2 */
#define PWC22 pwc22.word
#define PWC22_D9 pwc22.bit._D9
#define PWC22_D8 pwc22.bit._D8
#define PWC22_D7 pwc22.bit._D7
#define PWC22_D6 pwc22.bit._D6
#define PWC22_D5 pwc22.bit._D5
#define PWC22_D4 pwc22.bit._D4
#define PWC22_D3 pwc22.bit._D3
#define PWC22_D2 pwc22.bit._D2
#define PWC22_D1 pwc22.bit._D1
#define PWC22_D0 pwc22.bit._D0
__IO_EXTERN __io PWC12STR pwc12;  
#define PWC12 pwc12.word
#define PWC12_D9 pwc12.bit._D9
#define PWC12_D8 pwc12.bit._D8
#define PWC12_D7 pwc12.bit._D7
#define PWC12_D6 pwc12.bit._D6
#define PWC12_D5 pwc12.bit._D5
#define PWC12_D4 pwc12.bit._D4
#define PWC12_D3 pwc12.bit._D3
#define PWC12_D2 pwc12.bit._D2
#define PWC12_D1 pwc12.bit._D1
#define PWC12_D0 pwc12.bit._D0
__IO_EXTERN __io PWS22STR pws22;  
#define PWS22 pws22.byte
#define PWS22_BS pws22.bit._BS
#define PWS22_P2 pws22.bit._P2
#define PWS22_P1 pws22.bit._P1
#define PWS22_P0 pws22.bit._P0
#define PWS22_M2 pws22.bit._M2
#define PWS22_M1 pws22.bit._M1
#define PWS22_M0 pws22.bit._M0
#define PWS22_P pws22.bitc._P
#define PWS22_M pws22.bitc._M
__IO_EXTERN __io PWS12STR pws12;  
#define PWS12 pws12.byte
#define PWS12_P2 pws12.bit._P2
#define PWS12_P1 pws12.bit._P1
#define PWS12_P0 pws12.bit._P0
#define PWS12_M2 pws12.bit._M2
#define PWS12_M1 pws12.bit._M1
#define PWS12_M0 pws12.bit._M0
#define PWS12_P pws12.bitc._P
#define PWS12_M pws12.bitc._M
__IO_EXTERN __io PWC23STR pwc23;   /* Stepper Motor 3 */
#define PWC23 pwc23.word
#define PWC23_D9 pwc23.bit._D9
#define PWC23_D8 pwc23.bit._D8
#define PWC23_D7 pwc23.bit._D7
#define PWC23_D6 pwc23.bit._D6
#define PWC23_D5 pwc23.bit._D5
#define PWC23_D4 pwc23.bit._D4
#define PWC23_D3 pwc23.bit._D3
#define PWC23_D2 pwc23.bit._D2
#define PWC23_D1 pwc23.bit._D1
#define PWC23_D0 pwc23.bit._D0
__IO_EXTERN __io PWC13STR pwc13;  
#define PWC13 pwc13.word
#define PWC13_D9 pwc13.bit._D9
#define PWC13_D8 pwc13.bit._D8
#define PWC13_D7 pwc13.bit._D7
#define PWC13_D6 pwc13.bit._D6
#define PWC13_D5 pwc13.bit._D5
#define PWC13_D4 pwc13.bit._D4
#define PWC13_D3 pwc13.bit._D3
#define PWC13_D2 pwc13.bit._D2
#define PWC13_D1 pwc13.bit._D1
#define PWC13_D0 pwc13.bit._D0
__IO_EXTERN __io PWS23STR pws23;  
#define PWS23 pws23.byte
#define PWS23_BS pws23.bit._BS
#define PWS23_P2 pws23.bit._P2
#define PWS23_P1 pws23.bit._P1
#define PWS23_P0 pws23.bit._P0
#define PWS23_M2 pws23.bit._M2
#define PWS23_M1 pws23.bit._M1
#define PWS23_M0 pws23.bit._M0
#define PWS23_P pws23.bitc._P
#define PWS23_M pws23.bitc._M
__IO_EXTERN __io PWS13STR pws13;  
#define PWS13 pws13.byte
#define PWS13_P2 pws13.bit._P2
#define PWS13_P1 pws13.bit._P1
#define PWS13_P0 pws13.bit._P0
#define PWS13_M2 pws13.bit._M2
#define PWS13_M1 pws13.bit._M1
#define PWS13_M0 pws13.bit._M0
#define PWS13_P pws13.bitc._P
#define PWS13_M pws13.bitc._M
__IO_EXTERN __io PWC24STR pwc24;   /* Stepper Motor 4 */
#define PWC24 pwc24.word
#define PWC24_D9 pwc24.bit._D9
#define PWC24_D8 pwc24.bit._D8
#define PWC24_D7 pwc24.bit._D7
#define PWC24_D6 pwc24.bit._D6
#define PWC24_D5 pwc24.bit._D5
#define PWC24_D4 pwc24.bit._D4
#define PWC24_D3 pwc24.bit._D3
#define PWC24_D2 pwc24.bit._D2
#define PWC24_D1 pwc24.bit._D1
#define PWC24_D0 pwc24.bit._D0
__IO_EXTERN __io PWC14STR pwc14;  
#define PWC14 pwc14.word
#define PWC14_D9 pwc14.bit._D9
#define PWC14_D8 pwc14.bit._D8
#define PWC14_D7 pwc14.bit._D7
#define PWC14_D6 pwc14.bit._D6
#define PWC14_D5 pwc14.bit._D5
#define PWC14_D4 pwc14.bit._D4
#define PWC14_D3 pwc14.bit._D3
#define PWC14_D2 pwc14.bit._D2
#define PWC14_D1 pwc14.bit._D1
#define PWC14_D0 pwc14.bit._D0
__IO_EXTERN __io PWS24STR pws24;  
#define PWS24 pws24.byte
#define PWS24_BS pws24.bit._BS
#define PWS24_P2 pws24.bit._P2
#define PWS24_P1 pws24.bit._P1
#define PWS24_P0 pws24.bit._P0
#define PWS24_M2 pws24.bit._M2
#define PWS24_M1 pws24.bit._M1
#define PWS24_M0 pws24.bit._M0
#define PWS24_P pws24.bitc._P
#define PWS24_M pws24.bitc._M
__IO_EXTERN __io PWS14STR pws14;  
#define PWS14 pws14.byte
#define PWS14_P2 pws14.bit._P2
#define PWS14_P1 pws14.bit._P1
#define PWS14_P0 pws14.bit._P0
#define PWS14_M2 pws14.bit._M2
#define PWS14_M1 pws14.bit._M1
#define PWS14_M0 pws14.bit._M0
#define PWS14_P pws14.bitc._P
#define PWS14_M pws14.bitc._M
__IO_EXTERN __io PWC25STR pwc25;   /* Stepper Motor 5 */
#define PWC25 pwc25.word
#define PWC25_D9 pwc25.bit._D9
#define PWC25_D8 pwc25.bit._D8
#define PWC25_D7 pwc25.bit._D7
#define PWC25_D6 pwc25.bit._D6
#define PWC25_D5 pwc25.bit._D5
#define PWC25_D4 pwc25.bit._D4
#define PWC25_D3 pwc25.bit._D3
#define PWC25_D2 pwc25.bit._D2
#define PWC25_D1 pwc25.bit._D1
#define PWC25_D0 pwc25.bit._D0
__IO_EXTERN __io PWC15STR pwc15;  
#define PWC15 pwc15.word
#define PWC15_D9 pwc15.bit._D9
#define PWC15_D8 pwc15.bit._D8
#define PWC15_D7 pwc15.bit._D7
#define PWC15_D6 pwc15.bit._D6
#define PWC15_D5 pwc15.bit._D5
#define PWC15_D4 pwc15.bit._D4
#define PWC15_D3 pwc15.bit._D3
#define PWC15_D2 pwc15.bit._D2
#define PWC15_D1 pwc15.bit._D1
#define PWC15_D0 pwc15.bit._D0
__IO_EXTERN __io PWS25STR pws25;  
#define PWS25 pws25.byte
#define PWS25_BS pws25.bit._BS
#define PWS25_P2 pws25.bit._P2
#define PWS25_P1 pws25.bit._P1
#define PWS25_P0 pws25.bit._P0
#define PWS25_M2 pws25.bit._M2
#define PWS25_M1 pws25.bit._M1
#define PWS25_M0 pws25.bit._M0
#define PWS25_P pws25.bitc._P
#define PWS25_M pws25.bitc._M
__IO_EXTERN __io PWS15STR pws15;  
#define PWS15 pws15.byte
#define PWS15_P2 pws15.bit._P2
#define PWS15_P1 pws15.bit._P1
#define PWS15_P0 pws15.bit._P0
#define PWS15_M2 pws15.bit._M2
#define PWS15_M1 pws15.bit._M1
#define PWS15_M0 pws15.bit._M0
#define PWS15_P pws15.bitc._P
#define PWS15_M pws15.bitc._M
__IO_EXTERN __io PWC0STR pwc0;   /* Stepper Motor Control 0-5 */
#define PWC0 pwc0.byte
#define PWC0_S2 pwc0.bit._S2
#define PWC0_P2 pwc0.bit._P2
#define PWC0_P1 pwc0.bit._P1
#define PWC0_P0 pwc0.bit._P0
#define PWC0_CE pwc0.bit._CE
#define PWC0_SC pwc0.bit._SC
#define PWC0_P pwc0.bitc._P
__IO_EXTERN __io PWC1STR pwc1;  
#define PWC1 pwc1.byte
#define PWC1_S2 pwc1.bit._S2
#define PWC1_P2 pwc1.bit._P2
#define PWC1_P1 pwc1.bit._P1
#define PWC1_P0 pwc1.bit._P0
#define PWC1_CE pwc1.bit._CE
#define PWC1_SC pwc1.bit._SC
#define PWC1_P pwc1.bitc._P
__IO_EXTERN __io PWC2STR pwc2;  
#define PWC2 pwc2.byte
#define PWC2_S2 pwc2.bit._S2
#define PWC2_P2 pwc2.bit._P2
#define PWC2_P1 pwc2.bit._P1
#define PWC2_P0 pwc2.bit._P0
#define PWC2_CE pwc2.bit._CE
#define PWC2_SC pwc2.bit._SC
#define PWC2_P pwc2.bitc._P
__IO_EXTERN __io PWC3STR pwc3;  
#define PWC3 pwc3.byte
#define PWC3_S2 pwc3.bit._S2
#define PWC3_P2 pwc3.bit._P2
#define PWC3_P1 pwc3.bit._P1
#define PWC3_P0 pwc3.bit._P0
#define PWC3_CE pwc3.bit._CE
#define PWC3_SC pwc3.bit._SC
#define PWC3_P pwc3.bitc._P
__IO_EXTERN __io PWC4STR pwc4;  
#define PWC4 pwc4.byte
#define PWC4_S2 pwc4.bit._S2
#define PWC4_P2 pwc4.bit._P2
#define PWC4_P1 pwc4.bit._P1
#define PWC4_P0 pwc4.bit._P0
#define PWC4_CE pwc4.bit._CE
#define PWC4_SC pwc4.bit._SC
#define PWC4_P pwc4.bitc._P
__IO_EXTERN __io PWC5STR pwc5;  
#define PWC5 pwc5.byte
#define PWC5_S2 pwc5.bit._S2
#define PWC5_P2 pwc5.bit._P2
#define PWC5_P1 pwc5.bit._P1
#define PWC5_P0 pwc5.bit._P0
#define PWC5_CE pwc5.bit._CE
#define PWC5_SC pwc5.bit._SC
#define PWC5_P pwc5.bitc._P
__IO_EXTERN __io IBCR0STR ibcr0;   /* I2C 0 */
#define IBCR0 ibcr0.byte
#define IBCR0_BER ibcr0.bit._BER
#define IBCR0_BEIE ibcr0.bit._BEIE
#define IBCR0_SCC ibcr0.bit._SCC
#define IBCR0_MSS ibcr0.bit._MSS
#define IBCR0_ACK ibcr0.bit._ACK
#define IBCR0_GCAA ibcr0.bit._GCAA
#define IBCR0_INTE ibcr0.bit._INTE
#define IBCR0_INT ibcr0.bit._INT
__IO_EXTERN __io IBSR0STR ibsr0;  
#define IBSR0 ibsr0.byte
#define IBSR0_BB ibsr0.bit._BB
#define IBSR0_RSC ibsr0.bit._RSC
#define IBSR0_AL ibsr0.bit._AL
#define IBSR0_LRB ibsr0.bit._LRB
#define IBSR0_TRX ibsr0.bit._TRX
#define IBSR0_AAS ibsr0.bit._AAS
#define IBSR0_GCA ibsr0.bit._GCA
#define IBSR0_ADT ibsr0.bit._ADT
__IO_EXTERN __io ITBA0STR itba0;  
#define ITBA0 itba0.word
#define ITBA0_TA9 itba0.bit._TA9
#define ITBA0_TA8 itba0.bit._TA8
#define ITBA0_TA7 itba0.bit._TA7
#define ITBA0_TA6 itba0.bit._TA6
#define ITBA0_TA5 itba0.bit._TA5
#define ITBA0_TA4 itba0.bit._TA4
#define ITBA0_TA3 itba0.bit._TA3
#define ITBA0_TA2 itba0.bit._TA2
#define ITBA0_TA1 itba0.bit._TA1
#define ITBA0_TA0 itba0.bit._TA0
__IO_EXTERN __io ITBAH0STR itbah0;  
#define ITBAH0 itbah0.byte
#define ITBAH0_TA9 itbah0.bit._TA9
#define ITBAH0_TA8 itbah0.bit._TA8
__IO_EXTERN __io ITBAL0STR itbal0;  
#define ITBAL0 itbal0.byte
#define ITBAL0_TA7 itbal0.bit._TA7
#define ITBAL0_TA6 itbal0.bit._TA6
#define ITBAL0_TA5 itbal0.bit._TA5
#define ITBAL0_TA4 itbal0.bit._TA4
#define ITBAL0_TA3 itbal0.bit._TA3
#define ITBAL0_TA2 itbal0.bit._TA2
#define ITBAL0_TA1 itbal0.bit._TA1
#define ITBAL0_TA0 itbal0.bit._TA0
__IO_EXTERN __io ITMK0STR itmk0;  
#define ITMK0 itmk0.word
#define ITMK0_ENTB itmk0.bit._ENTB
#define ITMK0_RAL itmk0.bit._RAL
#define ITMK0_TM9 itmk0.bit._TM9
#define ITMK0_TM8 itmk0.bit._TM8
#define ITMK0_TM7 itmk0.bit._TM7
#define ITMK0_TM6 itmk0.bit._TM6
#define ITMK0_TM5 itmk0.bit._TM5
#define ITMK0_TM4 itmk0.bit._TM4
#define ITMK0_TM3 itmk0.bit._TM3
#define ITMK0_TM2 itmk0.bit._TM2
#define ITMK0_TM1 itmk0.bit._TM1
#define ITMK0_TM0 itmk0.bit._TM0
__IO_EXTERN __io ITMKH0STR itmkh0;  
#define ITMKH0 itmkh0.byte
#define ITMKH0_ENTB itmkh0.bit._ENTB
#define ITMKH0_RAL itmkh0.bit._RAL
#define ITMKH0_TM9 itmkh0.bit._TM9
#define ITMKH0_TM8 itmkh0.bit._TM8
__IO_EXTERN __io ITMKL0STR itmkl0;  
#define ITMKL0 itmkl0.byte
#define ITMKL0_TM7 itmkl0.bit._TM7
#define ITMKL0_TM6 itmkl0.bit._TM6
#define ITMKL0_TM5 itmkl0.bit._TM5
#define ITMKL0_TM4 itmkl0.bit._TM4
#define ITMKL0_TM3 itmkl0.bit._TM3
#define ITMKL0_TM2 itmkl0.bit._TM2
#define ITMKL0_TM1 itmkl0.bit._TM1
#define ITMKL0_TM0 itmkl0.bit._TM0
__IO_EXTERN __io ISMK0STR ismk0;  
#define ISMK0 ismk0.byte
#define ISMK0_ENSB ismk0.bit._ENSB
#define ISMK0_SM6 ismk0.bit._SM6
#define ISMK0_SM5 ismk0.bit._SM5
#define ISMK0_SM4 ismk0.bit._SM4
#define ISMK0_SM3 ismk0.bit._SM3
#define ISMK0_SM2 ismk0.bit._SM2
#define ISMK0_SM1 ismk0.bit._SM1
#define ISMK0_SM0 ismk0.bit._SM0
__IO_EXTERN __io ISBA0STR isba0;  
#define ISBA0 isba0.byte
#define ISBA0_SA6 isba0.bit._SA6
#define ISBA0_SA5 isba0.bit._SA5
#define ISBA0_SA4 isba0.bit._SA4
#define ISBA0_SA3 isba0.bit._SA3
#define ISBA0_SA2 isba0.bit._SA2
#define ISBA0_SA1 isba0.bit._SA1
#define ISBA0_SA0 isba0.bit._SA0
__IO_EXTERN __io IDAR0STR idar0;  
#define IDAR0 idar0.byte
#define IDAR0_D7 idar0.bit._D7
#define IDAR0_D6 idar0.bit._D6
#define IDAR0_D5 idar0.bit._D5
#define IDAR0_D4 idar0.bit._D4
#define IDAR0_D3 idar0.bit._D3
#define IDAR0_D2 idar0.bit._D2
#define IDAR0_D1 idar0.bit._D1
#define IDAR0_D0 idar0.bit._D0
__IO_EXTERN __io ICCR0STR iccr0;  
#define ICCR0 iccr0.byte
#define ICCR0_NSF iccr0.bit._NSF
#define ICCR0_EN iccr0.bit._EN
#define ICCR0_CS4 iccr0.bit._CS4
#define ICCR0_CS3 iccr0.bit._CS3
#define ICCR0_CS2 iccr0.bit._CS2
#define ICCR0_CS1 iccr0.bit._CS1
#define ICCR0_CS0 iccr0.bit._CS0
#define ICCR0_CS iccr0.bitc._CS
__IO_EXTERN GCN11STR gcn11;   /* PPG Control 4-7 */
#define GCN11 gcn11.word
#define GCN11_TSEL33 gcn11.bit._TSEL33
#define GCN11_TSEL32 gcn11.bit._TSEL32
#define GCN11_TSEL31 gcn11.bit._TSEL31
#define GCN11_TSEL30 gcn11.bit._TSEL30
#define GCN11_TSEL23 gcn11.bit._TSEL23
#define GCN11_TSEL22 gcn11.bit._TSEL22
#define GCN11_TSEL21 gcn11.bit._TSEL21
#define GCN11_TSEL20 gcn11.bit._TSEL20
#define GCN11_TSEL13 gcn11.bit._TSEL13
#define GCN11_TSEL12 gcn11.bit._TSEL12
#define GCN11_TSEL11 gcn11.bit._TSEL11
#define GCN11_TSEL10 gcn11.bit._TSEL10
#define GCN11_TSEL03 gcn11.bit._TSEL03
#define GCN11_TSEL02 gcn11.bit._TSEL02
#define GCN11_TSEL01 gcn11.bit._TSEL01
#define GCN11_TSEL00 gcn11.bit._TSEL00
__IO_EXTERN GCN21STR gcn21;  
#define GCN21 gcn21.byte
#define GCN21_EN3 gcn21.bit._EN3
#define GCN21_EN2 gcn21.bit._EN2
#define GCN21_EN1 gcn21.bit._EN1
#define GCN21_EN0 gcn21.bit._EN0
__IO_EXTERN GCN12STR gcn12;   /* PPG Control 8-11 */
#define GCN12 gcn12.word
#define GCN12_TSEL33 gcn12.bit._TSEL33
#define GCN12_TSEL32 gcn12.bit._TSEL32
#define GCN12_TSEL31 gcn12.bit._TSEL31
#define GCN12_TSEL30 gcn12.bit._TSEL30
#define GCN12_TSEL23 gcn12.bit._TSEL23
#define GCN12_TSEL22 gcn12.bit._TSEL22
#define GCN12_TSEL21 gcn12.bit._TSEL21
#define GCN12_TSEL20 gcn12.bit._TSEL20
#define GCN12_TSEL13 gcn12.bit._TSEL13
#define GCN12_TSEL12 gcn12.bit._TSEL12
#define GCN12_TSEL11 gcn12.bit._TSEL11
#define GCN12_TSEL10 gcn12.bit._TSEL10
#define GCN12_TSEL03 gcn12.bit._TSEL03
#define GCN12_TSEL02 gcn12.bit._TSEL02
#define GCN12_TSEL01 gcn12.bit._TSEL01
#define GCN12_TSEL00 gcn12.bit._TSEL00
__IO_EXTERN GCN22STR gcn22;  
#define GCN22 gcn22.byte
#define GCN22_EN3 gcn22.bit._EN3
#define GCN22_EN2 gcn22.bit._EN2
#define GCN22_EN1 gcn22.bit._EN1
#define GCN22_EN0 gcn22.bit._EN0
__IO_EXTERN IO_WORD ptmr04;   /* PPG 4 */
#define PTMR04 ptmr04
__IO_EXTERN IO_WORD pcsr04;  
#define PCSR04 pcsr04
__IO_EXTERN IO_WORD pdut04;  
#define PDUT04 pdut04
__IO_EXTERN PCN04STR pcn04;  
#define PCN04 pcn04.word
#define PCN04_CNTE pcn04.bit._CNTE
#define PCN04_STGR pcn04.bit._STGR
#define PCN04_MDSE pcn04.bit._MDSE
#define PCN04_RTRG pcn04.bit._RTRG
#define PCN04_CKS1 pcn04.bit._CKS1
#define PCN04_CKS0 pcn04.bit._CKS0
#define PCN04_PGMS pcn04.bit._PGMS
#define PCN04_EGS1 pcn04.bit._EGS1
#define PCN04_EGS0 pcn04.bit._EGS0
#define PCN04_IREN pcn04.bit._IREN
#define PCN04_IRQF pcn04.bit._IRQF
#define PCN04_IRS1 pcn04.bit._IRS1
#define PCN04_IRS0 pcn04.bit._IRS0
#define PCN04_OSEL pcn04.bit._OSEL
#define PCN04_CKS pcn04.bitc._CKS
#define PCN04_EGS pcn04.bitc._EGS
#define PCN04_IRS pcn04.bitc._IRS
__IO_EXTERN PCNH04STR pcnh04;  
#define PCNH04 pcnh04.byte
#define PCNH04_CNTE pcnh04.bit._CNTE
#define PCNH04_STGR pcnh04.bit._STGR
#define PCNH04_MDSE pcnh04.bit._MDSE
#define PCNH04_RTRG pcnh04.bit._RTRG
#define PCNH04_CKS1 pcnh04.bit._CKS1
#define PCNH04_CKS0 pcnh04.bit._CKS0
#define PCNH04_PGMS pcnh04.bit._PGMS
#define PCNH04_CKS pcnh04.bitc._CKS
__IO_EXTERN PCNL04STR pcnl04;  
#define PCNL04 pcnl04.byte
#define PCNL04_EGS1 pcnl04.bit._EGS1
#define PCNL04_EGS0 pcnl04.bit._EGS0
#define PCNL04_IREN pcnl04.bit._IREN
#define PCNL04_IRQF pcnl04.bit._IRQF
#define PCNL04_IRS1 pcnl04.bit._IRS1
#define PCNL04_IRS0 pcnl04.bit._IRS0
#define PCNL04_OSEL pcnl04.bit._OSEL
#define PCNL04_EGS pcnl04.bitc._EGS
#define PCNL04_IRS pcnl04.bitc._IRS
__IO_EXTERN IO_WORD ptmr05;   /* PPG 5 */
#define PTMR05 ptmr05
__IO_EXTERN IO_WORD pcsr05;  
#define PCSR05 pcsr05
__IO_EXTERN IO_WORD pdut05;  
#define PDUT05 pdut05
__IO_EXTERN PCN05STR pcn05;  
#define PCN05 pcn05.word
#define PCN05_CNTE pcn05.bit._CNTE
#define PCN05_STGR pcn05.bit._STGR
#define PCN05_MDSE pcn05.bit._MDSE
#define PCN05_RTRG pcn05.bit._RTRG
#define PCN05_CKS1 pcn05.bit._CKS1
#define PCN05_CKS0 pcn05.bit._CKS0
#define PCN05_PGMS pcn05.bit._PGMS
#define PCN05_EGS1 pcn05.bit._EGS1
#define PCN05_EGS0 pcn05.bit._EGS0
#define PCN05_IREN pcn05.bit._IREN
#define PCN05_IRQF pcn05.bit._IRQF
#define PCN05_IRS1 pcn05.bit._IRS1
#define PCN05_IRS0 pcn05.bit._IRS0
#define PCN05_OSEL pcn05.bit._OSEL
#define PCN05_CKS pcn05.bitc._CKS
#define PCN05_EGS pcn05.bitc._EGS
#define PCN05_IRS pcn05.bitc._IRS
__IO_EXTERN PCNH05STR pcnh05;  
#define PCNH05 pcnh05.byte
#define PCNH05_CNTE pcnh05.bit._CNTE
#define PCNH05_STGR pcnh05.bit._STGR
#define PCNH05_MDSE pcnh05.bit._MDSE
#define PCNH05_RTRG pcnh05.bit._RTRG
#define PCNH05_CKS1 pcnh05.bit._CKS1
#define PCNH05_CKS0 pcnh05.bit._CKS0
#define PCNH05_PGMS pcnh05.bit._PGMS
#define PCNH05_CKS pcnh05.bitc._CKS
__IO_EXTERN PCNL05STR pcnl05;  
#define PCNL05 pcnl05.byte
#define PCNL05_EGS1 pcnl05.bit._EGS1
#define PCNL05_EGS0 pcnl05.bit._EGS0
#define PCNL05_IREN pcnl05.bit._IREN
#define PCNL05_IRQF pcnl05.bit._IRQF
#define PCNL05_IRS1 pcnl05.bit._IRS1
#define PCNL05_IRS0 pcnl05.bit._IRS0
#define PCNL05_OSEL pcnl05.bit._OSEL
#define PCNL05_EGS pcnl05.bitc._EGS
#define PCNL05_IRS pcnl05.bitc._IRS
__IO_EXTERN IO_WORD ptmr06;   /* PPG 6 */
#define PTMR06 ptmr06
__IO_EXTERN IO_WORD pcsr06;  
#define PCSR06 pcsr06
__IO_EXTERN IO_WORD pdut06;  
#define PDUT06 pdut06
__IO_EXTERN PCN06STR pcn06;  
#define PCN06 pcn06.word
#define PCN06_CNTE pcn06.bit._CNTE
#define PCN06_STGR pcn06.bit._STGR
#define PCN06_MDSE pcn06.bit._MDSE
#define PCN06_RTRG pcn06.bit._RTRG
#define PCN06_CKS1 pcn06.bit._CKS1
#define PCN06_CKS0 pcn06.bit._CKS0
#define PCN06_PGMS pcn06.bit._PGMS
#define PCN06_EGS1 pcn06.bit._EGS1
#define PCN06_EGS0 pcn06.bit._EGS0
#define PCN06_IREN pcn06.bit._IREN
#define PCN06_IRQF pcn06.bit._IRQF
#define PCN06_IRS1 pcn06.bit._IRS1
#define PCN06_IRS0 pcn06.bit._IRS0
#define PCN06_OSEL pcn06.bit._OSEL
#define PCN06_CKS pcn06.bitc._CKS
#define PCN06_EGS pcn06.bitc._EGS
#define PCN06_IRS pcn06.bitc._IRS
__IO_EXTERN PCNH06STR pcnh06;  
#define PCNH06 pcnh06.byte
#define PCNH06_CNTE pcnh06.bit._CNTE
#define PCNH06_STGR pcnh06.bit._STGR
#define PCNH06_MDSE pcnh06.bit._MDSE
#define PCNH06_RTRG pcnh06.bit._RTRG
#define PCNH06_CKS1 pcnh06.bit._CKS1
#define PCNH06_CKS0 pcnh06.bit._CKS0
#define PCNH06_PGMS pcnh06.bit._PGMS
#define PCNH06_CKS pcnh06.bitc._CKS
__IO_EXTERN PCNL06STR pcnl06;  
#define PCNL06 pcnl06.byte
#define PCNL06_EGS1 pcnl06.bit._EGS1
#define PCNL06_EGS0 pcnl06.bit._EGS0
#define PCNL06_IREN pcnl06.bit._IREN
#define PCNL06_IRQF pcnl06.bit._IRQF
#define PCNL06_IRS1 pcnl06.bit._IRS1
#define PCNL06_IRS0 pcnl06.bit._IRS0
#define PCNL06_OSEL pcnl06.bit._OSEL
#define PCNL06_EGS pcnl06.bitc._EGS
#define PCNL06_IRS pcnl06.bitc._IRS
__IO_EXTERN IO_WORD ptmr07;   /* PPG 7 */
#define PTMR07 ptmr07
__IO_EXTERN IO_WORD pcsr07;  
#define PCSR07 pcsr07
__IO_EXTERN IO_WORD pdut07;  
#define PDUT07 pdut07
__IO_EXTERN PCN07STR pcn07;  
#define PCN07 pcn07.word
#define PCN07_CNTE pcn07.bit._CNTE
#define PCN07_STGR pcn07.bit._STGR
#define PCN07_MDSE pcn07.bit._MDSE
#define PCN07_RTRG pcn07.bit._RTRG
#define PCN07_CKS1 pcn07.bit._CKS1
#define PCN07_CKS0 pcn07.bit._CKS0
#define PCN07_PGMS pcn07.bit._PGMS
#define PCN07_EGS1 pcn07.bit._EGS1
#define PCN07_EGS0 pcn07.bit._EGS0
#define PCN07_IREN pcn07.bit._IREN
#define PCN07_IRQF pcn07.bit._IRQF
#define PCN07_IRS1 pcn07.bit._IRS1
#define PCN07_IRS0 pcn07.bit._IRS0
#define PCN07_OSEL pcn07.bit._OSEL
#define PCN07_CKS pcn07.bitc._CKS
#define PCN07_EGS pcn07.bitc._EGS
#define PCN07_IRS pcn07.bitc._IRS
__IO_EXTERN PCNH07STR pcnh07;  
#define PCNH07 pcnh07.byte
#define PCNH07_CNTE pcnh07.bit._CNTE
#define PCNH07_STGR pcnh07.bit._STGR
#define PCNH07_MDSE pcnh07.bit._MDSE
#define PCNH07_RTRG pcnh07.bit._RTRG
#define PCNH07_CKS1 pcnh07.bit._CKS1
#define PCNH07_CKS0 pcnh07.bit._CKS0
#define PCNH07_PGMS pcnh07.bit._PGMS
#define PCNH07_CKS pcnh07.bitc._CKS
__IO_EXTERN PCNL07STR pcnl07;  
#define PCNL07 pcnl07.byte
#define PCNL07_EGS1 pcnl07.bit._EGS1
#define PCNL07_EGS0 pcnl07.bit._EGS0
#define PCNL07_IREN pcnl07.bit._IREN
#define PCNL07_IRQF pcnl07.bit._IRQF
#define PCNL07_IRS1 pcnl07.bit._IRS1
#define PCNL07_IRS0 pcnl07.bit._IRS0
#define PCNL07_OSEL pcnl07.bit._OSEL
#define PCNL07_EGS pcnl07.bitc._EGS
#define PCNL07_IRS pcnl07.bitc._IRS
__IO_EXTERN IO_WORD ptmr08;   /* PPG 8 */
#define PTMR08 ptmr08
__IO_EXTERN IO_WORD pcsr08;  
#define PCSR08 pcsr08
__IO_EXTERN IO_WORD pdut08;  
#define PDUT08 pdut08
__IO_EXTERN PCN08STR pcn08;  
#define PCN08 pcn08.word
#define PCN08_CNTE pcn08.bit._CNTE
#define PCN08_STGR pcn08.bit._STGR
#define PCN08_MDSE pcn08.bit._MDSE
#define PCN08_RTRG pcn08.bit._RTRG
#define PCN08_CKS1 pcn08.bit._CKS1
#define PCN08_CKS0 pcn08.bit._CKS0
#define PCN08_PGMS pcn08.bit._PGMS
#define PCN08_EGS1 pcn08.bit._EGS1
#define PCN08_EGS0 pcn08.bit._EGS0
#define PCN08_IREN pcn08.bit._IREN
#define PCN08_IRQF pcn08.bit._IRQF
#define PCN08_IRS1 pcn08.bit._IRS1
#define PCN08_IRS0 pcn08.bit._IRS0
#define PCN08_OSEL pcn08.bit._OSEL
#define PCN08_CKS pcn08.bitc._CKS
#define PCN08_EGS pcn08.bitc._EGS
#define PCN08_IRS pcn08.bitc._IRS
__IO_EXTERN PCNH08STR pcnh08;  
#define PCNH08 pcnh08.byte
#define PCNH08_CNTE pcnh08.bit._CNTE
#define PCNH08_STGR pcnh08.bit._STGR
#define PCNH08_MDSE pcnh08.bit._MDSE
#define PCNH08_RTRG pcnh08.bit._RTRG
#define PCNH08_CKS1 pcnh08.bit._CKS1
#define PCNH08_CKS0 pcnh08.bit._CKS0
#define PCNH08_PGMS pcnh08.bit._PGMS
#define PCNH08_CKS pcnh08.bitc._CKS
__IO_EXTERN PCNL08STR pcnl08;  
#define PCNL08 pcnl08.byte
#define PCNL08_EGS1 pcnl08.bit._EGS1
#define PCNL08_EGS0 pcnl08.bit._EGS0
#define PCNL08_IREN pcnl08.bit._IREN
#define PCNL08_IRQF pcnl08.bit._IRQF
#define PCNL08_IRS1 pcnl08.bit._IRS1
#define PCNL08_IRS0 pcnl08.bit._IRS0
#define PCNL08_OSEL pcnl08.bit._OSEL
#define PCNL08_EGS pcnl08.bitc._EGS
#define PCNL08_IRS pcnl08.bitc._IRS
__IO_EXTERN IO_WORD ptmr09;   /* PPG 9 */
#define PTMR09 ptmr09
__IO_EXTERN IO_WORD pcsr09;  
#define PCSR09 pcsr09
__IO_EXTERN IO_WORD pdut09;  
#define PDUT09 pdut09
__IO_EXTERN PCN09STR pcn09;  
#define PCN09 pcn09.word
#define PCN09_CNTE pcn09.bit._CNTE
#define PCN09_STGR pcn09.bit._STGR
#define PCN09_MDSE pcn09.bit._MDSE
#define PCN09_RTRG pcn09.bit._RTRG
#define PCN09_CKS1 pcn09.bit._CKS1
#define PCN09_CKS0 pcn09.bit._CKS0
#define PCN09_PGMS pcn09.bit._PGMS
#define PCN09_EGS1 pcn09.bit._EGS1
#define PCN09_EGS0 pcn09.bit._EGS0
#define PCN09_IREN pcn09.bit._IREN
#define PCN09_IRQF pcn09.bit._IRQF
#define PCN09_IRS1 pcn09.bit._IRS1
#define PCN09_IRS0 pcn09.bit._IRS0
#define PCN09_OSEL pcn09.bit._OSEL
#define PCN09_CKS pcn09.bitc._CKS
#define PCN09_EGS pcn09.bitc._EGS
#define PCN09_IRS pcn09.bitc._IRS
__IO_EXTERN PCNH09STR pcnh09;  
#define PCNH09 pcnh09.byte
#define PCNH09_CNTE pcnh09.bit._CNTE
#define PCNH09_STGR pcnh09.bit._STGR
#define PCNH09_MDSE pcnh09.bit._MDSE
#define PCNH09_RTRG pcnh09.bit._RTRG
#define PCNH09_CKS1 pcnh09.bit._CKS1
#define PCNH09_CKS0 pcnh09.bit._CKS0
#define PCNH09_PGMS pcnh09.bit._PGMS
#define PCNH09_CKS pcnh09.bitc._CKS
__IO_EXTERN PCNL09STR pcnl09;  
#define PCNL09 pcnl09.byte
#define PCNL09_EGS1 pcnl09.bit._EGS1
#define PCNL09_EGS0 pcnl09.bit._EGS0
#define PCNL09_IREN pcnl09.bit._IREN
#define PCNL09_IRQF pcnl09.bit._IRQF
#define PCNL09_IRS1 pcnl09.bit._IRS1
#define PCNL09_IRS0 pcnl09.bit._IRS0
#define PCNL09_OSEL pcnl09.bit._OSEL
#define PCNL09_EGS pcnl09.bitc._EGS
#define PCNL09_IRS pcnl09.bitc._IRS
__IO_EXTERN IO_WORD ptmr10;   /* PPG 10 */
#define PTMR10 ptmr10
__IO_EXTERN IO_WORD pcsr10;  
#define PCSR10 pcsr10
__IO_EXTERN IO_WORD pdut10;  
#define PDUT10 pdut10
__IO_EXTERN PCN10STR pcn10;  
#define PCN10 pcn10.word
#define PCN10_CNTE pcn10.bit._CNTE
#define PCN10_STGR pcn10.bit._STGR
#define PCN10_MDSE pcn10.bit._MDSE
#define PCN10_RTRG pcn10.bit._RTRG
#define PCN10_CKS1 pcn10.bit._CKS1
#define PCN10_CKS0 pcn10.bit._CKS0
#define PCN10_PGMS pcn10.bit._PGMS
#define PCN10_EGS1 pcn10.bit._EGS1
#define PCN10_EGS0 pcn10.bit._EGS0
#define PCN10_IREN pcn10.bit._IREN
#define PCN10_IRQF pcn10.bit._IRQF
#define PCN10_IRS1 pcn10.bit._IRS1
#define PCN10_IRS0 pcn10.bit._IRS0
#define PCN10_OSEL pcn10.bit._OSEL
#define PCN10_CKS pcn10.bitc._CKS
#define PCN10_EGS pcn10.bitc._EGS
#define PCN10_IRS pcn10.bitc._IRS
__IO_EXTERN PCNH10STR pcnh10;  
#define PCNH10 pcnh10.byte
#define PCNH10_CNTE pcnh10.bit._CNTE
#define PCNH10_STGR pcnh10.bit._STGR
#define PCNH10_MDSE pcnh10.bit._MDSE
#define PCNH10_RTRG pcnh10.bit._RTRG
#define PCNH10_CKS1 pcnh10.bit._CKS1
#define PCNH10_CKS0 pcnh10.bit._CKS0
#define PCNH10_PGMS pcnh10.bit._PGMS
#define PCNH10_CKS pcnh10.bitc._CKS
__IO_EXTERN PCNL10STR pcnl10;  
#define PCNL10 pcnl10.byte
#define PCNL10_EGS1 pcnl10.bit._EGS1
#define PCNL10_EGS0 pcnl10.bit._EGS0
#define PCNL10_IREN pcnl10.bit._IREN
#define PCNL10_IRQF pcnl10.bit._IRQF
#define PCNL10_IRS1 pcnl10.bit._IRS1
#define PCNL10_IRS0 pcnl10.bit._IRS0
#define PCNL10_OSEL pcnl10.bit._OSEL
#define PCNL10_EGS pcnl10.bitc._EGS
#define PCNL10_IRS pcnl10.bitc._IRS
__IO_EXTERN IO_WORD ptmr11;   /* PPG 11 */
#define PTMR11 ptmr11
__IO_EXTERN IO_WORD pcsr11;  
#define PCSR11 pcsr11
__IO_EXTERN IO_WORD pdut11;  
#define PDUT11 pdut11
__IO_EXTERN PCN11STR pcn11;  
#define PCN11 pcn11.word
#define PCN11_CNTE pcn11.bit._CNTE
#define PCN11_STGR pcn11.bit._STGR
#define PCN11_MDSE pcn11.bit._MDSE
#define PCN11_RTRG pcn11.bit._RTRG
#define PCN11_CKS1 pcn11.bit._CKS1
#define PCN11_CKS0 pcn11.bit._CKS0
#define PCN11_PGMS pcn11.bit._PGMS
#define PCN11_EGS1 pcn11.bit._EGS1
#define PCN11_EGS0 pcn11.bit._EGS0
#define PCN11_IREN pcn11.bit._IREN
#define PCN11_IRQF pcn11.bit._IRQF
#define PCN11_IRS1 pcn11.bit._IRS1
#define PCN11_IRS0 pcn11.bit._IRS0
#define PCN11_OSEL pcn11.bit._OSEL
#define PCN11_CKS pcn11.bitc._CKS
#define PCN11_EGS pcn11.bitc._EGS
#define PCN11_IRS pcn11.bitc._IRS
__IO_EXTERN PCNH11STR pcnh11;  
#define PCNH11 pcnh11.byte
#define PCNH11_CNTE pcnh11.bit._CNTE
#define PCNH11_STGR pcnh11.bit._STGR
#define PCNH11_MDSE pcnh11.bit._MDSE
#define PCNH11_RTRG pcnh11.bit._RTRG
#define PCNH11_CKS1 pcnh11.bit._CKS1
#define PCNH11_CKS0 pcnh11.bit._CKS0
#define PCNH11_PGMS pcnh11.bit._PGMS
#define PCNH11_CKS pcnh11.bitc._CKS
__IO_EXTERN PCNL11STR pcnl11;  
#define PCNL11 pcnl11.byte
#define PCNL11_EGS1 pcnl11.bit._EGS1
#define PCNL11_EGS0 pcnl11.bit._EGS0
#define PCNL11_IREN pcnl11.bit._IREN
#define PCNL11_IRQF pcnl11.bit._IRQF
#define PCNL11_IRS1 pcnl11.bit._IRS1
#define PCNL11_IRS0 pcnl11.bit._IRS0
#define PCNL11_OSEL pcnl11.bit._OSEL
#define PCNL11_EGS pcnl11.bitc._EGS
#define PCNL11_IRS pcnl11.bitc._IRS
__IO_EXTERN P0TMCSRSTR p0tmcsr;   /* Pulse Frequency Modulator (PFM) */
#define P0TMCSR p0tmcsr.word
#define P0TMCSR_INV p0tmcsr.bit._INV
#define P0TMCSR_CSL2 p0tmcsr.bit._CSL2
#define P0TMCSR_CSL1 p0tmcsr.bit._CSL1
#define P0TMCSR_CSL0 p0tmcsr.bit._CSL0
#define P0TMCSR_MOD1 p0tmcsr.bit._MOD1
#define P0TMCSR_RELD p0tmcsr.bit._RELD
#define P0TMCSR_INTE p0tmcsr.bit._INTE
#define P0TMCSR_UF p0tmcsr.bit._UF
#define P0TMCSR_CNTE p0tmcsr.bit._CNTE
#define P0TMCSR_TRG p0tmcsr.bit._TRG
#define P0TMCSR_CSL p0tmcsr.bitc._CSL
__IO_EXTERN P0TMCSRHSTR p0tmcsrh;  
#define P0TMCSRH p0tmcsrh.byte
#define P0TMCSRH_INV p0tmcsrh.bit._INV
#define P0TMCSRH_CSL2 p0tmcsrh.bit._CSL2
#define P0TMCSRH_CSL1 p0tmcsrh.bit._CSL1
#define P0TMCSRH_CSL0 p0tmcsrh.bit._CSL0
#define P0TMCSRH_MOD1 p0tmcsrh.bit._MOD1
#define P0TMCSRH_CSL p0tmcsrh.bitc._CSL
__IO_EXTERN P0TMCSRLSTR p0tmcsrl;  
#define P0TMCSRL p0tmcsrl.byte
#define P0TMCSRL_RELD p0tmcsrl.bit._RELD
#define P0TMCSRL_INTE p0tmcsrl.bit._INTE
#define P0TMCSRL_UF p0tmcsrl.bit._UF
#define P0TMCSRL_CNTE p0tmcsrl.bit._CNTE
#define P0TMCSRL_TRG p0tmcsrl.bit._TRG
__IO_EXTERN P1TMCSRSTR p1tmcsr;  
#define P1TMCSR p1tmcsr.word
#define P1TMCSR_INV p1tmcsr.bit._INV
#define P1TMCSR_CSL2 p1tmcsr.bit._CSL2
#define P1TMCSR_CSL1 p1tmcsr.bit._CSL1
#define P1TMCSR_CSL0 p1tmcsr.bit._CSL0
#define P1TMCSR_MOD1 p1tmcsr.bit._MOD1
#define P1TMCSR_RELD p1tmcsr.bit._RELD
#define P1TMCSR_INTE p1tmcsr.bit._INTE
#define P1TMCSR_UF p1tmcsr.bit._UF
#define P1TMCSR_CNTE p1tmcsr.bit._CNTE
#define P1TMCSR_TRG p1tmcsr.bit._TRG
#define P1TMCSR_CSL p1tmcsr.bitc._CSL
__IO_EXTERN P1TMCSRHSTR p1tmcsrh;  
#define P1TMCSRH p1tmcsrh.byte
#define P1TMCSRH_INV p1tmcsrh.bit._INV
#define P1TMCSRH_CSL2 p1tmcsrh.bit._CSL2
#define P1TMCSRH_CSL1 p1tmcsrh.bit._CSL1
#define P1TMCSRH_CSL0 p1tmcsrh.bit._CSL0
#define P1TMCSRH_MOD1 p1tmcsrh.bit._MOD1
#define P1TMCSRH_CSL p1tmcsrh.bitc._CSL
__IO_EXTERN P1TMCSRLSTR p1tmcsrl;  
#define P1TMCSRL p1tmcsrl.byte
#define P1TMCSRL_RELD p1tmcsrl.bit._RELD
#define P1TMCSRL_INTE p1tmcsrl.bit._INTE
#define P1TMCSRL_UF p1tmcsrl.bit._UF
#define P1TMCSRL_CNTE p1tmcsrl.bit._CNTE
#define P1TMCSRL_TRG p1tmcsrl.bit._TRG
__IO_EXTERN IO_WORD p0tmrlr;  
#define P0TMRLR p0tmrlr
__IO_EXTERN IO_WORD p0tmr;  
#define P0TMR p0tmr
__IO_EXTERN IO_WORD p1tmrlr;  
#define P1TMRLR p1tmrlr
__IO_EXTERN IO_WORD p1tmr;  
#define P1TMR p1tmr
__IO_EXTERN ICS01STR ics01;   /* Input Capture 0-3 */
#define ICS01 ics01.byte
#define ICS01_ICP1 ics01.bit._ICP1
#define ICS01_ICP0 ics01.bit._ICP0
#define ICS01_ICE1 ics01.bit._ICE1
#define ICS01_ICE0 ics01.bit._ICE0
#define ICS01_EG11 ics01.bit._EG11
#define ICS01_EG10 ics01.bit._EG10
#define ICS01_EG01 ics01.bit._EG01
#define ICS01_EG00 ics01.bit._EG00
#define ICS01_EG1 ics01.bitc._EG1
#define ICS01_EG0 ics01.bitc._EG0
__IO_EXTERN ICS23STR ics23;  
#define ICS23 ics23.byte
#define ICS23_ICP3 ics23.bit._ICP3
#define ICS23_ICP2 ics23.bit._ICP2
#define ICS23_ICE3 ics23.bit._ICE3
#define ICS23_ICE2 ics23.bit._ICE2
#define ICS23_EG31 ics23.bit._EG31
#define ICS23_EG30 ics23.bit._EG30
#define ICS23_EG21 ics23.bit._EG21
#define ICS23_EG20 ics23.bit._EG20
#define ICS23_EG3 ics23.bitc._EG3
#define ICS23_EG2 ics23.bitc._EG2
__IO_EXTERN IPCP0STR ipcp0;  
#define IPCP0 ipcp0.word
#define IPCP0_CP15 ipcp0.bit._CP15
#define IPCP0_CP14 ipcp0.bit._CP14
#define IPCP0_CP13 ipcp0.bit._CP13
#define IPCP0_CP12 ipcp0.bit._CP12
#define IPCP0_CP11 ipcp0.bit._CP11
#define IPCP0_CP10 ipcp0.bit._CP10
#define IPCP0_CP9 ipcp0.bit._CP9
#define IPCP0_CP8 ipcp0.bit._CP8
#define IPCP0_CP7 ipcp0.bit._CP7
#define IPCP0_CP6 ipcp0.bit._CP6
#define IPCP0_CP5 ipcp0.bit._CP5
#define IPCP0_CP4 ipcp0.bit._CP4
#define IPCP0_CP3 ipcp0.bit._CP3
#define IPCP0_CP2 ipcp0.bit._CP2
#define IPCP0_CP1 ipcp0.bit._CP1
#define IPCP0_CP0 ipcp0.bit._CP0
__IO_EXTERN IPCP1STR ipcp1;  
#define IPCP1 ipcp1.word
#define IPCP1_CP15 ipcp1.bit._CP15
#define IPCP1_CP14 ipcp1.bit._CP14
#define IPCP1_CP13 ipcp1.bit._CP13
#define IPCP1_CP12 ipcp1.bit._CP12
#define IPCP1_CP11 ipcp1.bit._CP11
#define IPCP1_CP10 ipcp1.bit._CP10
#define IPCP1_CP9 ipcp1.bit._CP9
#define IPCP1_CP8 ipcp1.bit._CP8
#define IPCP1_CP7 ipcp1.bit._CP7
#define IPCP1_CP6 ipcp1.bit._CP6
#define IPCP1_CP5 ipcp1.bit._CP5
#define IPCP1_CP4 ipcp1.bit._CP4
#define IPCP1_CP3 ipcp1.bit._CP3
#define IPCP1_CP2 ipcp1.bit._CP2
#define IPCP1_CP1 ipcp1.bit._CP1
#define IPCP1_CP0 ipcp1.bit._CP0
__IO_EXTERN IPCP2STR ipcp2;  
#define IPCP2 ipcp2.word
#define IPCP2_CP15 ipcp2.bit._CP15
#define IPCP2_CP14 ipcp2.bit._CP14
#define IPCP2_CP13 ipcp2.bit._CP13
#define IPCP2_CP12 ipcp2.bit._CP12
#define IPCP2_CP11 ipcp2.bit._CP11
#define IPCP2_CP10 ipcp2.bit._CP10
#define IPCP2_CP9 ipcp2.bit._CP9
#define IPCP2_CP8 ipcp2.bit._CP8
#define IPCP2_CP7 ipcp2.bit._CP7
#define IPCP2_CP6 ipcp2.bit._CP6
#define IPCP2_CP5 ipcp2.bit._CP5
#define IPCP2_CP4 ipcp2.bit._CP4
#define IPCP2_CP3 ipcp2.bit._CP3
#define IPCP2_CP2 ipcp2.bit._CP2
#define IPCP2_CP1 ipcp2.bit._CP1
#define IPCP2_CP0 ipcp2.bit._CP0
__IO_EXTERN IPCP3STR ipcp3;  
#define IPCP3 ipcp3.word
#define IPCP3_CP15 ipcp3.bit._CP15
#define IPCP3_CP14 ipcp3.bit._CP14
#define IPCP3_CP13 ipcp3.bit._CP13
#define IPCP3_CP12 ipcp3.bit._CP12
#define IPCP3_CP11 ipcp3.bit._CP11
#define IPCP3_CP10 ipcp3.bit._CP10
#define IPCP3_CP9 ipcp3.bit._CP9
#define IPCP3_CP8 ipcp3.bit._CP8
#define IPCP3_CP7 ipcp3.bit._CP7
#define IPCP3_CP6 ipcp3.bit._CP6
#define IPCP3_CP5 ipcp3.bit._CP5
#define IPCP3_CP4 ipcp3.bit._CP4
#define IPCP3_CP3 ipcp3.bit._CP3
#define IPCP3_CP2 ipcp3.bit._CP2
#define IPCP3_CP1 ipcp3.bit._CP1
#define IPCP3_CP0 ipcp3.bit._CP0
__IO_EXTERN OCS01STR ocs01;   /* Output Compare 0-3 */
#define OCS01 ocs01.word
#define OCS01_CMOD ocs01.bit._CMOD
#define OCS01_OTD1 ocs01.bit._OTD1
#define OCS01_OTD0 ocs01.bit._OTD0
#define OCS01_ICP1 ocs01.bit._ICP1
#define OCS01_ICP0 ocs01.bit._ICP0
#define OCS01_ICE1 ocs01.bit._ICE1
#define OCS01_ICE0 ocs01.bit._ICE0
#define OCS01_CST1 ocs01.bit._CST1
#define OCS01_CST0 ocs01.bit._CST0
__IO_EXTERN OCS23STR ocs23;  
#define OCS23 ocs23.word
#define OCS23_CMOD ocs23.bit._CMOD
#define OCS23_OTD3 ocs23.bit._OTD3
#define OCS23_OTD2 ocs23.bit._OTD2
#define OCS23_ICP3 ocs23.bit._ICP3
#define OCS23_ICP2 ocs23.bit._ICP2
#define OCS23_ICE3 ocs23.bit._ICE3
#define OCS23_ICE2 ocs23.bit._ICE2
#define OCS23_CST3 ocs23.bit._CST3
#define OCS23_CST2 ocs23.bit._CST2
__IO_EXTERN OCCP0STR occp0;  
#define OCCP0 occp0.word
#define OCCP0_C15 occp0.bit._C15
#define OCCP0_C14 occp0.bit._C14
#define OCCP0_C13 occp0.bit._C13
#define OCCP0_C12 occp0.bit._C12
#define OCCP0_C11 occp0.bit._C11
#define OCCP0_C10 occp0.bit._C10
#define OCCP0_C9 occp0.bit._C9
#define OCCP0_C8 occp0.bit._C8
#define OCCP0_C7 occp0.bit._C7
#define OCCP0_C6 occp0.bit._C6
#define OCCP0_C5 occp0.bit._C5
#define OCCP0_C4 occp0.bit._C4
#define OCCP0_C3 occp0.bit._C3
#define OCCP0_C2 occp0.bit._C2
#define OCCP0_C1 occp0.bit._C1
#define OCCP0_C0 occp0.bit._C0
__IO_EXTERN OCCP1STR occp1;  
#define OCCP1 occp1.word
#define OCCP1_C15 occp1.bit._C15
#define OCCP1_C14 occp1.bit._C14
#define OCCP1_C13 occp1.bit._C13
#define OCCP1_C12 occp1.bit._C12
#define OCCP1_C11 occp1.bit._C11
#define OCCP1_C10 occp1.bit._C10
#define OCCP1_C9 occp1.bit._C9
#define OCCP1_C8 occp1.bit._C8
#define OCCP1_C7 occp1.bit._C7
#define OCCP1_C6 occp1.bit._C6
#define OCCP1_C5 occp1.bit._C5
#define OCCP1_C4 occp1.bit._C4
#define OCCP1_C3 occp1.bit._C3
#define OCCP1_C2 occp1.bit._C2
#define OCCP1_C1 occp1.bit._C1
#define OCCP1_C0 occp1.bit._C0
__IO_EXTERN OCCP2STR occp2;  
#define OCCP2 occp2.word
#define OCCP2_C15 occp2.bit._C15
#define OCCP2_C14 occp2.bit._C14
#define OCCP2_C13 occp2.bit._C13
#define OCCP2_C12 occp2.bit._C12
#define OCCP2_C11 occp2.bit._C11
#define OCCP2_C10 occp2.bit._C10
#define OCCP2_C9 occp2.bit._C9
#define OCCP2_C8 occp2.bit._C8
#define OCCP2_C7 occp2.bit._C7
#define OCCP2_C6 occp2.bit._C6
#define OCCP2_C5 occp2.bit._C5
#define OCCP2_C4 occp2.bit._C4
#define OCCP2_C3 occp2.bit._C3
#define OCCP2_C2 occp2.bit._C2
#define OCCP2_C1 occp2.bit._C1
#define OCCP2_C0 occp2.bit._C0
__IO_EXTERN OCCP3STR occp3;  
#define OCCP3 occp3.word
#define OCCP3_C15 occp3.bit._C15
#define OCCP3_C14 occp3.bit._C14
#define OCCP3_C13 occp3.bit._C13
#define OCCP3_C12 occp3.bit._C12
#define OCCP3_C11 occp3.bit._C11
#define OCCP3_C10 occp3.bit._C10
#define OCCP3_C9 occp3.bit._C9
#define OCCP3_C8 occp3.bit._C8
#define OCCP3_C7 occp3.bit._C7
#define OCCP3_C6 occp3.bit._C6
#define OCCP3_C5 occp3.bit._C5
#define OCCP3_C4 occp3.bit._C4
#define OCCP3_C3 occp3.bit._C3
#define OCCP3_C2 occp3.bit._C2
#define OCCP3_C1 occp3.bit._C1
#define OCCP3_C0 occp3.bit._C0
__IO_EXTERN SGCRSTR sgcr;   /* Sound Generator */
#define SGCR sgcr.word
#define SGCR_TST sgcr.bit._TST
#define SGCR_S2 sgcr.bit._S2
#define SGCR_S1 sgcr.bit._S1
#define SGCR_S0 sgcr.bit._S0
#define SGCR_BUSY sgcr.bit._BUSY
#define SGCR_DEC sgcr.bit._DEC
#define SGCR_TONE sgcr.bit._TONE
#define SGCR_INTE sgcr.bit._INTE
#define SGCR_INT sgcr.bit._INT
#define SGCR_ST sgcr.bit._ST
#define SGCR_S sgcr.bitc._S
__IO_EXTERN SGCRHSTR sgcrh;  
#define SGCRH sgcrh.byte
#define SGCRH_TST sgcrh.bit._TST
#define SGCRH_S2 sgcrh.bit._S2
#define SGCRH_S1 sgcrh.bit._S1
#define SGCRH_S0 sgcrh.bit._S0
#define SGCRH_BUSY sgcrh.bit._BUSY
#define SGCRH_DEC sgcrh.bit._DEC
#define SGCRH_S sgcrh.bitc._S
__IO_EXTERN SGCRLSTR sgcrl;  
#define SGCRL sgcrl.byte
#define SGCRL_TONE sgcrl.bit._TONE
#define SGCRL_INTE sgcrl.bit._INTE
#define SGCRL_INT sgcrl.bit._INT
#define SGCRL_ST sgcrl.bit._ST
__IO_EXTERN SGFRSTR sgfr;  
#define SGFR sgfr.word
#define SGFR_D15 sgfr.bit._D15
#define SGFR_D14 sgfr.bit._D14
#define SGFR_D13 sgfr.bit._D13
#define SGFR_D12 sgfr.bit._D12
#define SGFR_D11 sgfr.bit._D11
#define SGFR_D10 sgfr.bit._D10
#define SGFR_D9 sgfr.bit._D9
#define SGFR_D8 sgfr.bit._D8
#define SGFR_D7 sgfr.bit._D7
#define SGFR_D6 sgfr.bit._D6
#define SGFR_D5 sgfr.bit._D5
#define SGFR_D4 sgfr.bit._D4
#define SGFR_D3 sgfr.bit._D3
#define SGFR_D2 sgfr.bit._D2
#define SGFR_D1 sgfr.bit._D1
#define SGFR_D0 sgfr.bit._D0
__IO_EXTERN SGARSTR sgar;  
#define SGAR sgar.byte
#define SGAR_D7 sgar.bit._D7
#define SGAR_D6 sgar.bit._D6
#define SGAR_D5 sgar.bit._D5
#define SGAR_D4 sgar.bit._D4
#define SGAR_D3 sgar.bit._D3
#define SGAR_D2 sgar.bit._D2
#define SGAR_D1 sgar.bit._D1
#define SGAR_D0 sgar.bit._D0
__IO_EXTERN SGTRSTR sgtr;  
#define SGTR sgtr.byte
#define SGTR_D7 sgtr.bit._D7
#define SGTR_D6 sgtr.bit._D6
#define SGTR_D5 sgtr.bit._D5
#define SGTR_D4 sgtr.bit._D4
#define SGTR_D3 sgtr.bit._D3
#define SGTR_D2 sgtr.bit._D2
#define SGTR_D1 sgtr.bit._D1
#define SGTR_D0 sgtr.bit._D0
__IO_EXTERN SGDRSTR sgdr;  
#define SGDR sgdr.byte
#define SGDR_D7 sgdr.bit._D7
#define SGDR_D6 sgdr.bit._D6
#define SGDR_D5 sgdr.bit._D5
#define SGDR_D4 sgdr.bit._D4
#define SGDR_D3 sgdr.bit._D3
#define SGDR_D2 sgdr.bit._D2
#define SGDR_D1 sgdr.bit._D1
#define SGDR_D0 sgdr.bit._D0
__IO_EXTERN ADERHSTR aderh;   /* ADC */
#define ADERH aderh.word
#define ADERH_ADE31 aderh.bit._ADE31
#define ADERH_ADE30 aderh.bit._ADE30
#define ADERH_ADE29 aderh.bit._ADE29
#define ADERH_ADE28 aderh.bit._ADE28
#define ADERH_ADE27 aderh.bit._ADE27
#define ADERH_ADE26 aderh.bit._ADE26
#define ADERH_ADE25 aderh.bit._ADE25
#define ADERH_ADE24 aderh.bit._ADE24
#define ADERH_ADE23 aderh.bit._ADE23
#define ADERH_ADE22 aderh.bit._ADE22
#define ADERH_ADE21 aderh.bit._ADE21
#define ADERH_ADE20 aderh.bit._ADE20
#define ADERH_ADE19 aderh.bit._ADE19
#define ADERH_ADE18 aderh.bit._ADE18
#define ADERH_ADE17 aderh.bit._ADE17
#define ADERH_ADE16 aderh.bit._ADE16
__IO_EXTERN ADERLSTR aderl;  
#define ADERL aderl.word
#define ADERL_ADE15 aderl.bit._ADE15
#define ADERL_ADE14 aderl.bit._ADE14
#define ADERL_ADE13 aderl.bit._ADE13
#define ADERL_ADE12 aderl.bit._ADE12
#define ADERL_ADE11 aderl.bit._ADE11
#define ADERL_ADE10 aderl.bit._ADE10
#define ADERL_ADE9 aderl.bit._ADE9
#define ADERL_ADE8 aderl.bit._ADE8
#define ADERL_ADE7 aderl.bit._ADE7
#define ADERL_ADE6 aderl.bit._ADE6
#define ADERL_ADE5 aderl.bit._ADE5
#define ADERL_ADE4 aderl.bit._ADE4
#define ADERL_ADE3 aderl.bit._ADE3
#define ADERL_ADE2 aderl.bit._ADE2
#define ADERL_ADE1 aderl.bit._ADE1
#define ADERL_ADE0 aderl.bit._ADE0
__IO_EXTERN IO_LWORD ader;  
#define ADER ader
__IO_EXTERN ADCS1STR adcs1;  
#define ADCS1 adcs1.byte
#define ADCS1_BUSY adcs1.bit._BUSY
#define ADCS1_INT adcs1.bit._INT
#define ADCS1_INTE adcs1.bit._INTE
#define ADCS1_PAUS adcs1.bit._PAUS
#define ADCS1_STS1 adcs1.bit._STS1
#define ADCS1_STS0 adcs1.bit._STS0
#define ADCS1_STRT adcs1.bit._STRT
#define ADCS1_STS adcs1.bitc._STS
__IO_EXTERN ADCS0STR adcs0;  
#define ADCS0 adcs0.byte
#define ADCS0_MD1 adcs0.bit._MD1
#define ADCS0_MD0 adcs0.bit._MD0
#define ADCS0_S10 adcs0.bit._S10
#define ADCS0_ACH4 adcs0.bit._ACH4
#define ADCS0_ACH3 adcs0.bit._ACH3
#define ADCS0_ACH2 adcs0.bit._ACH2
#define ADCS0_ACH1 adcs0.bit._ACH1
#define ADCS0_ACH0 adcs0.bit._ACH0
#define ADCS0_MD adcs0.bitc._MD
#define ADCS0_ACH adcs0.bitc._ACH
__IO_EXTERN IO_WORD adcs;  
#define ADCS adcs
__IO_EXTERN ADCR1STR adcr1;  
#define ADCR1 adcr1.byte
#define ADCR1_D9 adcr1.bit._D9
#define ADCR1_D8 adcr1.bit._D8
__IO_EXTERN ADCR0STR adcr0;  
#define ADCR0 adcr0.byte
#define ADCR0_D7 adcr0.bit._D7
#define ADCR0_D6 adcr0.bit._D6
#define ADCR0_D5 adcr0.bit._D5
#define ADCR0_D4 adcr0.bit._D4
#define ADCR0_D3 adcr0.bit._D3
#define ADCR0_D2 adcr0.bit._D2
#define ADCR0_D1 adcr0.bit._D1
#define ADCR0_D0 adcr0.bit._D0
__IO_EXTERN IO_WORD adcr;  
#define ADCR adcr
__IO_EXTERN ADCT1STR adct1;  
#define ADCT1 adct1.byte
#define ADCT1_CT5 adct1.bit._CT5
#define ADCT1_CT4 adct1.bit._CT4
#define ADCT1_CT3 adct1.bit._CT3
#define ADCT1_CT2 adct1.bit._CT2
#define ADCT1_CT1 adct1.bit._CT1
#define ADCT1_CT0 adct1.bit._CT0
#define ADCT1_ST9 adct1.bit._ST9
#define ADCT1_ST8 adct1.bit._ST8
__IO_EXTERN ADCT0STR adct0;  
#define ADCT0 adct0.byte
#define ADCT0_ST7 adct0.bit._ST7
#define ADCT0_ST6 adct0.bit._ST6
#define ADCT0_ST5 adct0.bit._ST5
#define ADCT0_ST4 adct0.bit._ST4
#define ADCT0_ST3 adct0.bit._ST3
#define ADCT0_ST2 adct0.bit._ST2
#define ADCT0_ST1 adct0.bit._ST1
#define ADCT0_ST0 adct0.bit._ST0
__IO_EXTERN IO_WORD adct;  
#define ADCT adct
__IO_EXTERN ADSCHSTR adsch;  
#define ADSCH adsch.byte
#define ADSCH_ANS4 adsch.bit._ANS4
#define ADSCH_ANS3 adsch.bit._ANS3
#define ADSCH_ANS2 adsch.bit._ANS2
#define ADSCH_ANS1 adsch.bit._ANS1
#define ADSCH_ASN0 adsch.bit._ASN0
#define ADSCH_ANS adsch.bitc._ANS
__IO_EXTERN ADECHSTR adech;  
#define ADECH adech.byte
#define ADECH_ANE4 adech.bit._ANE4
#define ADECH_ANE3 adech.bit._ANE3
#define ADECH_ANE2 adech.bit._ANE2
#define ADECH_ANE1 adech.bit._ANE1
#define ADECH_ANE0 adech.bit._ANE0
#define ADECH_ANE adech.bitc._ANE
__IO_EXTERN ACSR0STR acsr0;   /* Alarm Comparator 0-1 */
#define ACSR0 acsr0.byte
#define ACSR0_MD acsr0.bit._MD
#define ACSR0_OV_EN acsr0.bit._OV_EN
#define ACSR0_UV_EN acsr0.bit._UV_EN
#define ACSR0_OUT2 acsr0.bit._OUT2
#define ACSR0_OUT1 acsr0.bit._OUT1
#define ACSR0_IRQ acsr0.bit._IRQ
#define ACSR0_IEN acsr0.bit._IEN
#define ACSR0_PD acsr0.bit._PD
__IO_EXTERN TMRLR0STR tmrlr0;   /* Reload Timer 0 */
#define TMRLR0 tmrlr0.word
#define TMRLR0_D15 tmrlr0.bit._D15
#define TMRLR0_D14 tmrlr0.bit._D14
#define TMRLR0_D13 tmrlr0.bit._D13
#define TMRLR0_D12 tmrlr0.bit._D12
#define TMRLR0_D11 tmrlr0.bit._D11
#define TMRLR0_D10 tmrlr0.bit._D10
#define TMRLR0_D9 tmrlr0.bit._D9
#define TMRLR0_D8 tmrlr0.bit._D8
#define TMRLR0_D7 tmrlr0.bit._D7
#define TMRLR0_D6 tmrlr0.bit._D6
#define TMRLR0_D5 tmrlr0.bit._D5
#define TMRLR0_D4 tmrlr0.bit._D4
#define TMRLR0_D3 tmrlr0.bit._D3
#define TMRLR0_D2 tmrlr0.bit._D2
#define TMRLR0_D1 tmrlr0.bit._D1
#define TMRLR0_D0 tmrlr0.bit._D0
__IO_EXTERN TMR0STR tmr0;  
#define TMR0 tmr0.word
#define TMR0_D15 tmr0.bit._D15
#define TMR0_D14 tmr0.bit._D14
#define TMR0_D13 tmr0.bit._D13
#define TMR0_D12 tmr0.bit._D12
#define TMR0_D11 tmr0.bit._D11
#define TMR0_D10 tmr0.bit._D10
#define TMR0_D9 tmr0.bit._D9
#define TMR0_D8 tmr0.bit._D8
#define TMR0_D7 tmr0.bit._D7
#define TMR0_D6 tmr0.bit._D6
#define TMR0_D5 tmr0.bit._D5
#define TMR0_D4 tmr0.bit._D4
#define TMR0_D3 tmr0.bit._D3
#define TMR0_D2 tmr0.bit._D2
#define TMR0_D1 tmr0.bit._D1
#define TMR0_D0 tmr0.bit._D0
__IO_EXTERN TMCSR0STR tmcsr0;  
#define TMCSR0 tmcsr0.word
#define TMCSR0_CSL2 tmcsr0.bit._CSL2
#define TMCSR0_CSL1 tmcsr0.bit._CSL1
#define TMCSR0_CSL0 tmcsr0.bit._CSL0
#define TMCSR0_MOD2 tmcsr0.bit._MOD2
#define TMCSR0_MOD1 tmcsr0.bit._MOD1
#define TMCSR0_MOD0 tmcsr0.bit._MOD0
#define TMCSR0_OUTL tmcsr0.bit._OUTL
#define TMCSR0_RELD tmcsr0.bit._RELD
#define TMCSR0_INTE tmcsr0.bit._INTE
#define TMCSR0_UF tmcsr0.bit._UF
#define TMCSR0_CNTE tmcsr0.bit._CNTE
#define TMCSR0_TRG tmcsr0.bit._TRG
#define TMCSR0_CSL tmcsr0.bitc._CSL
#define TMCSR0_MOD tmcsr0.bitc._MOD
__IO_EXTERN TMCSRH0STR tmcsrh0;  
#define TMCSRH0 tmcsrh0.byte
#define TMCSRH0_CSL2 tmcsrh0.bit._CSL2
#define TMCSRH0_CSL1 tmcsrh0.bit._CSL1
#define TMCSRH0_CSL0 tmcsrh0.bit._CSL0
#define TMCSRH0_MOD2 tmcsrh0.bit._MOD2
#define TMCSRH0_MOD1 tmcsrh0.bit._MOD1
#define TMCSRH0_CSL tmcsrh0.bitc._CSL
__IO_EXTERN TMCSRL0STR tmcsrl0;  
#define TMCSRL0 tmcsrl0.byte
#define TMCSRL0_MOD0 tmcsrl0.bit._MOD0
#define TMCSRL0_OUTL tmcsrl0.bit._OUTL
#define TMCSRL0_RELD tmcsrl0.bit._RELD
#define TMCSRL0_INTE tmcsrl0.bit._INTE
#define TMCSRL0_UF tmcsrl0.bit._UF
#define TMCSRL0_CNTE tmcsrl0.bit._CNTE
#define TMCSRL0_TRG tmcsrl0.bit._TRG
__IO_EXTERN TMRLR1STR tmrlr1;   /* Reload Timer 1 */
#define TMRLR1 tmrlr1.word
#define TMRLR1_D15 tmrlr1.bit._D15
#define TMRLR1_D14 tmrlr1.bit._D14
#define TMRLR1_D13 tmrlr1.bit._D13
#define TMRLR1_D12 tmrlr1.bit._D12
#define TMRLR1_D11 tmrlr1.bit._D11
#define TMRLR1_D10 tmrlr1.bit._D10
#define TMRLR1_D9 tmrlr1.bit._D9
#define TMRLR1_D8 tmrlr1.bit._D8
#define TMRLR1_D7 tmrlr1.bit._D7
#define TMRLR1_D6 tmrlr1.bit._D6
#define TMRLR1_D5 tmrlr1.bit._D5
#define TMRLR1_D4 tmrlr1.bit._D4
#define TMRLR1_D3 tmrlr1.bit._D3
#define TMRLR1_D2 tmrlr1.bit._D2
#define TMRLR1_D1 tmrlr1.bit._D1
#define TMRLR1_D0 tmrlr1.bit._D0
__IO_EXTERN TMR1STR tmr1;  
#define TMR1 tmr1.word
#define TMR1_D15 tmr1.bit._D15
#define TMR1_D14 tmr1.bit._D14
#define TMR1_D13 tmr1.bit._D13
#define TMR1_D12 tmr1.bit._D12
#define TMR1_D11 tmr1.bit._D11
#define TMR1_D10 tmr1.bit._D10
#define TMR1_D9 tmr1.bit._D9
#define TMR1_D8 tmr1.bit._D8
#define TMR1_D7 tmr1.bit._D7
#define TMR1_D6 tmr1.bit._D6
#define TMR1_D5 tmr1.bit._D5
#define TMR1_D4 tmr1.bit._D4
#define TMR1_D3 tmr1.bit._D3
#define TMR1_D2 tmr1.bit._D2
#define TMR1_D1 tmr1.bit._D1
#define TMR1_D0 tmr1.bit._D0
__IO_EXTERN TMCSR1STR tmcsr1;  
#define TMCSR1 tmcsr1.word
#define TMCSR1_CSL2 tmcsr1.bit._CSL2
#define TMCSR1_CSL1 tmcsr1.bit._CSL1
#define TMCSR1_CSL0 tmcsr1.bit._CSL0
#define TMCSR1_MOD2 tmcsr1.bit._MOD2
#define TMCSR1_MOD1 tmcsr1.bit._MOD1
#define TMCSR1_MOD0 tmcsr1.bit._MOD0
#define TMCSR1_OUTL tmcsr1.bit._OUTL
#define TMCSR1_RELD tmcsr1.bit._RELD
#define TMCSR1_INTE tmcsr1.bit._INTE
#define TMCSR1_UF tmcsr1.bit._UF
#define TMCSR1_CNTE tmcsr1.bit._CNTE
#define TMCSR1_TRG tmcsr1.bit._TRG
#define TMCSR1_CSL tmcsr1.bitc._CSL
#define TMCSR1_MOD tmcsr1.bitc._MOD
__IO_EXTERN TMCSRH1STR tmcsrh1;  
#define TMCSRH1 tmcsrh1.byte
#define TMCSRH1_CSL2 tmcsrh1.bit._CSL2
#define TMCSRH1_CSL1 tmcsrh1.bit._CSL1
#define TMCSRH1_CSL0 tmcsrh1.bit._CSL0
#define TMCSRH1_MOD2 tmcsrh1.bit._MOD2
#define TMCSRH1_MOD1 tmcsrh1.bit._MOD1
#define TMCSRH1_CSL tmcsrh1.bitc._CSL
__IO_EXTERN TMCSRL1STR tmcsrl1;  
#define TMCSRL1 tmcsrl1.byte
#define TMCSRL1_MOD0 tmcsrl1.bit._MOD0
#define TMCSRL1_OUTL tmcsrl1.bit._OUTL
#define TMCSRL1_RELD tmcsrl1.bit._RELD
#define TMCSRL1_INTE tmcsrl1.bit._INTE
#define TMCSRL1_UF tmcsrl1.bit._UF
#define TMCSRL1_CNTE tmcsrl1.bit._CNTE
#define TMCSRL1_TRG tmcsrl1.bit._TRG
__IO_EXTERN TMRLR2STR tmrlr2;   /* Reload Timer 2 */
#define TMRLR2 tmrlr2.word
#define TMRLR2_D15 tmrlr2.bit._D15
#define TMRLR2_D14 tmrlr2.bit._D14
#define TMRLR2_D13 tmrlr2.bit._D13
#define TMRLR2_D12 tmrlr2.bit._D12
#define TMRLR2_D11 tmrlr2.bit._D11
#define TMRLR2_D10 tmrlr2.bit._D10
#define TMRLR2_D9 tmrlr2.bit._D9
#define TMRLR2_D8 tmrlr2.bit._D8
#define TMRLR2_D7 tmrlr2.bit._D7
#define TMRLR2_D6 tmrlr2.bit._D6
#define TMRLR2_D5 tmrlr2.bit._D5
#define TMRLR2_D4 tmrlr2.bit._D4
#define TMRLR2_D3 tmrlr2.bit._D3
#define TMRLR2_D2 tmrlr2.bit._D2
#define TMRLR2_D1 tmrlr2.bit._D1
#define TMRLR2_D0 tmrlr2.bit._D0
__IO_EXTERN TMR2STR tmr2;  
#define TMR2 tmr2.word
#define TMR2_D15 tmr2.bit._D15
#define TMR2_D14 tmr2.bit._D14
#define TMR2_D13 tmr2.bit._D13
#define TMR2_D12 tmr2.bit._D12
#define TMR2_D11 tmr2.bit._D11
#define TMR2_D10 tmr2.bit._D10
#define TMR2_D9 tmr2.bit._D9
#define TMR2_D8 tmr2.bit._D8
#define TMR2_D7 tmr2.bit._D7
#define TMR2_D6 tmr2.bit._D6
#define TMR2_D5 tmr2.bit._D5
#define TMR2_D4 tmr2.bit._D4
#define TMR2_D3 tmr2.bit._D3
#define TMR2_D2 tmr2.bit._D2
#define TMR2_D1 tmr2.bit._D1
#define TMR2_D0 tmr2.bit._D0
__IO_EXTERN TMCSR2STR tmcsr2;  
#define TMCSR2 tmcsr2.word
#define TMCSR2_CSL2 tmcsr2.bit._CSL2
#define TMCSR2_CSL1 tmcsr2.bit._CSL1
#define TMCSR2_CSL0 tmcsr2.bit._CSL0
#define TMCSR2_MOD2 tmcsr2.bit._MOD2
#define TMCSR2_MOD1 tmcsr2.bit._MOD1
#define TMCSR2_MOD0 tmcsr2.bit._MOD0
#define TMCSR2_OUTL tmcsr2.bit._OUTL
#define TMCSR2_RELD tmcsr2.bit._RELD
#define TMCSR2_INTE tmcsr2.bit._INTE
#define TMCSR2_UF tmcsr2.bit._UF
#define TMCSR2_CNTE tmcsr2.bit._CNTE
#define TMCSR2_TRG tmcsr2.bit._TRG
#define TMCSR2_CSL tmcsr2.bitc._CSL
#define TMCSR2_MOD tmcsr2.bitc._MOD
__IO_EXTERN TMCSRH2STR tmcsrh2;  
#define TMCSRH2 tmcsrh2.byte
#define TMCSRH2_CSL2 tmcsrh2.bit._CSL2
#define TMCSRH2_CSL1 tmcsrh2.bit._CSL1
#define TMCSRH2_CSL0 tmcsrh2.bit._CSL0
#define TMCSRH2_MOD2 tmcsrh2.bit._MOD2
#define TMCSRH2_MOD1 tmcsrh2.bit._MOD1
#define TMCSRH2_CSL tmcsrh2.bitc._CSL
__IO_EXTERN TMCSRL2STR tmcsrl2;  
#define TMCSRL2 tmcsrl2.byte
#define TMCSRL2_MOD0 tmcsrl2.bit._MOD0
#define TMCSRL2_OUTL tmcsrl2.bit._OUTL
#define TMCSRL2_RELD tmcsrl2.bit._RELD
#define TMCSRL2_INTE tmcsrl2.bit._INTE
#define TMCSRL2_UF tmcsrl2.bit._UF
#define TMCSRL2_CNTE tmcsrl2.bit._CNTE
#define TMCSRL2_TRG tmcsrl2.bit._TRG
__IO_EXTERN TMRLR3STR tmrlr3;   /* Reload Timer 3 */
#define TMRLR3 tmrlr3.word
#define TMRLR3_D15 tmrlr3.bit._D15
#define TMRLR3_D14 tmrlr3.bit._D14
#define TMRLR3_D13 tmrlr3.bit._D13
#define TMRLR3_D12 tmrlr3.bit._D12
#define TMRLR3_D11 tmrlr3.bit._D11
#define TMRLR3_D10 tmrlr3.bit._D10
#define TMRLR3_D9 tmrlr3.bit._D9
#define TMRLR3_D8 tmrlr3.bit._D8
#define TMRLR3_D7 tmrlr3.bit._D7
#define TMRLR3_D6 tmrlr3.bit._D6
#define TMRLR3_D5 tmrlr3.bit._D5
#define TMRLR3_D4 tmrlr3.bit._D4
#define TMRLR3_D3 tmrlr3.bit._D3
#define TMRLR3_D2 tmrlr3.bit._D2
#define TMRLR3_D1 tmrlr3.bit._D1
#define TMRLR3_D0 tmrlr3.bit._D0
__IO_EXTERN TMR3STR tmr3;  
#define TMR3 tmr3.word
#define TMR3_D15 tmr3.bit._D15
#define TMR3_D14 tmr3.bit._D14
#define TMR3_D13 tmr3.bit._D13
#define TMR3_D12 tmr3.bit._D12
#define TMR3_D11 tmr3.bit._D11
#define TMR3_D10 tmr3.bit._D10
#define TMR3_D9 tmr3.bit._D9
#define TMR3_D8 tmr3.bit._D8
#define TMR3_D7 tmr3.bit._D7
#define TMR3_D6 tmr3.bit._D6
#define TMR3_D5 tmr3.bit._D5
#define TMR3_D4 tmr3.bit._D4
#define TMR3_D3 tmr3.bit._D3
#define TMR3_D2 tmr3.bit._D2
#define TMR3_D1 tmr3.bit._D1
#define TMR3_D0 tmr3.bit._D0
__IO_EXTERN TMCSR3STR tmcsr3;  
#define TMCSR3 tmcsr3.word
#define TMCSR3_CSL2 tmcsr3.bit._CSL2
#define TMCSR3_CSL1 tmcsr3.bit._CSL1
#define TMCSR3_CSL0 tmcsr3.bit._CSL0
#define TMCSR3_MOD2 tmcsr3.bit._MOD2
#define TMCSR3_MOD1 tmcsr3.bit._MOD1
#define TMCSR3_MOD0 tmcsr3.bit._MOD0
#define TMCSR3_OUTL tmcsr3.bit._OUTL
#define TMCSR3_RELD tmcsr3.bit._RELD
#define TMCSR3_INTE tmcsr3.bit._INTE
#define TMCSR3_UF tmcsr3.bit._UF
#define TMCSR3_CNTE tmcsr3.bit._CNTE
#define TMCSR3_TRG tmcsr3.bit._TRG
#define TMCSR3_CSL tmcsr3.bitc._CSL
#define TMCSR3_MOD tmcsr3.bitc._MOD
__IO_EXTERN TMCSRH3STR tmcsrh3;  
#define TMCSRH3 tmcsrh3.byte
#define TMCSRH3_CSL2 tmcsrh3.bit._CSL2
#define TMCSRH3_CSL1 tmcsrh3.bit._CSL1
#define TMCSRH3_CSL0 tmcsrh3.bit._CSL0
#define TMCSRH3_MOD2 tmcsrh3.bit._MOD2
#define TMCSRH3_MOD1 tmcsrh3.bit._MOD1
#define TMCSRH3_CSL tmcsrh3.bitc._CSL
__IO_EXTERN TMCSRL3STR tmcsrl3;  
#define TMCSRL3 tmcsrl3.byte
#define TMCSRL3_MOD0 tmcsrl3.bit._MOD0
#define TMCSRL3_OUTL tmcsrl3.bit._OUTL
#define TMCSRL3_RELD tmcsrl3.bit._RELD
#define TMCSRL3_INTE tmcsrl3.bit._INTE
#define TMCSRL3_UF tmcsrl3.bit._UF
#define TMCSRL3_CNTE tmcsrl3.bit._CNTE
#define TMCSRL3_TRG tmcsrl3.bit._TRG
__IO_EXTERN TMRLR4STR tmrlr4;   /* Reload Timer 4 */
#define TMRLR4 tmrlr4.word
#define TMRLR4_D15 tmrlr4.bit._D15
#define TMRLR4_D14 tmrlr4.bit._D14
#define TMRLR4_D13 tmrlr4.bit._D13
#define TMRLR4_D12 tmrlr4.bit._D12
#define TMRLR4_D11 tmrlr4.bit._D11
#define TMRLR4_D10 tmrlr4.bit._D10
#define TMRLR4_D9 tmrlr4.bit._D9
#define TMRLR4_D8 tmrlr4.bit._D8
#define TMRLR4_D7 tmrlr4.bit._D7
#define TMRLR4_D6 tmrlr4.bit._D6
#define TMRLR4_D5 tmrlr4.bit._D5
#define TMRLR4_D4 tmrlr4.bit._D4
#define TMRLR4_D3 tmrlr4.bit._D3
#define TMRLR4_D2 tmrlr4.bit._D2
#define TMRLR4_D1 tmrlr4.bit._D1
#define TMRLR4_D0 tmrlr4.bit._D0
__IO_EXTERN TMR4STR tmr4;  
#define TMR4 tmr4.word
#define TMR4_D15 tmr4.bit._D15
#define TMR4_D14 tmr4.bit._D14
#define TMR4_D13 tmr4.bit._D13
#define TMR4_D12 tmr4.bit._D12
#define TMR4_D11 tmr4.bit._D11
#define TMR4_D10 tmr4.bit._D10
#define TMR4_D9 tmr4.bit._D9
#define TMR4_D8 tmr4.bit._D8
#define TMR4_D7 tmr4.bit._D7
#define TMR4_D6 tmr4.bit._D6
#define TMR4_D5 tmr4.bit._D5
#define TMR4_D4 tmr4.bit._D4
#define TMR4_D3 tmr4.bit._D3
#define TMR4_D2 tmr4.bit._D2
#define TMR4_D1 tmr4.bit._D1
#define TMR4_D0 tmr4.bit._D0
__IO_EXTERN TMCSR4STR tmcsr4;  
#define TMCSR4 tmcsr4.word
#define TMCSR4_CSL2 tmcsr4.bit._CSL2
#define TMCSR4_CSL1 tmcsr4.bit._CSL1
#define TMCSR4_CSL0 tmcsr4.bit._CSL0
#define TMCSR4_MOD2 tmcsr4.bit._MOD2
#define TMCSR4_MOD1 tmcsr4.bit._MOD1
#define TMCSR4_MOD0 tmcsr4.bit._MOD0
#define TMCSR4_OUTL tmcsr4.bit._OUTL
#define TMCSR4_RELD tmcsr4.bit._RELD
#define TMCSR4_INTE tmcsr4.bit._INTE
#define TMCSR4_UF tmcsr4.bit._UF
#define TMCSR4_CNTE tmcsr4.bit._CNTE
#define TMCSR4_TRG tmcsr4.bit._TRG
#define TMCSR4_CSL tmcsr4.bitc._CSL
#define TMCSR4_MOD tmcsr4.bitc._MOD
__IO_EXTERN TMCSRH4STR tmcsrh4;  
#define TMCSRH4 tmcsrh4.byte
#define TMCSRH4_CSL2 tmcsrh4.bit._CSL2
#define TMCSRH4_CSL1 tmcsrh4.bit._CSL1
#define TMCSRH4_CSL0 tmcsrh4.bit._CSL0
#define TMCSRH4_MOD2 tmcsrh4.bit._MOD2
#define TMCSRH4_MOD1 tmcsrh4.bit._MOD1
#define TMCSRH4_CSL tmcsrh4.bitc._CSL
__IO_EXTERN TMCSRL4STR tmcsrl4;  
#define TMCSRL4 tmcsrl4.byte
#define TMCSRL4_MOD0 tmcsrl4.bit._MOD0
#define TMCSRL4_OUTL tmcsrl4.bit._OUTL
#define TMCSRL4_RELD tmcsrl4.bit._RELD
#define TMCSRL4_INTE tmcsrl4.bit._INTE
#define TMCSRL4_UF tmcsrl4.bit._UF
#define TMCSRL4_CNTE tmcsrl4.bit._CNTE
#define TMCSRL4_TRG tmcsrl4.bit._TRG
__IO_EXTERN TMRLR5STR tmrlr5;   /* Reload Timer 5 */
#define TMRLR5 tmrlr5.word
#define TMRLR5_D15 tmrlr5.bit._D15
#define TMRLR5_D14 tmrlr5.bit._D14
#define TMRLR5_D13 tmrlr5.bit._D13
#define TMRLR5_D12 tmrlr5.bit._D12
#define TMRLR5_D11 tmrlr5.bit._D11
#define TMRLR5_D10 tmrlr5.bit._D10
#define TMRLR5_D9 tmrlr5.bit._D9
#define TMRLR5_D8 tmrlr5.bit._D8
#define TMRLR5_D7 tmrlr5.bit._D7
#define TMRLR5_D6 tmrlr5.bit._D6
#define TMRLR5_D5 tmrlr5.bit._D5
#define TMRLR5_D4 tmrlr5.bit._D4
#define TMRLR5_D3 tmrlr5.bit._D3
#define TMRLR5_D2 tmrlr5.bit._D2
#define TMRLR5_D1 tmrlr5.bit._D1
#define TMRLR5_D0 tmrlr5.bit._D0
__IO_EXTERN TMR5STR tmr5;  
#define TMR5 tmr5.word
#define TMR5_D15 tmr5.bit._D15
#define TMR5_D14 tmr5.bit._D14
#define TMR5_D13 tmr5.bit._D13
#define TMR5_D12 tmr5.bit._D12
#define TMR5_D11 tmr5.bit._D11
#define TMR5_D10 tmr5.bit._D10
#define TMR5_D9 tmr5.bit._D9
#define TMR5_D8 tmr5.bit._D8
#define TMR5_D7 tmr5.bit._D7
#define TMR5_D6 tmr5.bit._D6
#define TMR5_D5 tmr5.bit._D5
#define TMR5_D4 tmr5.bit._D4
#define TMR5_D3 tmr5.bit._D3
#define TMR5_D2 tmr5.bit._D2
#define TMR5_D1 tmr5.bit._D1
#define TMR5_D0 tmr5.bit._D0
__IO_EXTERN TMCSR5STR tmcsr5;  
#define TMCSR5 tmcsr5.word
#define TMCSR5_CSL2 tmcsr5.bit._CSL2
#define TMCSR5_CSL1 tmcsr5.bit._CSL1
#define TMCSR5_CSL0 tmcsr5.bit._CSL0
#define TMCSR5_MOD2 tmcsr5.bit._MOD2
#define TMCSR5_MOD1 tmcsr5.bit._MOD1
#define TMCSR5_MOD0 tmcsr5.bit._MOD0
#define TMCSR5_OUTL tmcsr5.bit._OUTL
#define TMCSR5_RELD tmcsr5.bit._RELD
#define TMCSR5_INTE tmcsr5.bit._INTE
#define TMCSR5_UF tmcsr5.bit._UF
#define TMCSR5_CNTE tmcsr5.bit._CNTE
#define TMCSR5_TRG tmcsr5.bit._TRG
#define TMCSR5_CSL tmcsr5.bitc._CSL
#define TMCSR5_MOD tmcsr5.bitc._MOD
__IO_EXTERN TMCSRH5STR tmcsrh5;  
#define TMCSRH5 tmcsrh5.byte
#define TMCSRH5_CSL2 tmcsrh5.bit._CSL2
#define TMCSRH5_CSL1 tmcsrh5.bit._CSL1
#define TMCSRH5_CSL0 tmcsrh5.bit._CSL0
#define TMCSRH5_MOD2 tmcsrh5.bit._MOD2
#define TMCSRH5_MOD1 tmcsrh5.bit._MOD1
#define TMCSRH5_CSL tmcsrh5.bitc._CSL
__IO_EXTERN TMCSRL5STR tmcsrl5;  
#define TMCSRL5 tmcsrl5.byte
#define TMCSRL5_MOD0 tmcsrl5.bit._MOD0
#define TMCSRL5_OUTL tmcsrl5.bit._OUTL
#define TMCSRL5_RELD tmcsrl5.bit._RELD
#define TMCSRL5_INTE tmcsrl5.bit._INTE
#define TMCSRL5_UF tmcsrl5.bit._UF
#define TMCSRL5_CNTE tmcsrl5.bit._CNTE
#define TMCSRL5_TRG tmcsrl5.bit._TRG
__IO_EXTERN TMRLR6STR tmrlr6;   /* Reload Timer 6 */
#define TMRLR6 tmrlr6.word
#define TMRLR6_D15 tmrlr6.bit._D15
#define TMRLR6_D14 tmrlr6.bit._D14
#define TMRLR6_D13 tmrlr6.bit._D13
#define TMRLR6_D12 tmrlr6.bit._D12
#define TMRLR6_D11 tmrlr6.bit._D11
#define TMRLR6_D10 tmrlr6.bit._D10
#define TMRLR6_D9 tmrlr6.bit._D9
#define TMRLR6_D8 tmrlr6.bit._D8
#define TMRLR6_D7 tmrlr6.bit._D7
#define TMRLR6_D6 tmrlr6.bit._D6
#define TMRLR6_D5 tmrlr6.bit._D5
#define TMRLR6_D4 tmrlr6.bit._D4
#define TMRLR6_D3 tmrlr6.bit._D3
#define TMRLR6_D2 tmrlr6.bit._D2
#define TMRLR6_D1 tmrlr6.bit._D1
#define TMRLR6_D0 tmrlr6.bit._D0
__IO_EXTERN TMR6STR tmr6;  
#define TMR6 tmr6.word
#define TMR6_D15 tmr6.bit._D15
#define TMR6_D14 tmr6.bit._D14
#define TMR6_D13 tmr6.bit._D13
#define TMR6_D12 tmr6.bit._D12
#define TMR6_D11 tmr6.bit._D11
#define TMR6_D10 tmr6.bit._D10
#define TMR6_D9 tmr6.bit._D9
#define TMR6_D8 tmr6.bit._D8
#define TMR6_D7 tmr6.bit._D7
#define TMR6_D6 tmr6.bit._D6
#define TMR6_D5 tmr6.bit._D5
#define TMR6_D4 tmr6.bit._D4
#define TMR6_D3 tmr6.bit._D3
#define TMR6_D2 tmr6.bit._D2
#define TMR6_D1 tmr6.bit._D1
#define TMR6_D0 tmr6.bit._D0
__IO_EXTERN TMCSR6STR tmcsr6;  
#define TMCSR6 tmcsr6.word
#define TMCSR6_CSL2 tmcsr6.bit._CSL2
#define TMCSR6_CSL1 tmcsr6.bit._CSL1
#define TMCSR6_CSL0 tmcsr6.bit._CSL0
#define TMCSR6_MOD2 tmcsr6.bit._MOD2
#define TMCSR6_MOD1 tmcsr6.bit._MOD1
#define TMCSR6_MOD0 tmcsr6.bit._MOD0
#define TMCSR6_OUTL tmcsr6.bit._OUTL
#define TMCSR6_RELD tmcsr6.bit._RELD
#define TMCSR6_INTE tmcsr6.bit._INTE
#define TMCSR6_UF tmcsr6.bit._UF
#define TMCSR6_CNTE tmcsr6.bit._CNTE
#define TMCSR6_TRG tmcsr6.bit._TRG
#define TMCSR6_CSL tmcsr6.bitc._CSL
#define TMCSR6_MOD tmcsr6.bitc._MOD
__IO_EXTERN TMCSRH6STR tmcsrh6;  
#define TMCSRH6 tmcsrh6.byte
#define TMCSRH6_CSL2 tmcsrh6.bit._CSL2
#define TMCSRH6_CSL1 tmcsrh6.bit._CSL1
#define TMCSRH6_CSL0 tmcsrh6.bit._CSL0
#define TMCSRH6_MOD2 tmcsrh6.bit._MOD2
#define TMCSRH6_MOD1 tmcsrh6.bit._MOD1
#define TMCSRH6_CSL tmcsrh6.bitc._CSL
__IO_EXTERN TMCSRL6STR tmcsrl6;  
#define TMCSRL6 tmcsrl6.byte
#define TMCSRL6_MOD0 tmcsrl6.bit._MOD0
#define TMCSRL6_OUTL tmcsrl6.bit._OUTL
#define TMCSRL6_RELD tmcsrl6.bit._RELD
#define TMCSRL6_INTE tmcsrl6.bit._INTE
#define TMCSRL6_UF tmcsrl6.bit._UF
#define TMCSRL6_CNTE tmcsrl6.bit._CNTE
#define TMCSRL6_TRG tmcsrl6.bit._TRG
__IO_EXTERN TMRLR7STR tmrlr7;   /* Reload Timer 7 */
#define TMRLR7 tmrlr7.word
#define TMRLR7_D15 tmrlr7.bit._D15
#define TMRLR7_D14 tmrlr7.bit._D14
#define TMRLR7_D13 tmrlr7.bit._D13
#define TMRLR7_D12 tmrlr7.bit._D12
#define TMRLR7_D11 tmrlr7.bit._D11
#define TMRLR7_D10 tmrlr7.bit._D10
#define TMRLR7_D9 tmrlr7.bit._D9
#define TMRLR7_D8 tmrlr7.bit._D8
#define TMRLR7_D7 tmrlr7.bit._D7
#define TMRLR7_D6 tmrlr7.bit._D6
#define TMRLR7_D5 tmrlr7.bit._D5
#define TMRLR7_D4 tmrlr7.bit._D4
#define TMRLR7_D3 tmrlr7.bit._D3
#define TMRLR7_D2 tmrlr7.bit._D2
#define TMRLR7_D1 tmrlr7.bit._D1
#define TMRLR7_D0 tmrlr7.bit._D0
__IO_EXTERN TMR7STR tmr7;  
#define TMR7 tmr7.word
#define TMR7_D15 tmr7.bit._D15
#define TMR7_D14 tmr7.bit._D14
#define TMR7_D13 tmr7.bit._D13
#define TMR7_D12 tmr7.bit._D12
#define TMR7_D11 tmr7.bit._D11
#define TMR7_D10 tmr7.bit._D10
#define TMR7_D9 tmr7.bit._D9
#define TMR7_D8 tmr7.bit._D8
#define TMR7_D7 tmr7.bit._D7
#define TMR7_D6 tmr7.bit._D6
#define TMR7_D5 tmr7.bit._D5
#define TMR7_D4 tmr7.bit._D4
#define TMR7_D3 tmr7.bit._D3
#define TMR7_D2 tmr7.bit._D2
#define TMR7_D1 tmr7.bit._D1
#define TMR7_D0 tmr7.bit._D0
__IO_EXTERN TMCSR7STR tmcsr7;  
#define TMCSR7 tmcsr7.word
#define TMCSR7_CSL2 tmcsr7.bit._CSL2
#define TMCSR7_CSL1 tmcsr7.bit._CSL1
#define TMCSR7_CSL0 tmcsr7.bit._CSL0
#define TMCSR7_MOD2 tmcsr7.bit._MOD2
#define TMCSR7_MOD1 tmcsr7.bit._MOD1
#define TMCSR7_MOD0 tmcsr7.bit._MOD0
#define TMCSR7_OUTL tmcsr7.bit._OUTL
#define TMCSR7_RELD tmcsr7.bit._RELD
#define TMCSR7_INTE tmcsr7.bit._INTE
#define TMCSR7_UF tmcsr7.bit._UF
#define TMCSR7_CNTE tmcsr7.bit._CNTE
#define TMCSR7_TRG tmcsr7.bit._TRG
#define TMCSR7_CSL tmcsr7.bitc._CSL
#define TMCSR7_MOD tmcsr7.bitc._MOD
__IO_EXTERN TMCSRH7STR tmcsrh7;  
#define TMCSRH7 tmcsrh7.byte
#define TMCSRH7_CSL2 tmcsrh7.bit._CSL2
#define TMCSRH7_CSL1 tmcsrh7.bit._CSL1
#define TMCSRH7_CSL0 tmcsrh7.bit._CSL0
#define TMCSRH7_MOD2 tmcsrh7.bit._MOD2
#define TMCSRH7_MOD1 tmcsrh7.bit._MOD1
#define TMCSRH7_CSL tmcsrh7.bitc._CSL
__IO_EXTERN TMCSRL7STR tmcsrl7;  
#define TMCSRL7 tmcsrl7.byte
#define TMCSRL7_MOD0 tmcsrl7.bit._MOD0
#define TMCSRL7_OUTL tmcsrl7.bit._OUTL
#define TMCSRL7_RELD tmcsrl7.bit._RELD
#define TMCSRL7_INTE tmcsrl7.bit._INTE
#define TMCSRL7_UF tmcsrl7.bit._UF
#define TMCSRL7_CNTE tmcsrl7.bit._CNTE
#define TMCSRL7_TRG tmcsrl7.bit._TRG
__IO_EXTERN TCDT0STR tcdt0;   /* Free Running Timer0 */
#define TCDT0 tcdt0.word
#define TCDT0_T15 tcdt0.bit._T15
#define TCDT0_T14 tcdt0.bit._T14
#define TCDT0_T13 tcdt0.bit._T13
#define TCDT0_T12 tcdt0.bit._T12
#define TCDT0_T11 tcdt0.bit._T11
#define TCDT0_T10 tcdt0.bit._T10
#define TCDT0_T9 tcdt0.bit._T9
#define TCDT0_T8 tcdt0.bit._T8
#define TCDT0_T7 tcdt0.bit._T7
#define TCDT0_T6 tcdt0.bit._T6
#define TCDT0_T5 tcdt0.bit._T5
#define TCDT0_T4 tcdt0.bit._T4
#define TCDT0_T3 tcdt0.bit._T3
#define TCDT0_T2 tcdt0.bit._T2
#define TCDT0_T1 tcdt0.bit._T1
#define TCDT0_T0 tcdt0.bit._T0
__IO_EXTERN TCCS0STR tccs0;  
#define TCCS0 tccs0.byte
#define TCCS0_ECLK tccs0.bit._ECLK
#define TCCS0_IVF tccs0.bit._IVF
#define TCCS0_IVFE tccs0.bit._IVFE
#define TCCS0_STOP tccs0.bit._STOP
#define TCCS0_MODE tccs0.bit._MODE
#define TCCS0_CLR tccs0.bit._CLR
#define TCCS0_CLK1 tccs0.bit._CLK1
#define TCCS0_CLK0 tccs0.bit._CLK0
#define TCCS0_CLK tccs0.bitc._CLK
__IO_EXTERN TCDT1STR tcdt1;   /* Free Running Timer1 */
#define TCDT1 tcdt1.word
#define TCDT1_T15 tcdt1.bit._T15
#define TCDT1_T14 tcdt1.bit._T14
#define TCDT1_T13 tcdt1.bit._T13
#define TCDT1_T12 tcdt1.bit._T12
#define TCDT1_T11 tcdt1.bit._T11
#define TCDT1_T10 tcdt1.bit._T10
#define TCDT1_T9 tcdt1.bit._T9
#define TCDT1_T8 tcdt1.bit._T8
#define TCDT1_T7 tcdt1.bit._T7
#define TCDT1_T6 tcdt1.bit._T6
#define TCDT1_T5 tcdt1.bit._T5
#define TCDT1_T4 tcdt1.bit._T4
#define TCDT1_T3 tcdt1.bit._T3
#define TCDT1_T2 tcdt1.bit._T2
#define TCDT1_T1 tcdt1.bit._T1
#define TCDT1_T0 tcdt1.bit._T0
__IO_EXTERN TCCS1STR tccs1;  
#define TCCS1 tccs1.byte
#define TCCS1_ECLK tccs1.bit._ECLK
#define TCCS1_IVF tccs1.bit._IVF
#define TCCS1_IVFE tccs1.bit._IVFE
#define TCCS1_STOP tccs1.bit._STOP
#define TCCS1_MODE tccs1.bit._MODE
#define TCCS1_CLR tccs1.bit._CLR
#define TCCS1_CLK1 tccs1.bit._CLK1
#define TCCS1_CLK0 tccs1.bit._CLK0
#define TCCS1_CLK tccs1.bitc._CLK
__IO_EXTERN TCDT2STR tcdt2;   /* Free Running Timer2 */
#define TCDT2 tcdt2.word
#define TCDT2_T15 tcdt2.bit._T15
#define TCDT2_T14 tcdt2.bit._T14
#define TCDT2_T13 tcdt2.bit._T13
#define TCDT2_T12 tcdt2.bit._T12
#define TCDT2_T11 tcdt2.bit._T11
#define TCDT2_T10 tcdt2.bit._T10
#define TCDT2_T9 tcdt2.bit._T9
#define TCDT2_T8 tcdt2.bit._T8
#define TCDT2_T7 tcdt2.bit._T7
#define TCDT2_T6 tcdt2.bit._T6
#define TCDT2_T5 tcdt2.bit._T5
#define TCDT2_T4 tcdt2.bit._T4
#define TCDT2_T3 tcdt2.bit._T3
#define TCDT2_T2 tcdt2.bit._T2
#define TCDT2_T1 tcdt2.bit._T1
#define TCDT2_T0 tcdt2.bit._T0
__IO_EXTERN TCCS2STR tccs2;  
#define TCCS2 tccs2.byte
#define TCCS2_ECLK tccs2.bit._ECLK
#define TCCS2_IVF tccs2.bit._IVF
#define TCCS2_IVFE tccs2.bit._IVFE
#define TCCS2_STOP tccs2.bit._STOP
#define TCCS2_MODE tccs2.bit._MODE
#define TCCS2_CLR tccs2.bit._CLR
#define TCCS2_CLK1 tccs2.bit._CLK1
#define TCCS2_CLK0 tccs2.bit._CLK0
#define TCCS2_CLK tccs2.bitc._CLK
__IO_EXTERN TCDT3STR tcdt3;   /* Free Running Timer3 */
#define TCDT3 tcdt3.word
#define TCDT3_T15 tcdt3.bit._T15
#define TCDT3_T14 tcdt3.bit._T14
#define TCDT3_T13 tcdt3.bit._T13
#define TCDT3_T12 tcdt3.bit._T12
#define TCDT3_T11 tcdt3.bit._T11
#define TCDT3_T10 tcdt3.bit._T10
#define TCDT3_T9 tcdt3.bit._T9
#define TCDT3_T8 tcdt3.bit._T8
#define TCDT3_T7 tcdt3.bit._T7
#define TCDT3_T6 tcdt3.bit._T6
#define TCDT3_T5 tcdt3.bit._T5
#define TCDT3_T4 tcdt3.bit._T4
#define TCDT3_T3 tcdt3.bit._T3
#define TCDT3_T2 tcdt3.bit._T2
#define TCDT3_T1 tcdt3.bit._T1
#define TCDT3_T0 tcdt3.bit._T0
__IO_EXTERN TCCS3STR tccs3;  
#define TCCS3 tccs3.byte
#define TCCS3_ECLK tccs3.bit._ECLK
#define TCCS3_IVF tccs3.bit._IVF
#define TCCS3_IVFE tccs3.bit._IVFE
#define TCCS3_STOP tccs3.bit._STOP
#define TCCS3_MODE tccs3.bit._MODE
#define TCCS3_CLR tccs3.bit._CLR
#define TCCS3_CLK1 tccs3.bit._CLK1
#define TCCS3_CLK0 tccs3.bit._CLK0
#define TCCS3_CLK tccs3.bitc._CLK
__IO_EXTERN DMACA0STR dmaca0;   /* DMAC */
#define DMACA0 dmaca0.lword
#define DMACA0_DENB dmaca0.bit._DENB
#define DMACA0_PAUS dmaca0.bit._PAUS
#define DMACA0_STRG dmaca0.bit._STRG
#define DMACA0_IS4 dmaca0.bit._IS4
#define DMACA0_IS3 dmaca0.bit._IS3
#define DMACA0_IS2 dmaca0.bit._IS2
#define DMACA0_IS1 dmaca0.bit._IS1
#define DMACA0_IS0 dmaca0.bit._IS0
#define DMACA0_EIS3 dmaca0.bit._EIS3
#define DMACA0_EIS2 dmaca0.bit._EIS2
#define DMACA0_EIS1 dmaca0.bit._EIS1
#define DMACA0_EIS0 dmaca0.bit._EIS0
#define DMACA0_BLK3 dmaca0.bit._BLK3
#define DMACA0_BLK2 dmaca0.bit._BLK2
#define DMACA0_BLK1 dmaca0.bit._BLK1
#define DMACA0_BLK0 dmaca0.bit._BLK0
#define DMACA0_DTCF dmaca0.bit._DTCF
#define DMACA0_DTCE dmaca0.bit._DTCE
#define DMACA0_DTCD dmaca0.bit._DTCD
#define DMACA0_DTCC dmaca0.bit._DTCC
#define DMACA0_DTCB dmaca0.bit._DTCB
#define DMACA0_DTCA dmaca0.bit._DTCA
#define DMACA0_DTC9 dmaca0.bit._DTC9
#define DMACA0_DTC8 dmaca0.bit._DTC8
#define DMACA0_DTC7 dmaca0.bit._DTC7
#define DMACA0_DTC6 dmaca0.bit._DTC6
#define DMACA0_DTC5 dmaca0.bit._DTC5
#define DMACA0_DTC4 dmaca0.bit._DTC4
#define DMACA0_DTC3 dmaca0.bit._DTC3
#define DMACA0_DTC2 dmaca0.bit._DTC2
#define DMACA0_DTC1 dmaca0.bit._DTC1
#define DMACA0_DTC0 dmaca0.bit._DTC0
#define DMACA0_IS dmaca0.bitc._IS
#define DMACA0_EIS dmaca0.bitc._EIS
#define DMACA0_BLK dmaca0.bitc._BLK
#define DMACA0_DTC dmaca0.bitc._DTC
__IO_EXTERN DMACB0STR dmacb0;  
#define DMACB0 dmacb0.lword
#define DMACB0_TYPE1 dmacb0.bit._TYPE1
#define DMACB0_TYPE0 dmacb0.bit._TYPE0
#define DMACB0_MOD1 dmacb0.bit._MOD1
#define DMACB0_MOD0 dmacb0.bit._MOD0
#define DMACB0_WS1 dmacb0.bit._WS1
#define DMACB0_WS0 dmacb0.bit._WS0
#define DMACB0_SADM dmacb0.bit._SADM
#define DMACB0_DADM dmacb0.bit._DADM
#define DMACB0_DTCR dmacb0.bit._DTCR
#define DMACB0_SADR dmacb0.bit._SADR
#define DMACB0_DADR dmacb0.bit._DADR
#define DMACB0_ERIE dmacb0.bit._ERIE
#define DMACB0_EDIE dmacb0.bit._EDIE
#define DMACB0_DSS2 dmacb0.bit._DSS2
#define DMACB0_DSS1 dmacb0.bit._DSS1
#define DMACB0_DSS0 dmacb0.bit._DSS0
#define DMACB0_SASZ7 dmacb0.bit._SASZ7
#define DMACB0_SASZ6 dmacb0.bit._SASZ6
#define DMACB0_SASZ5 dmacb0.bit._SASZ5
#define DMACB0_SASZ4 dmacb0.bit._SASZ4
#define DMACB0_SASZ3 dmacb0.bit._SASZ3
#define DMACB0_SASZ2 dmacb0.bit._SASZ2
#define DMACB0_SASZ1 dmacb0.bit._SASZ1
#define DMACB0_SASZ0 dmacb0.bit._SASZ0
#define DMACB0_DASZ7 dmacb0.bit._DASZ7
#define DMACB0_DASZ6 dmacb0.bit._DASZ6
#define DMACB0_DASZ5 dmacb0.bit._DASZ5
#define DMACB0_DASZ4 dmacb0.bit._DASZ4
#define DMACB0_DASZ3 dmacb0.bit._DASZ3
#define DMACB0_DASZ2 dmacb0.bit._DASZ2
#define DMACB0_DASZ1 dmacb0.bit._DASZ1
#define DMACB0_DASZ0 dmacb0.bit._DASZ0
#define DMACB0_TYPE dmacb0.bitc._TYPE
#define DMACB0_MOD dmacb0.bitc._MOD
#define DMACB0_WS dmacb0.bitc._WS
#define DMACB0_DSS dmacb0.bitc._DSS
#define DMACB0_SASZ dmacb0.bitc._SASZ
#define DMACB0_DASZ dmacb0.bitc._DASZ
__IO_EXTERN DMACA1STR dmaca1;  
#define DMACA1 dmaca1.lword
#define DMACA1_DENB dmaca1.bit._DENB
#define DMACA1_PAUS dmaca1.bit._PAUS
#define DMACA1_STRG dmaca1.bit._STRG
#define DMACA1_IS4 dmaca1.bit._IS4
#define DMACA1_IS3 dmaca1.bit._IS3
#define DMACA1_IS2 dmaca1.bit._IS2
#define DMACA1_IS1 dmaca1.bit._IS1
#define DMACA1_IS0 dmaca1.bit._IS0
#define DMACA1_EIS3 dmaca1.bit._EIS3
#define DMACA1_EIS2 dmaca1.bit._EIS2
#define DMACA1_EIS1 dmaca1.bit._EIS1
#define DMACA1_EIS0 dmaca1.bit._EIS0
#define DMACA1_BLK3 dmaca1.bit._BLK3
#define DMACA1_BLK2 dmaca1.bit._BLK2
#define DMACA1_BLK1 dmaca1.bit._BLK1
#define DMACA1_BLK0 dmaca1.bit._BLK0
#define DMACA1_DTCF dmaca1.bit._DTCF
#define DMACA1_DTCE dmaca1.bit._DTCE
#define DMACA1_DTCD dmaca1.bit._DTCD
#define DMACA1_DTCC dmaca1.bit._DTCC
#define DMACA1_DTCB dmaca1.bit._DTCB
#define DMACA1_DTCA dmaca1.bit._DTCA
#define DMACA1_DTC9 dmaca1.bit._DTC9
#define DMACA1_DTC8 dmaca1.bit._DTC8
#define DMACA1_DTC7 dmaca1.bit._DTC7
#define DMACA1_DTC6 dmaca1.bit._DTC6
#define DMACA1_DTC5 dmaca1.bit._DTC5
#define DMACA1_DTC4 dmaca1.bit._DTC4
#define DMACA1_DTC3 dmaca1.bit._DTC3
#define DMACA1_DTC2 dmaca1.bit._DTC2
#define DMACA1_DTC1 dmaca1.bit._DTC1
#define DMACA1_DTC0 dmaca1.bit._DTC0
#define DMACA1_IS dmaca1.bitc._IS
#define DMACA1_EIS dmaca1.bitc._EIS
#define DMACA1_BLK dmaca1.bitc._BLK
#define DMACA1_DTC dmaca1.bitc._DTC
__IO_EXTERN DMACB1STR dmacb1;  
#define DMACB1 dmacb1.lword
#define DMACB1_TYPE1 dmacb1.bit._TYPE1
#define DMACB1_TYPE0 dmacb1.bit._TYPE0
#define DMACB1_MOD1 dmacb1.bit._MOD1
#define DMACB1_MOD0 dmacb1.bit._MOD0
#define DMACB1_WS1 dmacb1.bit._WS1
#define DMACB1_WS0 dmacb1.bit._WS0
#define DMACB1_SADM dmacb1.bit._SADM
#define DMACB1_DADM dmacb1.bit._DADM
#define DMACB1_DTCR dmacb1.bit._DTCR
#define DMACB1_SADR dmacb1.bit._SADR
#define DMACB1_DADR dmacb1.bit._DADR
#define DMACB1_ERIE dmacb1.bit._ERIE
#define DMACB1_EDIE dmacb1.bit._EDIE
#define DMACB1_DSS2 dmacb1.bit._DSS2
#define DMACB1_DSS1 dmacb1.bit._DSS1
#define DMACB1_DSS0 dmacb1.bit._DSS0
#define DMACB1_SASZ7 dmacb1.bit._SASZ7
#define DMACB1_SASZ6 dmacb1.bit._SASZ6
#define DMACB1_SASZ5 dmacb1.bit._SASZ5
#define DMACB1_SASZ4 dmacb1.bit._SASZ4
#define DMACB1_SASZ3 dmacb1.bit._SASZ3
#define DMACB1_SASZ2 dmacb1.bit._SASZ2
#define DMACB1_SASZ1 dmacb1.bit._SASZ1
#define DMACB1_SASZ0 dmacb1.bit._SASZ0
#define DMACB1_DASZ7 dmacb1.bit._DASZ7
#define DMACB1_DASZ6 dmacb1.bit._DASZ6
#define DMACB1_DASZ5 dmacb1.bit._DASZ5
#define DMACB1_DASZ4 dmacb1.bit._DASZ4
#define DMACB1_DASZ3 dmacb1.bit._DASZ3
#define DMACB1_DASZ2 dmacb1.bit._DASZ2
#define DMACB1_DASZ1 dmacb1.bit._DASZ1
#define DMACB1_DASZ0 dmacb1.bit._DASZ0
#define DMACB1_TYPE dmacb1.bitc._TYPE
#define DMACB1_MOD dmacb1.bitc._MOD
#define DMACB1_WS dmacb1.bitc._WS
#define DMACB1_DSS dmacb1.bitc._DSS
#define DMACB1_SASZ dmacb1.bitc._SASZ
#define DMACB1_DASZ dmacb1.bitc._DASZ
__IO_EXTERN DMACA2STR dmaca2;  
#define DMACA2 dmaca2.lword
#define DMACA2_DENB dmaca2.bit._DENB
#define DMACA2_PAUS dmaca2.bit._PAUS
#define DMACA2_STRG dmaca2.bit._STRG
#define DMACA2_IS4 dmaca2.bit._IS4
#define DMACA2_IS3 dmaca2.bit._IS3
#define DMACA2_IS2 dmaca2.bit._IS2
#define DMACA2_IS1 dmaca2.bit._IS1
#define DMACA2_IS0 dmaca2.bit._IS0
#define DMACA2_EIS3 dmaca2.bit._EIS3
#define DMACA2_EIS2 dmaca2.bit._EIS2
#define DMACA2_EIS1 dmaca2.bit._EIS1
#define DMACA2_EIS0 dmaca2.bit._EIS0
#define DMACA2_BLK3 dmaca2.bit._BLK3
#define DMACA2_BLK2 dmaca2.bit._BLK2
#define DMACA2_BLK1 dmaca2.bit._BLK1
#define DMACA2_BLK0 dmaca2.bit._BLK0
#define DMACA2_DTCF dmaca2.bit._DTCF
#define DMACA2_DTCE dmaca2.bit._DTCE
#define DMACA2_DTCD dmaca2.bit._DTCD
#define DMACA2_DTCC dmaca2.bit._DTCC
#define DMACA2_DTCB dmaca2.bit._DTCB
#define DMACA2_DTCA dmaca2.bit._DTCA
#define DMACA2_DTC9 dmaca2.bit._DTC9
#define DMACA2_DTC8 dmaca2.bit._DTC8
#define DMACA2_DTC7 dmaca2.bit._DTC7
#define DMACA2_DTC6 dmaca2.bit._DTC6
#define DMACA2_DTC5 dmaca2.bit._DTC5
#define DMACA2_DTC4 dmaca2.bit._DTC4
#define DMACA2_DTC3 dmaca2.bit._DTC3
#define DMACA2_DTC2 dmaca2.bit._DTC2
#define DMACA2_DTC1 dmaca2.bit._DTC1
#define DMACA2_DTC0 dmaca2.bit._DTC0
#define DMACA2_IS dmaca2.bitc._IS
#define DMACA2_EIS dmaca2.bitc._EIS
#define DMACA2_BLK dmaca2.bitc._BLK
#define DMACA2_DTC dmaca2.bitc._DTC
__IO_EXTERN DMACB2STR dmacb2;  
#define DMACB2 dmacb2.lword
#define DMACB2_TYPE1 dmacb2.bit._TYPE1
#define DMACB2_TYPE0 dmacb2.bit._TYPE0
#define DMACB2_MOD1 dmacb2.bit._MOD1
#define DMACB2_MOD0 dmacb2.bit._MOD0
#define DMACB2_WS1 dmacb2.bit._WS1
#define DMACB2_WS0 dmacb2.bit._WS0
#define DMACB2_SADM dmacb2.bit._SADM
#define DMACB2_DADM dmacb2.bit._DADM
#define DMACB2_DTCR dmacb2.bit._DTCR
#define DMACB2_SADR dmacb2.bit._SADR
#define DMACB2_DADR dmacb2.bit._DADR
#define DMACB2_ERIE dmacb2.bit._ERIE
#define DMACB2_EDIE dmacb2.bit._EDIE
#define DMACB2_DSS2 dmacb2.bit._DSS2
#define DMACB2_DSS1 dmacb2.bit._DSS1
#define DMACB2_DSS0 dmacb2.bit._DSS0
#define DMACB2_SASZ7 dmacb2.bit._SASZ7
#define DMACB2_SASZ6 dmacb2.bit._SASZ6
#define DMACB2_SASZ5 dmacb2.bit._SASZ5
#define DMACB2_SASZ4 dmacb2.bit._SASZ4
#define DMACB2_SASZ3 dmacb2.bit._SASZ3
#define DMACB2_SASZ2 dmacb2.bit._SASZ2
#define DMACB2_SASZ1 dmacb2.bit._SASZ1
#define DMACB2_SASZ0 dmacb2.bit._SASZ0
#define DMACB2_DASZ7 dmacb2.bit._DASZ7
#define DMACB2_DASZ6 dmacb2.bit._DASZ6
#define DMACB2_DASZ5 dmacb2.bit._DASZ5
#define DMACB2_DASZ4 dmacb2.bit._DASZ4
#define DMACB2_DASZ3 dmacb2.bit._DASZ3
#define DMACB2_DASZ2 dmacb2.bit._DASZ2
#define DMACB2_DASZ1 dmacb2.bit._DASZ1
#define DMACB2_DASZ0 dmacb2.bit._DASZ0
#define DMACB2_TYPE dmacb2.bitc._TYPE
#define DMACB2_MOD dmacb2.bitc._MOD
#define DMACB2_WS dmacb2.bitc._WS
#define DMACB2_DSS dmacb2.bitc._DSS
#define DMACB2_SASZ dmacb2.bitc._SASZ
#define DMACB2_DASZ dmacb2.bitc._DASZ
__IO_EXTERN DMACA3STR dmaca3;  
#define DMACA3 dmaca3.lword
#define DMACA3_DENB dmaca3.bit._DENB
#define DMACA3_PAUS dmaca3.bit._PAUS
#define DMACA3_STRG dmaca3.bit._STRG
#define DMACA3_IS4 dmaca3.bit._IS4
#define DMACA3_IS3 dmaca3.bit._IS3
#define DMACA3_IS2 dmaca3.bit._IS2
#define DMACA3_IS1 dmaca3.bit._IS1
#define DMACA3_IS0 dmaca3.bit._IS0
#define DMACA3_EIS3 dmaca3.bit._EIS3
#define DMACA3_EIS2 dmaca3.bit._EIS2
#define DMACA3_EIS1 dmaca3.bit._EIS1
#define DMACA3_EIS0 dmaca3.bit._EIS0
#define DMACA3_BLK3 dmaca3.bit._BLK3
#define DMACA3_BLK2 dmaca3.bit._BLK2
#define DMACA3_BLK1 dmaca3.bit._BLK1
#define DMACA3_BLK0 dmaca3.bit._BLK0
#define DMACA3_DTCF dmaca3.bit._DTCF
#define DMACA3_DTCE dmaca3.bit._DTCE
#define DMACA3_DTCD dmaca3.bit._DTCD
#define DMACA3_DTCC dmaca3.bit._DTCC
#define DMACA3_DTCB dmaca3.bit._DTCB
#define DMACA3_DTCA dmaca3.bit._DTCA
#define DMACA3_DTC9 dmaca3.bit._DTC9
#define DMACA3_DTC8 dmaca3.bit._DTC8
#define DMACA3_DTC7 dmaca3.bit._DTC7
#define DMACA3_DTC6 dmaca3.bit._DTC6
#define DMACA3_DTC5 dmaca3.bit._DTC5
#define DMACA3_DTC4 dmaca3.bit._DTC4
#define DMACA3_DTC3 dmaca3.bit._DTC3
#define DMACA3_DTC2 dmaca3.bit._DTC2
#define DMACA3_DTC1 dmaca3.bit._DTC1
#define DMACA3_DTC0 dmaca3.bit._DTC0
#define DMACA3_IS dmaca3.bitc._IS
#define DMACA3_EIS dmaca3.bitc._EIS
#define DMACA3_BLK dmaca3.bitc._BLK
#define DMACA3_DTC dmaca3.bitc._DTC
__IO_EXTERN DMACB3STR dmacb3;  
#define DMACB3 dmacb3.lword
#define DMACB3_TYPE1 dmacb3.bit._TYPE1
#define DMACB3_TYPE0 dmacb3.bit._TYPE0
#define DMACB3_MOD1 dmacb3.bit._MOD1
#define DMACB3_MOD0 dmacb3.bit._MOD0
#define DMACB3_WS1 dmacb3.bit._WS1
#define DMACB3_WS0 dmacb3.bit._WS0
#define DMACB3_SADM dmacb3.bit._SADM
#define DMACB3_DADM dmacb3.bit._DADM
#define DMACB3_DTCR dmacb3.bit._DTCR
#define DMACB3_SADR dmacb3.bit._SADR
#define DMACB3_DADR dmacb3.bit._DADR
#define DMACB3_ERIE dmacb3.bit._ERIE
#define DMACB3_EDIE dmacb3.bit._EDIE
#define DMACB3_DSS2 dmacb3.bit._DSS2
#define DMACB3_DSS1 dmacb3.bit._DSS1
#define DMACB3_DSS0 dmacb3.bit._DSS0
#define DMACB3_SASZ7 dmacb3.bit._SASZ7
#define DMACB3_SASZ6 dmacb3.bit._SASZ6
#define DMACB3_SASZ5 dmacb3.bit._SASZ5
#define DMACB3_SASZ4 dmacb3.bit._SASZ4
#define DMACB3_SASZ3 dmacb3.bit._SASZ3
#define DMACB3_SASZ2 dmacb3.bit._SASZ2
#define DMACB3_SASZ1 dmacb3.bit._SASZ1
#define DMACB3_SASZ0 dmacb3.bit._SASZ0
#define DMACB3_DASZ7 dmacb3.bit._DASZ7
#define DMACB3_DASZ6 dmacb3.bit._DASZ6
#define DMACB3_DASZ5 dmacb3.bit._DASZ5
#define DMACB3_DASZ4 dmacb3.bit._DASZ4
#define DMACB3_DASZ3 dmacb3.bit._DASZ3
#define DMACB3_DASZ2 dmacb3.bit._DASZ2
#define DMACB3_DASZ1 dmacb3.bit._DASZ1
#define DMACB3_DASZ0 dmacb3.bit._DASZ0
#define DMACB3_TYPE dmacb3.bitc._TYPE
#define DMACB3_MOD dmacb3.bitc._MOD
#define DMACB3_WS dmacb3.bitc._WS
#define DMACB3_DSS dmacb3.bitc._DSS
#define DMACB3_SASZ dmacb3.bitc._SASZ
#define DMACB3_DASZ dmacb3.bitc._DASZ
__IO_EXTERN DMACA4STR dmaca4;  
#define DMACA4 dmaca4.lword
#define DMACA4_DENB dmaca4.bit._DENB
#define DMACA4_PAUS dmaca4.bit._PAUS
#define DMACA4_STRG dmaca4.bit._STRG
#define DMACA4_IS4 dmaca4.bit._IS4
#define DMACA4_IS3 dmaca4.bit._IS3
#define DMACA4_IS2 dmaca4.bit._IS2
#define DMACA4_IS1 dmaca4.bit._IS1
#define DMACA4_IS0 dmaca4.bit._IS0
#define DMACA4_EIS3 dmaca4.bit._EIS3
#define DMACA4_EIS2 dmaca4.bit._EIS2
#define DMACA4_EIS1 dmaca4.bit._EIS1
#define DMACA4_EIS0 dmaca4.bit._EIS0
#define DMACA4_BLK3 dmaca4.bit._BLK3
#define DMACA4_BLK2 dmaca4.bit._BLK2
#define DMACA4_BLK1 dmaca4.bit._BLK1
#define DMACA4_BLK0 dmaca4.bit._BLK0
#define DMACA4_DTCF dmaca4.bit._DTCF
#define DMACA4_DTCE dmaca4.bit._DTCE
#define DMACA4_DTCD dmaca4.bit._DTCD
#define DMACA4_DTCC dmaca4.bit._DTCC
#define DMACA4_DTCB dmaca4.bit._DTCB
#define DMACA4_DTCA dmaca4.bit._DTCA
#define DMACA4_DTC9 dmaca4.bit._DTC9
#define DMACA4_DTC8 dmaca4.bit._DTC8
#define DMACA4_DTC7 dmaca4.bit._DTC7
#define DMACA4_DTC6 dmaca4.bit._DTC6
#define DMACA4_DTC5 dmaca4.bit._DTC5
#define DMACA4_DTC4 dmaca4.bit._DTC4
#define DMACA4_DTC3 dmaca4.bit._DTC3
#define DMACA4_DTC2 dmaca4.bit._DTC2
#define DMACA4_DTC1 dmaca4.bit._DTC1
#define DMACA4_DTC0 dmaca4.bit._DTC0
#define DMACA4_IS dmaca4.bitc._IS
#define DMACA4_EIS dmaca4.bitc._EIS
#define DMACA4_BLK dmaca4.bitc._BLK
#define DMACA4_DTC dmaca4.bitc._DTC
__IO_EXTERN DMACB4STR dmacb4;  
#define DMACB4 dmacb4.lword
#define DMACB4_TYPE1 dmacb4.bit._TYPE1
#define DMACB4_TYPE0 dmacb4.bit._TYPE0
#define DMACB4_MOD1 dmacb4.bit._MOD1
#define DMACB4_MOD0 dmacb4.bit._MOD0
#define DMACB4_WS1 dmacb4.bit._WS1
#define DMACB4_WS0 dmacb4.bit._WS0
#define DMACB4_SADM dmacb4.bit._SADM
#define DMACB4_DADM dmacb4.bit._DADM
#define DMACB4_DTCR dmacb4.bit._DTCR
#define DMACB4_SADR dmacb4.bit._SADR
#define DMACB4_DADR dmacb4.bit._DADR
#define DMACB4_ERIE dmacb4.bit._ERIE
#define DMACB4_EDIE dmacb4.bit._EDIE
#define DMACB4_DSS2 dmacb4.bit._DSS2
#define DMACB4_DSS1 dmacb4.bit._DSS1
#define DMACB4_DSS0 dmacb4.bit._DSS0
#define DMACB4_SASZ7 dmacb4.bit._SASZ7
#define DMACB4_SASZ6 dmacb4.bit._SASZ6
#define DMACB4_SASZ5 dmacb4.bit._SASZ5
#define DMACB4_SASZ4 dmacb4.bit._SASZ4
#define DMACB4_SASZ3 dmacb4.bit._SASZ3
#define DMACB4_SASZ2 dmacb4.bit._SASZ2
#define DMACB4_SASZ1 dmacb4.bit._SASZ1
#define DMACB4_SASZ0 dmacb4.bit._SASZ0
#define DMACB4_DASZ7 dmacb4.bit._DASZ7
#define DMACB4_DASZ6 dmacb4.bit._DASZ6
#define DMACB4_DASZ5 dmacb4.bit._DASZ5
#define DMACB4_DASZ4 dmacb4.bit._DASZ4
#define DMACB4_DASZ3 dmacb4.bit._DASZ3
#define DMACB4_DASZ2 dmacb4.bit._DASZ2
#define DMACB4_DASZ1 dmacb4.bit._DASZ1
#define DMACB4_DASZ0 dmacb4.bit._DASZ0
#define DMACB4_TYPE dmacb4.bitc._TYPE
#define DMACB4_MOD dmacb4.bitc._MOD
#define DMACB4_WS dmacb4.bitc._WS
#define DMACB4_DSS dmacb4.bitc._DSS
#define DMACB4_SASZ dmacb4.bitc._SASZ
#define DMACB4_DASZ dmacb4.bitc._DASZ
__IO_EXTERN DMACRSTR dmacr;  
#define DMACR dmacr.byte
#define DMACR_DMAE dmacr.bit._DMAE
#define DMACR_PM01 dmacr.bit._PM01
#define DMACR_DMAH3 dmacr.bit._DMAH3
#define DMACR_DMAH2 dmacr.bit._DMAH2
#define DMACR_DMAH1 dmacr.bit._DMAH1
#define DMACR_DMAH0 dmacr.bit._DMAH0
#define DMACR_DMAH dmacr.bitc._DMAH
/* include : INC460_DMAC.INC */
/*-------------------------------------------------------------------*/
/* INC460.DMAC :  Old bit name of DMACx */

/* alias macro definition for DMACx */
#define DMACB0_MD dmacb0.bitc._MOD
#define DMACB0_MD1 dmacb0.bit._MOD1
#define DMACB0_MD0 dmacb0.bit._MOD0
#define DMACB1_MD dmacb1.bitc._MOD
#define DMACB1_MD1 dmacb1.bit._MOD1
#define DMACB1_MD0 dmacb1.bit._MOD0
#define DMACB2_MD dmacb2.bitc._MOD
#define DMACB2_MD1 dmacb2.bit._MOD1
#define DMACB2_MD0 dmacb2.bit._MOD0
#define DMACB3_MD dmacb3.bitc._MOD
#define DMACB3_MD1 dmacb3.bit._MOD1
#define DMACB3_MD0 dmacb3.bit._MOD0
#define DMACB4_MD dmacb4.bitc._MOD
#define DMACB4_MD1 dmacb4.bit._MOD1
#define DMACB4_MD0 dmacb4.bit._MOD0
/*-------------------------------------------------------------------*/
__IO_EXTERN ICS45STR ics45;   /* Input Capture 4-7 */
#define ICS45 ics45.byte
#define ICS45_ICP5 ics45.bit._ICP5
#define ICS45_ICP4 ics45.bit._ICP4
#define ICS45_ICE5 ics45.bit._ICE5
#define ICS45_ICE4 ics45.bit._ICE4
#define ICS45_EG51 ics45.bit._EG51
#define ICS45_EG50 ics45.bit._EG50
#define ICS45_EG41 ics45.bit._EG41
#define ICS45_EG40 ics45.bit._EG40
#define ICS45_EG5 ics45.bitc._EG5
#define ICS45_EG4 ics45.bitc._EG4
__IO_EXTERN ICS67STR ics67;  
#define ICS67 ics67.byte
#define ICS67_ICP7 ics67.bit._ICP7
#define ICS67_ICP6 ics67.bit._ICP6
#define ICS67_ICE7 ics67.bit._ICE7
#define ICS67_ICE6 ics67.bit._ICE6
#define ICS67_EG71 ics67.bit._EG71
#define ICS67_EG70 ics67.bit._EG70
#define ICS67_EG61 ics67.bit._EG61
#define ICS67_EG60 ics67.bit._EG60
#define ICS67_EG7 ics67.bitc._EG7
#define ICS67_EG6 ics67.bitc._EG6
__IO_EXTERN IPCP4STR ipcp4;  
#define IPCP4 ipcp4.word
#define IPCP4_CP15 ipcp4.bit._CP15
#define IPCP4_CP14 ipcp4.bit._CP14
#define IPCP4_CP13 ipcp4.bit._CP13
#define IPCP4_CP12 ipcp4.bit._CP12
#define IPCP4_CP11 ipcp4.bit._CP11
#define IPCP4_CP10 ipcp4.bit._CP10
#define IPCP4_CP9 ipcp4.bit._CP9
#define IPCP4_CP8 ipcp4.bit._CP8
#define IPCP4_CP7 ipcp4.bit._CP7
#define IPCP4_CP6 ipcp4.bit._CP6
#define IPCP4_CP5 ipcp4.bit._CP5
#define IPCP4_CP4 ipcp4.bit._CP4
#define IPCP4_CP3 ipcp4.bit._CP3
#define IPCP4_CP2 ipcp4.bit._CP2
#define IPCP4_CP1 ipcp4.bit._CP1
#define IPCP4_CP0 ipcp4.bit._CP0
__IO_EXTERN IPCP5STR ipcp5;  
#define IPCP5 ipcp5.word
#define IPCP5_CP15 ipcp5.bit._CP15
#define IPCP5_CP14 ipcp5.bit._CP14
#define IPCP5_CP13 ipcp5.bit._CP13
#define IPCP5_CP12 ipcp5.bit._CP12
#define IPCP5_CP11 ipcp5.bit._CP11
#define IPCP5_CP10 ipcp5.bit._CP10
#define IPCP5_CP9 ipcp5.bit._CP9
#define IPCP5_CP8 ipcp5.bit._CP8
#define IPCP5_CP7 ipcp5.bit._CP7
#define IPCP5_CP6 ipcp5.bit._CP6
#define IPCP5_CP5 ipcp5.bit._CP5
#define IPCP5_CP4 ipcp5.bit._CP4
#define IPCP5_CP3 ipcp5.bit._CP3
#define IPCP5_CP2 ipcp5.bit._CP2
#define IPCP5_CP1 ipcp5.bit._CP1
#define IPCP5_CP0 ipcp5.bit._CP0
__IO_EXTERN IPCP6STR ipcp6;  
#define IPCP6 ipcp6.word
#define IPCP6_CP15 ipcp6.bit._CP15
#define IPCP6_CP14 ipcp6.bit._CP14
#define IPCP6_CP13 ipcp6.bit._CP13
#define IPCP6_CP12 ipcp6.bit._CP12
#define IPCP6_CP11 ipcp6.bit._CP11
#define IPCP6_CP10 ipcp6.bit._CP10
#define IPCP6_CP9 ipcp6.bit._CP9
#define IPCP6_CP8 ipcp6.bit._CP8
#define IPCP6_CP7 ipcp6.bit._CP7
#define IPCP6_CP6 ipcp6.bit._CP6
#define IPCP6_CP5 ipcp6.bit._CP5
#define IPCP6_CP4 ipcp6.bit._CP4
#define IPCP6_CP3 ipcp6.bit._CP3
#define IPCP6_CP2 ipcp6.bit._CP2
#define IPCP6_CP1 ipcp6.bit._CP1
#define IPCP6_CP0 ipcp6.bit._CP0
__IO_EXTERN IPCP7STR ipcp7;  
#define IPCP7 ipcp7.word
#define IPCP7_CP15 ipcp7.bit._CP15
#define IPCP7_CP14 ipcp7.bit._CP14
#define IPCP7_CP13 ipcp7.bit._CP13
#define IPCP7_CP12 ipcp7.bit._CP12
#define IPCP7_CP11 ipcp7.bit._CP11
#define IPCP7_CP10 ipcp7.bit._CP10
#define IPCP7_CP9 ipcp7.bit._CP9
#define IPCP7_CP8 ipcp7.bit._CP8
#define IPCP7_CP7 ipcp7.bit._CP7
#define IPCP7_CP6 ipcp7.bit._CP6
#define IPCP7_CP5 ipcp7.bit._CP5
#define IPCP7_CP4 ipcp7.bit._CP4
#define IPCP7_CP3 ipcp7.bit._CP3
#define IPCP7_CP2 ipcp7.bit._CP2
#define IPCP7_CP1 ipcp7.bit._CP1
#define IPCP7_CP0 ipcp7.bit._CP0
__IO_EXTERN TCDT4STR tcdt4;   /* Free Running Timer4 */
#define TCDT4 tcdt4.word
#define TCDT4_T15 tcdt4.bit._T15
#define TCDT4_T14 tcdt4.bit._T14
#define TCDT4_T13 tcdt4.bit._T13
#define TCDT4_T12 tcdt4.bit._T12
#define TCDT4_T11 tcdt4.bit._T11
#define TCDT4_T10 tcdt4.bit._T10
#define TCDT4_T9 tcdt4.bit._T9
#define TCDT4_T8 tcdt4.bit._T8
#define TCDT4_T7 tcdt4.bit._T7
#define TCDT4_T6 tcdt4.bit._T6
#define TCDT4_T5 tcdt4.bit._T5
#define TCDT4_T4 tcdt4.bit._T4
#define TCDT4_T3 tcdt4.bit._T3
#define TCDT4_T2 tcdt4.bit._T2
#define TCDT4_T1 tcdt4.bit._T1
#define TCDT4_T0 tcdt4.bit._T0
__IO_EXTERN TCCS4STR tccs4;  
#define TCCS4 tccs4.byte
#define TCCS4_ECLK tccs4.bit._ECLK
#define TCCS4_IVF tccs4.bit._IVF
#define TCCS4_IVFE tccs4.bit._IVFE
#define TCCS4_STOP tccs4.bit._STOP
#define TCCS4_MODE tccs4.bit._MODE
#define TCCS4_CLR tccs4.bit._CLR
#define TCCS4_CLK1 tccs4.bit._CLK1
#define TCCS4_CLK0 tccs4.bit._CLK0
#define TCCS4_CLK tccs4.bitc._CLK
__IO_EXTERN TCDT5STR tcdt5;   /* Free Running Timer5 */
#define TCDT5 tcdt5.word
#define TCDT5_T15 tcdt5.bit._T15
#define TCDT5_T14 tcdt5.bit._T14
#define TCDT5_T13 tcdt5.bit._T13
#define TCDT5_T12 tcdt5.bit._T12
#define TCDT5_T11 tcdt5.bit._T11
#define TCDT5_T10 tcdt5.bit._T10
#define TCDT5_T9 tcdt5.bit._T9
#define TCDT5_T8 tcdt5.bit._T8
#define TCDT5_T7 tcdt5.bit._T7
#define TCDT5_T6 tcdt5.bit._T6
#define TCDT5_T5 tcdt5.bit._T5
#define TCDT5_T4 tcdt5.bit._T4
#define TCDT5_T3 tcdt5.bit._T3
#define TCDT5_T2 tcdt5.bit._T2
#define TCDT5_T1 tcdt5.bit._T1
#define TCDT5_T0 tcdt5.bit._T0
__IO_EXTERN TCCS5STR tccs5;  
#define TCCS5 tccs5.byte
#define TCCS5_ECLK tccs5.bit._ECLK
#define TCCS5_IVF tccs5.bit._IVF
#define TCCS5_IVFE tccs5.bit._IVFE
#define TCCS5_STOP tccs5.bit._STOP
#define TCCS5_MODE tccs5.bit._MODE
#define TCCS5_CLR tccs5.bit._CLR
#define TCCS5_CLK1 tccs5.bit._CLK1
#define TCCS5_CLK0 tccs5.bit._CLK0
#define TCCS5_CLK tccs5.bitc._CLK
__IO_EXTERN TCDT6STR tcdt6;   /* Free Running Timer6 */
#define TCDT6 tcdt6.word
#define TCDT6_T15 tcdt6.bit._T15
#define TCDT6_T14 tcdt6.bit._T14
#define TCDT6_T13 tcdt6.bit._T13
#define TCDT6_T12 tcdt6.bit._T12
#define TCDT6_T11 tcdt6.bit._T11
#define TCDT6_T10 tcdt6.bit._T10
#define TCDT6_T9 tcdt6.bit._T9
#define TCDT6_T8 tcdt6.bit._T8
#define TCDT6_T7 tcdt6.bit._T7
#define TCDT6_T6 tcdt6.bit._T6
#define TCDT6_T5 tcdt6.bit._T5
#define TCDT6_T4 tcdt6.bit._T4
#define TCDT6_T3 tcdt6.bit._T3
#define TCDT6_T2 tcdt6.bit._T2
#define TCDT6_T1 tcdt6.bit._T1
#define TCDT6_T0 tcdt6.bit._T0
__IO_EXTERN TCCS6STR tccs6;  
#define TCCS6 tccs6.byte
#define TCCS6_ECLK tccs6.bit._ECLK
#define TCCS6_IVF tccs6.bit._IVF
#define TCCS6_IVFE tccs6.bit._IVFE
#define TCCS6_STOP tccs6.bit._STOP
#define TCCS6_MODE tccs6.bit._MODE
#define TCCS6_CLR tccs6.bit._CLR
#define TCCS6_CLK1 tccs6.bit._CLK1
#define TCCS6_CLK0 tccs6.bit._CLK0
#define TCCS6_CLK tccs6.bitc._CLK
__IO_EXTERN TCDT7STR tcdt7;   /* Free Running Timer7 */
#define TCDT7 tcdt7.word
#define TCDT7_T15 tcdt7.bit._T15
#define TCDT7_T14 tcdt7.bit._T14
#define TCDT7_T13 tcdt7.bit._T13
#define TCDT7_T12 tcdt7.bit._T12
#define TCDT7_T11 tcdt7.bit._T11
#define TCDT7_T10 tcdt7.bit._T10
#define TCDT7_T9 tcdt7.bit._T9
#define TCDT7_T8 tcdt7.bit._T8
#define TCDT7_T7 tcdt7.bit._T7
#define TCDT7_T6 tcdt7.bit._T6
#define TCDT7_T5 tcdt7.bit._T5
#define TCDT7_T4 tcdt7.bit._T4
#define TCDT7_T3 tcdt7.bit._T3
#define TCDT7_T2 tcdt7.bit._T2
#define TCDT7_T1 tcdt7.bit._T1
#define TCDT7_T0 tcdt7.bit._T0
__IO_EXTERN TCCS7STR tccs7;  
#define TCCS7 tccs7.byte
#define TCCS7_ECLK tccs7.bit._ECLK
#define TCCS7_IVF tccs7.bit._IVF
#define TCCS7_IVFE tccs7.bit._IVFE
#define TCCS7_STOP tccs7.bit._STOP
#define TCCS7_MODE tccs7.bit._MODE
#define TCCS7_CLR tccs7.bit._CLR
#define TCCS7_CLK1 tccs7.bit._CLK1
#define TCCS7_CLK0 tccs7.bit._CLK0
#define TCCS7_CLK tccs7.bitc._CLK
__IO_EXTERN UDRC10STR udrc10;   /* Up/Down Counter 0-1 */
#define UDRC10 udrc10.word
#define UDRC10_D15 udrc10.bit._D15
#define UDRC10_D14 udrc10.bit._D14
#define UDRC10_D13 udrc10.bit._D13
#define UDRC10_D12 udrc10.bit._D12
#define UDRC10_D11 udrc10.bit._D11
#define UDRC10_D10 udrc10.bit._D10
#define UDRC10_D9 udrc10.bit._D9
#define UDRC10_D8 udrc10.bit._D8
#define UDRC10_D7 udrc10.bit._D7
#define UDRC10_D6 udrc10.bit._D6
#define UDRC10_D5 udrc10.bit._D5
#define UDRC10_D4 udrc10.bit._D4
#define UDRC10_D3 udrc10.bit._D3
#define UDRC10_D2 udrc10.bit._D2
#define UDRC10_D1 udrc10.bit._D1
#define UDRC10_D0 udrc10.bit._D0
__IO_EXTERN UDRC1STR udrc1;  
#define UDRC1 udrc1.byte
#define UDRC1_D7 udrc1.bit._D7
#define UDRC1_D6 udrc1.bit._D6
#define UDRC1_D5 udrc1.bit._D5
#define UDRC1_D4 udrc1.bit._D4
#define UDRC1_D3 udrc1.bit._D3
#define UDRC1_D2 udrc1.bit._D2
#define UDRC1_D1 udrc1.bit._D1
#define UDRC1_D0 udrc1.bit._D0
__IO_EXTERN UDRC0STR udrc0;  
#define UDRC0 udrc0.byte
#define UDRC0_D7 udrc0.bit._D7
#define UDRC0_D6 udrc0.bit._D6
#define UDRC0_D5 udrc0.bit._D5
#define UDRC0_D4 udrc0.bit._D4
#define UDRC0_D3 udrc0.bit._D3
#define UDRC0_D2 udrc0.bit._D2
#define UDRC0_D1 udrc0.bit._D1
#define UDRC0_D0 udrc0.bit._D0
__IO_EXTERN UDCR10STR udcr10;  
#define UDCR10 udcr10.word
#define UDCR10_D15 udcr10.bit._D15
#define UDCR10_D14 udcr10.bit._D14
#define UDCR10_D13 udcr10.bit._D13
#define UDCR10_D12 udcr10.bit._D12
#define UDCR10_D11 udcr10.bit._D11
#define UDCR10_D10 udcr10.bit._D10
#define UDCR10_D9 udcr10.bit._D9
#define UDCR10_D8 udcr10.bit._D8
#define UDCR10_D7 udcr10.bit._D7
#define UDCR10_D6 udcr10.bit._D6
#define UDCR10_D5 udcr10.bit._D5
#define UDCR10_D4 udcr10.bit._D4
#define UDCR10_D3 udcr10.bit._D3
#define UDCR10_D2 udcr10.bit._D2
#define UDCR10_D1 udcr10.bit._D1
#define UDCR10_D0 udcr10.bit._D0
__IO_EXTERN UDCR1STR udcr1;  
#define UDCR1 udcr1.byte
#define UDCR1_D7 udcr1.bit._D7
#define UDCR1_D6 udcr1.bit._D6
#define UDCR1_D5 udcr1.bit._D5
#define UDCR1_D4 udcr1.bit._D4
#define UDCR1_D3 udcr1.bit._D3
#define UDCR1_D2 udcr1.bit._D2
#define UDCR1_D1 udcr1.bit._D1
#define UDCR1_D0 udcr1.bit._D0
__IO_EXTERN UDCR0STR udcr0;  
#define UDCR0 udcr0.byte
#define UDCR0_D7 udcr0.bit._D7
#define UDCR0_D6 udcr0.bit._D6
#define UDCR0_D5 udcr0.bit._D5
#define UDCR0_D4 udcr0.bit._D4
#define UDCR0_D3 udcr0.bit._D3
#define UDCR0_D2 udcr0.bit._D2
#define UDCR0_D1 udcr0.bit._D1
#define UDCR0_D0 udcr0.bit._D0
__IO_EXTERN UDCC0STR udcc0;  
#define UDCC0 udcc0.word
#define UDCC0_M16E udcc0.bit._M16E
#define UDCC0_CDCF udcc0.bit._CDCF
#define UDCC0_CFIE udcc0.bit._CFIE
#define UDCC0_CLKS udcc0.bit._CLKS
#define UDCC0_CMS1 udcc0.bit._CMS1
#define UDCC0_CMS0 udcc0.bit._CMS0
#define UDCC0_CES1 udcc0.bit._CES1
#define UDCC0_CES0 udcc0.bit._CES0
#define UDCC0_CTUT udcc0.bit._CTUT
#define UDCC0_UCRE udcc0.bit._UCRE
#define UDCC0_RLDE udcc0.bit._RLDE
#define UDCC0_UDCLR udcc0.bit._UDCLR
#define UDCC0_CGSC udcc0.bit._CGSC
#define UDCC0_CGE1 udcc0.bit._CGE1
#define UDCC0_CGE0 udcc0.bit._CGE0
#define UDCC0_CMS udcc0.bitc._CMS
#define UDCC0_CES udcc0.bitc._CES
#define UDCC0_CGE udcc0.bitc._CGE
__IO_EXTERN UDCCH0STR udcch0;  
#define UDCCH0 udcch0.byte
#define UDCCH0_M16E udcch0.bit._M16E
#define UDCCH0_CDCF udcch0.bit._CDCF
#define UDCCH0_CFIE udcch0.bit._CFIE
#define UDCCH0_CLKS udcch0.bit._CLKS
#define UDCCH0_CMS1 udcch0.bit._CMS1
#define UDCCH0_CMS0 udcch0.bit._CMS0
#define UDCCH0_CES1 udcch0.bit._CES1
#define UDCCH0_CES0 udcch0.bit._CES0
#define UDCCH0_CMS udcch0.bitc._CMS
#define UDCCH0_CES udcch0.bitc._CES
__IO_EXTERN UDCCL0STR udccl0;  
#define UDCCL0 udccl0.byte
#define UDCCL0_CTUT udccl0.bit._CTUT
#define UDCCL0_UCRE udccl0.bit._UCRE
#define UDCCL0_RLDE udccl0.bit._RLDE
#define UDCCL0_UDCLR udccl0.bit._UDCLR
#define UDCCL0_CGSC udccl0.bit._CGSC
#define UDCCL0_CGE1 udccl0.bit._CGE1
#define UDCCL0_CGE0 udccl0.bit._CGE0
#define UDCCL0_CGE udccl0.bitc._CGE
__IO_EXTERN UDCS0STR udcs0;  
#define UDCS0 udcs0.byte
#define UDCS0_CSTR udcs0.bit._CSTR
#define UDCS0_CITE udcs0.bit._CITE
#define UDCS0_UDIE udcs0.bit._UDIE
#define UDCS0_CMPF udcs0.bit._CMPF
#define UDCS0_OVFF udcs0.bit._OVFF
#define UDCS0_UDFF udcs0.bit._UDFF
#define UDCS0_UDF1 udcs0.bit._UDF1
#define UDCS0_UDF0 udcs0.bit._UDF0
#define UDCS0_UDF udcs0.bitc._UDF
__IO_EXTERN UDCC1STR udcc1;  
#define UDCC1 udcc1.word
#define UDCC1_RESV15 udcc1.bit._RESV15
#define UDCC1_CDCF udcc1.bit._CDCF
#define UDCC1_CFIE udcc1.bit._CFIE
#define UDCC1_CLKS udcc1.bit._CLKS
#define UDCC1_CMS1 udcc1.bit._CMS1
#define UDCC1_CMS0 udcc1.bit._CMS0
#define UDCC1_CES1 udcc1.bit._CES1
#define UDCC1_CES0 udcc1.bit._CES0
#define UDCC1_CTUT udcc1.bit._CTUT
#define UDCC1_UCRE udcc1.bit._UCRE
#define UDCC1_RLDE udcc1.bit._RLDE
#define UDCC1_UDCLR udcc1.bit._UDCLR
#define UDCC1_CGSC udcc1.bit._CGSC
#define UDCC1_CGE1 udcc1.bit._CGE1
#define UDCC1_CGE0 udcc1.bit._CGE0
#define UDCC1_CMS udcc1.bitc._CMS
#define UDCC1_CES udcc1.bitc._CES
#define UDCC1_CGE udcc1.bitc._CGE
__IO_EXTERN UDCCH1STR udcch1;  
#define UDCCH1 udcch1.byte
#define UDCCH1_RESV15 udcch1.bit._RESV15
#define UDCCH1_CDCF udcch1.bit._CDCF
#define UDCCH1_CFIE udcch1.bit._CFIE
#define UDCCH1_CLKS udcch1.bit._CLKS
#define UDCCH1_CMS1 udcch1.bit._CMS1
#define UDCCH1_CMS0 udcch1.bit._CMS0
#define UDCCH1_CES1 udcch1.bit._CES1
#define UDCCH1_CES0 udcch1.bit._CES0
#define UDCCH1_CMS udcch1.bitc._CMS
#define UDCCH1_CES udcch1.bitc._CES
__IO_EXTERN UDCCL1STR udccl1;  
#define UDCCL1 udccl1.byte
#define UDCCL1_CTUT udccl1.bit._CTUT
#define UDCCL1_UCRE udccl1.bit._UCRE
#define UDCCL1_RLDE udccl1.bit._RLDE
#define UDCCL1_UDCLR udccl1.bit._UDCLR
#define UDCCL1_CGSC udccl1.bit._CGSC
#define UDCCL1_CGE1 udccl1.bit._CGE1
#define UDCCL1_CGE0 udccl1.bit._CGE0
#define UDCCL1_CGE udccl1.bitc._CGE
__IO_EXTERN UDCS1STR udcs1;  
#define UDCS1 udcs1.byte
#define UDCS1_CSTR udcs1.bit._CSTR
#define UDCS1_CITE udcs1.bit._CITE
#define UDCS1_UDIE udcs1.bit._UDIE
#define UDCS1_CMPF udcs1.bit._CMPF
#define UDCS1_OVFF udcs1.bit._OVFF
#define UDCS1_UDFF udcs1.bit._UDFF
#define UDCS1_UDF1 udcs1.bit._UDF1
#define UDCS1_UDF0 udcs1.bit._UDF0
#define UDCS1_UDF udcs1.bitc._UDF
__IO_EXTERN UDRC32STR udrc32;   /* Up/Down Counter 2-3 */
#define UDRC32 udrc32.word
#define UDRC32_D15 udrc32.bit._D15
#define UDRC32_D14 udrc32.bit._D14
#define UDRC32_D13 udrc32.bit._D13
#define UDRC32_D12 udrc32.bit._D12
#define UDRC32_D11 udrc32.bit._D11
#define UDRC32_D10 udrc32.bit._D10
#define UDRC32_D9 udrc32.bit._D9
#define UDRC32_D8 udrc32.bit._D8
#define UDRC32_D7 udrc32.bit._D7
#define UDRC32_D6 udrc32.bit._D6
#define UDRC32_D5 udrc32.bit._D5
#define UDRC32_D4 udrc32.bit._D4
#define UDRC32_D3 udrc32.bit._D3
#define UDRC32_D2 udrc32.bit._D2
#define UDRC32_D1 udrc32.bit._D1
#define UDRC32_D0 udrc32.bit._D0
__IO_EXTERN UDRC3STR udrc3;  
#define UDRC3 udrc3.byte
#define UDRC3_D7 udrc3.bit._D7
#define UDRC3_D6 udrc3.bit._D6
#define UDRC3_D5 udrc3.bit._D5
#define UDRC3_D4 udrc3.bit._D4
#define UDRC3_D3 udrc3.bit._D3
#define UDRC3_D2 udrc3.bit._D2
#define UDRC3_D1 udrc3.bit._D1
#define UDRC3_D0 udrc3.bit._D0
__IO_EXTERN UDRC2STR udrc2;  
#define UDRC2 udrc2.byte
#define UDRC2_D7 udrc2.bit._D7
#define UDRC2_D6 udrc2.bit._D6
#define UDRC2_D5 udrc2.bit._D5
#define UDRC2_D4 udrc2.bit._D4
#define UDRC2_D3 udrc2.bit._D3
#define UDRC2_D2 udrc2.bit._D2
#define UDRC2_D1 udrc2.bit._D1
#define UDRC2_D0 udrc2.bit._D0
__IO_EXTERN UDCR32STR udcr32;  
#define UDCR32 udcr32.word
#define UDCR32_D15 udcr32.bit._D15
#define UDCR32_D14 udcr32.bit._D14
#define UDCR32_D13 udcr32.bit._D13
#define UDCR32_D12 udcr32.bit._D12
#define UDCR32_D11 udcr32.bit._D11
#define UDCR32_D10 udcr32.bit._D10
#define UDCR32_D9 udcr32.bit._D9
#define UDCR32_D8 udcr32.bit._D8
#define UDCR32_D7 udcr32.bit._D7
#define UDCR32_D6 udcr32.bit._D6
#define UDCR32_D5 udcr32.bit._D5
#define UDCR32_D4 udcr32.bit._D4
#define UDCR32_D3 udcr32.bit._D3
#define UDCR32_D2 udcr32.bit._D2
#define UDCR32_D1 udcr32.bit._D1
#define UDCR32_D0 udcr32.bit._D0
__IO_EXTERN UDCR3STR udcr3;  
#define UDCR3 udcr3.byte
#define UDCR3_D7 udcr3.bit._D7
#define UDCR3_D6 udcr3.bit._D6
#define UDCR3_D5 udcr3.bit._D5
#define UDCR3_D4 udcr3.bit._D4
#define UDCR3_D3 udcr3.bit._D3
#define UDCR3_D2 udcr3.bit._D2
#define UDCR3_D1 udcr3.bit._D1
#define UDCR3_D0 udcr3.bit._D0
__IO_EXTERN UDCR2STR udcr2;  
#define UDCR2 udcr2.byte
#define UDCR2_D7 udcr2.bit._D7
#define UDCR2_D6 udcr2.bit._D6
#define UDCR2_D5 udcr2.bit._D5
#define UDCR2_D4 udcr2.bit._D4
#define UDCR2_D3 udcr2.bit._D3
#define UDCR2_D2 udcr2.bit._D2
#define UDCR2_D1 udcr2.bit._D1
#define UDCR2_D0 udcr2.bit._D0
__IO_EXTERN UDCC2STR udcc2;  
#define UDCC2 udcc2.word
#define UDCC2_M16E udcc2.bit._M16E
#define UDCC2_CDCF udcc2.bit._CDCF
#define UDCC2_CFIE udcc2.bit._CFIE
#define UDCC2_CLKS udcc2.bit._CLKS
#define UDCC2_CMS1 udcc2.bit._CMS1
#define UDCC2_CMS0 udcc2.bit._CMS0
#define UDCC2_CES1 udcc2.bit._CES1
#define UDCC2_CES0 udcc2.bit._CES0
#define UDCC2_CTUT udcc2.bit._CTUT
#define UDCC2_UCRE udcc2.bit._UCRE
#define UDCC2_RLDE udcc2.bit._RLDE
#define UDCC2_UDCLR udcc2.bit._UDCLR
#define UDCC2_CGSC udcc2.bit._CGSC
#define UDCC2_CGE1 udcc2.bit._CGE1
#define UDCC2_CGE0 udcc2.bit._CGE0
#define UDCC2_CMS udcc2.bitc._CMS
#define UDCC2_CES udcc2.bitc._CES
#define UDCC2_CGE udcc2.bitc._CGE
__IO_EXTERN UDCCH2STR udcch2;  
#define UDCCH2 udcch2.byte
#define UDCCH2_M16E udcch2.bit._M16E
#define UDCCH2_CDCF udcch2.bit._CDCF
#define UDCCH2_CFIE udcch2.bit._CFIE
#define UDCCH2_CLKS udcch2.bit._CLKS
#define UDCCH2_CMS1 udcch2.bit._CMS1
#define UDCCH2_CMS0 udcch2.bit._CMS0
#define UDCCH2_CES1 udcch2.bit._CES1
#define UDCCH2_CES0 udcch2.bit._CES0
#define UDCCH2_CMS udcch2.bitc._CMS
#define UDCCH2_CES udcch2.bitc._CES
__IO_EXTERN UDCCL2STR udccl2;  
#define UDCCL2 udccl2.byte
#define UDCCL2_CTUT udccl2.bit._CTUT
#define UDCCL2_UCRE udccl2.bit._UCRE
#define UDCCL2_RLDE udccl2.bit._RLDE
#define UDCCL2_UDCLR udccl2.bit._UDCLR
#define UDCCL2_CGSC udccl2.bit._CGSC
#define UDCCL2_CGE1 udccl2.bit._CGE1
#define UDCCL2_CGE0 udccl2.bit._CGE0
#define UDCCL2_CGE udccl2.bitc._CGE
__IO_EXTERN UDCS2STR udcs2;  
#define UDCS2 udcs2.byte
#define UDCS2_CSTR udcs2.bit._CSTR
#define UDCS2_CITE udcs2.bit._CITE
#define UDCS2_UDIE udcs2.bit._UDIE
#define UDCS2_CMPF udcs2.bit._CMPF
#define UDCS2_OVFF udcs2.bit._OVFF
#define UDCS2_UDFF udcs2.bit._UDFF
#define UDCS2_UDF1 udcs2.bit._UDF1
#define UDCS2_UDF0 udcs2.bit._UDF0
#define UDCS2_UDF udcs2.bitc._UDF
__IO_EXTERN UDCC3STR udcc3;  
#define UDCC3 udcc3.word
#define UDCC3_RESV15 udcc3.bit._RESV15
#define UDCC3_CDCF udcc3.bit._CDCF
#define UDCC3_CFIE udcc3.bit._CFIE
#define UDCC3_CLKS udcc3.bit._CLKS
#define UDCC3_CMS1 udcc3.bit._CMS1
#define UDCC3_CMS0 udcc3.bit._CMS0
#define UDCC3_CES1 udcc3.bit._CES1
#define UDCC3_CES0 udcc3.bit._CES0
#define UDCC3_CTUT udcc3.bit._CTUT
#define UDCC3_UCRE udcc3.bit._UCRE
#define UDCC3_RLDE udcc3.bit._RLDE
#define UDCC3_UDCLR udcc3.bit._UDCLR
#define UDCC3_CGSC udcc3.bit._CGSC
#define UDCC3_CGE1 udcc3.bit._CGE1
#define UDCC3_CGE0 udcc3.bit._CGE0
#define UDCC3_CMS udcc3.bitc._CMS
#define UDCC3_CES udcc3.bitc._CES
#define UDCC3_CGE udcc3.bitc._CGE
__IO_EXTERN UDCCH3STR udcch3;  
#define UDCCH3 udcch3.byte
#define UDCCH3_RESV15 udcch3.bit._RESV15
#define UDCCH3_CDCF udcch3.bit._CDCF
#define UDCCH3_CFIE udcch3.bit._CFIE
#define UDCCH3_CLKS udcch3.bit._CLKS
#define UDCCH3_CMS1 udcch3.bit._CMS1
#define UDCCH3_CMS0 udcch3.bit._CMS0
#define UDCCH3_CES1 udcch3.bit._CES1
#define UDCCH3_CES0 udcch3.bit._CES0
#define UDCCH3_CMS udcch3.bitc._CMS
#define UDCCH3_CES udcch3.bitc._CES
__IO_EXTERN UDCCL3STR udccl3;  
#define UDCCL3 udccl3.byte
#define UDCCL3_CTUT udccl3.bit._CTUT
#define UDCCL3_UCRE udccl3.bit._UCRE
#define UDCCL3_RLDE udccl3.bit._RLDE
#define UDCCL3_UDCLR udccl3.bit._UDCLR
#define UDCCL3_CGSC udccl3.bit._CGSC
#define UDCCL3_CGE1 udccl3.bit._CGE1
#define UDCCL3_CGE0 udccl3.bit._CGE0
#define UDCCL3_CGE udccl3.bitc._CGE
__IO_EXTERN UDCS3STR udcs3;  
#define UDCS3 udcs3.byte
#define UDCS3_CSTR udcs3.bit._CSTR
#define UDCS3_CITE udcs3.bit._CITE
#define UDCS3_UDIE udcs3.bit._UDIE
#define UDCS3_CMPF udcs3.bit._CMPF
#define UDCS3_OVFF udcs3.bit._OVFF
#define UDCS3_UDFF udcs3.bit._UDFF
#define UDCS3_UDF1 udcs3.bit._UDF1
#define UDCS3_UDF0 udcs3.bit._UDF0
#define UDCS3_UDF udcs3.bitc._UDF
__IO_EXTERN GCN13STR gcn13;   /* PPG Control 12-15 */
#define GCN13 gcn13.word
#define GCN13_TSEL33 gcn13.bit._TSEL33
#define GCN13_TSEL32 gcn13.bit._TSEL32
#define GCN13_TSEL31 gcn13.bit._TSEL31
#define GCN13_TSEL30 gcn13.bit._TSEL30
#define GCN13_TSEL23 gcn13.bit._TSEL23
#define GCN13_TSEL22 gcn13.bit._TSEL22
#define GCN13_TSEL21 gcn13.bit._TSEL21
#define GCN13_TSEL20 gcn13.bit._TSEL20
#define GCN13_TSEL13 gcn13.bit._TSEL13
#define GCN13_TSEL12 gcn13.bit._TSEL12
#define GCN13_TSEL11 gcn13.bit._TSEL11
#define GCN13_TSEL10 gcn13.bit._TSEL10
#define GCN13_TSEL03 gcn13.bit._TSEL03
#define GCN13_TSEL02 gcn13.bit._TSEL02
#define GCN13_TSEL01 gcn13.bit._TSEL01
#define GCN13_TSEL00 gcn13.bit._TSEL00
__IO_EXTERN GCN23STR gcn23;  
#define GCN23 gcn23.byte
#define GCN23_EN3 gcn23.bit._EN3
#define GCN23_EN2 gcn23.bit._EN2
#define GCN23_EN1 gcn23.bit._EN1
#define GCN23_EN0 gcn23.bit._EN0
__IO_EXTERN IO_WORD ptmr12;   /* PPG 12 */
#define PTMR12 ptmr12
__IO_EXTERN IO_WORD pcsr12;  
#define PCSR12 pcsr12
__IO_EXTERN IO_WORD pdut12;  
#define PDUT12 pdut12
__IO_EXTERN PCN12STR pcn12;  
#define PCN12 pcn12.word
#define PCN12_CNTE pcn12.bit._CNTE
#define PCN12_STGR pcn12.bit._STGR
#define PCN12_MDSE pcn12.bit._MDSE
#define PCN12_RTRG pcn12.bit._RTRG
#define PCN12_CKS1 pcn12.bit._CKS1
#define PCN12_CKS0 pcn12.bit._CKS0
#define PCN12_PGMS pcn12.bit._PGMS
#define PCN12_EGS1 pcn12.bit._EGS1
#define PCN12_EGS0 pcn12.bit._EGS0
#define PCN12_IREN pcn12.bit._IREN
#define PCN12_IRQF pcn12.bit._IRQF
#define PCN12_IRS1 pcn12.bit._IRS1
#define PCN12_IRS0 pcn12.bit._IRS0
#define PCN12_OSEL pcn12.bit._OSEL
#define PCN12_CKS pcn12.bitc._CKS
#define PCN12_EGS pcn12.bitc._EGS
#define PCN12_IRS pcn12.bitc._IRS
__IO_EXTERN PCNH12STR pcnh12;  
#define PCNH12 pcnh12.byte
#define PCNH12_CNTE pcnh12.bit._CNTE
#define PCNH12_STGR pcnh12.bit._STGR
#define PCNH12_MDSE pcnh12.bit._MDSE
#define PCNH12_RTRG pcnh12.bit._RTRG
#define PCNH12_CKS1 pcnh12.bit._CKS1
#define PCNH12_CKS0 pcnh12.bit._CKS0
#define PCNH12_PGMS pcnh12.bit._PGMS
#define PCNH12_CKS pcnh12.bitc._CKS
__IO_EXTERN PCNL12STR pcnl12;  
#define PCNL12 pcnl12.byte
#define PCNL12_EGS1 pcnl12.bit._EGS1
#define PCNL12_EGS0 pcnl12.bit._EGS0
#define PCNL12_IREN pcnl12.bit._IREN
#define PCNL12_IRQF pcnl12.bit._IRQF
#define PCNL12_IRS1 pcnl12.bit._IRS1
#define PCNL12_IRS0 pcnl12.bit._IRS0
#define PCNL12_OSEL pcnl12.bit._OSEL
#define PCNL12_EGS pcnl12.bitc._EGS
#define PCNL12_IRS pcnl12.bitc._IRS
__IO_EXTERN IO_WORD ptmr13;   /* PPG 13 */
#define PTMR13 ptmr13
__IO_EXTERN IO_WORD pcsr13;  
#define PCSR13 pcsr13
__IO_EXTERN IO_WORD pdut13;  
#define PDUT13 pdut13
__IO_EXTERN PCN13STR pcn13;  
#define PCN13 pcn13.word
#define PCN13_CNTE pcn13.bit._CNTE
#define PCN13_STGR pcn13.bit._STGR
#define PCN13_MDSE pcn13.bit._MDSE
#define PCN13_RTRG pcn13.bit._RTRG
#define PCN13_CKS1 pcn13.bit._CKS1
#define PCN13_CKS0 pcn13.bit._CKS0
#define PCN13_PGMS pcn13.bit._PGMS
#define PCN13_EGS1 pcn13.bit._EGS1
#define PCN13_EGS0 pcn13.bit._EGS0
#define PCN13_IREN pcn13.bit._IREN
#define PCN13_IRQF pcn13.bit._IRQF
#define PCN13_IRS1 pcn13.bit._IRS1
#define PCN13_IRS0 pcn13.bit._IRS0
#define PCN13_OSEL pcn13.bit._OSEL
#define PCN13_CKS pcn13.bitc._CKS
#define PCN13_EGS pcn13.bitc._EGS
#define PCN13_IRS pcn13.bitc._IRS
__IO_EXTERN PCNH13STR pcnh13;  
#define PCNH13 pcnh13.byte
#define PCNH13_CNTE pcnh13.bit._CNTE
#define PCNH13_STGR pcnh13.bit._STGR
#define PCNH13_MDSE pcnh13.bit._MDSE
#define PCNH13_RTRG pcnh13.bit._RTRG
#define PCNH13_CKS1 pcnh13.bit._CKS1
#define PCNH13_CKS0 pcnh13.bit._CKS0
#define PCNH13_PGMS pcnh13.bit._PGMS
#define PCNH13_CKS pcnh13.bitc._CKS
__IO_EXTERN PCNL13STR pcnl13;  
#define PCNL13 pcnl13.byte
#define PCNL13_EGS1 pcnl13.bit._EGS1
#define PCNL13_EGS0 pcnl13.bit._EGS0
#define PCNL13_IREN pcnl13.bit._IREN
#define PCNL13_IRQF pcnl13.bit._IRQF
#define PCNL13_IRS1 pcnl13.bit._IRS1
#define PCNL13_IRS0 pcnl13.bit._IRS0
#define PCNL13_OSEL pcnl13.bit._OSEL
#define PCNL13_EGS pcnl13.bitc._EGS
#define PCNL13_IRS pcnl13.bitc._IRS
__IO_EXTERN IO_WORD ptmr14;   /* PPG 14 */
#define PTMR14 ptmr14
__IO_EXTERN IO_WORD pcsr14;  
#define PCSR14 pcsr14
__IO_EXTERN IO_WORD pdut14;  
#define PDUT14 pdut14
__IO_EXTERN PCN14STR pcn14;  
#define PCN14 pcn14.word
#define PCN14_CNTE pcn14.bit._CNTE
#define PCN14_STGR pcn14.bit._STGR
#define PCN14_MDSE pcn14.bit._MDSE
#define PCN14_RTRG pcn14.bit._RTRG
#define PCN14_CKS1 pcn14.bit._CKS1
#define PCN14_CKS0 pcn14.bit._CKS0
#define PCN14_PGMS pcn14.bit._PGMS
#define PCN14_EGS1 pcn14.bit._EGS1
#define PCN14_EGS0 pcn14.bit._EGS0
#define PCN14_IREN pcn14.bit._IREN
#define PCN14_IRQF pcn14.bit._IRQF
#define PCN14_IRS1 pcn14.bit._IRS1
#define PCN14_IRS0 pcn14.bit._IRS0
#define PCN14_OSEL pcn14.bit._OSEL
#define PCN14_CKS pcn14.bitc._CKS
#define PCN14_EGS pcn14.bitc._EGS
#define PCN14_IRS pcn14.bitc._IRS
__IO_EXTERN PCNH14STR pcnh14;  
#define PCNH14 pcnh14.byte
#define PCNH14_CNTE pcnh14.bit._CNTE
#define PCNH14_STGR pcnh14.bit._STGR
#define PCNH14_MDSE pcnh14.bit._MDSE
#define PCNH14_RTRG pcnh14.bit._RTRG
#define PCNH14_CKS1 pcnh14.bit._CKS1
#define PCNH14_CKS0 pcnh14.bit._CKS0
#define PCNH14_PGMS pcnh14.bit._PGMS
#define PCNH14_CKS pcnh14.bitc._CKS
__IO_EXTERN PCNL14STR pcnl14;  
#define PCNL14 pcnl14.byte
#define PCNL14_EGS1 pcnl14.bit._EGS1
#define PCNL14_EGS0 pcnl14.bit._EGS0
#define PCNL14_IREN pcnl14.bit._IREN
#define PCNL14_IRQF pcnl14.bit._IRQF
#define PCNL14_IRS1 pcnl14.bit._IRS1
#define PCNL14_IRS0 pcnl14.bit._IRS0
#define PCNL14_OSEL pcnl14.bit._OSEL
#define PCNL14_EGS pcnl14.bitc._EGS
#define PCNL14_IRS pcnl14.bitc._IRS
__IO_EXTERN IO_WORD ptmr15;   /* PPG 15 */
#define PTMR15 ptmr15
__IO_EXTERN IO_WORD pcsr15;  
#define PCSR15 pcsr15
__IO_EXTERN IO_WORD pdut15;  
#define PDUT15 pdut15
__IO_EXTERN PCN15STR pcn15;  
#define PCN15 pcn15.word
#define PCN15_CNTE pcn15.bit._CNTE
#define PCN15_STGR pcn15.bit._STGR
#define PCN15_MDSE pcn15.bit._MDSE
#define PCN15_RTRG pcn15.bit._RTRG
#define PCN15_CKS1 pcn15.bit._CKS1
#define PCN15_CKS0 pcn15.bit._CKS0
#define PCN15_PGMS pcn15.bit._PGMS
#define PCN15_EGS1 pcn15.bit._EGS1
#define PCN15_EGS0 pcn15.bit._EGS0
#define PCN15_IREN pcn15.bit._IREN
#define PCN15_IRQF pcn15.bit._IRQF
#define PCN15_IRS1 pcn15.bit._IRS1
#define PCN15_IRS0 pcn15.bit._IRS0
#define PCN15_OSEL pcn15.bit._OSEL
#define PCN15_CKS pcn15.bitc._CKS
#define PCN15_EGS pcn15.bitc._EGS
#define PCN15_IRS pcn15.bitc._IRS
__IO_EXTERN PCNH15STR pcnh15;  
#define PCNH15 pcnh15.byte
#define PCNH15_CNTE pcnh15.bit._CNTE
#define PCNH15_STGR pcnh15.bit._STGR
#define PCNH15_MDSE pcnh15.bit._MDSE
#define PCNH15_RTRG pcnh15.bit._RTRG
#define PCNH15_CKS1 pcnh15.bit._CKS1
#define PCNH15_CKS0 pcnh15.bit._CKS0
#define PCNH15_PGMS pcnh15.bit._PGMS
#define PCNH15_CKS pcnh15.bitc._CKS
__IO_EXTERN PCNL15STR pcnl15;  
#define PCNL15 pcnl15.byte
#define PCNL15_EGS1 pcnl15.bit._EGS1
#define PCNL15_EGS0 pcnl15.bit._EGS0
#define PCNL15_IREN pcnl15.bit._IREN
#define PCNL15_IRQF pcnl15.bit._IRQF
#define PCNL15_IRS1 pcnl15.bit._IRS1
#define PCNL15_IRS0 pcnl15.bit._IRS0
#define PCNL15_OSEL pcnl15.bit._OSEL
#define PCNL15_EGS pcnl15.bitc._EGS
#define PCNL15_IRS pcnl15.bitc._IRS
__IO_EXTERN IBCR2STR ibcr2;   /* I2C 2 */
#define IBCR2 ibcr2.byte
#define IBCR2_BER ibcr2.bit._BER
#define IBCR2_BEIE ibcr2.bit._BEIE
#define IBCR2_SCC ibcr2.bit._SCC
#define IBCR2_MSS ibcr2.bit._MSS
#define IBCR2_ACK ibcr2.bit._ACK
#define IBCR2_GCAA ibcr2.bit._GCAA
#define IBCR2_INTE ibcr2.bit._INTE
#define IBCR2_INT ibcr2.bit._INT
__IO_EXTERN IBSR2STR ibsr2;  
#define IBSR2 ibsr2.byte
#define IBSR2_BB ibsr2.bit._BB
#define IBSR2_RSC ibsr2.bit._RSC
#define IBSR2_AL ibsr2.bit._AL
#define IBSR2_LRB ibsr2.bit._LRB
#define IBSR2_TRX ibsr2.bit._TRX
#define IBSR2_AAS ibsr2.bit._AAS
#define IBSR2_GCA ibsr2.bit._GCA
#define IBSR2_ADT ibsr2.bit._ADT
__IO_EXTERN ITBA2STR itba2;  
#define ITBA2 itba2.word
#define ITBA2_TA9 itba2.bit._TA9
#define ITBA2_TA8 itba2.bit._TA8
#define ITBA2_TA7 itba2.bit._TA7
#define ITBA2_TA6 itba2.bit._TA6
#define ITBA2_TA5 itba2.bit._TA5
#define ITBA2_TA4 itba2.bit._TA4
#define ITBA2_TA3 itba2.bit._TA3
#define ITBA2_TA2 itba2.bit._TA2
#define ITBA2_TA1 itba2.bit._TA1
#define ITBA2_TA0 itba2.bit._TA0
__IO_EXTERN ITBAH2STR itbah2;  
#define ITBAH2 itbah2.byte
#define ITBAH2_TA9 itbah2.bit._TA9
#define ITBAH2_TA8 itbah2.bit._TA8
__IO_EXTERN ITBAL2STR itbal2;  
#define ITBAL2 itbal2.byte
#define ITBAL2_TA7 itbal2.bit._TA7
#define ITBAL2_TA6 itbal2.bit._TA6
#define ITBAL2_TA5 itbal2.bit._TA5
#define ITBAL2_TA4 itbal2.bit._TA4
#define ITBAL2_TA3 itbal2.bit._TA3
#define ITBAL2_TA2 itbal2.bit._TA2
#define ITBAL2_TA1 itbal2.bit._TA1
#define ITBAL2_TA0 itbal2.bit._TA0
__IO_EXTERN ITMK2STR itmk2;  
#define ITMK2 itmk2.word
#define ITMK2_ENTB itmk2.bit._ENTB
#define ITMK2_RAL itmk2.bit._RAL
#define ITMK2_TM9 itmk2.bit._TM9
#define ITMK2_TM8 itmk2.bit._TM8
#define ITMK2_TM7 itmk2.bit._TM7
#define ITMK2_TM6 itmk2.bit._TM6
#define ITMK2_TM5 itmk2.bit._TM5
#define ITMK2_TM4 itmk2.bit._TM4
#define ITMK2_TM3 itmk2.bit._TM3
#define ITMK2_TM2 itmk2.bit._TM2
#define ITMK2_TM1 itmk2.bit._TM1
#define ITMK2_TM0 itmk2.bit._TM0
__IO_EXTERN ITMKH2STR itmkh2;  
#define ITMKH2 itmkh2.byte
#define ITMKH2_ENTB itmkh2.bit._ENTB
#define ITMKH2_RAL itmkh2.bit._RAL
#define ITMKH2_TM9 itmkh2.bit._TM9
#define ITMKH2_TM8 itmkh2.bit._TM8
__IO_EXTERN ITMKL2STR itmkl2;  
#define ITMKL2 itmkl2.byte
#define ITMKL2_TM7 itmkl2.bit._TM7
#define ITMKL2_TM6 itmkl2.bit._TM6
#define ITMKL2_TM5 itmkl2.bit._TM5
#define ITMKL2_TM4 itmkl2.bit._TM4
#define ITMKL2_TM3 itmkl2.bit._TM3
#define ITMKL2_TM2 itmkl2.bit._TM2
#define ITMKL2_TM1 itmkl2.bit._TM1
#define ITMKL2_TM0 itmkl2.bit._TM0
__IO_EXTERN ISMK2STR ismk2;  
#define ISMK2 ismk2.byte
#define ISMK2_ENSB ismk2.bit._ENSB
#define ISMK2_SM6 ismk2.bit._SM6
#define ISMK2_SM5 ismk2.bit._SM5
#define ISMK2_SM4 ismk2.bit._SM4
#define ISMK2_SM3 ismk2.bit._SM3
#define ISMK2_SM2 ismk2.bit._SM2
#define ISMK2_SM1 ismk2.bit._SM1
#define ISMK2_SM0 ismk2.bit._SM0
__IO_EXTERN ISBA2STR isba2;  
#define ISBA2 isba2.byte
#define ISBA2_SA6 isba2.bit._SA6
#define ISBA2_SA5 isba2.bit._SA5
#define ISBA2_SA4 isba2.bit._SA4
#define ISBA2_SA3 isba2.bit._SA3
#define ISBA2_SA2 isba2.bit._SA2
#define ISBA2_SA1 isba2.bit._SA1
#define ISBA2_SA0 isba2.bit._SA0
__IO_EXTERN IDAR2STR idar2;  
#define IDAR2 idar2.byte
#define IDAR2_D7 idar2.bit._D7
#define IDAR2_D6 idar2.bit._D6
#define IDAR2_D5 idar2.bit._D5
#define IDAR2_D4 idar2.bit._D4
#define IDAR2_D3 idar2.bit._D3
#define IDAR2_D2 idar2.bit._D2
#define IDAR2_D1 idar2.bit._D1
#define IDAR2_D0 idar2.bit._D0
__IO_EXTERN ICCR2STR iccr2;  
#define ICCR2 iccr2.byte
#define ICCR2_NSF iccr2.bit._NSF
#define ICCR2_EN iccr2.bit._EN
#define ICCR2_CS4 iccr2.bit._CS4
#define ICCR2_CS3 iccr2.bit._CS3
#define ICCR2_CS2 iccr2.bit._CS2
#define ICCR2_CS1 iccr2.bit._CS1
#define ICCR2_CS0 iccr2.bit._CS0
#define ICCR2_CS iccr2.bitc._CS
__IO_EXTERN IBCR3STR ibcr3;   /* I2C 3 */
#define IBCR3 ibcr3.byte
#define IBCR3_BER ibcr3.bit._BER
#define IBCR3_BEIE ibcr3.bit._BEIE
#define IBCR3_SCC ibcr3.bit._SCC
#define IBCR3_MSS ibcr3.bit._MSS
#define IBCR3_ACK ibcr3.bit._ACK
#define IBCR3_GCAA ibcr3.bit._GCAA
#define IBCR3_INTE ibcr3.bit._INTE
#define IBCR3_INT ibcr3.bit._INT
__IO_EXTERN IBSR3STR ibsr3;  
#define IBSR3 ibsr3.byte
#define IBSR3_BB ibsr3.bit._BB
#define IBSR3_RSC ibsr3.bit._RSC
#define IBSR3_AL ibsr3.bit._AL
#define IBSR3_LRB ibsr3.bit._LRB
#define IBSR3_TRX ibsr3.bit._TRX
#define IBSR3_AAS ibsr3.bit._AAS
#define IBSR3_GCA ibsr3.bit._GCA
#define IBSR3_ADT ibsr3.bit._ADT
__IO_EXTERN ITBA3STR itba3;  
#define ITBA3 itba3.word
#define ITBA3_TA9 itba3.bit._TA9
#define ITBA3_TA8 itba3.bit._TA8
#define ITBA3_TA7 itba3.bit._TA7
#define ITBA3_TA6 itba3.bit._TA6
#define ITBA3_TA5 itba3.bit._TA5
#define ITBA3_TA4 itba3.bit._TA4
#define ITBA3_TA3 itba3.bit._TA3
#define ITBA3_TA2 itba3.bit._TA2
#define ITBA3_TA1 itba3.bit._TA1
#define ITBA3_TA0 itba3.bit._TA0
__IO_EXTERN ITBAH3STR itbah3;  
#define ITBAH3 itbah3.byte
#define ITBAH3_TA9 itbah3.bit._TA9
#define ITBAH3_TA8 itbah3.bit._TA8
__IO_EXTERN ITBAL3STR itbal3;  
#define ITBAL3 itbal3.byte
#define ITBAL3_TA7 itbal3.bit._TA7
#define ITBAL3_TA6 itbal3.bit._TA6
#define ITBAL3_TA5 itbal3.bit._TA5
#define ITBAL3_TA4 itbal3.bit._TA4
#define ITBAL3_TA3 itbal3.bit._TA3
#define ITBAL3_TA2 itbal3.bit._TA2
#define ITBAL3_TA1 itbal3.bit._TA1
#define ITBAL3_TA0 itbal3.bit._TA0
__IO_EXTERN ITMK3STR itmk3;  
#define ITMK3 itmk3.word
#define ITMK3_ENTB itmk3.bit._ENTB
#define ITMK3_RAL itmk3.bit._RAL
#define ITMK3_TM9 itmk3.bit._TM9
#define ITMK3_TM8 itmk3.bit._TM8
#define ITMK3_TM7 itmk3.bit._TM7
#define ITMK3_TM6 itmk3.bit._TM6
#define ITMK3_TM5 itmk3.bit._TM5
#define ITMK3_TM4 itmk3.bit._TM4
#define ITMK3_TM3 itmk3.bit._TM3
#define ITMK3_TM2 itmk3.bit._TM2
#define ITMK3_TM1 itmk3.bit._TM1
#define ITMK3_TM0 itmk3.bit._TM0
__IO_EXTERN ITMKH3STR itmkh3;  
#define ITMKH3 itmkh3.byte
#define ITMKH3_ENTB itmkh3.bit._ENTB
#define ITMKH3_RAL itmkh3.bit._RAL
#define ITMKH3_TM9 itmkh3.bit._TM9
#define ITMKH3_TM8 itmkh3.bit._TM8
__IO_EXTERN ITMKL3STR itmkl3;  
#define ITMKL3 itmkl3.byte
#define ITMKL3_TM7 itmkl3.bit._TM7
#define ITMKL3_TM6 itmkl3.bit._TM6
#define ITMKL3_TM5 itmkl3.bit._TM5
#define ITMKL3_TM4 itmkl3.bit._TM4
#define ITMKL3_TM3 itmkl3.bit._TM3
#define ITMKL3_TM2 itmkl3.bit._TM2
#define ITMKL3_TM1 itmkl3.bit._TM1
#define ITMKL3_TM0 itmkl3.bit._TM0
__IO_EXTERN ISMK3STR ismk3;  
#define ISMK3 ismk3.byte
#define ISMK3_ENSB ismk3.bit._ENSB
#define ISMK3_SM6 ismk3.bit._SM6
#define ISMK3_SM5 ismk3.bit._SM5
#define ISMK3_SM4 ismk3.bit._SM4
#define ISMK3_SM3 ismk3.bit._SM3
#define ISMK3_SM2 ismk3.bit._SM2
#define ISMK3_SM1 ismk3.bit._SM1
#define ISMK3_SM0 ismk3.bit._SM0
__IO_EXTERN ISBA3STR isba3;  
#define ISBA3 isba3.byte
#define ISBA3_SA6 isba3.bit._SA6
#define ISBA3_SA5 isba3.bit._SA5
#define ISBA3_SA4 isba3.bit._SA4
#define ISBA3_SA3 isba3.bit._SA3
#define ISBA3_SA2 isba3.bit._SA2
#define ISBA3_SA1 isba3.bit._SA1
#define ISBA3_SA0 isba3.bit._SA0
__IO_EXTERN IDAR3STR idar3;  
#define IDAR3 idar3.byte
#define IDAR3_D7 idar3.bit._D7
#define IDAR3_D6 idar3.bit._D6
#define IDAR3_D5 idar3.bit._D5
#define IDAR3_D4 idar3.bit._D4
#define IDAR3_D3 idar3.bit._D3
#define IDAR3_D2 idar3.bit._D2
#define IDAR3_D1 idar3.bit._D1
#define IDAR3_D0 idar3.bit._D0
__IO_EXTERN ICCR3STR iccr3;  
#define ICCR3 iccr3.byte
#define ICCR3_NSF iccr3.bit._NSF
#define ICCR3_EN iccr3.bit._EN
#define ICCR3_CS4 iccr3.bit._CS4
#define ICCR3_CS3 iccr3.bit._CS3
#define ICCR3_CS2 iccr3.bit._CS2
#define ICCR3_CS1 iccr3.bit._CS1
#define ICCR3_CS0 iccr3.bit._CS0
#define ICCR3_CS iccr3.bitc._CS
__IO_EXTERN ROMSSTR roms;   /* ROM Select Register */
#define ROMS roms.word
#define ROMS_D15 roms.bit._D15
#define ROMS_D14 roms.bit._D14
#define ROMS_D13 roms.bit._D13
#define ROMS_D12 roms.bit._D12
#define ROMS_D11 roms.bit._D11
#define ROMS_D10 roms.bit._D10
#define ROMS_D9 roms.bit._D9
#define ROMS_D8 roms.bit._D8
#define ROMS_D7 roms.bit._D7
#define ROMS_D6 roms.bit._D6
#define ROMS_D5 roms.bit._D5
#define ROMS_D4 roms.bit._D4
#define ROMS_D3 roms.bit._D3
#define ROMS_D2 roms.bit._D2
#define ROMS_D1 roms.bit._D1
#define ROMS_D0 roms.bit._D0
__IO_EXTERN IO_LWORD bsd0;   /* Bit Search Module */
#define BSD0 bsd0
__IO_EXTERN IO_LWORD bsd1;  
#define BSD1 bsd1
__IO_EXTERN IO_LWORD bsdc;  
#define BSDC bsdc
__IO_EXTERN IO_LWORD bsrr;  
#define BSRR bsrr
__IO_EXTERN ICR00STR icr00;   /* Interrupt Control Unit */
#define ICR00 icr00.byte
#define ICR00_ICR4 icr00.bit._ICR4
#define ICR00_ICR3 icr00.bit._ICR3
#define ICR00_ICR2 icr00.bit._ICR2
#define ICR00_ICR1 icr00.bit._ICR1
#define ICR00_ICR0 icr00.bit._ICR0
__IO_EXTERN ICR01STR icr01;  
#define ICR01 icr01.byte
#define ICR01_ICR4 icr01.bit._ICR4
#define ICR01_ICR3 icr01.bit._ICR3
#define ICR01_ICR2 icr01.bit._ICR2
#define ICR01_ICR1 icr01.bit._ICR1
#define ICR01_ICR0 icr01.bit._ICR0
__IO_EXTERN ICR02STR icr02;  
#define ICR02 icr02.byte
#define ICR02_ICR4 icr02.bit._ICR4
#define ICR02_ICR3 icr02.bit._ICR3
#define ICR02_ICR2 icr02.bit._ICR2
#define ICR02_ICR1 icr02.bit._ICR1
#define ICR02_ICR0 icr02.bit._ICR0
__IO_EXTERN ICR03STR icr03;  
#define ICR03 icr03.byte
#define ICR03_ICR4 icr03.bit._ICR4
#define ICR03_ICR3 icr03.bit._ICR3
#define ICR03_ICR2 icr03.bit._ICR2
#define ICR03_ICR1 icr03.bit._ICR1
#define ICR03_ICR0 icr03.bit._ICR0
__IO_EXTERN ICR04STR icr04;  
#define ICR04 icr04.byte
#define ICR04_ICR4 icr04.bit._ICR4
#define ICR04_ICR3 icr04.bit._ICR3
#define ICR04_ICR2 icr04.bit._ICR2
#define ICR04_ICR1 icr04.bit._ICR1
#define ICR04_ICR0 icr04.bit._ICR0
__IO_EXTERN ICR05STR icr05;  
#define ICR05 icr05.byte
#define ICR05_ICR4 icr05.bit._ICR4
#define ICR05_ICR3 icr05.bit._ICR3
#define ICR05_ICR2 icr05.bit._ICR2
#define ICR05_ICR1 icr05.bit._ICR1
#define ICR05_ICR0 icr05.bit._ICR0
__IO_EXTERN ICR06STR icr06;  
#define ICR06 icr06.byte
#define ICR06_ICR4 icr06.bit._ICR4
#define ICR06_ICR3 icr06.bit._ICR3
#define ICR06_ICR2 icr06.bit._ICR2
#define ICR06_ICR1 icr06.bit._ICR1
#define ICR06_ICR0 icr06.bit._ICR0
__IO_EXTERN ICR07STR icr07;  
#define ICR07 icr07.byte
#define ICR07_ICR4 icr07.bit._ICR4
#define ICR07_ICR3 icr07.bit._ICR3
#define ICR07_ICR2 icr07.bit._ICR2
#define ICR07_ICR1 icr07.bit._ICR1
#define ICR07_ICR0 icr07.bit._ICR0
__IO_EXTERN ICR08STR icr08;  
#define ICR08 icr08.byte
#define ICR08_ICR4 icr08.bit._ICR4
#define ICR08_ICR3 icr08.bit._ICR3
#define ICR08_ICR2 icr08.bit._ICR2
#define ICR08_ICR1 icr08.bit._ICR1
#define ICR08_ICR0 icr08.bit._ICR0
__IO_EXTERN ICR09STR icr09;  
#define ICR09 icr09.byte
#define ICR09_ICR4 icr09.bit._ICR4
#define ICR09_ICR3 icr09.bit._ICR3
#define ICR09_ICR2 icr09.bit._ICR2
#define ICR09_ICR1 icr09.bit._ICR1
#define ICR09_ICR0 icr09.bit._ICR0
__IO_EXTERN ICR10STR icr10;  
#define ICR10 icr10.byte
#define ICR10_ICR4 icr10.bit._ICR4
#define ICR10_ICR3 icr10.bit._ICR3
#define ICR10_ICR2 icr10.bit._ICR2
#define ICR10_ICR1 icr10.bit._ICR1
#define ICR10_ICR0 icr10.bit._ICR0
__IO_EXTERN ICR11STR icr11;  
#define ICR11 icr11.byte
#define ICR11_ICR4 icr11.bit._ICR4
#define ICR11_ICR3 icr11.bit._ICR3
#define ICR11_ICR2 icr11.bit._ICR2
#define ICR11_ICR1 icr11.bit._ICR1
#define ICR11_ICR0 icr11.bit._ICR0
__IO_EXTERN ICR12STR icr12;  
#define ICR12 icr12.byte
#define ICR12_ICR4 icr12.bit._ICR4
#define ICR12_ICR3 icr12.bit._ICR3
#define ICR12_ICR2 icr12.bit._ICR2
#define ICR12_ICR1 icr12.bit._ICR1
#define ICR12_ICR0 icr12.bit._ICR0
__IO_EXTERN ICR13STR icr13;  
#define ICR13 icr13.byte
#define ICR13_ICR4 icr13.bit._ICR4
#define ICR13_ICR3 icr13.bit._ICR3
#define ICR13_ICR2 icr13.bit._ICR2
#define ICR13_ICR1 icr13.bit._ICR1
#define ICR13_ICR0 icr13.bit._ICR0
__IO_EXTERN ICR14STR icr14;  
#define ICR14 icr14.byte
#define ICR14_ICR4 icr14.bit._ICR4
#define ICR14_ICR3 icr14.bit._ICR3
#define ICR14_ICR2 icr14.bit._ICR2
#define ICR14_ICR1 icr14.bit._ICR1
#define ICR14_ICR0 icr14.bit._ICR0
__IO_EXTERN ICR15STR icr15;  
#define ICR15 icr15.byte
#define ICR15_ICR4 icr15.bit._ICR4
#define ICR15_ICR3 icr15.bit._ICR3
#define ICR15_ICR2 icr15.bit._ICR2
#define ICR15_ICR1 icr15.bit._ICR1
#define ICR15_ICR0 icr15.bit._ICR0
__IO_EXTERN ICR16STR icr16;  
#define ICR16 icr16.byte
#define ICR16_ICR4 icr16.bit._ICR4
#define ICR16_ICR3 icr16.bit._ICR3
#define ICR16_ICR2 icr16.bit._ICR2
#define ICR16_ICR1 icr16.bit._ICR1
#define ICR16_ICR0 icr16.bit._ICR0
__IO_EXTERN ICR17STR icr17;  
#define ICR17 icr17.byte
#define ICR17_ICR4 icr17.bit._ICR4
#define ICR17_ICR3 icr17.bit._ICR3
#define ICR17_ICR2 icr17.bit._ICR2
#define ICR17_ICR1 icr17.bit._ICR1
#define ICR17_ICR0 icr17.bit._ICR0
__IO_EXTERN ICR18STR icr18;  
#define ICR18 icr18.byte
#define ICR18_ICR4 icr18.bit._ICR4
#define ICR18_ICR3 icr18.bit._ICR3
#define ICR18_ICR2 icr18.bit._ICR2
#define ICR18_ICR1 icr18.bit._ICR1
#define ICR18_ICR0 icr18.bit._ICR0
__IO_EXTERN ICR19STR icr19;  
#define ICR19 icr19.byte
#define ICR19_ICR4 icr19.bit._ICR4
#define ICR19_ICR3 icr19.bit._ICR3
#define ICR19_ICR2 icr19.bit._ICR2
#define ICR19_ICR1 icr19.bit._ICR1
#define ICR19_ICR0 icr19.bit._ICR0
__IO_EXTERN ICR20STR icr20;  
#define ICR20 icr20.byte
#define ICR20_ICR4 icr20.bit._ICR4
#define ICR20_ICR3 icr20.bit._ICR3
#define ICR20_ICR2 icr20.bit._ICR2
#define ICR20_ICR1 icr20.bit._ICR1
#define ICR20_ICR0 icr20.bit._ICR0
__IO_EXTERN ICR21STR icr21;  
#define ICR21 icr21.byte
#define ICR21_ICR4 icr21.bit._ICR4
#define ICR21_ICR3 icr21.bit._ICR3
#define ICR21_ICR2 icr21.bit._ICR2
#define ICR21_ICR1 icr21.bit._ICR1
#define ICR21_ICR0 icr21.bit._ICR0
__IO_EXTERN ICR22STR icr22;  
#define ICR22 icr22.byte
#define ICR22_ICR4 icr22.bit._ICR4
#define ICR22_ICR3 icr22.bit._ICR3
#define ICR22_ICR2 icr22.bit._ICR2
#define ICR22_ICR1 icr22.bit._ICR1
#define ICR22_ICR0 icr22.bit._ICR0
__IO_EXTERN ICR23STR icr23;  
#define ICR23 icr23.byte
#define ICR23_ICR4 icr23.bit._ICR4
#define ICR23_ICR3 icr23.bit._ICR3
#define ICR23_ICR2 icr23.bit._ICR2
#define ICR23_ICR1 icr23.bit._ICR1
#define ICR23_ICR0 icr23.bit._ICR0
__IO_EXTERN ICR24STR icr24;  
#define ICR24 icr24.byte
#define ICR24_ICR4 icr24.bit._ICR4
#define ICR24_ICR3 icr24.bit._ICR3
#define ICR24_ICR2 icr24.bit._ICR2
#define ICR24_ICR1 icr24.bit._ICR1
#define ICR24_ICR0 icr24.bit._ICR0
__IO_EXTERN ICR25STR icr25;  
#define ICR25 icr25.byte
#define ICR25_ICR4 icr25.bit._ICR4
#define ICR25_ICR3 icr25.bit._ICR3
#define ICR25_ICR2 icr25.bit._ICR2
#define ICR25_ICR1 icr25.bit._ICR1
#define ICR25_ICR0 icr25.bit._ICR0
__IO_EXTERN ICR26STR icr26;  
#define ICR26 icr26.byte
#define ICR26_ICR4 icr26.bit._ICR4
#define ICR26_ICR3 icr26.bit._ICR3
#define ICR26_ICR2 icr26.bit._ICR2
#define ICR26_ICR1 icr26.bit._ICR1
#define ICR26_ICR0 icr26.bit._ICR0
__IO_EXTERN ICR27STR icr27;  
#define ICR27 icr27.byte
#define ICR27_ICR4 icr27.bit._ICR4
#define ICR27_ICR3 icr27.bit._ICR3
#define ICR27_ICR2 icr27.bit._ICR2
#define ICR27_ICR1 icr27.bit._ICR1
#define ICR27_ICR0 icr27.bit._ICR0
__IO_EXTERN ICR28STR icr28;  
#define ICR28 icr28.byte
#define ICR28_ICR4 icr28.bit._ICR4
#define ICR28_ICR3 icr28.bit._ICR3
#define ICR28_ICR2 icr28.bit._ICR2
#define ICR28_ICR1 icr28.bit._ICR1
#define ICR28_ICR0 icr28.bit._ICR0
__IO_EXTERN ICR29STR icr29;  
#define ICR29 icr29.byte
#define ICR29_ICR4 icr29.bit._ICR4
#define ICR29_ICR3 icr29.bit._ICR3
#define ICR29_ICR2 icr29.bit._ICR2
#define ICR29_ICR1 icr29.bit._ICR1
#define ICR29_ICR0 icr29.bit._ICR0
__IO_EXTERN ICR30STR icr30;  
#define ICR30 icr30.byte
#define ICR30_ICR4 icr30.bit._ICR4
#define ICR30_ICR3 icr30.bit._ICR3
#define ICR30_ICR2 icr30.bit._ICR2
#define ICR30_ICR1 icr30.bit._ICR1
#define ICR30_ICR0 icr30.bit._ICR0
__IO_EXTERN ICR31STR icr31;  
#define ICR31 icr31.byte
#define ICR31_ICR4 icr31.bit._ICR4
#define ICR31_ICR3 icr31.bit._ICR3
#define ICR31_ICR2 icr31.bit._ICR2
#define ICR31_ICR1 icr31.bit._ICR1
#define ICR31_ICR0 icr31.bit._ICR0
__IO_EXTERN ICR32STR icr32;  
#define ICR32 icr32.byte
#define ICR32_ICR4 icr32.bit._ICR4
#define ICR32_ICR3 icr32.bit._ICR3
#define ICR32_ICR2 icr32.bit._ICR2
#define ICR32_ICR1 icr32.bit._ICR1
#define ICR32_ICR0 icr32.bit._ICR0
__IO_EXTERN ICR33STR icr33;  
#define ICR33 icr33.byte
#define ICR33_ICR4 icr33.bit._ICR4
#define ICR33_ICR3 icr33.bit._ICR3
#define ICR33_ICR2 icr33.bit._ICR2
#define ICR33_ICR1 icr33.bit._ICR1
#define ICR33_ICR0 icr33.bit._ICR0
__IO_EXTERN ICR34STR icr34;  
#define ICR34 icr34.byte
#define ICR34_ICR4 icr34.bit._ICR4
#define ICR34_ICR3 icr34.bit._ICR3
#define ICR34_ICR2 icr34.bit._ICR2
#define ICR34_ICR1 icr34.bit._ICR1
#define ICR34_ICR0 icr34.bit._ICR0
__IO_EXTERN ICR35STR icr35;  
#define ICR35 icr35.byte
#define ICR35_ICR4 icr35.bit._ICR4
#define ICR35_ICR3 icr35.bit._ICR3
#define ICR35_ICR2 icr35.bit._ICR2
#define ICR35_ICR1 icr35.bit._ICR1
#define ICR35_ICR0 icr35.bit._ICR0
__IO_EXTERN ICR36STR icr36;  
#define ICR36 icr36.byte
#define ICR36_ICR4 icr36.bit._ICR4
#define ICR36_ICR3 icr36.bit._ICR3
#define ICR36_ICR2 icr36.bit._ICR2
#define ICR36_ICR1 icr36.bit._ICR1
#define ICR36_ICR0 icr36.bit._ICR0
__IO_EXTERN ICR37STR icr37;  
#define ICR37 icr37.byte
#define ICR37_ICR4 icr37.bit._ICR4
#define ICR37_ICR3 icr37.bit._ICR3
#define ICR37_ICR2 icr37.bit._ICR2
#define ICR37_ICR1 icr37.bit._ICR1
#define ICR37_ICR0 icr37.bit._ICR0
__IO_EXTERN ICR38STR icr38;  
#define ICR38 icr38.byte
#define ICR38_ICR4 icr38.bit._ICR4
#define ICR38_ICR3 icr38.bit._ICR3
#define ICR38_ICR2 icr38.bit._ICR2
#define ICR38_ICR1 icr38.bit._ICR1
#define ICR38_ICR0 icr38.bit._ICR0
__IO_EXTERN ICR39STR icr39;  
#define ICR39 icr39.byte
#define ICR39_ICR4 icr39.bit._ICR4
#define ICR39_ICR3 icr39.bit._ICR3
#define ICR39_ICR2 icr39.bit._ICR2
#define ICR39_ICR1 icr39.bit._ICR1
#define ICR39_ICR0 icr39.bit._ICR0
__IO_EXTERN ICR40STR icr40;  
#define ICR40 icr40.byte
#define ICR40_ICR4 icr40.bit._ICR4
#define ICR40_ICR3 icr40.bit._ICR3
#define ICR40_ICR2 icr40.bit._ICR2
#define ICR40_ICR1 icr40.bit._ICR1
#define ICR40_ICR0 icr40.bit._ICR0
__IO_EXTERN ICR41STR icr41;  
#define ICR41 icr41.byte
#define ICR41_ICR4 icr41.bit._ICR4
#define ICR41_ICR3 icr41.bit._ICR3
#define ICR41_ICR2 icr41.bit._ICR2
#define ICR41_ICR1 icr41.bit._ICR1
#define ICR41_ICR0 icr41.bit._ICR0
__IO_EXTERN ICR42STR icr42;  
#define ICR42 icr42.byte
#define ICR42_ICR4 icr42.bit._ICR4
#define ICR42_ICR3 icr42.bit._ICR3
#define ICR42_ICR2 icr42.bit._ICR2
#define ICR42_ICR1 icr42.bit._ICR1
#define ICR42_ICR0 icr42.bit._ICR0
__IO_EXTERN ICR43STR icr43;  
#define ICR43 icr43.byte
#define ICR43_ICR4 icr43.bit._ICR4
#define ICR43_ICR3 icr43.bit._ICR3
#define ICR43_ICR2 icr43.bit._ICR2
#define ICR43_ICR1 icr43.bit._ICR1
#define ICR43_ICR0 icr43.bit._ICR0
__IO_EXTERN ICR44STR icr44;  
#define ICR44 icr44.byte
#define ICR44_ICR4 icr44.bit._ICR4
#define ICR44_ICR3 icr44.bit._ICR3
#define ICR44_ICR2 icr44.bit._ICR2
#define ICR44_ICR1 icr44.bit._ICR1
#define ICR44_ICR0 icr44.bit._ICR0
__IO_EXTERN ICR45STR icr45;  
#define ICR45 icr45.byte
#define ICR45_ICR4 icr45.bit._ICR4
#define ICR45_ICR3 icr45.bit._ICR3
#define ICR45_ICR2 icr45.bit._ICR2
#define ICR45_ICR1 icr45.bit._ICR1
#define ICR45_ICR0 icr45.bit._ICR0
__IO_EXTERN ICR46STR icr46;  
#define ICR46 icr46.byte
#define ICR46_ICR4 icr46.bit._ICR4
#define ICR46_ICR3 icr46.bit._ICR3
#define ICR46_ICR2 icr46.bit._ICR2
#define ICR46_ICR1 icr46.bit._ICR1
#define ICR46_ICR0 icr46.bit._ICR0
__IO_EXTERN ICR47STR icr47;  
#define ICR47 icr47.byte
#define ICR47_ICR4 icr47.bit._ICR4
#define ICR47_ICR3 icr47.bit._ICR3
#define ICR47_ICR2 icr47.bit._ICR2
#define ICR47_ICR1 icr47.bit._ICR1
#define ICR47_ICR0 icr47.bit._ICR0
__IO_EXTERN ICR48STR icr48;  
#define ICR48 icr48.byte
#define ICR48_ICR4 icr48.bit._ICR4
#define ICR48_ICR3 icr48.bit._ICR3
#define ICR48_ICR2 icr48.bit._ICR2
#define ICR48_ICR1 icr48.bit._ICR1
#define ICR48_ICR0 icr48.bit._ICR0
__IO_EXTERN ICR49STR icr49;  
#define ICR49 icr49.byte
#define ICR49_ICR4 icr49.bit._ICR4
#define ICR49_ICR3 icr49.bit._ICR3
#define ICR49_ICR2 icr49.bit._ICR2
#define ICR49_ICR1 icr49.bit._ICR1
#define ICR49_ICR0 icr49.bit._ICR0
__IO_EXTERN ICR50STR icr50;  
#define ICR50 icr50.byte
#define ICR50_ICR4 icr50.bit._ICR4
#define ICR50_ICR3 icr50.bit._ICR3
#define ICR50_ICR2 icr50.bit._ICR2
#define ICR50_ICR1 icr50.bit._ICR1
#define ICR50_ICR0 icr50.bit._ICR0
__IO_EXTERN ICR51STR icr51;  
#define ICR51 icr51.byte
#define ICR51_ICR4 icr51.bit._ICR4
#define ICR51_ICR3 icr51.bit._ICR3
#define ICR51_ICR2 icr51.bit._ICR2
#define ICR51_ICR1 icr51.bit._ICR1
#define ICR51_ICR0 icr51.bit._ICR0
__IO_EXTERN ICR52STR icr52;  
#define ICR52 icr52.byte
#define ICR52_ICR4 icr52.bit._ICR4
#define ICR52_ICR3 icr52.bit._ICR3
#define ICR52_ICR2 icr52.bit._ICR2
#define ICR52_ICR1 icr52.bit._ICR1
#define ICR52_ICR0 icr52.bit._ICR0
__IO_EXTERN ICR53STR icr53;  
#define ICR53 icr53.byte
#define ICR53_ICR4 icr53.bit._ICR4
#define ICR53_ICR3 icr53.bit._ICR3
#define ICR53_ICR2 icr53.bit._ICR2
#define ICR53_ICR1 icr53.bit._ICR1
#define ICR53_ICR0 icr53.bit._ICR0
__IO_EXTERN ICR54STR icr54;  
#define ICR54 icr54.byte
#define ICR54_ICR4 icr54.bit._ICR4
#define ICR54_ICR3 icr54.bit._ICR3
#define ICR54_ICR2 icr54.bit._ICR2
#define ICR54_ICR1 icr54.bit._ICR1
#define ICR54_ICR0 icr54.bit._ICR0
__IO_EXTERN ICR55STR icr55;  
#define ICR55 icr55.byte
#define ICR55_ICR4 icr55.bit._ICR4
#define ICR55_ICR3 icr55.bit._ICR3
#define ICR55_ICR2 icr55.bit._ICR2
#define ICR55_ICR1 icr55.bit._ICR1
#define ICR55_ICR0 icr55.bit._ICR0
__IO_EXTERN ICR56STR icr56;  
#define ICR56 icr56.byte
#define ICR56_ICR4 icr56.bit._ICR4
#define ICR56_ICR3 icr56.bit._ICR3
#define ICR56_ICR2 icr56.bit._ICR2
#define ICR56_ICR1 icr56.bit._ICR1
#define ICR56_ICR0 icr56.bit._ICR0
__IO_EXTERN ICR57STR icr57;  
#define ICR57 icr57.byte
#define ICR57_ICR4 icr57.bit._ICR4
#define ICR57_ICR3 icr57.bit._ICR3
#define ICR57_ICR2 icr57.bit._ICR2
#define ICR57_ICR1 icr57.bit._ICR1
#define ICR57_ICR0 icr57.bit._ICR0
__IO_EXTERN ICR58STR icr58;  
#define ICR58 icr58.byte
#define ICR58_ICR4 icr58.bit._ICR4
#define ICR58_ICR3 icr58.bit._ICR3
#define ICR58_ICR2 icr58.bit._ICR2
#define ICR58_ICR1 icr58.bit._ICR1
#define ICR58_ICR0 icr58.bit._ICR0
__IO_EXTERN ICR59STR icr59;  
#define ICR59 icr59.byte
#define ICR59_ICR4 icr59.bit._ICR4
#define ICR59_ICR3 icr59.bit._ICR3
#define ICR59_ICR2 icr59.bit._ICR2
#define ICR59_ICR1 icr59.bit._ICR1
#define ICR59_ICR0 icr59.bit._ICR0
__IO_EXTERN ICR60STR icr60;  
#define ICR60 icr60.byte
#define ICR60_ICR4 icr60.bit._ICR4
#define ICR60_ICR3 icr60.bit._ICR3
#define ICR60_ICR2 icr60.bit._ICR2
#define ICR60_ICR1 icr60.bit._ICR1
#define ICR60_ICR0 icr60.bit._ICR0
__IO_EXTERN ICR61STR icr61;  
#define ICR61 icr61.byte
#define ICR61_ICR4 icr61.bit._ICR4
#define ICR61_ICR3 icr61.bit._ICR3
#define ICR61_ICR2 icr61.bit._ICR2
#define ICR61_ICR1 icr61.bit._ICR1
#define ICR61_ICR0 icr61.bit._ICR0
__IO_EXTERN ICR62STR icr62;  
#define ICR62 icr62.byte
#define ICR62_ICR4 icr62.bit._ICR4
#define ICR62_ICR3 icr62.bit._ICR3
#define ICR62_ICR2 icr62.bit._ICR2
#define ICR62_ICR1 icr62.bit._ICR1
#define ICR62_ICR0 icr62.bit._ICR0
__IO_EXTERN ICR63STR icr63;  
#define ICR63 icr63.byte
#define ICR63_ICR4 icr63.bit._ICR4
#define ICR63_ICR3 icr63.bit._ICR3
#define ICR63_ICR2 icr63.bit._ICR2
#define ICR63_ICR1 icr63.bit._ICR1
#define ICR63_ICR0 icr63.bit._ICR0
__IO_EXTERN RSRRSTR rsrr;   /* Clock Control Unit */
#define RSRR rsrr.byte
#define RSRR_INIT rsrr.bit._INIT
#define RSRR_HSTB rsrr.bit._HSTB
#define RSRR_WDOG rsrr.bit._WDOG
#define RSRR_ERST rsrr.bit._ERST
#define RSRR_SRST rsrr.bit._SRST
#define RSRR_LINIT rsrr.bit._LINIT
#define RSRR_WT1 rsrr.bit._WT1
#define RSRR_WT0 rsrr.bit._WT0
#define RSRR_WT rsrr.bitc._WT
__IO_EXTERN STCRSTR stcr;  
#define STCR stcr.byte
#define STCR_STOP stcr.bit._STOP
#define STCR_SLEEP stcr.bit._SLEEP
#define STCR_HIZ stcr.bit._HIZ
#define STCR_SRST stcr.bit._SRST
#define STCR_OS1 stcr.bit._OS1
#define STCR_OS0 stcr.bit._OS0
#define STCR_OSCD2 stcr.bit._OSCD2
#define STCR_OSCD1 stcr.bit._OSCD1
#define STCR_OS stcr.bitc._OS
#define STCR_OSCD stcr.bitc._OSCD
__IO_EXTERN TBCRSTR tbcr;  
#define TBCR tbcr.byte
#define TBCR_TBIF tbcr.bit._TBIF
#define TBCR_TBIE tbcr.bit._TBIE
#define TBCR_TBC2 tbcr.bit._TBC2
#define TBCR_TBC1 tbcr.bit._TBC1
#define TBCR_TBC0 tbcr.bit._TBC0
#define TBCR_SYNCR tbcr.bit._SYNCR
#define TBCR_SYNCS tbcr.bit._SYNCS
#define TBCR_TBC tbcr.bitc._TBC
__IO_EXTERN CTBRSTR ctbr;  
#define CTBR ctbr.byte
#define CTBR_D7 ctbr.bit._D7
#define CTBR_D6 ctbr.bit._D6
#define CTBR_D5 ctbr.bit._D5
#define CTBR_D4 ctbr.bit._D4
#define CTBR_D3 ctbr.bit._D3
#define CTBR_D2 ctbr.bit._D2
#define CTBR_D1 ctbr.bit._D1
#define CTBR_D0 ctbr.bit._D0
__IO_EXTERN CLKRSTR clkr;  
#define CLKR clkr.byte
#define CLKR_SCKEN clkr.bit._SCKEN
#define CLKR_PLL1EN clkr.bit._PLL1EN
#define CLKR_CLKS1 clkr.bit._CLKS1
#define CLKR_CLKS0 clkr.bit._CLKS0
#define CLKR_CLKS clkr.bitc._CLKS
/* include : INC460_CLKR.INC */
/*-------------------------------------------------------------------*/
/* INC460.INC :  Old bit name of CLKR */

/* alias macro definition for CLKR*/
#define CLKR_PLL2EN clkr.bit._SCKEN
/*-------------------------------------------------------------------*/
__IO_EXTERN WPRSTR wpr;  
#define WPR wpr.byte
#define WPR_D7 wpr.bit._D7
#define WPR_D6 wpr.bit._D6
#define WPR_D5 wpr.bit._D5
#define WPR_D4 wpr.bit._D4
#define WPR_D3 wpr.bit._D3
#define WPR_D2 wpr.bit._D2
#define WPR_D1 wpr.bit._D1
#define WPR_D0 wpr.bit._D0
__IO_EXTERN DIVR0STR divr0;  
#define DIVR0 divr0.byte
#define DIVR0_B3 divr0.bit._B3
#define DIVR0_B2 divr0.bit._B2
#define DIVR0_B1 divr0.bit._B1
#define DIVR0_B0 divr0.bit._B0
#define DIVR0_P3 divr0.bit._P3
#define DIVR0_P2 divr0.bit._P2
#define DIVR0_P1 divr0.bit._P1
#define DIVR0_P0 divr0.bit._P0
#define DIVR0_B divr0.bitc._B
#define DIVR0_P divr0.bitc._P
__IO_EXTERN DIVR1STR divr1;  
#define DIVR1 divr1.byte
#define DIVR1_T3 divr1.bit._T3
#define DIVR1_T2 divr1.bit._T2
#define DIVR1_T1 divr1.bit._T1
#define DIVR1_T0 divr1.bit._T0
#define DIVR1_T divr1.bitc._T
__IO_EXTERN PLLDIVMSTR plldivm;   /* PLL - Clock Gear Unit: */
#define PLLDIVM plldivm.byte
#define PLLDIVM_DVM3 plldivm.bit._DVM3
#define PLLDIVM_DVM2 plldivm.bit._DVM2
#define PLLDIVM_DVM1 plldivm.bit._DVM1
#define PLLDIVM_DVM0 plldivm.bit._DVM0
#define PLLDIVM_DVM plldivm.bitc._DVM
__IO_EXTERN PLLDIVNSTR plldivn;  
#define PLLDIVN plldivn.byte
#define PLLDIVN_DVN5 plldivn.bit._DVN5
#define PLLDIVN_DVN4 plldivn.bit._DVN4
#define PLLDIVN_DVN3 plldivn.bit._DVN3
#define PLLDIVN_DVN2 plldivn.bit._DVN2
#define PLLDIVN_DVN1 plldivn.bit._DVN1
#define PLLDIVN_DVN0 plldivn.bit._DVN0
#define PLLDIVN_DVN plldivn.bitc._DVN
__IO_EXTERN PLLDIVGSTR plldivg;  
#define PLLDIVG plldivg.byte
#define PLLDIVG_DVG3 plldivg.bit._DVG3
#define PLLDIVG_DVG2 plldivg.bit._DVG2
#define PLLDIVG_DVG1 plldivg.bit._DVG1
#define PLLDIVG_DVG0 plldivg.bit._DVG0
#define PLLDIVG_DVG plldivg.bitc._DVG
__IO_EXTERN PLLMULGSTR pllmulg;  
#define PLLMULG pllmulg.byte
#define PLLMULG_MLG7 pllmulg.bit._MLG7
#define PLLMULG_MLG6 pllmulg.bit._MLG6
#define PLLMULG_MLG5 pllmulg.bit._MLG5
#define PLLMULG_MLG4 pllmulg.bit._MLG4
#define PLLMULG_MLG3 pllmulg.bit._MLG3
#define PLLMULG_MLG2 pllmulg.bit._MLG2
#define PLLMULG_MLG1 pllmulg.bit._MLG1
#define PLLMULG_MLG0 pllmulg.bit._MLG0
#define PLLMULG_MLG pllmulg.bitc._MLG
__IO_EXTERN PLLCTRLSTR pllctrl;  
#define PLLCTRL pllctrl.byte
#define PLLCTRL_IEDN pllctrl.bit._IEDN
#define PLLCTRL_GRDN pllctrl.bit._GRDN
#define PLLCTRL_IEUP pllctrl.bit._IEUP
#define PLLCTRL_GRUP pllctrl.bit._GRUP
__IO_EXTERN OSCC1STR oscc1;   /* Main/Sub Oscillator Control */
#define OSCC1 oscc1.byte
#define OSCC1_FCI oscc1.bit._FCI
#define OSCC1_RFBEN oscc1.bit._RFBEN
#define OSCC1_OSCR oscc1.bit._OSCR
__IO_EXTERN OSCS1STR oscs1;  
#define OSCS1 oscs1.byte
#define OSCS1_OSCS7 oscs1.bit._OSCS7
#define OSCS1_OSCS6 oscs1.bit._OSCS6
#define OSCS1_OSCS5 oscs1.bit._OSCS5
#define OSCS1_OSCS4 oscs1.bit._OSCS4
#define OSCS1_OSCS3 oscs1.bit._OSCS3
#define OSCS1_OSCS2 oscs1.bit._OSCS2
#define OSCS1_OSCS1 oscs1.bit._OSCS1
#define OSCS1_OSCS0 oscs1.bit._OSCS0
__IO_EXTERN OSCC2STR oscc2;  
#define OSCC2 oscc2.byte
#define OSCC2_FCI oscc2.bit._FCI
#define OSCC2_RFBEN oscc2.bit._RFBEN
#define OSCC2_OSCR oscc2.bit._OSCR
__IO_EXTERN OSCS2STR oscs2;  
#define OSCS2 oscs2.byte
#define OSCS2_OSCS7 oscs2.bit._OSCS7
#define OSCS2_OSCS6 oscs2.bit._OSCS6
#define OSCS2_OSCS5 oscs2.bit._OSCS5
#define OSCS2_OSCS4 oscs2.bit._OSCS4
#define OSCS2_OSCS3 oscs2.bit._OSCS3
#define OSCS2_OSCS2 oscs2.bit._OSCS2
#define OSCS2_OSCS1 oscs2.bit._OSCS1
#define OSCS2_OSCS0 oscs2.bit._OSCS0
__IO_EXTERN PORTENSTR porten;   /* Port Input Enable Control */
#define PORTEN porten.byte
#define PORTEN_CPORTEN porten.bit._CPORTEN
#define PORTEN_GPORTEN porten.bit._GPORTEN
__IO_EXTERN WTCERSTR wtcer;   /* Real Time Clock (Watch Timer) */
#define WTCER wtcer.byte
#define WTCER_INTE4 wtcer.bit._INTE4
#define WTCER_INT4 wtcer.bit._INT4
__IO_EXTERN WTCRSTR wtcr;  
#define WTCR wtcr.word
#define WTCR_INTE3 wtcr.bit._INTE3
#define WTCR_INT3 wtcr.bit._INT3
#define WTCR_INTE2 wtcr.bit._INTE2
#define WTCR_INT2 wtcr.bit._INT2
#define WTCR_INTE1 wtcr.bit._INTE1
#define WTCR_INT1 wtcr.bit._INT1
#define WTCR_INTE0 wtcr.bit._INTE0
#define WTCR_INT0 wtcr.bit._INT0
#define WTCR_RUN wtcr.bit._RUN
#define WTCR_UPDT wtcr.bit._UPDT
#define WTCR_ST wtcr.bit._ST
__IO_EXTERN WTBRSTR wtbr;  
#define WTBR wtbr.lword
#define WTBR_D20 wtbr.bit._D20
#define WTBR_D19 wtbr.bit._D19
#define WTBR_D18 wtbr.bit._D18
#define WTBR_D17 wtbr.bit._D17
#define WTBR_D16 wtbr.bit._D16
#define WTBR_D15 wtbr.bit._D15
#define WTBR_D14 wtbr.bit._D14
#define WTBR_D13 wtbr.bit._D13
#define WTBR_D12 wtbr.bit._D12
#define WTBR_D11 wtbr.bit._D11
#define WTBR_D10 wtbr.bit._D10
#define WTBR_D9 wtbr.bit._D9
#define WTBR_D8 wtbr.bit._D8
#define WTBR_D7 wtbr.bit._D7
#define WTBR_D6 wtbr.bit._D6
#define WTBR_D5 wtbr.bit._D5
#define WTBR_D4 wtbr.bit._D4
#define WTBR_D3 wtbr.bit._D3
#define WTBR_D2 wtbr.bit._D2
#define WTBR_D1 wtbr.bit._D1
#define WTBR_D0 wtbr.bit._D0
__IO_EXTERN WTHRSTR wthr;  
#define WTHR wthr.byte
#define WTHR_H4 wthr.bit._H4
#define WTHR_H3 wthr.bit._H3
#define WTHR_H2 wthr.bit._H2
#define WTHR_H1 wthr.bit._H1
#define WTHR_H0 wthr.bit._H0
__IO_EXTERN WTMRSTR wtmr;  
#define WTMR wtmr.byte
#define WTMR_M5 wtmr.bit._M5
#define WTMR_M4 wtmr.bit._M4
#define WTMR_M3 wtmr.bit._M3
#define WTMR_M2 wtmr.bit._M2
#define WTMR_M1 wtmr.bit._M1
#define WTMR_M0 wtmr.bit._M0
__IO_EXTERN WTSRSTR wtsr;  
#define WTSR wtsr.byte
#define WTSR_S5 wtsr.bit._S5
#define WTSR_S4 wtsr.bit._S4
#define WTSR_S3 wtsr.bit._S3
#define WTSR_S2 wtsr.bit._S2
#define WTSR_S1 wtsr.bit._S1
#define WTSR_S0 wtsr.bit._S0
__IO_EXTERN IO_BYTE csvtr;   /* Clock-Supervisor / Selecor / Monitor */
#define CSVTR csvtr
__IO_EXTERN CSVCRSTR csvcr;  
#define CSVCR csvcr.byte
#define CSVCR_SCKS csvcr.bit._SCKS
#define CSVCR_MM csvcr.bit._MM
#define CSVCR_SM csvcr.bit._SM
#define CSVCR_RCE csvcr.bit._RCE
#define CSVCR_MSVE csvcr.bit._MSVE
#define CSVCR_SSVE csvcr.bit._SSVE
#define CSVCR_SRST csvcr.bit._SRST
#define CSVCR_OUTE csvcr.bit._OUTE
__IO_EXTERN CSCFGSTR cscfg;  
#define CSCFG cscfg.byte
#define CSCFG_EDSUEN cscfg.bit._EDSUEN
#define CSCFG_PLLLOCK cscfg.bit._PLLLOCK
#define CSCFG_RCSEL cscfg.bit._RCSEL
#define CSCFG_MONCKI cscfg.bit._MONCKI
#define CSCFG_CSC3 cscfg.bit._CSC3
#define CSCFG_CSC2 cscfg.bit._CSC2
#define CSCFG_CSC1 cscfg.bit._CSC1
#define CSCFG_CSC0 cscfg.bit._CSC0
#define CSCFG_CSC cscfg.bitc._CSC
__IO_EXTERN CMCFGSTR cmcfg;  
#define CMCFG cmcfg.byte
#define CMCFG_CMPRE3 cmcfg.bit._CMPRE3
#define CMCFG_CMPRE2 cmcfg.bit._CMPRE2
#define CMCFG_CMPRE1 cmcfg.bit._CMPRE1
#define CMCFG_CMPRE0 cmcfg.bit._CMPRE0
#define CMCFG_CMSEL3 cmcfg.bit._CMSEL3
#define CMCFG_CMSEL2 cmcfg.bit._CMSEL2
#define CMCFG_CMSEL1 cmcfg.bit._CMSEL1
#define CMCFG_CMSEL0 cmcfg.bit._CMSEL0
#define CMCFG_CMPRE cmcfg.bitc._CMPRE
#define CMCFG_CMSEL cmcfg.bitc._CMSEL
/* include : INC460_CSV.INC */
/*-------------------------------------------------------------------*/
/* INC460.DMAC :  Old bit name of CSV */
 
/* alias macro definition for CSV */
#define CSVCR_MS csvcr.bit._SM
#define CSVCR_REC csvcr.bit._RCE
/*-------------------------------------------------------------------*/
__IO_EXTERN CUCRSTR cucr;   /* Calibration Unit of Sub Oszillation */
#define CUCR cucr.word
#define CUCR_STRT cucr.bit._STRT
#define CUCR_INT cucr.bit._INT
#define CUCR_INTEN cucr.bit._INTEN
__IO_EXTERN CUTDSTR cutd;  
#define CUTD cutd.word
#define CUTD_TDD15 cutd.bit._TDD15
#define CUTD_TDD14 cutd.bit._TDD14
#define CUTD_TDD13 cutd.bit._TDD13
#define CUTD_TDD12 cutd.bit._TDD12
#define CUTD_TDD11 cutd.bit._TDD11
#define CUTD_TDD10 cutd.bit._TDD10
#define CUTD_TDD9 cutd.bit._TDD9
#define CUTD_TDD8 cutd.bit._TDD8
#define CUTD_TDD7 cutd.bit._TDD7
#define CUTD_TDD6 cutd.bit._TDD6
#define CUTD_TDD5 cutd.bit._TDD5
#define CUTD_TDD4 cutd.bit._TDD4
#define CUTD_TDD3 cutd.bit._TDD3
#define CUTD_TDD2 cutd.bit._TDD2
#define CUTD_TDD1 cutd.bit._TDD1
#define CUTD_TDD0 cutd.bit._TDD0
__IO_EXTERN CUTR1STR cutr1;  
#define CUTR1 cutr1.word
#define CUTR1_TDR23 cutr1.bit._TDR23
#define CUTR1_TDR22 cutr1.bit._TDR22
#define CUTR1_TDR21 cutr1.bit._TDR21
#define CUTR1_TDR20 cutr1.bit._TDR20
#define CUTR1_TDR19 cutr1.bit._TDR19
#define CUTR1_TDR18 cutr1.bit._TDR18
#define CUTR1_TDR17 cutr1.bit._TDR17
#define CUTR1_TDR16 cutr1.bit._TDR16
__IO_EXTERN CUTR2STR cutr2;  
#define CUTR2 cutr2.word
#define CUTR2_TDR15 cutr2.bit._TDR15
#define CUTR2_TDR14 cutr2.bit._TDR14
#define CUTR2_TDR13 cutr2.bit._TDR13
#define CUTR2_TDR12 cutr2.bit._TDR12
#define CUTR2_TDR11 cutr2.bit._TDR11
#define CUTR2_TDR10 cutr2.bit._TDR10
#define CUTR2_TDR9 cutr2.bit._TDR9
#define CUTR2_TDR8 cutr2.bit._TDR8
#define CUTR2_TDR7 cutr2.bit._TDR7
#define CUTR2_TDR6 cutr2.bit._TDR6
#define CUTR2_TDR5 cutr2.bit._TDR5
#define CUTR2_TDR4 cutr2.bit._TDR4
#define CUTR2_TDR3 cutr2.bit._TDR3
#define CUTR2_TDR2 cutr2.bit._TDR2
#define CUTR2_TDR1 cutr2.bit._TDR1
#define CUTR2_TDR0 cutr2.bit._TDR0
__IO_EXTERN CMPRSTR cmpr;   /* Clock Modulator */
#define CMPR cmpr.word
#define CMPR_MP13 cmpr.bit._MP13
#define CMPR_MP12 cmpr.bit._MP12
#define CMPR_MP11 cmpr.bit._MP11
#define CMPR_MP10 cmpr.bit._MP10
#define CMPR_MP9 cmpr.bit._MP9
#define CMPR_MP8 cmpr.bit._MP8
#define CMPR_MP7 cmpr.bit._MP7
#define CMPR_MP6 cmpr.bit._MP6
#define CMPR_MP5 cmpr.bit._MP5
#define CMPR_MP4 cmpr.bit._MP4
#define CMPR_MP3 cmpr.bit._MP3
#define CMPR_MP2 cmpr.bit._MP2
#define CMPR_MP1 cmpr.bit._MP1
#define CMPR_MP0 cmpr.bit._MP0
__IO_EXTERN CMCRSTR cmcr;  
#define CMCR cmcr.byte
#define CMCR_FMODRUN cmcr.bit._FMODRUN
#define CMCR_FMOD cmcr.bit._FMOD
#define CMCR_PDX cmcr.bit._PDX
__IO_EXTERN IO_WORD cmt1;  
#define CMT1 cmt1
__IO_EXTERN IO_WORD cmt2;  
#define CMT2 cmt2
__IO_EXTERN CANPRESTR canpre;   /* CAN clock control */
#define CANPRE canpre.byte
#define CANPRE_CPCKS1 canpre.bit._CPCKS1
#define CANPRE_CPCKS0 canpre.bit._CPCKS0
#define CANPRE_DVC3 canpre.bit._DVC3
#define CANPRE_DVC2 canpre.bit._DVC2
#define CANPRE_DVC1 canpre.bit._DVC1
#define CANPRE_DVC0 canpre.bit._DVC0
#define CANPRE_CPCKS canpre.bitc._CPCKS
#define CANPRE_DVC canpre.bitc._DVC
__IO_EXTERN CANCKDSTR canckd;  
#define CANCKD canckd.byte
#define CANCKD_CANCKD5 canckd.bit._CANCKD5
#define CANCKD_CANCKD4 canckd.bit._CANCKD4
#define CANCKD_CANCKD3 canckd.bit._CANCKD3
#define CANCKD_CANCKD2 canckd.bit._CANCKD2
#define CANCKD_CANCKD1 canckd.bit._CANCKD1
#define CANCKD_CANCKD0 canckd.bit._CANCKD0
__IO_EXTERN LVSELSTR lvsel;   /* LV Detection / Hardware-Watchdog */
#define LVSEL lvsel.byte
#define LVSEL_LVESEL3 lvsel.bit._LVESEL3
#define LVSEL_LVESEL2 lvsel.bit._LVESEL2
#define LVSEL_LVESEL1 lvsel.bit._LVESEL1
#define LVSEL_LVESEL0 lvsel.bit._LVESEL0
#define LVSEL_LVISEL3 lvsel.bit._LVISEL3
#define LVSEL_LVISEL2 lvsel.bit._LVISEL2
#define LVSEL_LVISEL1 lvsel.bit._LVISEL1
#define LVSEL_LVISEL0 lvsel.bit._LVISEL0
#define LVSEL_LVESEL lvsel.bitc._LVESEL
#define LVSEL_LVISEL lvsel.bitc._LVISEL
__IO_EXTERN LVDETSTR lvdet;  
#define LVDET lvdet.byte
#define LVDET_LVSEL lvdet.bit._LVSEL
#define LVDET_LVEPD lvdet.bit._LVEPD
#define LVDET_LVIPD lvdet.bit._LVIPD
#define LVDET_LVREN lvdet.bit._LVREN
#define LVDET_LVIEN lvdet.bit._LVIEN
#define LVDET_LVIRQ lvdet.bit._LVIRQ
__IO_EXTERN HWWDESTR hwwde;  
#define HWWDE hwwde.byte
#define HWWDE_ED1 hwwde.bit._ED1
#define HWWDE_ED0 hwwde.bit._ED0
#define HWWDE_ED hwwde.bitc._ED
__IO_EXTERN HWWDSTR hwwd;  
#define HWWD hwwd.byte
#define HWWD_CL hwwd.bit._CL
#define HWWD_CPUF hwwd.bit._CPUF
__IO_EXTERN OSCRHSTR oscrh;   /* Main-/Sub-Oscillatio Stabilization Timer */
#define OSCRH oscrh.byte
#define OSCRH_WIF oscrh.bit._WIF
#define OSCRH_WIE oscrh.bit._WIE
#define OSCRH_WEN oscrh.bit._WEN
#define OSCRH_WS1 oscrh.bit._WS1
#define OSCRH_WS0 oscrh.bit._WS0
#define OSCRH_WCL oscrh.bit._WCL
#define OSCRH_WS oscrh.bitc._WS
__IO_EXTERN IO_BYTE oscrl;  
#define OSCRL oscrl
__IO_EXTERN WPCRHSTR wpcrh;  
#define WPCRH wpcrh.byte
#define WPCRH_WIF wpcrh.bit._WIF
#define WPCRH_WIE wpcrh.bit._WIE
#define WPCRH_WEN wpcrh.bit._WEN
#define WPCRH_WS1 wpcrh.bit._WS1
#define WPCRH_WS0 wpcrh.bit._WS0
#define WPCRH_WCL wpcrh.bit._WCL
#define WPCRH_WS wpcrh.bitc._WS
__IO_EXTERN IO_BYTE wpcrl;  
#define WPCRL wpcrl
__IO_EXTERN OSCCRSTR osccr;   /* Main-/Sub-Oscillatio Standby Control */
#define OSCCR osccr.byte
#define OSCCR_OSCDS1 osccr.bit._OSCDS1
__IO_EXTERN REGSELSTR regsel;  
#define REGSEL regsel.byte
#define REGSEL_FLASHSEL regsel.bit._FLASHSEL
#define REGSEL_MAINSEL regsel.bit._MAINSEL
#define REGSEL_SUBSEL3 regsel.bit._SUBSEL3
#define REGSEL_SUBSEL2 regsel.bit._SUBSEL2
#define REGSEL_SUBSEL1 regsel.bit._SUBSEL1
#define REGSEL_SUBSEL0 regsel.bit._SUBSEL0
#define REGSEL_SUBSEL regsel.bitc._SUBSEL
__IO_EXTERN REGCTRSTR regctr;  
#define REGCTR regctr.byte
#define REGCTR_MSTBO regctr.bit._MSTBO
#define REGCTR_MAINKPEN regctr.bit._MAINKPEN
#define REGCTR_MAINDSBL regctr.bit._MAINDSBL
__IO_EXTERN ASR0STR asr0;   /* External Bus/Chip Select Registers */
#define ASR0 asr0.word
#define ASR0_A31 asr0.bit._A31
#define ASR0_A30 asr0.bit._A30
#define ASR0_A29 asr0.bit._A29
#define ASR0_A28 asr0.bit._A28
#define ASR0_A27 asr0.bit._A27
#define ASR0_A26 asr0.bit._A26
#define ASR0_A25 asr0.bit._A25
#define ASR0_A24 asr0.bit._A24
#define ASR0_A23 asr0.bit._A23
#define ASR0_A22 asr0.bit._A22
#define ASR0_A21 asr0.bit._A21
#define ASR0_A20 asr0.bit._A20
#define ASR0_A19 asr0.bit._A19
#define ASR0_A18 asr0.bit._A18
#define ASR0_A17 asr0.bit._A17
#define ASR0_A16 asr0.bit._A16
__IO_EXTERN ACR0STR acr0;  
#define ACR0 acr0.word
#define ACR0_ASZ3 acr0.bit._ASZ3
#define ACR0_ASZ2 acr0.bit._ASZ2
#define ACR0_ASZ1 acr0.bit._ASZ1
#define ACR0_ASZ0 acr0.bit._ASZ0
#define ACR0_DBW1 acr0.bit._DBW1
#define ACR0_DBW0 acr0.bit._DBW0
#define ACR0_BST1 acr0.bit._BST1
#define ACR0_BST0 acr0.bit._BST0
#define ACR0_SREN acr0.bit._SREN
#define ACR0_PFEN acr0.bit._PFEN
#define ACR0_WREN acr0.bit._WREN
#define ACR0_TYP3 acr0.bit._TYP3
#define ACR0_TYP2 acr0.bit._TYP2
#define ACR0_TYP1 acr0.bit._TYP1
#define ACR0_TYP0 acr0.bit._TYP0
#define ACR0_ASZ acr0.bitc._ASZ
#define ACR0_DBW acr0.bitc._DBW
#define ACR0_BST acr0.bitc._BST
#define ACR0_TYP acr0.bitc._TYP
__IO_EXTERN ASR1STR asr1;  
#define ASR1 asr1.word
#define ASR1_A31 asr1.bit._A31
#define ASR1_A30 asr1.bit._A30
#define ASR1_A29 asr1.bit._A29
#define ASR1_A28 asr1.bit._A28
#define ASR1_A27 asr1.bit._A27
#define ASR1_A26 asr1.bit._A26
#define ASR1_A25 asr1.bit._A25
#define ASR1_A24 asr1.bit._A24
#define ASR1_A23 asr1.bit._A23
#define ASR1_A22 asr1.bit._A22
#define ASR1_A21 asr1.bit._A21
#define ASR1_A20 asr1.bit._A20
#define ASR1_A19 asr1.bit._A19
#define ASR1_A18 asr1.bit._A18
#define ASR1_A17 asr1.bit._A17
#define ASR1_A16 asr1.bit._A16
__IO_EXTERN ACR1STR acr1;  
#define ACR1 acr1.word
#define ACR1_ASZ3 acr1.bit._ASZ3
#define ACR1_ASZ2 acr1.bit._ASZ2
#define ACR1_ASZ1 acr1.bit._ASZ1
#define ACR1_ASZ0 acr1.bit._ASZ0
#define ACR1_DBW1 acr1.bit._DBW1
#define ACR1_DBW0 acr1.bit._DBW0
#define ACR1_BST1 acr1.bit._BST1
#define ACR1_BST0 acr1.bit._BST0
#define ACR1_SREN acr1.bit._SREN
#define ACR1_PFEN acr1.bit._PFEN
#define ACR1_WREN acr1.bit._WREN
#define ACR1_LEND acr1.bit._LEND
#define ACR1_TYP3 acr1.bit._TYP3
#define ACR1_TYP2 acr1.bit._TYP2
#define ACR1_TYP1 acr1.bit._TYP1
#define ACR1_TYP0 acr1.bit._TYP0
#define ACR1_ASZ acr1.bitc._ASZ
#define ACR1_DBW acr1.bitc._DBW
#define ACR1_BST acr1.bitc._BST
#define ACR1_TYP acr1.bitc._TYP
__IO_EXTERN ASR2STR asr2;  
#define ASR2 asr2.word
#define ASR2_A31 asr2.bit._A31
#define ASR2_A30 asr2.bit._A30
#define ASR2_A29 asr2.bit._A29
#define ASR2_A28 asr2.bit._A28
#define ASR2_A27 asr2.bit._A27
#define ASR2_A26 asr2.bit._A26
#define ASR2_A25 asr2.bit._A25
#define ASR2_A24 asr2.bit._A24
#define ASR2_A23 asr2.bit._A23
#define ASR2_A22 asr2.bit._A22
#define ASR2_A21 asr2.bit._A21
#define ASR2_A20 asr2.bit._A20
#define ASR2_A19 asr2.bit._A19
#define ASR2_A18 asr2.bit._A18
#define ASR2_A17 asr2.bit._A17
#define ASR2_A16 asr2.bit._A16
__IO_EXTERN ACR2STR acr2;  
#define ACR2 acr2.word
#define ACR2_ASZ3 acr2.bit._ASZ3
#define ACR2_ASZ2 acr2.bit._ASZ2
#define ACR2_ASZ1 acr2.bit._ASZ1
#define ACR2_ASZ0 acr2.bit._ASZ0
#define ACR2_DBW1 acr2.bit._DBW1
#define ACR2_DBW0 acr2.bit._DBW0
#define ACR2_BST1 acr2.bit._BST1
#define ACR2_BST0 acr2.bit._BST0
#define ACR2_SREN acr2.bit._SREN
#define ACR2_PFEN acr2.bit._PFEN
#define ACR2_WREN acr2.bit._WREN
#define ACR2_LEND acr2.bit._LEND
#define ACR2_TYP3 acr2.bit._TYP3
#define ACR2_TYP2 acr2.bit._TYP2
#define ACR2_TYP1 acr2.bit._TYP1
#define ACR2_TYP0 acr2.bit._TYP0
#define ACR2_ASZ acr2.bitc._ASZ
#define ACR2_DBW acr2.bitc._DBW
#define ACR2_BST acr2.bitc._BST
#define ACR2_TYP acr2.bitc._TYP
__IO_EXTERN ASR3STR asr3;  
#define ASR3 asr3.word
#define ASR3_A31 asr3.bit._A31
#define ASR3_A30 asr3.bit._A30
#define ASR3_A29 asr3.bit._A29
#define ASR3_A28 asr3.bit._A28
#define ASR3_A27 asr3.bit._A27
#define ASR3_A26 asr3.bit._A26
#define ASR3_A25 asr3.bit._A25
#define ASR3_A24 asr3.bit._A24
#define ASR3_A23 asr3.bit._A23
#define ASR3_A22 asr3.bit._A22
#define ASR3_A21 asr3.bit._A21
#define ASR3_A20 asr3.bit._A20
#define ASR3_A19 asr3.bit._A19
#define ASR3_A18 asr3.bit._A18
#define ASR3_A17 asr3.bit._A17
#define ASR3_A16 asr3.bit._A16
__IO_EXTERN ACR3STR acr3;  
#define ACR3 acr3.word
#define ACR3_ASZ3 acr3.bit._ASZ3
#define ACR3_ASZ2 acr3.bit._ASZ2
#define ACR3_ASZ1 acr3.bit._ASZ1
#define ACR3_ASZ0 acr3.bit._ASZ0
#define ACR3_DBW1 acr3.bit._DBW1
#define ACR3_DBW0 acr3.bit._DBW0
#define ACR3_BST1 acr3.bit._BST1
#define ACR3_BST0 acr3.bit._BST0
#define ACR3_SREN acr3.bit._SREN
#define ACR3_PFEN acr3.bit._PFEN
#define ACR3_WREN acr3.bit._WREN
#define ACR3_LEND acr3.bit._LEND
#define ACR3_TYP3 acr3.bit._TYP3
#define ACR3_TYP2 acr3.bit._TYP2
#define ACR3_TYP1 acr3.bit._TYP1
#define ACR3_TYP0 acr3.bit._TYP0
#define ACR3_ASZ acr3.bitc._ASZ
#define ACR3_DBW acr3.bitc._DBW
#define ACR3_BST acr3.bitc._BST
#define ACR3_TYP acr3.bitc._TYP
__IO_EXTERN ASR4STR asr4;  
#define ASR4 asr4.word
#define ASR4_A31 asr4.bit._A31
#define ASR4_A30 asr4.bit._A30
#define ASR4_A29 asr4.bit._A29
#define ASR4_A28 asr4.bit._A28
#define ASR4_A27 asr4.bit._A27
#define ASR4_A26 asr4.bit._A26
#define ASR4_A25 asr4.bit._A25
#define ASR4_A24 asr4.bit._A24
#define ASR4_A23 asr4.bit._A23
#define ASR4_A22 asr4.bit._A22
#define ASR4_A21 asr4.bit._A21
#define ASR4_A20 asr4.bit._A20
#define ASR4_A19 asr4.bit._A19
#define ASR4_A18 asr4.bit._A18
#define ASR4_A17 asr4.bit._A17
#define ASR4_A16 asr4.bit._A16
__IO_EXTERN ACR4STR acr4;  
#define ACR4 acr4.word
#define ACR4_ASZ3 acr4.bit._ASZ3
#define ACR4_ASZ2 acr4.bit._ASZ2
#define ACR4_ASZ1 acr4.bit._ASZ1
#define ACR4_ASZ0 acr4.bit._ASZ0
#define ACR4_DBW1 acr4.bit._DBW1
#define ACR4_DBW0 acr4.bit._DBW0
#define ACR4_BST1 acr4.bit._BST1
#define ACR4_BST0 acr4.bit._BST0
#define ACR4_SREN acr4.bit._SREN
#define ACR4_PFEN acr4.bit._PFEN
#define ACR4_WREN acr4.bit._WREN
#define ACR4_LEND acr4.bit._LEND
#define ACR4_TYP3 acr4.bit._TYP3
#define ACR4_TYP2 acr4.bit._TYP2
#define ACR4_TYP1 acr4.bit._TYP1
#define ACR4_TYP0 acr4.bit._TYP0
#define ACR4_ASZ acr4.bitc._ASZ
#define ACR4_DBW acr4.bitc._DBW
#define ACR4_BST acr4.bitc._BST
#define ACR4_TYP acr4.bitc._TYP
__IO_EXTERN ASR5STR asr5;  
#define ASR5 asr5.word
#define ASR5_A31 asr5.bit._A31
#define ASR5_A30 asr5.bit._A30
#define ASR5_A29 asr5.bit._A29
#define ASR5_A28 asr5.bit._A28
#define ASR5_A27 asr5.bit._A27
#define ASR5_A26 asr5.bit._A26
#define ASR5_A25 asr5.bit._A25
#define ASR5_A24 asr5.bit._A24
#define ASR5_A23 asr5.bit._A23
#define ASR5_A22 asr5.bit._A22
#define ASR5_A21 asr5.bit._A21
#define ASR5_A20 asr5.bit._A20
#define ASR5_A19 asr5.bit._A19
#define ASR5_A18 asr5.bit._A18
#define ASR5_A17 asr5.bit._A17
#define ASR5_A16 asr5.bit._A16
__IO_EXTERN ACR5STR acr5;  
#define ACR5 acr5.word
#define ACR5_ASZ3 acr5.bit._ASZ3
#define ACR5_ASZ2 acr5.bit._ASZ2
#define ACR5_ASZ1 acr5.bit._ASZ1
#define ACR5_ASZ0 acr5.bit._ASZ0
#define ACR5_DBW1 acr5.bit._DBW1
#define ACR5_DBW0 acr5.bit._DBW0
#define ACR5_BST1 acr5.bit._BST1
#define ACR5_BST0 acr5.bit._BST0
#define ACR5_SREN acr5.bit._SREN
#define ACR5_PFEN acr5.bit._PFEN
#define ACR5_WREN acr5.bit._WREN
#define ACR5_LEND acr5.bit._LEND
#define ACR5_TYP3 acr5.bit._TYP3
#define ACR5_TYP2 acr5.bit._TYP2
#define ACR5_TYP1 acr5.bit._TYP1
#define ACR5_TYP0 acr5.bit._TYP0
#define ACR5_ASZ acr5.bitc._ASZ
#define ACR5_DBW acr5.bitc._DBW
#define ACR5_BST acr5.bitc._BST
#define ACR5_TYP acr5.bitc._TYP
__IO_EXTERN ASR6STR asr6;  
#define ASR6 asr6.word
#define ASR6_A31 asr6.bit._A31
#define ASR6_A30 asr6.bit._A30
#define ASR6_A29 asr6.bit._A29
#define ASR6_A28 asr6.bit._A28
#define ASR6_A27 asr6.bit._A27
#define ASR6_A26 asr6.bit._A26
#define ASR6_A25 asr6.bit._A25
#define ASR6_A24 asr6.bit._A24
#define ASR6_A23 asr6.bit._A23
#define ASR6_A22 asr6.bit._A22
#define ASR6_A21 asr6.bit._A21
#define ASR6_A20 asr6.bit._A20
#define ASR6_A19 asr6.bit._A19
#define ASR6_A18 asr6.bit._A18
#define ASR6_A17 asr6.bit._A17
#define ASR6_A16 asr6.bit._A16
__IO_EXTERN ACR6STR acr6;  
#define ACR6 acr6.word
#define ACR6_ASZ3 acr6.bit._ASZ3
#define ACR6_ASZ2 acr6.bit._ASZ2
#define ACR6_ASZ1 acr6.bit._ASZ1
#define ACR6_ASZ0 acr6.bit._ASZ0
#define ACR6_DBW1 acr6.bit._DBW1
#define ACR6_DBW0 acr6.bit._DBW0
#define ACR6_BST1 acr6.bit._BST1
#define ACR6_BST0 acr6.bit._BST0
#define ACR6_SREN acr6.bit._SREN
#define ACR6_PFEN acr6.bit._PFEN
#define ACR6_WREN acr6.bit._WREN
#define ACR6_LEND acr6.bit._LEND
#define ACR6_TYP3 acr6.bit._TYP3
#define ACR6_TYP2 acr6.bit._TYP2
#define ACR6_TYP1 acr6.bit._TYP1
#define ACR6_TYP0 acr6.bit._TYP0
#define ACR6_ASZ acr6.bitc._ASZ
#define ACR6_DBW acr6.bitc._DBW
#define ACR6_BST acr6.bitc._BST
#define ACR6_TYP acr6.bitc._TYP
__IO_EXTERN ASR7STR asr7;  
#define ASR7 asr7.word
#define ASR7_A31 asr7.bit._A31
#define ASR7_A30 asr7.bit._A30
#define ASR7_A29 asr7.bit._A29
#define ASR7_A28 asr7.bit._A28
#define ASR7_A27 asr7.bit._A27
#define ASR7_A26 asr7.bit._A26
#define ASR7_A25 asr7.bit._A25
#define ASR7_A24 asr7.bit._A24
#define ASR7_A23 asr7.bit._A23
#define ASR7_A22 asr7.bit._A22
#define ASR7_A21 asr7.bit._A21
#define ASR7_A20 asr7.bit._A20
#define ASR7_A19 asr7.bit._A19
#define ASR7_A18 asr7.bit._A18
#define ASR7_A17 asr7.bit._A17
#define ASR7_A16 asr7.bit._A16
__IO_EXTERN ACR7STR acr7;  
#define ACR7 acr7.word
#define ACR7_ASZ3 acr7.bit._ASZ3
#define ACR7_ASZ2 acr7.bit._ASZ2
#define ACR7_ASZ1 acr7.bit._ASZ1
#define ACR7_ASZ0 acr7.bit._ASZ0
#define ACR7_DBW1 acr7.bit._DBW1
#define ACR7_DBW0 acr7.bit._DBW0
#define ACR7_BST1 acr7.bit._BST1
#define ACR7_BST0 acr7.bit._BST0
#define ACR7_SREN acr7.bit._SREN
#define ACR7_PFEN acr7.bit._PFEN
#define ACR7_WREN acr7.bit._WREN
#define ACR7_LEND acr7.bit._LEND
#define ACR7_TYP3 acr7.bit._TYP3
#define ACR7_TYP2 acr7.bit._TYP2
#define ACR7_TYP1 acr7.bit._TYP1
#define ACR7_TYP0 acr7.bit._TYP0
#define ACR7_ASZ acr7.bitc._ASZ
#define ACR7_DBW acr7.bitc._DBW
#define ACR7_BST acr7.bitc._BST
#define ACR7_TYP acr7.bitc._TYP
__IO_EXTERN AWR0STR awr0;  
#define AWR0 awr0.word
#define AWR0_W15 awr0.bit._W15
#define AWR0_W14 awr0.bit._W14
#define AWR0_W13 awr0.bit._W13
#define AWR0_W12 awr0.bit._W12
#define AWR0_W11 awr0.bit._W11
#define AWR0_W10 awr0.bit._W10
#define AWR0_W9 awr0.bit._W9
#define AWR0_W8 awr0.bit._W8
#define AWR0_W7 awr0.bit._W7
#define AWR0_W6 awr0.bit._W6
#define AWR0_W5 awr0.bit._W5
#define AWR0_W4 awr0.bit._W4
#define AWR0_W3 awr0.bit._W3
#define AWR0_W2 awr0.bit._W2
#define AWR0_W1 awr0.bit._W1
#define AWR0_W0 awr0.bit._W0
__IO_EXTERN AWR1STR awr1;  
#define AWR1 awr1.word
#define AWR1_W15 awr1.bit._W15
#define AWR1_W14 awr1.bit._W14
#define AWR1_W13 awr1.bit._W13
#define AWR1_W12 awr1.bit._W12
#define AWR1_W11 awr1.bit._W11
#define AWR1_W10 awr1.bit._W10
#define AWR1_W9 awr1.bit._W9
#define AWR1_W8 awr1.bit._W8
#define AWR1_W7 awr1.bit._W7
#define AWR1_W6 awr1.bit._W6
#define AWR1_W5 awr1.bit._W5
#define AWR1_W4 awr1.bit._W4
#define AWR1_W3 awr1.bit._W3
#define AWR1_W2 awr1.bit._W2
#define AWR1_W1 awr1.bit._W1
#define AWR1_W0 awr1.bit._W0
__IO_EXTERN AWR2STR awr2;  
#define AWR2 awr2.word
#define AWR2_W15 awr2.bit._W15
#define AWR2_W14 awr2.bit._W14
#define AWR2_W13 awr2.bit._W13
#define AWR2_W12 awr2.bit._W12
#define AWR2_W11 awr2.bit._W11
#define AWR2_W10 awr2.bit._W10
#define AWR2_W9 awr2.bit._W9
#define AWR2_W8 awr2.bit._W8
#define AWR2_W7 awr2.bit._W7
#define AWR2_W6 awr2.bit._W6
#define AWR2_W5 awr2.bit._W5
#define AWR2_W4 awr2.bit._W4
#define AWR2_W3 awr2.bit._W3
#define AWR2_W2 awr2.bit._W2
#define AWR2_W1 awr2.bit._W1
#define AWR2_W0 awr2.bit._W0
__IO_EXTERN AWR3STR awr3;  
#define AWR3 awr3.word
#define AWR3_W15 awr3.bit._W15
#define AWR3_W14 awr3.bit._W14
#define AWR3_W13 awr3.bit._W13
#define AWR3_W12 awr3.bit._W12
#define AWR3_W11 awr3.bit._W11
#define AWR3_W10 awr3.bit._W10
#define AWR3_W9 awr3.bit._W9
#define AWR3_W8 awr3.bit._W8
#define AWR3_W7 awr3.bit._W7
#define AWR3_W6 awr3.bit._W6
#define AWR3_W5 awr3.bit._W5
#define AWR3_W4 awr3.bit._W4
#define AWR3_W3 awr3.bit._W3
#define AWR3_W2 awr3.bit._W2
#define AWR3_W1 awr3.bit._W1
#define AWR3_W0 awr3.bit._W0
__IO_EXTERN AWR4STR awr4;  
#define AWR4 awr4.word
#define AWR4_W15 awr4.bit._W15
#define AWR4_W14 awr4.bit._W14
#define AWR4_W13 awr4.bit._W13
#define AWR4_W12 awr4.bit._W12
#define AWR4_W11 awr4.bit._W11
#define AWR4_W10 awr4.bit._W10
#define AWR4_W9 awr4.bit._W9
#define AWR4_W8 awr4.bit._W8
#define AWR4_W7 awr4.bit._W7
#define AWR4_W6 awr4.bit._W6
#define AWR4_W5 awr4.bit._W5
#define AWR4_W4 awr4.bit._W4
#define AWR4_W3 awr4.bit._W3
#define AWR4_W2 awr4.bit._W2
#define AWR4_W1 awr4.bit._W1
#define AWR4_W0 awr4.bit._W0
__IO_EXTERN AWR5STR awr5;  
#define AWR5 awr5.word
#define AWR5_W15 awr5.bit._W15
#define AWR5_W14 awr5.bit._W14
#define AWR5_W13 awr5.bit._W13
#define AWR5_W12 awr5.bit._W12
#define AWR5_W11 awr5.bit._W11
#define AWR5_W10 awr5.bit._W10
#define AWR5_W9 awr5.bit._W9
#define AWR5_W8 awr5.bit._W8
#define AWR5_W7 awr5.bit._W7
#define AWR5_W6 awr5.bit._W6
#define AWR5_W5 awr5.bit._W5
#define AWR5_W4 awr5.bit._W4
#define AWR5_W3 awr5.bit._W3
#define AWR5_W2 awr5.bit._W2
#define AWR5_W1 awr5.bit._W1
#define AWR5_W0 awr5.bit._W0
__IO_EXTERN AWR6STR awr6;  
#define AWR6 awr6.word
#define AWR6_W15 awr6.bit._W15
#define AWR6_W14 awr6.bit._W14
#define AWR6_W13 awr6.bit._W13
#define AWR6_W12 awr6.bit._W12
#define AWR6_W11 awr6.bit._W11
#define AWR6_W10 awr6.bit._W10
#define AWR6_W9 awr6.bit._W9
#define AWR6_W8 awr6.bit._W8
#define AWR6_W7 awr6.bit._W7
#define AWR6_W6 awr6.bit._W6
#define AWR6_W5 awr6.bit._W5
#define AWR6_W4 awr6.bit._W4
#define AWR6_W3 awr6.bit._W3
#define AWR6_W2 awr6.bit._W2
#define AWR6_W1 awr6.bit._W1
#define AWR6_W0 awr6.bit._W0
__IO_EXTERN AWR7STR awr7;  
#define AWR7 awr7.word
#define AWR7_W15 awr7.bit._W15
#define AWR7_W14 awr7.bit._W14
#define AWR7_W13 awr7.bit._W13
#define AWR7_W12 awr7.bit._W12
#define AWR7_W11 awr7.bit._W11
#define AWR7_W10 awr7.bit._W10
#define AWR7_W9 awr7.bit._W9
#define AWR7_W8 awr7.bit._W8
#define AWR7_W7 awr7.bit._W7
#define AWR7_W6 awr7.bit._W6
#define AWR7_W5 awr7.bit._W5
#define AWR7_W4 awr7.bit._W4
#define AWR7_W3 awr7.bit._W3
#define AWR7_W2 awr7.bit._W2
#define AWR7_W1 awr7.bit._W1
#define AWR7_W0 awr7.bit._W0
__IO_EXTERN MCRASTR mcra;  
#define MCRA mcra.byte
#define MCRA_PSZ2 mcra.bit._PSZ2
#define MCRA_PSZ1 mcra.bit._PSZ1
#define MCRA_PSZ0 mcra.bit._PSZ0
#define MCRA_WBST mcra.bit._WBST
#define MCRA_BANK mcra.bit._BANK
#define MCRA_ABS1 mcra.bit._ABS1
#define MCRA_ABS0 mcra.bit._ABS0
#define MCRA_PSZ mcra.bitc._PSZ
#define MCRA_ABS mcra.bitc._ABS
__IO_EXTERN MCRBSTR mcrb;  
#define MCRB mcrb.byte
#define MCRB_PSZ2 mcrb.bit._PSZ2
#define MCRB_PSZ1 mcrb.bit._PSZ1
#define MCRB_PSZ0 mcrb.bit._PSZ0
#define MCRB_WBST mcrb.bit._WBST
#define MCRB_BANK mcrb.bit._BANK
#define MCRB_ABS1 mcrb.bit._ABS1
#define MCRB_ABS0 mcrb.bit._ABS0
#define MCRB_PSZ mcrb.bitc._PSZ
#define MCRB_ABS mcrb.bitc._ABS
__IO_EXTERN IOWR0STR iowr0;  
#define IOWR0 iowr0.byte
#define IOWR0_RYE0 iowr0.bit._RYE0
#define IOWR0_HLD0 iowr0.bit._HLD0
#define IOWR0_WR01 iowr0.bit._WR01
#define IOWR0_WR00 iowr0.bit._WR00
#define IOWR0_IW03 iowr0.bit._IW03
#define IOWR0_IW02 iowr0.bit._IW02
#define IOWR0_IW01 iowr0.bit._IW01
#define IOWR0_IW00 iowr0.bit._IW00
#define IOWR0_WR0 iowr0.bitc._WR0
#define IOWR0_IW0 iowr0.bitc._IW0
__IO_EXTERN IOWR1STR iowr1;  
#define IOWR1 iowr1.byte
#define IOWR1_RYE1 iowr1.bit._RYE1
#define IOWR1_HLD1 iowr1.bit._HLD1
#define IOWR1_WR11 iowr1.bit._WR11
#define IOWR1_WR10 iowr1.bit._WR10
#define IOWR1_IW13 iowr1.bit._IW13
#define IOWR1_IW12 iowr1.bit._IW12
#define IOWR1_IW11 iowr1.bit._IW11
#define IOWR1_IW10 iowr1.bit._IW10
#define IOWR1_WR1 iowr1.bitc._WR1
#define IOWR1_IW1 iowr1.bitc._IW1
__IO_EXTERN IOWR2STR iowr2;  
#define IOWR2 iowr2.byte
#define IOWR2_RYE2 iowr2.bit._RYE2
#define IOWR2_HLD2 iowr2.bit._HLD2
#define IOWR2_WR21 iowr2.bit._WR21
#define IOWR2_WR20 iowr2.bit._WR20
#define IOWR2_IW23 iowr2.bit._IW23
#define IOWR2_IW22 iowr2.bit._IW22
#define IOWR2_IW21 iowr2.bit._IW21
#define IOWR2_IW20 iowr2.bit._IW20
#define IOWR2_WR2 iowr2.bitc._WR2
#define IOWR2_IW2 iowr2.bitc._IW2
__IO_EXTERN IOWR3STR iowr3;  
#define IOWR3 iowr3.byte
#define IOWR3_RYE3 iowr3.bit._RYE3
#define IOWR3_HLD3 iowr3.bit._HLD3
#define IOWR3_WR31 iowr3.bit._WR31
#define IOWR3_WR30 iowr3.bit._WR30
#define IOWR3_IW33 iowr3.bit._IW33
#define IOWR3_IW32 iowr3.bit._IW32
#define IOWR3_IW31 iowr3.bit._IW31
#define IOWR3_IW30 iowr3.bit._IW30
#define IOWR3_WR3 iowr3.bitc._WR3
#define IOWR3_IW3 iowr3.bitc._IW3
__IO_EXTERN CSERSTR cser;  
#define CSER cser.byte
#define CSER_CSE7 cser.bit._CSE7
#define CSER_CSE6 cser.bit._CSE6
#define CSER_CSE5 cser.bit._CSE5
#define CSER_CSE4 cser.bit._CSE4
#define CSER_CSE3 cser.bit._CSE3
#define CSER_CSE2 cser.bit._CSE2
#define CSER_CSE1 cser.bit._CSE1
#define CSER_CSE0 cser.bit._CSE0
__IO_EXTERN CHERSTR cher;  
#define CHER cher.byte
#define CHER_CHE7 cher.bit._CHE7
#define CHER_CHE6 cher.bit._CHE6
#define CHER_CHE5 cher.bit._CHE5
#define CHER_CHE4 cher.bit._CHE4
#define CHER_CHE3 cher.bit._CHE3
#define CHER_CHE2 cher.bit._CHE2
#define CHER_CHE1 cher.bit._CHE1
#define CHER_CHE0 cher.bit._CHE0
__IO_EXTERN TCRSTR tcr;  
#define TCR tcr.byte
#define TCR_BREN tcr.bit._BREN
#define TCR_PSUS tcr.bit._PSUS
#define TCR_PCLR tcr.bit._PCLR
#define TCR_RDW1 tcr.bit._RDW1
#define TCR_RDW0 tcr.bit._RDW0
#define TCR_RDW tcr.bitc._RDW
__IO_EXTERN RCRSTR rcr;  
#define RCR rcr.word
#define RCR_SELF rcr.bit._SELF
#define RCR_RRLD rcr.bit._RRLD
#define RCR_RFINT5 rcr.bit._RFINT5
#define RCR_RFINT4 rcr.bit._RFINT4
#define RCR_RDINT3 rcr.bit._RDINT3
#define RCR_RFINT2 rcr.bit._RFINT2
#define RCR_RFINT1 rcr.bit._RFINT1
#define RCR_RFINT0 rcr.bit._RFINT0
#define RCR_BRST rcr.bit._BRST
#define RCR_RFC2 rcr.bit._RFC2
#define RCR_RFC1 rcr.bit._RFC1
#define RCR_RFC0 rcr.bit._RFC0
#define RCR_PON rcr.bit._PON
#define RCR_TRC2 rcr.bit._TRC2
#define RCR_TRC1 rcr.bit._TRC1
#define RCR_TRC0 rcr.bit._TRC0
#define RCR_RFINT rcr.bitc._RFINT
#define RCR_RFC rcr.bitc._RFC
#define RCR_TRC rcr.bitc._TRC
__IO_EXTERN MODRSTR modr;   /* Mode Register */
#define MODR modr.byte
#define MODR_ROMA modr.bit._ROMA
#define MODR_WTH1 modr.bit._WTH1
#define MODR_WTH0 modr.bit._WTH0
#define MODR_WTH modr.bitc._WTH
__IO_EXTERN PDRD00STR pdrd00;   /* R-bus Port Data Direct Read Register */
#define PDRD00 pdrd00.byte
#define PDRD00_D7 pdrd00.bit._D7
#define PDRD00_D6 pdrd00.bit._D6
#define PDRD00_D5 pdrd00.bit._D5
#define PDRD00_D4 pdrd00.bit._D4
#define PDRD00_D3 pdrd00.bit._D3
#define PDRD00_D2 pdrd00.bit._D2
#define PDRD00_D1 pdrd00.bit._D1
#define PDRD00_D0 pdrd00.bit._D0
__IO_EXTERN PDRD01STR pdrd01;  
#define PDRD01 pdrd01.byte
#define PDRD01_D7 pdrd01.bit._D7
#define PDRD01_D6 pdrd01.bit._D6
#define PDRD01_D5 pdrd01.bit._D5
#define PDRD01_D4 pdrd01.bit._D4
#define PDRD01_D3 pdrd01.bit._D3
#define PDRD01_D2 pdrd01.bit._D2
#define PDRD01_D1 pdrd01.bit._D1
#define PDRD01_D0 pdrd01.bit._D0
__IO_EXTERN PDRD02STR pdrd02;  
#define PDRD02 pdrd02.byte
#define PDRD02_D7 pdrd02.bit._D7
#define PDRD02_D6 pdrd02.bit._D6
#define PDRD02_D5 pdrd02.bit._D5
#define PDRD02_D4 pdrd02.bit._D4
#define PDRD02_D3 pdrd02.bit._D3
#define PDRD02_D2 pdrd02.bit._D2
#define PDRD02_D1 pdrd02.bit._D1
#define PDRD02_D0 pdrd02.bit._D0
__IO_EXTERN PDRD03STR pdrd03;  
#define PDRD03 pdrd03.byte
#define PDRD03_D7 pdrd03.bit._D7
#define PDRD03_D6 pdrd03.bit._D6
#define PDRD03_D5 pdrd03.bit._D5
#define PDRD03_D4 pdrd03.bit._D4
#define PDRD03_D3 pdrd03.bit._D3
#define PDRD03_D2 pdrd03.bit._D2
#define PDRD03_D1 pdrd03.bit._D1
#define PDRD03_D0 pdrd03.bit._D0
__IO_EXTERN PDRD04STR pdrd04;  
#define PDRD04 pdrd04.byte
#define PDRD04_D1 pdrd04.bit._D1
#define PDRD04_D0 pdrd04.bit._D0
__IO_EXTERN PDRD05STR pdrd05;  
#define PDRD05 pdrd05.byte
#define PDRD05_D7 pdrd05.bit._D7
#define PDRD05_D6 pdrd05.bit._D6
#define PDRD05_D5 pdrd05.bit._D5
#define PDRD05_D4 pdrd05.bit._D4
#define PDRD05_D3 pdrd05.bit._D3
#define PDRD05_D2 pdrd05.bit._D2
#define PDRD05_D1 pdrd05.bit._D1
#define PDRD05_D0 pdrd05.bit._D0
__IO_EXTERN PDRD06STR pdrd06;  
#define PDRD06 pdrd06.byte
#define PDRD06_D7 pdrd06.bit._D7
#define PDRD06_D6 pdrd06.bit._D6
#define PDRD06_D5 pdrd06.bit._D5
#define PDRD06_D4 pdrd06.bit._D4
#define PDRD06_D3 pdrd06.bit._D3
#define PDRD06_D2 pdrd06.bit._D2
#define PDRD06_D1 pdrd06.bit._D1
#define PDRD06_D0 pdrd06.bit._D0
__IO_EXTERN PDRD07STR pdrd07;  
#define PDRD07 pdrd07.byte
#define PDRD07_D7 pdrd07.bit._D7
#define PDRD07_D6 pdrd07.bit._D6
#define PDRD07_D5 pdrd07.bit._D5
#define PDRD07_D4 pdrd07.bit._D4
#define PDRD07_D3 pdrd07.bit._D3
#define PDRD07_D2 pdrd07.bit._D2
#define PDRD07_D1 pdrd07.bit._D1
#define PDRD07_D0 pdrd07.bit._D0
__IO_EXTERN PDRD08STR pdrd08;  
#define PDRD08 pdrd08.byte
#define PDRD08_D7 pdrd08.bit._D7
#define PDRD08_D6 pdrd08.bit._D6
#define PDRD08_D5 pdrd08.bit._D5
#define PDRD08_D4 pdrd08.bit._D4
#define PDRD08_D3 pdrd08.bit._D3
#define PDRD08_D2 pdrd08.bit._D2
#define PDRD08_D1 pdrd08.bit._D1
#define PDRD08_D0 pdrd08.bit._D0
__IO_EXTERN PDRD09STR pdrd09;  
#define PDRD09 pdrd09.byte
#define PDRD09_D7 pdrd09.bit._D7
#define PDRD09_D6 pdrd09.bit._D6
#define PDRD09_D3 pdrd09.bit._D3
#define PDRD09_D2 pdrd09.bit._D2
#define PDRD09_D1 pdrd09.bit._D1
#define PDRD09_D0 pdrd09.bit._D0
__IO_EXTERN PDRD10STR pdrd10;  
#define PDRD10 pdrd10.byte
#define PDRD10_D6 pdrd10.bit._D6
#define PDRD10_D5 pdrd10.bit._D5
#define PDRD10_D4 pdrd10.bit._D4
#define PDRD10_D3 pdrd10.bit._D3
#define PDRD10_D2 pdrd10.bit._D2
#define PDRD10_D1 pdrd10.bit._D1
__IO_EXTERN PDRD13STR pdrd13;  
#define PDRD13 pdrd13.byte
#define PDRD13_D2 pdrd13.bit._D2
#define PDRD13_D1 pdrd13.bit._D1
#define PDRD13_D0 pdrd13.bit._D0
__IO_EXTERN PDRD14STR pdrd14;  
#define PDRD14 pdrd14.byte
#define PDRD14_D7 pdrd14.bit._D7
#define PDRD14_D6 pdrd14.bit._D6
#define PDRD14_D5 pdrd14.bit._D5
#define PDRD14_D4 pdrd14.bit._D4
#define PDRD14_D3 pdrd14.bit._D3
#define PDRD14_D2 pdrd14.bit._D2
#define PDRD14_D1 pdrd14.bit._D1
#define PDRD14_D0 pdrd14.bit._D0
__IO_EXTERN PDRD15STR pdrd15;  
#define PDRD15 pdrd15.byte
#define PDRD15_D3 pdrd15.bit._D3
#define PDRD15_D2 pdrd15.bit._D2
#define PDRD15_D1 pdrd15.bit._D1
#define PDRD15_D0 pdrd15.bit._D0
__IO_EXTERN PDRD16STR pdrd16;  
#define PDRD16 pdrd16.byte
#define PDRD16_D7 pdrd16.bit._D7
#define PDRD16_D6 pdrd16.bit._D6
#define PDRD16_D5 pdrd16.bit._D5
#define PDRD16_D4 pdrd16.bit._D4
#define PDRD16_D3 pdrd16.bit._D3
#define PDRD16_D2 pdrd16.bit._D2
#define PDRD16_D1 pdrd16.bit._D1
#define PDRD16_D0 pdrd16.bit._D0
__IO_EXTERN PDRD17STR pdrd17;  
#define PDRD17 pdrd17.byte
#define PDRD17_D7 pdrd17.bit._D7
#define PDRD17_D6 pdrd17.bit._D6
#define PDRD17_D5 pdrd17.bit._D5
#define PDRD17_D4 pdrd17.bit._D4
__IO_EXTERN PDRD18STR pdrd18;  
#define PDRD18 pdrd18.byte
#define PDRD18_D6 pdrd18.bit._D6
#define PDRD18_D5 pdrd18.bit._D5
#define PDRD18_D4 pdrd18.bit._D4
#define PDRD18_D2 pdrd18.bit._D2
#define PDRD18_D1 pdrd18.bit._D1
#define PDRD18_D0 pdrd18.bit._D0
__IO_EXTERN PDRD19STR pdrd19;  
#define PDRD19 pdrd19.byte
#define PDRD19_D6 pdrd19.bit._D6
#define PDRD19_D5 pdrd19.bit._D5
#define PDRD19_D4 pdrd19.bit._D4
#define PDRD19_D2 pdrd19.bit._D2
#define PDRD19_D1 pdrd19.bit._D1
#define PDRD19_D0 pdrd19.bit._D0
__IO_EXTERN PDRD20STR pdrd20;  
#define PDRD20 pdrd20.byte
#define PDRD20_D2 pdrd20.bit._D2
#define PDRD20_D1 pdrd20.bit._D1
#define PDRD20_D0 pdrd20.bit._D0
__IO_EXTERN PDRD22STR pdrd22;  
#define PDRD22 pdrd22.byte
#define PDRD22_D5 pdrd22.bit._D5
#define PDRD22_D4 pdrd22.bit._D4
#define PDRD22_D2 pdrd22.bit._D2
#define PDRD22_D0 pdrd22.bit._D0
__IO_EXTERN PDRD23STR pdrd23;  
#define PDRD23 pdrd23.byte
#define PDRD23_D5 pdrd23.bit._D5
#define PDRD23_D4 pdrd23.bit._D4
#define PDRD23_D3 pdrd23.bit._D3
#define PDRD23_D2 pdrd23.bit._D2
#define PDRD23_D1 pdrd23.bit._D1
#define PDRD23_D0 pdrd23.bit._D0
__IO_EXTERN PDRD24STR pdrd24;  
#define PDRD24 pdrd24.byte
#define PDRD24_D7 pdrd24.bit._D7
#define PDRD24_D6 pdrd24.bit._D6
#define PDRD24_D5 pdrd24.bit._D5
#define PDRD24_D4 pdrd24.bit._D4
#define PDRD24_D3 pdrd24.bit._D3
#define PDRD24_D2 pdrd24.bit._D2
#define PDRD24_D1 pdrd24.bit._D1
#define PDRD24_D0 pdrd24.bit._D0
__IO_EXTERN PDRD25STR pdrd25;  
#define PDRD25 pdrd25.byte
#define PDRD25_D7 pdrd25.bit._D7
#define PDRD25_D6 pdrd25.bit._D6
#define PDRD25_D5 pdrd25.bit._D5
#define PDRD25_D4 pdrd25.bit._D4
#define PDRD25_D3 pdrd25.bit._D3
#define PDRD25_D2 pdrd25.bit._D2
#define PDRD25_D1 pdrd25.bit._D1
#define PDRD25_D0 pdrd25.bit._D0
__IO_EXTERN PDRD26STR pdrd26;  
#define PDRD26 pdrd26.byte
#define PDRD26_D7 pdrd26.bit._D7
#define PDRD26_D6 pdrd26.bit._D6
#define PDRD26_D5 pdrd26.bit._D5
#define PDRD26_D4 pdrd26.bit._D4
#define PDRD26_D3 pdrd26.bit._D3
#define PDRD26_D2 pdrd26.bit._D2
#define PDRD26_D1 pdrd26.bit._D1
#define PDRD26_D0 pdrd26.bit._D0
__IO_EXTERN PDRD27STR pdrd27;  
#define PDRD27 pdrd27.byte
#define PDRD27_D7 pdrd27.bit._D7
#define PDRD27_D6 pdrd27.bit._D6
#define PDRD27_D5 pdrd27.bit._D5
#define PDRD27_D4 pdrd27.bit._D4
#define PDRD27_D3 pdrd27.bit._D3
#define PDRD27_D2 pdrd27.bit._D2
#define PDRD27_D1 pdrd27.bit._D1
#define PDRD27_D0 pdrd27.bit._D0
__IO_EXTERN PDRD29STR pdrd29;  
#define PDRD29 pdrd29.byte
#define PDRD29_D7 pdrd29.bit._D7
#define PDRD29_D6 pdrd29.bit._D6
#define PDRD29_D5 pdrd29.bit._D5
#define PDRD29_D4 pdrd29.bit._D4
#define PDRD29_D3 pdrd29.bit._D3
#define PDRD29_D2 pdrd29.bit._D2
#define PDRD29_D1 pdrd29.bit._D1
#define PDRD29_D0 pdrd29.bit._D0
__IO_EXTERN DDR00STR ddr00;   /* R-bus Port Direction Register */
#define DDR00 ddr00.byte
#define DDR00_D7 ddr00.bit._D7
#define DDR00_D6 ddr00.bit._D6
#define DDR00_D5 ddr00.bit._D5
#define DDR00_D4 ddr00.bit._D4
#define DDR00_D3 ddr00.bit._D3
#define DDR00_D2 ddr00.bit._D2
#define DDR00_D1 ddr00.bit._D1
#define DDR00_D0 ddr00.bit._D0
__IO_EXTERN DDR01STR ddr01;  
#define DDR01 ddr01.byte
#define DDR01_D7 ddr01.bit._D7
#define DDR01_D6 ddr01.bit._D6
#define DDR01_D5 ddr01.bit._D5
#define DDR01_D4 ddr01.bit._D4
#define DDR01_D3 ddr01.bit._D3
#define DDR01_D2 ddr01.bit._D2
#define DDR01_D1 ddr01.bit._D1
#define DDR01_D0 ddr01.bit._D0
__IO_EXTERN DDR02STR ddr02;  
#define DDR02 ddr02.byte
#define DDR02_D7 ddr02.bit._D7
#define DDR02_D6 ddr02.bit._D6
#define DDR02_D5 ddr02.bit._D5
#define DDR02_D4 ddr02.bit._D4
#define DDR02_D3 ddr02.bit._D3
#define DDR02_D2 ddr02.bit._D2
#define DDR02_D1 ddr02.bit._D1
#define DDR02_D0 ddr02.bit._D0
__IO_EXTERN DDR03STR ddr03;  
#define DDR03 ddr03.byte
#define DDR03_D7 ddr03.bit._D7
#define DDR03_D6 ddr03.bit._D6
#define DDR03_D5 ddr03.bit._D5
#define DDR03_D4 ddr03.bit._D4
#define DDR03_D3 ddr03.bit._D3
#define DDR03_D2 ddr03.bit._D2
#define DDR03_D1 ddr03.bit._D1
#define DDR03_D0 ddr03.bit._D0
__IO_EXTERN DDR04STR ddr04;  
#define DDR04 ddr04.byte
#define DDR04_D1 ddr04.bit._D1
#define DDR04_D0 ddr04.bit._D0
__IO_EXTERN DDR05STR ddr05;  
#define DDR05 ddr05.byte
#define DDR05_D7 ddr05.bit._D7
#define DDR05_D6 ddr05.bit._D6
#define DDR05_D5 ddr05.bit._D5
#define DDR05_D4 ddr05.bit._D4
#define DDR05_D3 ddr05.bit._D3
#define DDR05_D2 ddr05.bit._D2
#define DDR05_D1 ddr05.bit._D1
#define DDR05_D0 ddr05.bit._D0
__IO_EXTERN DDR06STR ddr06;  
#define DDR06 ddr06.byte
#define DDR06_D7 ddr06.bit._D7
#define DDR06_D6 ddr06.bit._D6
#define DDR06_D5 ddr06.bit._D5
#define DDR06_D4 ddr06.bit._D4
#define DDR06_D3 ddr06.bit._D3
#define DDR06_D2 ddr06.bit._D2
#define DDR06_D1 ddr06.bit._D1
#define DDR06_D0 ddr06.bit._D0
__IO_EXTERN DDR07STR ddr07;  
#define DDR07 ddr07.byte
#define DDR07_D7 ddr07.bit._D7
#define DDR07_D6 ddr07.bit._D6
#define DDR07_D5 ddr07.bit._D5
#define DDR07_D4 ddr07.bit._D4
#define DDR07_D3 ddr07.bit._D3
#define DDR07_D2 ddr07.bit._D2
#define DDR07_D1 ddr07.bit._D1
#define DDR07_D0 ddr07.bit._D0
__IO_EXTERN DDR08STR ddr08;  
#define DDR08 ddr08.byte
#define DDR08_D7 ddr08.bit._D7
#define DDR08_D6 ddr08.bit._D6
#define DDR08_D5 ddr08.bit._D5
#define DDR08_D4 ddr08.bit._D4
#define DDR08_D3 ddr08.bit._D3
#define DDR08_D2 ddr08.bit._D2
#define DDR08_D1 ddr08.bit._D1
#define DDR08_D0 ddr08.bit._D0
__IO_EXTERN DDR09STR ddr09;  
#define DDR09 ddr09.byte
#define DDR09_D7 ddr09.bit._D7
#define DDR09_D6 ddr09.bit._D6
#define DDR09_D3 ddr09.bit._D3
#define DDR09_D2 ddr09.bit._D2
#define DDR09_D1 ddr09.bit._D1
#define DDR09_D0 ddr09.bit._D0
__IO_EXTERN DDR10STR ddr10;  
#define DDR10 ddr10.byte
#define DDR10_D6 ddr10.bit._D6
#define DDR10_D5 ddr10.bit._D5
#define DDR10_D4 ddr10.bit._D4
#define DDR10_D3 ddr10.bit._D3
#define DDR10_D2 ddr10.bit._D2
#define DDR10_D1 ddr10.bit._D1
__IO_EXTERN DDR13STR ddr13;  
#define DDR13 ddr13.byte
#define DDR13_D2 ddr13.bit._D2
#define DDR13_D1 ddr13.bit._D1
#define DDR13_D0 ddr13.bit._D0
__IO_EXTERN DDR14STR ddr14;  
#define DDR14 ddr14.byte
#define DDR14_D7 ddr14.bit._D7
#define DDR14_D6 ddr14.bit._D6
#define DDR14_D5 ddr14.bit._D5
#define DDR14_D4 ddr14.bit._D4
#define DDR14_D3 ddr14.bit._D3
#define DDR14_D2 ddr14.bit._D2
#define DDR14_D1 ddr14.bit._D1
#define DDR14_D0 ddr14.bit._D0
__IO_EXTERN DDR15STR ddr15;  
#define DDR15 ddr15.byte
#define DDR15_D3 ddr15.bit._D3
#define DDR15_D2 ddr15.bit._D2
#define DDR15_D1 ddr15.bit._D1
#define DDR15_D0 ddr15.bit._D0
__IO_EXTERN DDR16STR ddr16;  
#define DDR16 ddr16.byte
#define DDR16_D7 ddr16.bit._D7
#define DDR16_D6 ddr16.bit._D6
#define DDR16_D5 ddr16.bit._D5
#define DDR16_D4 ddr16.bit._D4
#define DDR16_D3 ddr16.bit._D3
#define DDR16_D2 ddr16.bit._D2
#define DDR16_D1 ddr16.bit._D1
#define DDR16_D0 ddr16.bit._D0
__IO_EXTERN DDR17STR ddr17;  
#define DDR17 ddr17.byte
#define DDR17_D7 ddr17.bit._D7
#define DDR17_D6 ddr17.bit._D6
#define DDR17_D5 ddr17.bit._D5
#define DDR17_D4 ddr17.bit._D4
__IO_EXTERN DDR18STR ddr18;  
#define DDR18 ddr18.byte
#define DDR18_D6 ddr18.bit._D6
#define DDR18_D5 ddr18.bit._D5
#define DDR18_D4 ddr18.bit._D4
#define DDR18_D2 ddr18.bit._D2
#define DDR18_D1 ddr18.bit._D1
#define DDR18_D0 ddr18.bit._D0
__IO_EXTERN DDR19STR ddr19;  
#define DDR19 ddr19.byte
#define DDR19_D6 ddr19.bit._D6
#define DDR19_D5 ddr19.bit._D5
#define DDR19_D4 ddr19.bit._D4
#define DDR19_D2 ddr19.bit._D2
#define DDR19_D1 ddr19.bit._D1
#define DDR19_D0 ddr19.bit._D0
__IO_EXTERN DDR20STR ddr20;  
#define DDR20 ddr20.byte
#define DDR20_D2 ddr20.bit._D2
#define DDR20_D1 ddr20.bit._D1
#define DDR20_D0 ddr20.bit._D0
__IO_EXTERN DDR22STR ddr22;  
#define DDR22 ddr22.byte
#define DDR22_D5 ddr22.bit._D5
#define DDR22_D4 ddr22.bit._D4
#define DDR22_D2 ddr22.bit._D2
#define DDR22_D0 ddr22.bit._D0
__IO_EXTERN DDR23STR ddr23;  
#define DDR23 ddr23.byte
#define DDR23_D5 ddr23.bit._D5
#define DDR23_D4 ddr23.bit._D4
#define DDR23_D3 ddr23.bit._D3
#define DDR23_D2 ddr23.bit._D2
#define DDR23_D1 ddr23.bit._D1
#define DDR23_D0 ddr23.bit._D0
__IO_EXTERN DDR24STR ddr24;  
#define DDR24 ddr24.byte
#define DDR24_D7 ddr24.bit._D7
#define DDR24_D6 ddr24.bit._D6
#define DDR24_D5 ddr24.bit._D5
#define DDR24_D4 ddr24.bit._D4
#define DDR24_D3 ddr24.bit._D3
#define DDR24_D2 ddr24.bit._D2
#define DDR24_D1 ddr24.bit._D1
#define DDR24_D0 ddr24.bit._D0
__IO_EXTERN DDR25STR ddr25;  
#define DDR25 ddr25.byte
#define DDR25_D7 ddr25.bit._D7
#define DDR25_D6 ddr25.bit._D6
#define DDR25_D5 ddr25.bit._D5
#define DDR25_D4 ddr25.bit._D4
#define DDR25_D3 ddr25.bit._D3
#define DDR25_D2 ddr25.bit._D2
#define DDR25_D1 ddr25.bit._D1
#define DDR25_D0 ddr25.bit._D0
__IO_EXTERN DDR26STR ddr26;  
#define DDR26 ddr26.byte
#define DDR26_D7 ddr26.bit._D7
#define DDR26_D6 ddr26.bit._D6
#define DDR26_D5 ddr26.bit._D5
#define DDR26_D4 ddr26.bit._D4
#define DDR26_D3 ddr26.bit._D3
#define DDR26_D2 ddr26.bit._D2
#define DDR26_D1 ddr26.bit._D1
#define DDR26_D0 ddr26.bit._D0
__IO_EXTERN DDR27STR ddr27;  
#define DDR27 ddr27.byte
#define DDR27_D7 ddr27.bit._D7
#define DDR27_D6 ddr27.bit._D6
#define DDR27_D5 ddr27.bit._D5
#define DDR27_D4 ddr27.bit._D4
#define DDR27_D3 ddr27.bit._D3
#define DDR27_D2 ddr27.bit._D2
#define DDR27_D1 ddr27.bit._D1
#define DDR27_D0 ddr27.bit._D0
__IO_EXTERN DDR29STR ddr29;  
#define DDR29 ddr29.byte
#define DDR29_D7 ddr29.bit._D7
#define DDR29_D6 ddr29.bit._D6
#define DDR29_D5 ddr29.bit._D5
#define DDR29_D4 ddr29.bit._D4
#define DDR29_D3 ddr29.bit._D3
#define DDR29_D2 ddr29.bit._D2
#define DDR29_D1 ddr29.bit._D1
#define DDR29_D0 ddr29.bit._D0
__IO_EXTERN PFR00STR pfr00;   /* R-bus Port Function Register */
#define PFR00 pfr00.byte
#define PFR00_D7 pfr00.bit._D7
#define PFR00_D6 pfr00.bit._D6
#define PFR00_D5 pfr00.bit._D5
#define PFR00_D4 pfr00.bit._D4
#define PFR00_D3 pfr00.bit._D3
#define PFR00_D2 pfr00.bit._D2
#define PFR00_D1 pfr00.bit._D1
#define PFR00_D0 pfr00.bit._D0
__IO_EXTERN PFR01STR pfr01;  
#define PFR01 pfr01.byte
#define PFR01_D7 pfr01.bit._D7
#define PFR01_D6 pfr01.bit._D6
#define PFR01_D5 pfr01.bit._D5
#define PFR01_D4 pfr01.bit._D4
#define PFR01_D3 pfr01.bit._D3
#define PFR01_D2 pfr01.bit._D2
#define PFR01_D1 pfr01.bit._D1
#define PFR01_D0 pfr01.bit._D0
__IO_EXTERN PFR02STR pfr02;  
#define PFR02 pfr02.byte
#define PFR02_D7 pfr02.bit._D7
#define PFR02_D6 pfr02.bit._D6
#define PFR02_D5 pfr02.bit._D5
#define PFR02_D4 pfr02.bit._D4
#define PFR02_D3 pfr02.bit._D3
#define PFR02_D2 pfr02.bit._D2
#define PFR02_D1 pfr02.bit._D1
#define PFR02_D0 pfr02.bit._D0
__IO_EXTERN PFR03STR pfr03;  
#define PFR03 pfr03.byte
#define PFR03_D7 pfr03.bit._D7
#define PFR03_D6 pfr03.bit._D6
#define PFR03_D5 pfr03.bit._D5
#define PFR03_D4 pfr03.bit._D4
#define PFR03_D3 pfr03.bit._D3
#define PFR03_D2 pfr03.bit._D2
#define PFR03_D1 pfr03.bit._D1
#define PFR03_D0 pfr03.bit._D0
__IO_EXTERN PFR04STR pfr04;  
#define PFR04 pfr04.byte
#define PFR04_D1 pfr04.bit._D1
#define PFR04_D0 pfr04.bit._D0
__IO_EXTERN PFR05STR pfr05;  
#define PFR05 pfr05.byte
#define PFR05_D7 pfr05.bit._D7
#define PFR05_D6 pfr05.bit._D6
#define PFR05_D5 pfr05.bit._D5
#define PFR05_D4 pfr05.bit._D4
#define PFR05_D3 pfr05.bit._D3
#define PFR05_D2 pfr05.bit._D2
#define PFR05_D1 pfr05.bit._D1
#define PFR05_D0 pfr05.bit._D0
__IO_EXTERN PFR06STR pfr06;  
#define PFR06 pfr06.byte
#define PFR06_D7 pfr06.bit._D7
#define PFR06_D6 pfr06.bit._D6
#define PFR06_D5 pfr06.bit._D5
#define PFR06_D4 pfr06.bit._D4
#define PFR06_D3 pfr06.bit._D3
#define PFR06_D2 pfr06.bit._D2
#define PFR06_D1 pfr06.bit._D1
#define PFR06_D0 pfr06.bit._D0
__IO_EXTERN PFR07STR pfr07;  
#define PFR07 pfr07.byte
#define PFR07_D7 pfr07.bit._D7
#define PFR07_D6 pfr07.bit._D6
#define PFR07_D5 pfr07.bit._D5
#define PFR07_D4 pfr07.bit._D4
#define PFR07_D3 pfr07.bit._D3
#define PFR07_D2 pfr07.bit._D2
#define PFR07_D1 pfr07.bit._D1
#define PFR07_D0 pfr07.bit._D0
__IO_EXTERN PFR08STR pfr08;  
#define PFR08 pfr08.byte
#define PFR08_D7 pfr08.bit._D7
#define PFR08_D6 pfr08.bit._D6
#define PFR08_D5 pfr08.bit._D5
#define PFR08_D4 pfr08.bit._D4
#define PFR08_D3 pfr08.bit._D3
#define PFR08_D2 pfr08.bit._D2
#define PFR08_D1 pfr08.bit._D1
#define PFR08_D0 pfr08.bit._D0
__IO_EXTERN PFR09STR pfr09;  
#define PFR09 pfr09.byte
#define PFR09_D7 pfr09.bit._D7
#define PFR09_D6 pfr09.bit._D6
#define PFR09_D3 pfr09.bit._D3
#define PFR09_D2 pfr09.bit._D2
#define PFR09_D1 pfr09.bit._D1
#define PFR09_D0 pfr09.bit._D0
__IO_EXTERN PFR10STR pfr10;  
#define PFR10 pfr10.byte
#define PFR10_D6 pfr10.bit._D6
#define PFR10_D5 pfr10.bit._D5
#define PFR10_D4 pfr10.bit._D4
#define PFR10_D3 pfr10.bit._D3
#define PFR10_D2 pfr10.bit._D2
#define PFR10_D1 pfr10.bit._D1
__IO_EXTERN PFR13STR pfr13;  
#define PFR13 pfr13.byte
#define PFR13_D2 pfr13.bit._D2
#define PFR13_D1 pfr13.bit._D1
#define PFR13_D0 pfr13.bit._D0
__IO_EXTERN PFR14STR pfr14;  
#define PFR14 pfr14.byte
#define PFR14_D7 pfr14.bit._D7
#define PFR14_D6 pfr14.bit._D6
#define PFR14_D5 pfr14.bit._D5
#define PFR14_D4 pfr14.bit._D4
#define PFR14_D3 pfr14.bit._D3
#define PFR14_D2 pfr14.bit._D2
#define PFR14_D1 pfr14.bit._D1
#define PFR14_D0 pfr14.bit._D0
__IO_EXTERN PFR15STR pfr15;  
#define PFR15 pfr15.byte
#define PFR15_D3 pfr15.bit._D3
#define PFR15_D2 pfr15.bit._D2
#define PFR15_D1 pfr15.bit._D1
#define PFR15_D0 pfr15.bit._D0
__IO_EXTERN PFR16STR pfr16;  
#define PFR16 pfr16.byte
#define PFR16_D7 pfr16.bit._D7
#define PFR16_D6 pfr16.bit._D6
#define PFR16_D5 pfr16.bit._D5
#define PFR16_D4 pfr16.bit._D4
#define PFR16_D3 pfr16.bit._D3
#define PFR16_D2 pfr16.bit._D2
#define PFR16_D1 pfr16.bit._D1
#define PFR16_D0 pfr16.bit._D0
__IO_EXTERN PFR17STR pfr17;  
#define PFR17 pfr17.byte
#define PFR17_D7 pfr17.bit._D7
#define PFR17_D6 pfr17.bit._D6
#define PFR17_D5 pfr17.bit._D5
#define PFR17_D4 pfr17.bit._D4
__IO_EXTERN PFR18STR pfr18;  
#define PFR18 pfr18.byte
#define PFR18_D6 pfr18.bit._D6
#define PFR18_D5 pfr18.bit._D5
#define PFR18_D4 pfr18.bit._D4
#define PFR18_D2 pfr18.bit._D2
#define PFR18_D1 pfr18.bit._D1
#define PFR18_D0 pfr18.bit._D0
__IO_EXTERN PFR19STR pfr19;  
#define PFR19 pfr19.byte
#define PFR19_D6 pfr19.bit._D6
#define PFR19_D5 pfr19.bit._D5
#define PFR19_D4 pfr19.bit._D4
#define PFR19_D2 pfr19.bit._D2
#define PFR19_D1 pfr19.bit._D1
#define PFR19_D0 pfr19.bit._D0
__IO_EXTERN PFR20STR pfr20;  
#define PFR20 pfr20.byte
#define PFR20_D2 pfr20.bit._D2
#define PFR20_D1 pfr20.bit._D1
#define PFR20_D0 pfr20.bit._D0
__IO_EXTERN PFR22STR pfr22;  
#define PFR22 pfr22.byte
#define PFR22_D5 pfr22.bit._D5
#define PFR22_D4 pfr22.bit._D4
#define PFR22_D2 pfr22.bit._D2
#define PFR22_D0 pfr22.bit._D0
__IO_EXTERN PFR23STR pfr23;  
#define PFR23 pfr23.byte
#define PFR23_D5 pfr23.bit._D5
#define PFR23_D4 pfr23.bit._D4
#define PFR23_D3 pfr23.bit._D3
#define PFR23_D2 pfr23.bit._D2
#define PFR23_D1 pfr23.bit._D1
#define PFR23_D0 pfr23.bit._D0
__IO_EXTERN PFR24STR pfr24;  
#define PFR24 pfr24.byte
#define PFR24_D7 pfr24.bit._D7
#define PFR24_D6 pfr24.bit._D6
#define PFR24_D5 pfr24.bit._D5
#define PFR24_D4 pfr24.bit._D4
#define PFR24_D3 pfr24.bit._D3
#define PFR24_D2 pfr24.bit._D2
#define PFR24_D1 pfr24.bit._D1
#define PFR24_D0 pfr24.bit._D0
__IO_EXTERN PFR25STR pfr25;  
#define PFR25 pfr25.byte
#define PFR25_D7 pfr25.bit._D7
#define PFR25_D6 pfr25.bit._D6
#define PFR25_D5 pfr25.bit._D5
#define PFR25_D4 pfr25.bit._D4
#define PFR25_D3 pfr25.bit._D3
#define PFR25_D2 pfr25.bit._D2
#define PFR25_D1 pfr25.bit._D1
#define PFR25_D0 pfr25.bit._D0
__IO_EXTERN PFR26STR pfr26;  
#define PFR26 pfr26.byte
#define PFR26_D7 pfr26.bit._D7
#define PFR26_D6 pfr26.bit._D6
#define PFR26_D5 pfr26.bit._D5
#define PFR26_D4 pfr26.bit._D4
#define PFR26_D3 pfr26.bit._D3
#define PFR26_D2 pfr26.bit._D2
#define PFR26_D1 pfr26.bit._D1
#define PFR26_D0 pfr26.bit._D0
__IO_EXTERN PFR27STR pfr27;  
#define PFR27 pfr27.byte
#define PFR27_D7 pfr27.bit._D7
#define PFR27_D6 pfr27.bit._D6
#define PFR27_D5 pfr27.bit._D5
#define PFR27_D4 pfr27.bit._D4
#define PFR27_D3 pfr27.bit._D3
#define PFR27_D2 pfr27.bit._D2
#define PFR27_D1 pfr27.bit._D1
#define PFR27_D0 pfr27.bit._D0
__IO_EXTERN PFR29STR pfr29;  
#define PFR29 pfr29.byte
#define PFR29_D7 pfr29.bit._D7
#define PFR29_D6 pfr29.bit._D6
#define PFR29_D5 pfr29.bit._D5
#define PFR29_D4 pfr29.bit._D4
#define PFR29_D3 pfr29.bit._D3
#define PFR29_D2 pfr29.bit._D2
#define PFR29_D1 pfr29.bit._D1
#define PFR29_D0 pfr29.bit._D0
__IO_EXTERN EPFR10STR epfr10;   /* R-bus Port Extra Function Register */
#define EPFR10 epfr10.byte
#define EPFR10_D5 epfr10.bit._D5
#define EPFR10_D4 epfr10.bit._D4
__IO_EXTERN EPFR13STR epfr13;  
#define EPFR13 epfr13.byte
#define EPFR13_D2 epfr13.bit._D2
__IO_EXTERN EPFR14STR epfr14;  
#define EPFR14 epfr14.byte
#define EPFR14_D7 epfr14.bit._D7
#define EPFR14_D6 epfr14.bit._D6
#define EPFR14_D5 epfr14.bit._D5
#define EPFR14_D4 epfr14.bit._D4
#define EPFR14_D3 epfr14.bit._D3
#define EPFR14_D2 epfr14.bit._D2
#define EPFR14_D1 epfr14.bit._D1
#define EPFR14_D0 epfr14.bit._D0
__IO_EXTERN EPFR15STR epfr15;  
#define EPFR15 epfr15.byte
#define EPFR15_D3 epfr15.bit._D3
#define EPFR15_D2 epfr15.bit._D2
#define EPFR15_D1 epfr15.bit._D1
#define EPFR15_D0 epfr15.bit._D0
__IO_EXTERN EPFR16STR epfr16;  
#define EPFR16 epfr16.byte
#define EPFR16_D7 epfr16.bit._D7
#define EPFR16_D6 epfr16.bit._D6
#define EPFR16_D5 epfr16.bit._D5
#define EPFR16_D4 epfr16.bit._D4
__IO_EXTERN EPFR18STR epfr18;  
#define EPFR18 epfr18.byte
#define EPFR18_D6 epfr18.bit._D6
#define EPFR18_D5 epfr18.bit._D5
#define EPFR18_D4 epfr18.bit._D4
#define EPFR18_D2 epfr18.bit._D2
#define EPFR18_D1 epfr18.bit._D1
#define EPFR18_D0 epfr18.bit._D0
__IO_EXTERN EPFR19STR epfr19;  
#define EPFR19 epfr19.byte
#define EPFR19_D6 epfr19.bit._D6
#define EPFR19_D2 epfr19.bit._D2
__IO_EXTERN EPFR20STR epfr20;  
#define EPFR20 epfr20.byte
#define EPFR20_D2 epfr20.bit._D2
#define EPFR20_D1 epfr20.bit._D1
#define EPFR20_D0 epfr20.bit._D0
__IO_EXTERN EPFR26STR epfr26;  
#define EPFR26 epfr26.byte
#define EPFR26_D7 epfr26.bit._D7
#define EPFR26_D6 epfr26.bit._D6
#define EPFR26_D5 epfr26.bit._D5
#define EPFR26_D4 epfr26.bit._D4
#define EPFR26_D3 epfr26.bit._D3
#define EPFR26_D2 epfr26.bit._D2
#define EPFR26_D1 epfr26.bit._D1
#define EPFR26_D0 epfr26.bit._D0
__IO_EXTERN EPFR27STR epfr27;  
#define EPFR27 epfr27.byte
#define EPFR27_D7 epfr27.bit._D7
#define EPFR27_D6 epfr27.bit._D6
#define EPFR27_D5 epfr27.bit._D5
#define EPFR27_D4 epfr27.bit._D4
#define EPFR27_D3 epfr27.bit._D3
#define EPFR27_D2 epfr27.bit._D2
#define EPFR27_D1 epfr27.bit._D1
#define EPFR27_D0 epfr27.bit._D0
__IO_EXTERN PODR00STR podr00;   /* R-bus Port Output Drive Select Register */
#define PODR00 podr00.byte
#define PODR00_D7 podr00.bit._D7
#define PODR00_D6 podr00.bit._D6
#define PODR00_D5 podr00.bit._D5
#define PODR00_D4 podr00.bit._D4
#define PODR00_D3 podr00.bit._D3
#define PODR00_D2 podr00.bit._D2
#define PODR00_D1 podr00.bit._D1
#define PODR00_D0 podr00.bit._D0
__IO_EXTERN PODR01STR podr01;  
#define PODR01 podr01.byte
#define PODR01_D7 podr01.bit._D7
#define PODR01_D6 podr01.bit._D6
#define PODR01_D5 podr01.bit._D5
#define PODR01_D4 podr01.bit._D4
#define PODR01_D3 podr01.bit._D3
#define PODR01_D2 podr01.bit._D2
#define PODR01_D1 podr01.bit._D1
#define PODR01_D0 podr01.bit._D0
__IO_EXTERN PODR02STR podr02;  
#define PODR02 podr02.byte
#define PODR02_D7 podr02.bit._D7
#define PODR02_D6 podr02.bit._D6
#define PODR02_D5 podr02.bit._D5
#define PODR02_D4 podr02.bit._D4
#define PODR02_D3 podr02.bit._D3
#define PODR02_D2 podr02.bit._D2
#define PODR02_D1 podr02.bit._D1
#define PODR02_D0 podr02.bit._D0
__IO_EXTERN PODR03STR podr03;  
#define PODR03 podr03.byte
#define PODR03_D7 podr03.bit._D7
#define PODR03_D6 podr03.bit._D6
#define PODR03_D5 podr03.bit._D5
#define PODR03_D4 podr03.bit._D4
#define PODR03_D3 podr03.bit._D3
#define PODR03_D2 podr03.bit._D2
#define PODR03_D1 podr03.bit._D1
#define PODR03_D0 podr03.bit._D0
__IO_EXTERN PODR04STR podr04;  
#define PODR04 podr04.byte
#define PODR04_D1 podr04.bit._D1
#define PODR04_D0 podr04.bit._D0
__IO_EXTERN PODR05STR podr05;  
#define PODR05 podr05.byte
#define PODR05_D7 podr05.bit._D7
#define PODR05_D6 podr05.bit._D6
#define PODR05_D5 podr05.bit._D5
#define PODR05_D4 podr05.bit._D4
#define PODR05_D3 podr05.bit._D3
#define PODR05_D2 podr05.bit._D2
#define PODR05_D1 podr05.bit._D1
#define PODR05_D0 podr05.bit._D0
__IO_EXTERN PODR06STR podr06;  
#define PODR06 podr06.byte
#define PODR06_D7 podr06.bit._D7
#define PODR06_D6 podr06.bit._D6
#define PODR06_D5 podr06.bit._D5
#define PODR06_D4 podr06.bit._D4
#define PODR06_D3 podr06.bit._D3
#define PODR06_D2 podr06.bit._D2
#define PODR06_D1 podr06.bit._D1
#define PODR06_D0 podr06.bit._D0
__IO_EXTERN PODR07STR podr07;  
#define PODR07 podr07.byte
#define PODR07_D7 podr07.bit._D7
#define PODR07_D6 podr07.bit._D6
#define PODR07_D5 podr07.bit._D5
#define PODR07_D4 podr07.bit._D4
#define PODR07_D3 podr07.bit._D3
#define PODR07_D2 podr07.bit._D2
#define PODR07_D1 podr07.bit._D1
#define PODR07_D0 podr07.bit._D0
__IO_EXTERN PODR08STR podr08;  
#define PODR08 podr08.byte
#define PODR08_D7 podr08.bit._D7
#define PODR08_D6 podr08.bit._D6
#define PODR08_D5 podr08.bit._D5
#define PODR08_D4 podr08.bit._D4
#define PODR08_D3 podr08.bit._D3
#define PODR08_D2 podr08.bit._D2
#define PODR08_D1 podr08.bit._D1
#define PODR08_D0 podr08.bit._D0
__IO_EXTERN PODR09STR podr09;  
#define PODR09 podr09.byte
#define PODR09_D7 podr09.bit._D7
#define PODR09_D6 podr09.bit._D6
#define PODR09_D3 podr09.bit._D3
#define PODR09_D2 podr09.bit._D2
#define PODR09_D1 podr09.bit._D1
#define PODR09_D0 podr09.bit._D0
__IO_EXTERN PODR10STR podr10;  
#define PODR10 podr10.byte
#define PODR10_D6 podr10.bit._D6
#define PODR10_D5 podr10.bit._D5
#define PODR10_D4 podr10.bit._D4
#define PODR10_D3 podr10.bit._D3
#define PODR10_D2 podr10.bit._D2
#define PODR10_D1 podr10.bit._D1
__IO_EXTERN PODR13STR podr13;  
#define PODR13 podr13.byte
#define PODR13_D2 podr13.bit._D2
#define PODR13_D1 podr13.bit._D1
#define PODR13_D0 podr13.bit._D0
__IO_EXTERN PODR14STR podr14;  
#define PODR14 podr14.byte
#define PODR14_D7 podr14.bit._D7
#define PODR14_D6 podr14.bit._D6
#define PODR14_D5 podr14.bit._D5
#define PODR14_D4 podr14.bit._D4
#define PODR14_D3 podr14.bit._D3
#define PODR14_D2 podr14.bit._D2
#define PODR14_D1 podr14.bit._D1
#define PODR14_D0 podr14.bit._D0
__IO_EXTERN PODR15STR podr15;  
#define PODR15 podr15.byte
#define PODR15_D3 podr15.bit._D3
#define PODR15_D2 podr15.bit._D2
#define PODR15_D1 podr15.bit._D1
#define PODR15_D0 podr15.bit._D0
__IO_EXTERN PODR16STR podr16;  
#define PODR16 podr16.byte
#define PODR16_D7 podr16.bit._D7
#define PODR16_D6 podr16.bit._D6
#define PODR16_D5 podr16.bit._D5
#define PODR16_D4 podr16.bit._D4
#define PODR16_D3 podr16.bit._D3
#define PODR16_D2 podr16.bit._D2
#define PODR16_D1 podr16.bit._D1
#define PODR16_D0 podr16.bit._D0
__IO_EXTERN PODR17STR podr17;  
#define PODR17 podr17.byte
#define PODR17_D7 podr17.bit._D7
#define PODR17_D6 podr17.bit._D6
#define PODR17_D5 podr17.bit._D5
#define PODR17_D4 podr17.bit._D4
__IO_EXTERN PODR18STR podr18;  
#define PODR18 podr18.byte
#define PODR18_D6 podr18.bit._D6
#define PODR18_D5 podr18.bit._D5
#define PODR18_D4 podr18.bit._D4
#define PODR18_D2 podr18.bit._D2
#define PODR18_D1 podr18.bit._D1
#define PODR18_D0 podr18.bit._D0
__IO_EXTERN PODR19STR podr19;  
#define PODR19 podr19.byte
#define PODR19_D6 podr19.bit._D6
#define PODR19_D5 podr19.bit._D5
#define PODR19_D4 podr19.bit._D4
#define PODR19_D2 podr19.bit._D2
#define PODR19_D1 podr19.bit._D1
#define PODR19_D0 podr19.bit._D0
__IO_EXTERN PODR20STR podr20;  
#define PODR20 podr20.byte
#define PODR20_D2 podr20.bit._D2
#define PODR20_D1 podr20.bit._D1
#define PODR20_D0 podr20.bit._D0
__IO_EXTERN PODR22STR podr22;  
#define PODR22 podr22.byte
#define PODR22_D5 podr22.bit._D5
#define PODR22_D4 podr22.bit._D4
#define PODR22_D2 podr22.bit._D2
#define PODR22_D0 podr22.bit._D0
__IO_EXTERN PODR23STR podr23;  
#define PODR23 podr23.byte
#define PODR23_D5 podr23.bit._D5
#define PODR23_D4 podr23.bit._D4
#define PODR23_D3 podr23.bit._D3
#define PODR23_D2 podr23.bit._D2
#define PODR23_D1 podr23.bit._D1
#define PODR23_D0 podr23.bit._D0
__IO_EXTERN PODR24STR podr24;  
#define PODR24 podr24.byte
#define PODR24_D7 podr24.bit._D7
#define PODR24_D6 podr24.bit._D6
#define PODR24_D5 podr24.bit._D5
#define PODR24_D4 podr24.bit._D4
#define PODR24_D3 podr24.bit._D3
#define PODR24_D2 podr24.bit._D2
#define PODR24_D1 podr24.bit._D1
#define PODR24_D0 podr24.bit._D0
__IO_EXTERN PODR25STR podr25;  
#define PODR25 podr25.byte
#define PODR25_D7 podr25.bit._D7
#define PODR25_D6 podr25.bit._D6
#define PODR25_D5 podr25.bit._D5
#define PODR25_D4 podr25.bit._D4
#define PODR25_D3 podr25.bit._D3
#define PODR25_D2 podr25.bit._D2
#define PODR25_D1 podr25.bit._D1
#define PODR25_D0 podr25.bit._D0
__IO_EXTERN PODR26STR podr26;  
#define PODR26 podr26.byte
#define PODR26_D7 podr26.bit._D7
#define PODR26_D6 podr26.bit._D6
#define PODR26_D5 podr26.bit._D5
#define PODR26_D4 podr26.bit._D4
#define PODR26_D3 podr26.bit._D3
#define PODR26_D2 podr26.bit._D2
#define PODR26_D1 podr26.bit._D1
#define PODR26_D0 podr26.bit._D0
__IO_EXTERN PODR27STR podr27;  
#define PODR27 podr27.byte
#define PODR27_D7 podr27.bit._D7
#define PODR27_D6 podr27.bit._D6
#define PODR27_D5 podr27.bit._D5
#define PODR27_D4 podr27.bit._D4
#define PODR27_D3 podr27.bit._D3
#define PODR27_D2 podr27.bit._D2
#define PODR27_D1 podr27.bit._D1
#define PODR27_D0 podr27.bit._D0
__IO_EXTERN PODR29STR podr29;  
#define PODR29 podr29.byte
#define PODR29_D7 podr29.bit._D7
#define PODR29_D6 podr29.bit._D6
#define PODR29_D5 podr29.bit._D5
#define PODR29_D4 podr29.bit._D4
#define PODR29_D3 podr29.bit._D3
#define PODR29_D2 podr29.bit._D2
#define PODR29_D1 podr29.bit._D1
#define PODR29_D0 podr29.bit._D0
__IO_EXTERN PILR00STR pilr00;   /* R-bus Port Input Level Select Register */
#define PILR00 pilr00.byte
#define PILR00_D7 pilr00.bit._D7
#define PILR00_D6 pilr00.bit._D6
#define PILR00_D5 pilr00.bit._D5
#define PILR00_D4 pilr00.bit._D4
#define PILR00_D3 pilr00.bit._D3
#define PILR00_D2 pilr00.bit._D2
#define PILR00_D1 pilr00.bit._D1
#define PILR00_D0 pilr00.bit._D0
__IO_EXTERN PILR01STR pilr01;  
#define PILR01 pilr01.byte
#define PILR01_D7 pilr01.bit._D7
#define PILR01_D6 pilr01.bit._D6
#define PILR01_D5 pilr01.bit._D5
#define PILR01_D4 pilr01.bit._D4
#define PILR01_D3 pilr01.bit._D3
#define PILR01_D2 pilr01.bit._D2
#define PILR01_D1 pilr01.bit._D1
#define PILR01_D0 pilr01.bit._D0
__IO_EXTERN PILR02STR pilr02;  
#define PILR02 pilr02.byte
#define PILR02_D7 pilr02.bit._D7
#define PILR02_D6 pilr02.bit._D6
#define PILR02_D5 pilr02.bit._D5
#define PILR02_D4 pilr02.bit._D4
#define PILR02_D3 pilr02.bit._D3
#define PILR02_D2 pilr02.bit._D2
#define PILR02_D1 pilr02.bit._D1
#define PILR02_D0 pilr02.bit._D0
__IO_EXTERN PILR03STR pilr03;  
#define PILR03 pilr03.byte
#define PILR03_D7 pilr03.bit._D7
#define PILR03_D6 pilr03.bit._D6
#define PILR03_D5 pilr03.bit._D5
#define PILR03_D4 pilr03.bit._D4
#define PILR03_D3 pilr03.bit._D3
#define PILR03_D2 pilr03.bit._D2
#define PILR03_D1 pilr03.bit._D1
#define PILR03_D0 pilr03.bit._D0
__IO_EXTERN PILR04STR pilr04;  
#define PILR04 pilr04.byte
#define PILR04_D1 pilr04.bit._D1
#define PILR04_D0 pilr04.bit._D0
__IO_EXTERN PILR05STR pilr05;  
#define PILR05 pilr05.byte
#define PILR05_D7 pilr05.bit._D7
#define PILR05_D6 pilr05.bit._D6
#define PILR05_D5 pilr05.bit._D5
#define PILR05_D4 pilr05.bit._D4
#define PILR05_D3 pilr05.bit._D3
#define PILR05_D2 pilr05.bit._D2
#define PILR05_D1 pilr05.bit._D1
#define PILR05_D0 pilr05.bit._D0
__IO_EXTERN PILR06STR pilr06;  
#define PILR06 pilr06.byte
#define PILR06_D7 pilr06.bit._D7
#define PILR06_D6 pilr06.bit._D6
#define PILR06_D5 pilr06.bit._D5
#define PILR06_D4 pilr06.bit._D4
#define PILR06_D3 pilr06.bit._D3
#define PILR06_D2 pilr06.bit._D2
#define PILR06_D1 pilr06.bit._D1
#define PILR06_D0 pilr06.bit._D0
__IO_EXTERN PILR07STR pilr07;  
#define PILR07 pilr07.byte
#define PILR07_D7 pilr07.bit._D7
#define PILR07_D6 pilr07.bit._D6
#define PILR07_D5 pilr07.bit._D5
#define PILR07_D4 pilr07.bit._D4
#define PILR07_D3 pilr07.bit._D3
#define PILR07_D2 pilr07.bit._D2
#define PILR07_D1 pilr07.bit._D1
#define PILR07_D0 pilr07.bit._D0
__IO_EXTERN PILR08STR pilr08;  
#define PILR08 pilr08.byte
#define PILR08_D7 pilr08.bit._D7
#define PILR08_D6 pilr08.bit._D6
#define PILR08_D5 pilr08.bit._D5
#define PILR08_D4 pilr08.bit._D4
#define PILR08_D3 pilr08.bit._D3
#define PILR08_D2 pilr08.bit._D2
#define PILR08_D1 pilr08.bit._D1
#define PILR08_D0 pilr08.bit._D0
__IO_EXTERN PILR09STR pilr09;  
#define PILR09 pilr09.byte
#define PILR09_D7 pilr09.bit._D7
#define PILR09_D6 pilr09.bit._D6
#define PILR09_D3 pilr09.bit._D3
#define PILR09_D2 pilr09.bit._D2
#define PILR09_D1 pilr09.bit._D1
#define PILR09_D0 pilr09.bit._D0
__IO_EXTERN PILR10STR pilr10;  
#define PILR10 pilr10.byte
#define PILR10_D6 pilr10.bit._D6
#define PILR10_D5 pilr10.bit._D5
#define PILR10_D4 pilr10.bit._D4
#define PILR10_D3 pilr10.bit._D3
#define PILR10_D2 pilr10.bit._D2
#define PILR10_D1 pilr10.bit._D1
__IO_EXTERN PILR13STR pilr13;  
#define PILR13 pilr13.byte
#define PILR13_D2 pilr13.bit._D2
#define PILR13_D1 pilr13.bit._D1
#define PILR13_D0 pilr13.bit._D0
__IO_EXTERN PILR14STR pilr14;  
#define PILR14 pilr14.byte
#define PILR14_D7 pilr14.bit._D7
#define PILR14_D6 pilr14.bit._D6
#define PILR14_D5 pilr14.bit._D5
#define PILR14_D4 pilr14.bit._D4
#define PILR14_D3 pilr14.bit._D3
#define PILR14_D2 pilr14.bit._D2
#define PILR14_D1 pilr14.bit._D1
#define PILR14_D0 pilr14.bit._D0
__IO_EXTERN PILR15STR pilr15;  
#define PILR15 pilr15.byte
#define PILR15_D3 pilr15.bit._D3
#define PILR15_D2 pilr15.bit._D2
#define PILR15_D1 pilr15.bit._D1
#define PILR15_D0 pilr15.bit._D0
__IO_EXTERN PILR16STR pilr16;  
#define PILR16 pilr16.byte
#define PILR16_D7 pilr16.bit._D7
#define PILR16_D6 pilr16.bit._D6
#define PILR16_D5 pilr16.bit._D5
#define PILR16_D4 pilr16.bit._D4
#define PILR16_D3 pilr16.bit._D3
#define PILR16_D2 pilr16.bit._D2
#define PILR16_D1 pilr16.bit._D1
#define PILR16_D0 pilr16.bit._D0
__IO_EXTERN PILR17STR pilr17;  
#define PILR17 pilr17.byte
#define PILR17_D7 pilr17.bit._D7
#define PILR17_D6 pilr17.bit._D6
#define PILR17_D5 pilr17.bit._D5
#define PILR17_D4 pilr17.bit._D4
__IO_EXTERN PILR18STR pilr18;  
#define PILR18 pilr18.byte
#define PILR18_D6 pilr18.bit._D6
#define PILR18_D5 pilr18.bit._D5
#define PILR18_D4 pilr18.bit._D4
#define PILR18_D2 pilr18.bit._D2
#define PILR18_D1 pilr18.bit._D1
#define PILR18_D0 pilr18.bit._D0
__IO_EXTERN PILR19STR pilr19;  
#define PILR19 pilr19.byte
#define PILR19_D6 pilr19.bit._D6
#define PILR19_D5 pilr19.bit._D5
#define PILR19_D4 pilr19.bit._D4
#define PILR19_D2 pilr19.bit._D2
#define PILR19_D1 pilr19.bit._D1
#define PILR19_D0 pilr19.bit._D0
__IO_EXTERN PILR20STR pilr20;  
#define PILR20 pilr20.byte
#define PILR20_D2 pilr20.bit._D2
#define PILR20_D1 pilr20.bit._D1
#define PILR20_D0 pilr20.bit._D0
__IO_EXTERN PILR22STR pilr22;  
#define PILR22 pilr22.byte
#define PILR22_D5 pilr22.bit._D5
#define PILR22_D4 pilr22.bit._D4
#define PILR22_D2 pilr22.bit._D2
#define PILR22_D0 pilr22.bit._D0
__IO_EXTERN PILR23STR pilr23;  
#define PILR23 pilr23.byte
#define PILR23_D5 pilr23.bit._D5
#define PILR23_D4 pilr23.bit._D4
#define PILR23_D3 pilr23.bit._D3
#define PILR23_D2 pilr23.bit._D2
#define PILR23_D1 pilr23.bit._D1
#define PILR23_D0 pilr23.bit._D0
__IO_EXTERN PILR24STR pilr24;  
#define PILR24 pilr24.byte
#define PILR24_D7 pilr24.bit._D7
#define PILR24_D6 pilr24.bit._D6
#define PILR24_D5 pilr24.bit._D5
#define PILR24_D4 pilr24.bit._D4
#define PILR24_D3 pilr24.bit._D3
#define PILR24_D2 pilr24.bit._D2
#define PILR24_D1 pilr24.bit._D1
#define PILR24_D0 pilr24.bit._D0
__IO_EXTERN PILR25STR pilr25;  
#define PILR25 pilr25.byte
#define PILR25_D7 pilr25.bit._D7
#define PILR25_D6 pilr25.bit._D6
#define PILR25_D5 pilr25.bit._D5
#define PILR25_D4 pilr25.bit._D4
#define PILR25_D3 pilr25.bit._D3
#define PILR25_D2 pilr25.bit._D2
#define PILR25_D1 pilr25.bit._D1
#define PILR25_D0 pilr25.bit._D0
__IO_EXTERN PILR26STR pilr26;  
#define PILR26 pilr26.byte
#define PILR26_D7 pilr26.bit._D7
#define PILR26_D6 pilr26.bit._D6
#define PILR26_D5 pilr26.bit._D5
#define PILR26_D4 pilr26.bit._D4
#define PILR26_D3 pilr26.bit._D3
#define PILR26_D2 pilr26.bit._D2
#define PILR26_D1 pilr26.bit._D1
#define PILR26_D0 pilr26.bit._D0
__IO_EXTERN PILR27STR pilr27;  
#define PILR27 pilr27.byte
#define PILR27_D7 pilr27.bit._D7
#define PILR27_D6 pilr27.bit._D6
#define PILR27_D5 pilr27.bit._D5
#define PILR27_D4 pilr27.bit._D4
#define PILR27_D3 pilr27.bit._D3
#define PILR27_D2 pilr27.bit._D2
#define PILR27_D1 pilr27.bit._D1
#define PILR27_D0 pilr27.bit._D0
__IO_EXTERN PILR29STR pilr29;  
#define PILR29 pilr29.byte
#define PILR29_D7 pilr29.bit._D7
#define PILR29_D6 pilr29.bit._D6
#define PILR29_D5 pilr29.bit._D5
#define PILR29_D4 pilr29.bit._D4
#define PILR29_D3 pilr29.bit._D3
#define PILR29_D2 pilr29.bit._D2
#define PILR29_D1 pilr29.bit._D1
#define PILR29_D0 pilr29.bit._D0
__IO_EXTERN EPILR00STR epilr00;   /* R-bus Port Extra Input Level Select Register */
#define EPILR00 epilr00.byte
#define EPILR00_D7 epilr00.bit._D7
#define EPILR00_D6 epilr00.bit._D6
#define EPILR00_D5 epilr00.bit._D5
#define EPILR00_D4 epilr00.bit._D4
#define EPILR00_D3 epilr00.bit._D3
#define EPILR00_D2 epilr00.bit._D2
#define EPILR00_D1 epilr00.bit._D1
#define EPILR00_D0 epilr00.bit._D0
__IO_EXTERN EPILR01STR epilr01;  
#define EPILR01 epilr01.byte
#define EPILR01_D7 epilr01.bit._D7
#define EPILR01_D6 epilr01.bit._D6
#define EPILR01_D5 epilr01.bit._D5
#define EPILR01_D4 epilr01.bit._D4
#define EPILR01_D3 epilr01.bit._D3
#define EPILR01_D2 epilr01.bit._D2
#define EPILR01_D1 epilr01.bit._D1
#define EPILR01_D0 epilr01.bit._D0
__IO_EXTERN EPILR02STR epilr02;  
#define EPILR02 epilr02.byte
#define EPILR02_D7 epilr02.bit._D7
#define EPILR02_D6 epilr02.bit._D6
#define EPILR02_D5 epilr02.bit._D5
#define EPILR02_D4 epilr02.bit._D4
#define EPILR02_D3 epilr02.bit._D3
#define EPILR02_D2 epilr02.bit._D2
#define EPILR02_D1 epilr02.bit._D1
#define EPILR02_D0 epilr02.bit._D0
__IO_EXTERN EPILR03STR epilr03;  
#define EPILR03 epilr03.byte
#define EPILR03_D7 epilr03.bit._D7
#define EPILR03_D6 epilr03.bit._D6
#define EPILR03_D5 epilr03.bit._D5
#define EPILR03_D4 epilr03.bit._D4
#define EPILR03_D3 epilr03.bit._D3
#define EPILR03_D2 epilr03.bit._D2
#define EPILR03_D1 epilr03.bit._D1
#define EPILR03_D0 epilr03.bit._D0
__IO_EXTERN EPILR04STR epilr04;  
#define EPILR04 epilr04.byte
#define EPILR04_D1 epilr04.bit._D1
#define EPILR04_D0 epilr04.bit._D0
__IO_EXTERN EPILR05STR epilr05;  
#define EPILR05 epilr05.byte
#define EPILR05_D7 epilr05.bit._D7
#define EPILR05_D6 epilr05.bit._D6
#define EPILR05_D5 epilr05.bit._D5
#define EPILR05_D4 epilr05.bit._D4
#define EPILR05_D3 epilr05.bit._D3
#define EPILR05_D2 epilr05.bit._D2
#define EPILR05_D1 epilr05.bit._D1
#define EPILR05_D0 epilr05.bit._D0
__IO_EXTERN EPILR06STR epilr06;  
#define EPILR06 epilr06.byte
#define EPILR06_D7 epilr06.bit._D7
#define EPILR06_D6 epilr06.bit._D6
#define EPILR06_D5 epilr06.bit._D5
#define EPILR06_D4 epilr06.bit._D4
#define EPILR06_D3 epilr06.bit._D3
#define EPILR06_D2 epilr06.bit._D2
#define EPILR06_D1 epilr06.bit._D1
#define EPILR06_D0 epilr06.bit._D0
__IO_EXTERN EPILR07STR epilr07;  
#define EPILR07 epilr07.byte
#define EPILR07_D7 epilr07.bit._D7
#define EPILR07_D6 epilr07.bit._D6
#define EPILR07_D5 epilr07.bit._D5
#define EPILR07_D4 epilr07.bit._D4
#define EPILR07_D3 epilr07.bit._D3
#define EPILR07_D2 epilr07.bit._D2
#define EPILR07_D1 epilr07.bit._D1
#define EPILR07_D0 epilr07.bit._D0
__IO_EXTERN EPILR08STR epilr08;  
#define EPILR08 epilr08.byte
#define EPILR08_D7 epilr08.bit._D7
#define EPILR08_D6 epilr08.bit._D6
#define EPILR08_D5 epilr08.bit._D5
#define EPILR08_D4 epilr08.bit._D4
#define EPILR08_D3 epilr08.bit._D3
#define EPILR08_D2 epilr08.bit._D2
#define EPILR08_D1 epilr08.bit._D1
#define EPILR08_D0 epilr08.bit._D0
__IO_EXTERN EPILR09STR epilr09;  
#define EPILR09 epilr09.byte
#define EPILR09_D7 epilr09.bit._D7
#define EPILR09_D6 epilr09.bit._D6
#define EPILR09_D3 epilr09.bit._D3
#define EPILR09_D2 epilr09.bit._D2
#define EPILR09_D1 epilr09.bit._D1
#define EPILR09_D0 epilr09.bit._D0
__IO_EXTERN EPILR10STR epilr10;  
#define EPILR10 epilr10.byte
#define EPILR10_D6 epilr10.bit._D6
#define EPILR10_D5 epilr10.bit._D5
#define EPILR10_D4 epilr10.bit._D4
#define EPILR10_D3 epilr10.bit._D3
#define EPILR10_D2 epilr10.bit._D2
#define EPILR10_D1 epilr10.bit._D1
__IO_EXTERN EPILR13STR epilr13;  
#define EPILR13 epilr13.byte
#define EPILR13_D2 epilr13.bit._D2
#define EPILR13_D1 epilr13.bit._D1
#define EPILR13_D0 epilr13.bit._D0
__IO_EXTERN EPILR14STR epilr14;  
#define EPILR14 epilr14.byte
#define EPILR14_D7 epilr14.bit._D7
#define EPILR14_D6 epilr14.bit._D6
#define EPILR14_D5 epilr14.bit._D5
#define EPILR14_D4 epilr14.bit._D4
#define EPILR14_D3 epilr14.bit._D3
#define EPILR14_D2 epilr14.bit._D2
#define EPILR14_D1 epilr14.bit._D1
#define EPILR14_D0 epilr14.bit._D0
__IO_EXTERN EPILR15STR epilr15;  
#define EPILR15 epilr15.byte
#define EPILR15_D3 epilr15.bit._D3
#define EPILR15_D2 epilr15.bit._D2
#define EPILR15_D1 epilr15.bit._D1
#define EPILR15_D0 epilr15.bit._D0
__IO_EXTERN EPILR16STR epilr16;  
#define EPILR16 epilr16.byte
#define EPILR16_D7 epilr16.bit._D7
#define EPILR16_D6 epilr16.bit._D6
#define EPILR16_D5 epilr16.bit._D5
#define EPILR16_D4 epilr16.bit._D4
#define EPILR16_D3 epilr16.bit._D3
#define EPILR16_D2 epilr16.bit._D2
#define EPILR16_D1 epilr16.bit._D1
#define EPILR16_D0 epilr16.bit._D0
__IO_EXTERN EPILR17STR epilr17;  
#define EPILR17 epilr17.byte
#define EPILR17_D7 epilr17.bit._D7
#define EPILR17_D6 epilr17.bit._D6
#define EPILR17_D5 epilr17.bit._D5
#define EPILR17_D4 epilr17.bit._D4
__IO_EXTERN EPILR18STR epilr18;  
#define EPILR18 epilr18.byte
#define EPILR18_D6 epilr18.bit._D6
#define EPILR18_D5 epilr18.bit._D5
#define EPILR18_D4 epilr18.bit._D4
#define EPILR18_D2 epilr18.bit._D2
#define EPILR18_D1 epilr18.bit._D1
#define EPILR18_D0 epilr18.bit._D0
__IO_EXTERN EPILR19STR epilr19;  
#define EPILR19 epilr19.byte
#define EPILR19_D6 epilr19.bit._D6
#define EPILR19_D5 epilr19.bit._D5
#define EPILR19_D4 epilr19.bit._D4
#define EPILR19_D2 epilr19.bit._D2
#define EPILR19_D1 epilr19.bit._D1
#define EPILR19_D0 epilr19.bit._D0
__IO_EXTERN EPILR20STR epilr20;  
#define EPILR20 epilr20.byte
#define EPILR20_D2 epilr20.bit._D2
#define EPILR20_D1 epilr20.bit._D1
#define EPILR20_D0 epilr20.bit._D0
__IO_EXTERN EPILR22STR epilr22;  
#define EPILR22 epilr22.byte
#define EPILR22_D5 epilr22.bit._D5
#define EPILR22_D4 epilr22.bit._D4
#define EPILR22_D2 epilr22.bit._D2
#define EPILR22_D0 epilr22.bit._D0
__IO_EXTERN EPILR23STR epilr23;  
#define EPILR23 epilr23.byte
#define EPILR23_D5 epilr23.bit._D5
#define EPILR23_D4 epilr23.bit._D4
#define EPILR23_D3 epilr23.bit._D3
#define EPILR23_D2 epilr23.bit._D2
#define EPILR23_D1 epilr23.bit._D1
#define EPILR23_D0 epilr23.bit._D0
__IO_EXTERN EPILR24STR epilr24;  
#define EPILR24 epilr24.byte
#define EPILR24_D7 epilr24.bit._D7
#define EPILR24_D6 epilr24.bit._D6
#define EPILR24_D5 epilr24.bit._D5
#define EPILR24_D4 epilr24.bit._D4
#define EPILR24_D3 epilr24.bit._D3
#define EPILR24_D2 epilr24.bit._D2
#define EPILR24_D1 epilr24.bit._D1
#define EPILR24_D0 epilr24.bit._D0
__IO_EXTERN EPILR25STR epilr25;  
#define EPILR25 epilr25.byte
#define EPILR25_D7 epilr25.bit._D7
#define EPILR25_D6 epilr25.bit._D6
#define EPILR25_D5 epilr25.bit._D5
#define EPILR25_D4 epilr25.bit._D4
#define EPILR25_D3 epilr25.bit._D3
#define EPILR25_D2 epilr25.bit._D2
#define EPILR25_D1 epilr25.bit._D1
#define EPILR25_D0 epilr25.bit._D0
__IO_EXTERN EPILR26STR epilr26;  
#define EPILR26 epilr26.byte
#define EPILR26_D7 epilr26.bit._D7
#define EPILR26_D6 epilr26.bit._D6
#define EPILR26_D5 epilr26.bit._D5
#define EPILR26_D4 epilr26.bit._D4
#define EPILR26_D3 epilr26.bit._D3
#define EPILR26_D2 epilr26.bit._D2
#define EPILR26_D1 epilr26.bit._D1
#define EPILR26_D0 epilr26.bit._D0
__IO_EXTERN EPILR27STR epilr27;  
#define EPILR27 epilr27.byte
#define EPILR27_D7 epilr27.bit._D7
#define EPILR27_D6 epilr27.bit._D6
#define EPILR27_D5 epilr27.bit._D5
#define EPILR27_D4 epilr27.bit._D4
#define EPILR27_D3 epilr27.bit._D3
#define EPILR27_D2 epilr27.bit._D2
#define EPILR27_D1 epilr27.bit._D1
#define EPILR27_D0 epilr27.bit._D0
__IO_EXTERN EPILR29STR epilr29;  
#define EPILR29 epilr29.byte
#define EPILR29_D7 epilr29.bit._D7
#define EPILR29_D6 epilr29.bit._D6
#define EPILR29_D5 epilr29.bit._D5
#define EPILR29_D4 epilr29.bit._D4
#define EPILR29_D3 epilr29.bit._D3
#define EPILR29_D2 epilr29.bit._D2
#define EPILR29_D1 epilr29.bit._D1
#define EPILR29_D0 epilr29.bit._D0
__IO_EXTERN PPER00STR pper00;   /* R-bus Port Pull-Up/Down  Enable Register */
#define PPER00 pper00.byte
#define PPER00_D7 pper00.bit._D7
#define PPER00_D6 pper00.bit._D6
#define PPER00_D5 pper00.bit._D5
#define PPER00_D4 pper00.bit._D4
#define PPER00_D3 pper00.bit._D3
#define PPER00_D2 pper00.bit._D2
#define PPER00_D1 pper00.bit._D1
#define PPER00_D0 pper00.bit._D0
__IO_EXTERN PPER01STR pper01;  
#define PPER01 pper01.byte
#define PPER01_D7 pper01.bit._D7
#define PPER01_D6 pper01.bit._D6
#define PPER01_D5 pper01.bit._D5
#define PPER01_D4 pper01.bit._D4
#define PPER01_D3 pper01.bit._D3
#define PPER01_D2 pper01.bit._D2
#define PPER01_D1 pper01.bit._D1
#define PPER01_D0 pper01.bit._D0
__IO_EXTERN PPER02STR pper02;  
#define PPER02 pper02.byte
#define PPER02_D7 pper02.bit._D7
#define PPER02_D6 pper02.bit._D6
#define PPER02_D5 pper02.bit._D5
#define PPER02_D4 pper02.bit._D4
#define PPER02_D3 pper02.bit._D3
#define PPER02_D2 pper02.bit._D2
#define PPER02_D1 pper02.bit._D1
#define PPER02_D0 pper02.bit._D0
__IO_EXTERN PPER03STR pper03;  
#define PPER03 pper03.byte
#define PPER03_D7 pper03.bit._D7
#define PPER03_D6 pper03.bit._D6
#define PPER03_D5 pper03.bit._D5
#define PPER03_D4 pper03.bit._D4
#define PPER03_D3 pper03.bit._D3
#define PPER03_D2 pper03.bit._D2
#define PPER03_D1 pper03.bit._D1
#define PPER03_D0 pper03.bit._D0
__IO_EXTERN PPER04STR pper04;  
#define PPER04 pper04.byte
#define PPER04_D1 pper04.bit._D1
#define PPER04_D0 pper04.bit._D0
__IO_EXTERN PPER05STR pper05;  
#define PPER05 pper05.byte
#define PPER05_D7 pper05.bit._D7
#define PPER05_D6 pper05.bit._D6
#define PPER05_D5 pper05.bit._D5
#define PPER05_D4 pper05.bit._D4
#define PPER05_D3 pper05.bit._D3
#define PPER05_D2 pper05.bit._D2
#define PPER05_D1 pper05.bit._D1
#define PPER05_D0 pper05.bit._D0
__IO_EXTERN PPER06STR pper06;  
#define PPER06 pper06.byte
#define PPER06_D7 pper06.bit._D7
#define PPER06_D6 pper06.bit._D6
#define PPER06_D5 pper06.bit._D5
#define PPER06_D4 pper06.bit._D4
#define PPER06_D3 pper06.bit._D3
#define PPER06_D2 pper06.bit._D2
#define PPER06_D1 pper06.bit._D1
#define PPER06_D0 pper06.bit._D0
__IO_EXTERN PPER07STR pper07;  
#define PPER07 pper07.byte
#define PPER07_D7 pper07.bit._D7
#define PPER07_D6 pper07.bit._D6
#define PPER07_D5 pper07.bit._D5
#define PPER07_D4 pper07.bit._D4
#define PPER07_D3 pper07.bit._D3
#define PPER07_D2 pper07.bit._D2
#define PPER07_D1 pper07.bit._D1
#define PPER07_D0 pper07.bit._D0
__IO_EXTERN PPER08STR pper08;  
#define PPER08 pper08.byte
#define PPER08_D7 pper08.bit._D7
#define PPER08_D6 pper08.bit._D6
#define PPER08_D5 pper08.bit._D5
#define PPER08_D4 pper08.bit._D4
#define PPER08_D3 pper08.bit._D3
#define PPER08_D2 pper08.bit._D2
#define PPER08_D1 pper08.bit._D1
#define PPER08_D0 pper08.bit._D0
__IO_EXTERN PPER09STR pper09;  
#define PPER09 pper09.byte
#define PPER09_D7 pper09.bit._D7
#define PPER09_D6 pper09.bit._D6
#define PPER09_D3 pper09.bit._D3
#define PPER09_D2 pper09.bit._D2
#define PPER09_D1 pper09.bit._D1
#define PPER09_D0 pper09.bit._D0
__IO_EXTERN PPER10STR pper10;  
#define PPER10 pper10.byte
#define PPER10_D6 pper10.bit._D6
#define PPER10_D5 pper10.bit._D5
#define PPER10_D4 pper10.bit._D4
#define PPER10_D3 pper10.bit._D3
#define PPER10_D2 pper10.bit._D2
#define PPER10_D1 pper10.bit._D1
__IO_EXTERN PPER13STR pper13;  
#define PPER13 pper13.byte
#define PPER13_D2 pper13.bit._D2
#define PPER13_D1 pper13.bit._D1
#define PPER13_D0 pper13.bit._D0
__IO_EXTERN PPER14STR pper14;  
#define PPER14 pper14.byte
#define PPER14_D7 pper14.bit._D7
#define PPER14_D6 pper14.bit._D6
#define PPER14_D5 pper14.bit._D5
#define PPER14_D4 pper14.bit._D4
#define PPER14_D3 pper14.bit._D3
#define PPER14_D2 pper14.bit._D2
#define PPER14_D1 pper14.bit._D1
#define PPER14_D0 pper14.bit._D0
__IO_EXTERN PPER15STR pper15;  
#define PPER15 pper15.byte
#define PPER15_D3 pper15.bit._D3
#define PPER15_D2 pper15.bit._D2
#define PPER15_D1 pper15.bit._D1
#define PPER15_D0 pper15.bit._D0
__IO_EXTERN PPER16STR pper16;  
#define PPER16 pper16.byte
#define PPER16_D7 pper16.bit._D7
#define PPER16_D6 pper16.bit._D6
#define PPER16_D5 pper16.bit._D5
#define PPER16_D4 pper16.bit._D4
#define PPER16_D3 pper16.bit._D3
#define PPER16_D2 pper16.bit._D2
#define PPER16_D1 pper16.bit._D1
#define PPER16_D0 pper16.bit._D0
__IO_EXTERN PPER17STR pper17;  
#define PPER17 pper17.byte
#define PPER17_D7 pper17.bit._D7
#define PPER17_D6 pper17.bit._D6
#define PPER17_D5 pper17.bit._D5
#define PPER17_D4 pper17.bit._D4
__IO_EXTERN PPER18STR pper18;  
#define PPER18 pper18.byte
#define PPER18_D6 pper18.bit._D6
#define PPER18_D5 pper18.bit._D5
#define PPER18_D4 pper18.bit._D4
#define PPER18_D2 pper18.bit._D2
#define PPER18_D1 pper18.bit._D1
#define PPER18_D0 pper18.bit._D0
__IO_EXTERN PPER19STR pper19;  
#define PPER19 pper19.byte
#define PPER19_D6 pper19.bit._D6
#define PPER19_D5 pper19.bit._D5
#define PPER19_D4 pper19.bit._D4
#define PPER19_D2 pper19.bit._D2
#define PPER19_D1 pper19.bit._D1
#define PPER19_D0 pper19.bit._D0
__IO_EXTERN PPER20STR pper20;  
#define PPER20 pper20.byte
#define PPER20_D2 pper20.bit._D2
#define PPER20_D1 pper20.bit._D1
#define PPER20_D0 pper20.bit._D0
__IO_EXTERN PPER22STR pper22;  
#define PPER22 pper22.byte
#define PPER22_D5 pper22.bit._D5
#define PPER22_D4 pper22.bit._D4
#define PPER22_D2 pper22.bit._D2
#define PPER22_D0 pper22.bit._D0
__IO_EXTERN PPER23STR pper23;  
#define PPER23 pper23.byte
#define PPER23_D5 pper23.bit._D5
#define PPER23_D4 pper23.bit._D4
#define PPER23_D3 pper23.bit._D3
#define PPER23_D2 pper23.bit._D2
#define PPER23_D1 pper23.bit._D1
#define PPER23_D0 pper23.bit._D0
__IO_EXTERN PPER24STR pper24;  
#define PPER24 pper24.byte
#define PPER24_D7 pper24.bit._D7
#define PPER24_D6 pper24.bit._D6
#define PPER24_D5 pper24.bit._D5
#define PPER24_D4 pper24.bit._D4
#define PPER24_D3 pper24.bit._D3
#define PPER24_D2 pper24.bit._D2
#define PPER24_D1 pper24.bit._D1
#define PPER24_D0 pper24.bit._D0
__IO_EXTERN PPER25STR pper25;  
#define PPER25 pper25.byte
#define PPER25_D7 pper25.bit._D7
#define PPER25_D6 pper25.bit._D6
#define PPER25_D5 pper25.bit._D5
#define PPER25_D4 pper25.bit._D4
#define PPER25_D3 pper25.bit._D3
#define PPER25_D2 pper25.bit._D2
#define PPER25_D1 pper25.bit._D1
#define PPER25_D0 pper25.bit._D0
__IO_EXTERN PPER26STR pper26;  
#define PPER26 pper26.byte
#define PPER26_D7 pper26.bit._D7
#define PPER26_D6 pper26.bit._D6
#define PPER26_D5 pper26.bit._D5
#define PPER26_D4 pper26.bit._D4
#define PPER26_D3 pper26.bit._D3
#define PPER26_D2 pper26.bit._D2
#define PPER26_D1 pper26.bit._D1
#define PPER26_D0 pper26.bit._D0
__IO_EXTERN PPER27STR pper27;  
#define PPER27 pper27.byte
#define PPER27_D7 pper27.bit._D7
#define PPER27_D6 pper27.bit._D6
#define PPER27_D5 pper27.bit._D5
#define PPER27_D4 pper27.bit._D4
#define PPER27_D3 pper27.bit._D3
#define PPER27_D2 pper27.bit._D2
#define PPER27_D1 pper27.bit._D1
#define PPER27_D0 pper27.bit._D0
__IO_EXTERN PPER29STR pper29;  
#define PPER29 pper29.byte
#define PPER29_D7 pper29.bit._D7
#define PPER29_D6 pper29.bit._D6
#define PPER29_D5 pper29.bit._D5
#define PPER29_D4 pper29.bit._D4
#define PPER29_D3 pper29.bit._D3
#define PPER29_D2 pper29.bit._D2
#define PPER29_D1 pper29.bit._D1
#define PPER29_D0 pper29.bit._D0
__IO_EXTERN PPCR00STR ppcr00;   /* R-bus Port Pull-Up/Down Control Register */
#define PPCR00 ppcr00.byte
#define PPCR00_D7 ppcr00.bit._D7
#define PPCR00_D6 ppcr00.bit._D6
#define PPCR00_D5 ppcr00.bit._D5
#define PPCR00_D4 ppcr00.bit._D4
#define PPCR00_D3 ppcr00.bit._D3
#define PPCR00_D2 ppcr00.bit._D2
#define PPCR00_D1 ppcr00.bit._D1
#define PPCR00_D0 ppcr00.bit._D0
__IO_EXTERN PPCR01STR ppcr01;  
#define PPCR01 ppcr01.byte
#define PPCR01_D7 ppcr01.bit._D7
#define PPCR01_D6 ppcr01.bit._D6
#define PPCR01_D5 ppcr01.bit._D5
#define PPCR01_D4 ppcr01.bit._D4
#define PPCR01_D3 ppcr01.bit._D3
#define PPCR01_D2 ppcr01.bit._D2
#define PPCR01_D1 ppcr01.bit._D1
#define PPCR01_D0 ppcr01.bit._D0
__IO_EXTERN PPCR02STR ppcr02;  
#define PPCR02 ppcr02.byte
#define PPCR02_D7 ppcr02.bit._D7
#define PPCR02_D6 ppcr02.bit._D6
#define PPCR02_D5 ppcr02.bit._D5
#define PPCR02_D4 ppcr02.bit._D4
#define PPCR02_D3 ppcr02.bit._D3
#define PPCR02_D2 ppcr02.bit._D2
#define PPCR02_D1 ppcr02.bit._D1
#define PPCR02_D0 ppcr02.bit._D0
__IO_EXTERN PPCR03STR ppcr03;  
#define PPCR03 ppcr03.byte
#define PPCR03_D7 ppcr03.bit._D7
#define PPCR03_D6 ppcr03.bit._D6
#define PPCR03_D5 ppcr03.bit._D5
#define PPCR03_D4 ppcr03.bit._D4
#define PPCR03_D3 ppcr03.bit._D3
#define PPCR03_D2 ppcr03.bit._D2
#define PPCR03_D1 ppcr03.bit._D1
#define PPCR03_D0 ppcr03.bit._D0
__IO_EXTERN PPCR04STR ppcr04;  
#define PPCR04 ppcr04.byte
#define PPCR04_D1 ppcr04.bit._D1
#define PPCR04_D0 ppcr04.bit._D0
__IO_EXTERN PPCR05STR ppcr05;  
#define PPCR05 ppcr05.byte
#define PPCR05_D7 ppcr05.bit._D7
#define PPCR05_D6 ppcr05.bit._D6
#define PPCR05_D5 ppcr05.bit._D5
#define PPCR05_D4 ppcr05.bit._D4
#define PPCR05_D3 ppcr05.bit._D3
#define PPCR05_D2 ppcr05.bit._D2
#define PPCR05_D1 ppcr05.bit._D1
#define PPCR05_D0 ppcr05.bit._D0
__IO_EXTERN PPCR06STR ppcr06;  
#define PPCR06 ppcr06.byte
#define PPCR06_D7 ppcr06.bit._D7
#define PPCR06_D6 ppcr06.bit._D6
#define PPCR06_D5 ppcr06.bit._D5
#define PPCR06_D4 ppcr06.bit._D4
#define PPCR06_D3 ppcr06.bit._D3
#define PPCR06_D2 ppcr06.bit._D2
#define PPCR06_D1 ppcr06.bit._D1
#define PPCR06_D0 ppcr06.bit._D0
__IO_EXTERN PPCR07STR ppcr07;  
#define PPCR07 ppcr07.byte
#define PPCR07_D7 ppcr07.bit._D7
#define PPCR07_D6 ppcr07.bit._D6
#define PPCR07_D5 ppcr07.bit._D5
#define PPCR07_D4 ppcr07.bit._D4
#define PPCR07_D3 ppcr07.bit._D3
#define PPCR07_D2 ppcr07.bit._D2
#define PPCR07_D1 ppcr07.bit._D1
#define PPCR07_D0 ppcr07.bit._D0
__IO_EXTERN PPCR08STR ppcr08;  
#define PPCR08 ppcr08.byte
#define PPCR08_D7 ppcr08.bit._D7
#define PPCR08_D6 ppcr08.bit._D6
#define PPCR08_D5 ppcr08.bit._D5
#define PPCR08_D4 ppcr08.bit._D4
#define PPCR08_D3 ppcr08.bit._D3
#define PPCR08_D2 ppcr08.bit._D2
#define PPCR08_D1 ppcr08.bit._D1
#define PPCR08_D0 ppcr08.bit._D0
__IO_EXTERN PPCR09STR ppcr09;  
#define PPCR09 ppcr09.byte
#define PPCR09_D7 ppcr09.bit._D7
#define PPCR09_D6 ppcr09.bit._D6
#define PPCR09_D3 ppcr09.bit._D3
#define PPCR09_D2 ppcr09.bit._D2
#define PPCR09_D1 ppcr09.bit._D1
#define PPCR09_D0 ppcr09.bit._D0
__IO_EXTERN PPCR10STR ppcr10;  
#define PPCR10 ppcr10.byte
#define PPCR10_D6 ppcr10.bit._D6
#define PPCR10_D5 ppcr10.bit._D5
#define PPCR10_D4 ppcr10.bit._D4
#define PPCR10_D3 ppcr10.bit._D3
#define PPCR10_D2 ppcr10.bit._D2
#define PPCR10_D1 ppcr10.bit._D1
__IO_EXTERN PPCR13STR ppcr13;  
#define PPCR13 ppcr13.byte
#define PPCR13_D2 ppcr13.bit._D2
#define PPCR13_D1 ppcr13.bit._D1
#define PPCR13_D0 ppcr13.bit._D0
__IO_EXTERN PPCR14STR ppcr14;  
#define PPCR14 ppcr14.byte
#define PPCR14_D7 ppcr14.bit._D7
#define PPCR14_D6 ppcr14.bit._D6
#define PPCR14_D5 ppcr14.bit._D5
#define PPCR14_D4 ppcr14.bit._D4
#define PPCR14_D3 ppcr14.bit._D3
#define PPCR14_D2 ppcr14.bit._D2
#define PPCR14_D1 ppcr14.bit._D1
#define PPCR14_D0 ppcr14.bit._D0
__IO_EXTERN PPCR15STR ppcr15;  
#define PPCR15 ppcr15.byte
#define PPCR15_D3 ppcr15.bit._D3
#define PPCR15_D2 ppcr15.bit._D2
#define PPCR15_D1 ppcr15.bit._D1
#define PPCR15_D0 ppcr15.bit._D0
__IO_EXTERN PPCR16STR ppcr16;  
#define PPCR16 ppcr16.byte
#define PPCR16_D7 ppcr16.bit._D7
#define PPCR16_D6 ppcr16.bit._D6
#define PPCR16_D5 ppcr16.bit._D5
#define PPCR16_D4 ppcr16.bit._D4
#define PPCR16_D3 ppcr16.bit._D3
#define PPCR16_D2 ppcr16.bit._D2
#define PPCR16_D1 ppcr16.bit._D1
#define PPCR16_D0 ppcr16.bit._D0
__IO_EXTERN PPCR17STR ppcr17;  
#define PPCR17 ppcr17.byte
#define PPCR17_D7 ppcr17.bit._D7
#define PPCR17_D6 ppcr17.bit._D6
#define PPCR17_D5 ppcr17.bit._D5
#define PPCR17_D4 ppcr17.bit._D4
__IO_EXTERN PPCR18STR ppcr18;  
#define PPCR18 ppcr18.byte
#define PPCR18_D6 ppcr18.bit._D6
#define PPCR18_D5 ppcr18.bit._D5
#define PPCR18_D4 ppcr18.bit._D4
#define PPCR18_D2 ppcr18.bit._D2
#define PPCR18_D1 ppcr18.bit._D1
#define PPCR18_D0 ppcr18.bit._D0
__IO_EXTERN PPCR19STR ppcr19;  
#define PPCR19 ppcr19.byte
#define PPCR19_D6 ppcr19.bit._D6
#define PPCR19_D5 ppcr19.bit._D5
#define PPCR19_D4 ppcr19.bit._D4
#define PPCR19_D2 ppcr19.bit._D2
#define PPCR19_D1 ppcr19.bit._D1
#define PPCR19_D0 ppcr19.bit._D0
__IO_EXTERN PPCR20STR ppcr20;  
#define PPCR20 ppcr20.byte
#define PPCR20_D2 ppcr20.bit._D2
#define PPCR20_D1 ppcr20.bit._D1
#define PPCR20_D0 ppcr20.bit._D0
__IO_EXTERN PPCR22STR ppcr22;  
#define PPCR22 ppcr22.byte
#define PPCR22_D5 ppcr22.bit._D5
#define PPCR22_D4 ppcr22.bit._D4
#define PPCR22_D2 ppcr22.bit._D2
#define PPCR22_D0 ppcr22.bit._D0
__IO_EXTERN PPCR23STR ppcr23;  
#define PPCR23 ppcr23.byte
#define PPCR23_D5 ppcr23.bit._D5
#define PPCR23_D4 ppcr23.bit._D4
#define PPCR23_D3 ppcr23.bit._D3
#define PPCR23_D2 ppcr23.bit._D2
#define PPCR23_D1 ppcr23.bit._D1
#define PPCR23_D0 ppcr23.bit._D0
__IO_EXTERN PPCR24STR ppcr24;  
#define PPCR24 ppcr24.byte
#define PPCR24_D7 ppcr24.bit._D7
#define PPCR24_D6 ppcr24.bit._D6
#define PPCR24_D5 ppcr24.bit._D5
#define PPCR24_D4 ppcr24.bit._D4
#define PPCR24_D3 ppcr24.bit._D3
#define PPCR24_D2 ppcr24.bit._D2
#define PPCR24_D1 ppcr24.bit._D1
#define PPCR24_D0 ppcr24.bit._D0
__IO_EXTERN PPCR25STR ppcr25;  
#define PPCR25 ppcr25.byte
#define PPCR25_D7 ppcr25.bit._D7
#define PPCR25_D6 ppcr25.bit._D6
#define PPCR25_D5 ppcr25.bit._D5
#define PPCR25_D4 ppcr25.bit._D4
#define PPCR25_D3 ppcr25.bit._D3
#define PPCR25_D2 ppcr25.bit._D2
#define PPCR25_D1 ppcr25.bit._D1
#define PPCR25_D0 ppcr25.bit._D0
__IO_EXTERN PPCR26STR ppcr26;  
#define PPCR26 ppcr26.byte
#define PPCR26_D7 ppcr26.bit._D7
#define PPCR26_D6 ppcr26.bit._D6
#define PPCR26_D5 ppcr26.bit._D5
#define PPCR26_D4 ppcr26.bit._D4
#define PPCR26_D3 ppcr26.bit._D3
#define PPCR26_D2 ppcr26.bit._D2
#define PPCR26_D1 ppcr26.bit._D1
#define PPCR26_D0 ppcr26.bit._D0
__IO_EXTERN PPCR27STR ppcr27;  
#define PPCR27 ppcr27.byte
#define PPCR27_D7 ppcr27.bit._D7
#define PPCR27_D6 ppcr27.bit._D6
#define PPCR27_D5 ppcr27.bit._D5
#define PPCR27_D4 ppcr27.bit._D4
#define PPCR27_D3 ppcr27.bit._D3
#define PPCR27_D2 ppcr27.bit._D2
#define PPCR27_D1 ppcr27.bit._D1
#define PPCR27_D0 ppcr27.bit._D0
__IO_EXTERN PPCR29STR ppcr29;  
#define PPCR29 ppcr29.byte
#define PPCR29_D7 ppcr29.bit._D7
#define PPCR29_D6 ppcr29.bit._D6
#define PPCR29_D5 ppcr29.bit._D5
#define PPCR29_D4 ppcr29.bit._D4
#define PPCR29_D3 ppcr29.bit._D3
#define PPCR29_D2 ppcr29.bit._D2
#define PPCR29_D1 ppcr29.bit._D1
#define PPCR29_D0 ppcr29.bit._D0
__IO_EXTERN IO_LWORD dmasa0;   /* DMAC */
#define DMASA0 dmasa0
__IO_EXTERN IO_LWORD dmada0;  
#define DMADA0 dmada0
__IO_EXTERN IO_LWORD dmasa1;  
#define DMASA1 dmasa1
__IO_EXTERN IO_LWORD dmada1;  
#define DMADA1 dmada1
__IO_EXTERN IO_LWORD dmasa2;  
#define DMASA2 dmasa2
__IO_EXTERN IO_LWORD dmada2;  
#define DMADA2 dmada2
__IO_EXTERN IO_LWORD dmasa3;  
#define DMASA3 dmasa3
__IO_EXTERN IO_LWORD dmada3;  
#define DMADA3 dmada3
__IO_EXTERN IO_LWORD dmasa4;  
#define DMASA4 dmasa4
__IO_EXTERN IO_LWORD dmada4;  
#define DMADA4 dmada4
__IO_EXTERN FMCSSTR fmcs;   /* Flash Memory/I-Cache Control Register */
#define FMCS fmcs.byte
#define FMCS_ASYNC fmcs.bit._ASYNC
#define FMCS_FIXE fmcs.bit._FIXE
#define FMCS_BIRE fmcs.bit._BIRE
#define FMCS_RDYEG fmcs.bit._RDYEG
#define FMCS_RDY fmcs.bit._RDY
#define FMCS_RDYI fmcs.bit._RDYI
#define FMCS_RW16 fmcs.bit._RW16
#define FMCS_LPM fmcs.bit._LPM
__IO_EXTERN FMCRSTR fmcr;  
#define FMCR fmcr.byte
#define FMCR_LOCK fmcr.bit._LOCK
#define FMCR_PHASE fmcr.bit._PHASE
#define FMCR_PF2I fmcr.bit._PF2I
#define FMCR_RD64 fmcr.bit._RD64
__IO_EXTERN FCHCRSTR fchcr;  
#define FCHCR fchcr.word
#define FCHCR_REN fchcr.bit._REN
#define FCHCR_TAGE fchcr.bit._TAGE
#define FCHCR_FLUSH fchcr.bit._FLUSH
#define FCHCR_DBEN fchcr.bit._DBEN
#define FCHCR_PFEN fchcr.bit._PFEN
#define FCHCR_PFMC fchcr.bit._PFMC
#define FCHCR_LOCK fchcr.bit._LOCK
#define FCHCR_ENAB fchcr.bit._ENAB
#define FCHCR_SIZE1 fchcr.bit._SIZE1
#define FCHCR_SIZE0 fchcr.bit._SIZE0
#define FCHCR_SIZE fchcr.bitc._SIZE
__IO_EXTERN FMWTSTR fmwt;  
#define FMWT fmwt.word
#define FMWT_WTP1 fmwt.bit._WTP1
#define FMWT_WTP0 fmwt.bit._WTP0
#define FMWT_WEXH1 fmwt.bit._WEXH1
#define FMWT_WEXH0 fmwt.bit._WEXH0
#define FMWT_WTC3 fmwt.bit._WTC3
#define FMWT_WTC2 fmwt.bit._WTC2
#define FMWT_WTC1 fmwt.bit._WTC1
#define FMWT_WTC0 fmwt.bit._WTC0
#define FMWT_FRAM fmwt.bit._FRAM
#define FMWT_ATD2 fmwt.bit._ATD2
#define FMWT_ATD1 fmwt.bit._ATD1
#define FMWT_ATD0 fmwt.bit._ATD0
#define FMWT_EQ3 fmwt.bit._EQ3
#define FMWT_EQ2 fmwt.bit._EQ2
#define FMWT_EQ1 fmwt.bit._EQ1
#define FMWT_EQ0 fmwt.bit._EQ0
#define FMWT_WTP fmwt.bitc._WTP
#define FMWT_WEXH fmwt.bitc._WEXH
#define FMWT_WTC fmwt.bitc._WTC
#define FMWT_ATD fmwt.bitc._ATD
#define FMWT_EQ fmwt.bitc._EQ
__IO_EXTERN FMWT2STR fmwt2;  
#define FMWT2 fmwt2.byte
#define FMWT2_ALEH2 fmwt2.bit._ALEH2
#define FMWT2_ALEH1 fmwt2.bit._ALEH1
#define FMWT2_ALEH0 fmwt2.bit._ALEH0
#define FMWT2_ALEH fmwt2.bitc._ALEH
__IO_EXTERN FMPSSTR fmps;  
#define FMPS fmps.byte
#define FMPS_PS2 fmps.bit._PS2
#define FMPS_PS1 fmps.bit._PS1
#define FMPS_PS0 fmps.bit._PS0
#define FMPS_PS fmps.bitc._PS
__IO_EXTERN IO_LWORD fmac;  
#define FMAC fmac
__IO_EXTERN IO_LWORD fcha0;   /* I_Cache Nonchachable area settings Register */
#define FCHA0 fcha0
__IO_EXTERN IO_LWORD fcha1;  
#define FCHA1 fcha1
__IO_EXTERN FSCR0STR fscr0;   /* Flash Security Control Register */
#define FSCR0 fscr0.lword
#define FSCR0_CRC31 fscr0.bit._CRC31
#define FSCR0_CRC30 fscr0.bit._CRC30
#define FSCR0_CRC29 fscr0.bit._CRC29
#define FSCR0_CRC28 fscr0.bit._CRC28
#define FSCR0_CRC27 fscr0.bit._CRC27
#define FSCR0_CRC26 fscr0.bit._CRC26
#define FSCR0_CRC25 fscr0.bit._CRC25
#define FSCR0_CRC24 fscr0.bit._CRC24
#define FSCR0_CRC23 fscr0.bit._CRC23
#define FSCR0_CRC22 fscr0.bit._CRC22
#define FSCR0_CRC21 fscr0.bit._CRC21
#define FSCR0_CRC20 fscr0.bit._CRC20
#define FSCR0_CRC19 fscr0.bit._CRC19
#define FSCR0_CRC18 fscr0.bit._CRC18
#define FSCR0_CRC17 fscr0.bit._CRC17
#define FSCR0_CRC16 fscr0.bit._CRC16
#define FSCR0_CRC15 fscr0.bit._CRC15
#define FSCR0_CRC14 fscr0.bit._CRC14
#define FSCR0_CRC13 fscr0.bit._CRC13
#define FSCR0_CRC12 fscr0.bit._CRC12
#define FSCR0_CRC11 fscr0.bit._CRC11
#define FSCR0_CRC10 fscr0.bit._CRC10
#define FSCR0_CRC9 fscr0.bit._CRC9
#define FSCR0_CRC8 fscr0.bit._CRC8
#define FSCR0_CRC7 fscr0.bit._CRC7
#define FSCR0_CRC6 fscr0.bit._CRC6
#define FSCR0_CRC5 fscr0.bit._CRC5
#define FSCR0_CRC4 fscr0.bit._CRC4
#define FSCR0_CRC3 fscr0.bit._CRC3
#define FSCR0_CRC2 fscr0.bit._CRC2
#define FSCR0_CRC1 fscr0.bit._CRC1
#define FSCR0_CRC0 fscr0.bit._CRC0
__IO_EXTERN FSCR1STR fscr1;  
#define FSCR1 fscr1.lword
#define FSCR1_RDY fscr1.bit._RDY
#define FSCR1_CSZ3 fscr1.bit._CSZ3
#define FSCR1_CSZ2 fscr1.bit._CSZ2
#define FSCR1_CSZ1 fscr1.bit._CSZ1
#define FSCR1_CSZ0 fscr1.bit._CSZ0
#define FSCR1_CSA15 fscr1.bit._CSA15
#define FSCR1_CSA14 fscr1.bit._CSA14
#define FSCR1_CSA13 fscr1.bit._CSA13
#define FSCR1_CSA12 fscr1.bit._CSA12
#define FSCR1_CSA11 fscr1.bit._CSA11
#define FSCR1_CSA10 fscr1.bit._CSA10
#define FSCR1_CSA9 fscr1.bit._CSA9
#define FSCR1_CSA8 fscr1.bit._CSA8
#define FSCR1_CSA7 fscr1.bit._CSA7
#define FSCR1_CSA6 fscr1.bit._CSA6
#define FSCR1_CSA5 fscr1.bit._CSA5
#define FSCR1_CSA4 fscr1.bit._CSA4
#define FSCR1_CSA3 fscr1.bit._CSA3
#define FSCR1_CSA2 fscr1.bit._CSA2
#define FSCR1_CSA1 fscr1.bit._CSA1
#define FSCR1_CSA0 fscr1.bit._CSA0
#define FSCR1_CSZ fscr1.bitc._CSZ
__IO_EXTERN CTRLR0STR ctrlr0;   /* CAN 0 Control Register */
#define CTRLR0 ctrlr0.word
#define CTRLR0_Test ctrlr0.bit._Test
#define CTRLR0_CCE ctrlr0.bit._CCE
#define CTRLR0_DAR ctrlr0.bit._DAR
#define CTRLR0_EIE ctrlr0.bit._EIE
#define CTRLR0_SIE ctrlr0.bit._SIE
#define CTRLR0_IE ctrlr0.bit._IE
#define CTRLR0_Init ctrlr0.bit._Init
__IO_EXTERN STATR0STR statr0;  
#define STATR0 statr0.word
#define STATR0_BOff statr0.bit._BOff
#define STATR0_EWarn statr0.bit._EWarn
#define STATR0_EPass statr0.bit._EPass
#define STATR0_RxOK statr0.bit._RxOK
#define STATR0_TxOK statr0.bit._TxOK
#define STATR0_LEC2 statr0.bit._LEC2
#define STATR0_LEC1 statr0.bit._LEC1
#define STATR0_LEC0 statr0.bit._LEC0
#define STATR0_LEC statr0.bitc._LEC
__IO_EXTERN ERRCNT0STR errcnt0;  
#define ERRCNT0 errcnt0.word
#define ERRCNT0_RP errcnt0.bit._RP
#define ERRCNT0_REC6 errcnt0.bit._REC6
#define ERRCNT0_REC5 errcnt0.bit._REC5
#define ERRCNT0_REC4 errcnt0.bit._REC4
#define ERRCNT0_REC3 errcnt0.bit._REC3
#define ERRCNT0_REC2 errcnt0.bit._REC2
#define ERRCNT0_REC1 errcnt0.bit._REC1
#define ERRCNT0_REC0 errcnt0.bit._REC0
#define ERRCNT0_TEC7 errcnt0.bit._TEC7
#define ERRCNT0_TEC6 errcnt0.bit._TEC6
#define ERRCNT0_TEC5 errcnt0.bit._TEC5
#define ERRCNT0_TEC4 errcnt0.bit._TEC4
#define ERRCNT0_TEC3 errcnt0.bit._TEC3
#define ERRCNT0_TEC2 errcnt0.bit._TEC2
#define ERRCNT0_TEC1 errcnt0.bit._TEC1
#define ERRCNT0_TEC0 errcnt0.bit._TEC0
#define ERRCNT0_REC errcnt0.bitc._REC
#define ERRCNT0_TEC errcnt0.bitc._TEC
__IO_EXTERN BTR0STR btr0;  
#define BTR0 btr0.word
#define BTR0_Tseg22 btr0.bit._Tseg22
#define BTR0_Tseg21 btr0.bit._Tseg21
#define BTR0_Tseg20 btr0.bit._Tseg20
#define BTR0_Tseg13 btr0.bit._Tseg13
#define BTR0_Tseg12 btr0.bit._Tseg12
#define BTR0_Tseg11 btr0.bit._Tseg11
#define BTR0_Tseg10 btr0.bit._Tseg10
#define BTR0_SJW1 btr0.bit._SJW1
#define BTR0_SJW0 btr0.bit._SJW0
#define BTR0_BRP5 btr0.bit._BRP5
#define BTR0_BRP4 btr0.bit._BRP4
#define BTR0_BRP3 btr0.bit._BRP3
#define BTR0_BRP2 btr0.bit._BRP2
#define BTR0_BRP1 btr0.bit._BRP1
#define BTR0_BRP0 btr0.bit._BRP0
#define BTR0_Tseg2 btr0.bitc._Tseg2
#define BTR0_Tseg1 btr0.bitc._Tseg1
#define BTR0_SJW btr0.bitc._SJW
#define BTR0_BRP btr0.bitc._BRP
__IO_EXTERN IO_WORD intr0;  
#define INTR0 intr0
__IO_EXTERN TESTR0STR testr0;  
#define TESTR0 testr0.word
#define TESTR0_Rx testr0.bit._Rx
#define TESTR0_Tx1 testr0.bit._Tx1
#define TESTR0_Tx0 testr0.bit._Tx0
#define TESTR0_LBack testr0.bit._LBack
#define TESTR0_Silent testr0.bit._Silent
#define TESTR0_Basic testr0.bit._Basic
#define TESTR0_Tx testr0.bitc._Tx
__IO_EXTERN BRPER0STR brper0;  
#define BRPER0 brper0.word
#define BRPER0_BRPE3 brper0.bit._BRPE3
#define BRPER0_BRPE2 brper0.bit._BRPE2
#define BRPER0_BRPE1 brper0.bit._BRPE1
#define BRPER0_BRPE0 brper0.bit._BRPE0
#define BRPER0_BRPE brper0.bitc._BRPE
__IO_EXTERN BRPE0STR brpe0;  
#define BRPE0 brpe0.word
__IO_EXTERN CBSYNC0STR cbsync0;  
#define CBSYNC0 cbsync0.word
__IO_EXTERN IF1CREQ0STR if1creq0;   /* CAN 0 IF 1 */
#define IF1CREQ0 if1creq0.word
#define IF1CREQ0_Busy if1creq0.bit._Busy
#define IF1CREQ0_MN5 if1creq0.bit._MN5
#define IF1CREQ0_MN4 if1creq0.bit._MN4
#define IF1CREQ0_MN3 if1creq0.bit._MN3
#define IF1CREQ0_MN2 if1creq0.bit._MN2
#define IF1CREQ0_MN1 if1creq0.bit._MN1
#define IF1CREQ0_MN0 if1creq0.bit._MN0
#define IF1CREQ0_MN if1creq0.bitc._MN
__IO_EXTERN IF1CMSK0STR if1cmsk0;  
#define IF1CMSK0 if1cmsk0.word
#define IF1CMSK0_WR if1cmsk0.bit._WR
#define IF1CMSK0_Mask if1cmsk0.bit._Mask
#define IF1CMSK0_Arb if1cmsk0.bit._Arb
#define IF1CMSK0_Control if1cmsk0.bit._Control
#define IF1CMSK0_CIP if1cmsk0.bit._CIP
#define IF1CMSK0_TxReq if1cmsk0.bit._TxReq
#define IF1CMSK0_DataA if1cmsk0.bit._DataA
#define IF1CMSK0_DataB if1cmsk0.bit._DataB
__IO_EXTERN IO_LWORD if1msk120;  
#define IF1MSK120 if1msk120
__IO_EXTERN IF1MSK20STR if1msk20;  
#define IF1MSK20 if1msk20.word
#define IF1MSK20_MXtd if1msk20.bit._MXtd
#define IF1MSK20_MDir if1msk20.bit._MDir
__IO_EXTERN IO_WORD if1msk10;  
#define IF1MSK10 if1msk10
__IO_EXTERN IO_LWORD if1arb120;  
#define IF1ARB120 if1arb120
__IO_EXTERN IF1ARB20STR if1arb20;  
#define IF1ARB20 if1arb20.word
#define IF1ARB20_MsgVal if1arb20.bit._MsgVal
#define IF1ARB20_Xtd if1arb20.bit._Xtd
#define IF1ARB20_DIR if1arb20.bit._DIR
__IO_EXTERN IO_WORD if1arb10;  
#define IF1ARB10 if1arb10
__IO_EXTERN IF1MCTR0STR if1mctr0;  
#define IF1MCTR0 if1mctr0.word
#define IF1MCTR0_NewDat if1mctr0.bit._NewDat
#define IF1MCTR0_MsgLst if1mctr0.bit._MsgLst
#define IF1MCTR0_IntPnd if1mctr0.bit._IntPnd
#define IF1MCTR0_UMask if1mctr0.bit._UMask
#define IF1MCTR0_TxIE if1mctr0.bit._TxIE
#define IF1MCTR0_RxIE if1mctr0.bit._RxIE
#define IF1MCTR0_RmtEn if1mctr0.bit._RmtEn
#define IF1MCTR0_TxRqst if1mctr0.bit._TxRqst
#define IF1MCTR0_EoB if1mctr0.bit._EoB
#define IF1MCTR0_DLC3 if1mctr0.bit._DLC3
#define IF1MCTR0_DLC2 if1mctr0.bit._DLC2
#define IF1MCTR0_DLC1 if1mctr0.bit._DLC1
#define IF1MCTR0_DLC0 if1mctr0.bit._DLC0
#define IF1MCTR0_DLC if1mctr0.bitc._DLC
__IO_EXTERN IO_LWORD if1dta120;  
#define IF1DTA120 if1dta120
__IO_EXTERN IO_WORD if1dta10;  
#define IF1DTA10 if1dta10
__IO_EXTERN IO_WORD if1dta20;  
#define IF1DTA20 if1dta20
__IO_EXTERN IO_LWORD if1dtb120;  
#define IF1DTB120 if1dtb120
__IO_EXTERN IO_WORD if1dtb10;  
#define IF1DTB10 if1dtb10
__IO_EXTERN IO_WORD if1dtb20;  
#define IF1DTB20 if1dtb20
__IO_EXTERN IO_LWORD if1dta_swp120;  
#define IF1DTA_SWP120 if1dta_swp120
__IO_EXTERN IO_WORD if1dta_swp20;  
#define IF1DTA_SWP20 if1dta_swp20
__IO_EXTERN IO_WORD if1dta_swp10;  
#define IF1DTA_SWP10 if1dta_swp10
__IO_EXTERN IO_LWORD if1dtb_swp120;  
#define IF1DTB_SWP120 if1dtb_swp120
__IO_EXTERN IO_WORD if1dtb_swp20;  
#define IF1DTB_SWP20 if1dtb_swp20
__IO_EXTERN IO_WORD if1dtb_swp10;  
#define IF1DTB_SWP10 if1dtb_swp10
__IO_EXTERN IF2CREQ0STR if2creq0;   /* CAN 0 IF 2 */
#define IF2CREQ0 if2creq0.word
#define IF2CREQ0_Busy if2creq0.bit._Busy
#define IF2CREQ0_MN5 if2creq0.bit._MN5
#define IF2CREQ0_MN4 if2creq0.bit._MN4
#define IF2CREQ0_MN3 if2creq0.bit._MN3
#define IF2CREQ0_MN2 if2creq0.bit._MN2
#define IF2CREQ0_MN1 if2creq0.bit._MN1
#define IF2CREQ0_MN0 if2creq0.bit._MN0
#define IF2CREQ0_MN if2creq0.bitc._MN
__IO_EXTERN IF2CMSK0STR if2cmsk0;  
#define IF2CMSK0 if2cmsk0.word
#define IF2CMSK0_WR if2cmsk0.bit._WR
#define IF2CMSK0_Mask if2cmsk0.bit._Mask
#define IF2CMSK0_Arb if2cmsk0.bit._Arb
#define IF2CMSK0_Control if2cmsk0.bit._Control
#define IF2CMSK0_CIP if2cmsk0.bit._CIP
#define IF2CMSK0_TxReq if2cmsk0.bit._TxReq
#define IF2CMSK0_DataA if2cmsk0.bit._DataA
#define IF2CMSK0_DataB if2cmsk0.bit._DataB
__IO_EXTERN IO_LWORD if2msk120;  
#define IF2MSK120 if2msk120
__IO_EXTERN IF2MSK20STR if2msk20;  
#define IF2MSK20 if2msk20.word
#define IF2MSK20_MXtd if2msk20.bit._MXtd
#define IF2MSK20_MDir if2msk20.bit._MDir
__IO_EXTERN IO_WORD if2msk10;  
#define IF2MSK10 if2msk10
__IO_EXTERN IO_LWORD if2arb120;  
#define IF2ARB120 if2arb120
__IO_EXTERN IF2ARB20STR if2arb20;  
#define IF2ARB20 if2arb20.word
#define IF2ARB20_MsgVal if2arb20.bit._MsgVal
#define IF2ARB20_Xtd if2arb20.bit._Xtd
#define IF2ARB20_DIR if2arb20.bit._DIR
__IO_EXTERN IO_WORD if2arb10;  
#define IF2ARB10 if2arb10
__IO_EXTERN IF2MCTR0STR if2mctr0;  
#define IF2MCTR0 if2mctr0.word
#define IF2MCTR0_NewDat if2mctr0.bit._NewDat
#define IF2MCTR0_MsgLst if2mctr0.bit._MsgLst
#define IF2MCTR0_IntPnd if2mctr0.bit._IntPnd
#define IF2MCTR0_UMask if2mctr0.bit._UMask
#define IF2MCTR0_TxIE if2mctr0.bit._TxIE
#define IF2MCTR0_RxIE if2mctr0.bit._RxIE
#define IF2MCTR0_RmtEn if2mctr0.bit._RmtEn
#define IF2MCTR0_TxRqst if2mctr0.bit._TxRqst
#define IF2MCTR0_EoB if2mctr0.bit._EoB
#define IF2MCTR0_DLC3 if2mctr0.bit._DLC3
#define IF2MCTR0_DLC2 if2mctr0.bit._DLC2
#define IF2MCTR0_DLC1 if2mctr0.bit._DLC1
#define IF2MCTR0_DLC0 if2mctr0.bit._DLC0
#define IF2MCTR0_DLC if2mctr0.bitc._DLC
__IO_EXTERN IO_LWORD if2dta120;  
#define IF2DTA120 if2dta120
__IO_EXTERN IO_WORD if2dta10;  
#define IF2DTA10 if2dta10
__IO_EXTERN IO_WORD if2dta20;  
#define IF2DTA20 if2dta20
__IO_EXTERN IO_LWORD if2dtb120;  
#define IF2DTB120 if2dtb120
__IO_EXTERN IO_WORD if2dtb10;  
#define IF2DTB10 if2dtb10
__IO_EXTERN IO_WORD if2dtb20;  
#define IF2DTB20 if2dtb20
__IO_EXTERN IO_LWORD if2dta_swp120;  
#define IF2DTA_SWP120 if2dta_swp120
__IO_EXTERN IO_WORD if2dta_swp20;  
#define IF2DTA_SWP20 if2dta_swp20
__IO_EXTERN IO_WORD if2dta_swp10;  
#define IF2DTA_SWP10 if2dta_swp10
__IO_EXTERN IO_LWORD if2dtb_swp120;  
#define IF2DTB_SWP120 if2dtb_swp120
__IO_EXTERN IO_WORD if2dtb_swp20;  
#define IF2DTB_SWP20 if2dtb_swp20
__IO_EXTERN IO_WORD if2dtb_swp10;  
#define IF2DTB_SWP10 if2dtb_swp10
__IO_EXTERN IO_LWORD treqr120;   /* CAN 0 Status Flags */
#define TREQR120 treqr120
__IO_EXTERN IO_WORD treqr20;  
#define TREQR20 treqr20
__IO_EXTERN IO_WORD treqr10;  
#define TREQR10 treqr10
__IO_EXTERN IO_LWORD newdt120;  
#define NEWDT120 newdt120
__IO_EXTERN IO_WORD newdt20;  
#define NEWDT20 newdt20
__IO_EXTERN IO_WORD newdt10;  
#define NEWDT10 newdt10
__IO_EXTERN IO_LWORD intpnd120;  
#define INTPND120 intpnd120
__IO_EXTERN IO_WORD intpnd20;  
#define INTPND20 intpnd20
__IO_EXTERN IO_WORD intpnd10;  
#define INTPND10 intpnd10
__IO_EXTERN IO_LWORD msgval120;  
#define MSGVAL120 msgval120
__IO_EXTERN IO_WORD msgval20;  
#define MSGVAL20 msgval20
__IO_EXTERN IO_WORD msgval10;  
#define MSGVAL10 msgval10
__IO_EXTERN IO_LWORD msgval340;  
#define MSGVAL340 msgval340
__IO_EXTERN CTRLR1STR ctrlr1;   /* CAN 1 Control Register */
#define CTRLR1 ctrlr1.word
#define CTRLR1_Test ctrlr1.bit._Test
#define CTRLR1_CCE ctrlr1.bit._CCE
#define CTRLR1_DAR ctrlr1.bit._DAR
#define CTRLR1_EIE ctrlr1.bit._EIE
#define CTRLR1_SIE ctrlr1.bit._SIE
#define CTRLR1_IE ctrlr1.bit._IE
#define CTRLR1_Init ctrlr1.bit._Init
__IO_EXTERN STATR1STR statr1;  
#define STATR1 statr1.word
#define STATR1_BOff statr1.bit._BOff
#define STATR1_EWarn statr1.bit._EWarn
#define STATR1_EPass statr1.bit._EPass
#define STATR1_RxOK statr1.bit._RxOK
#define STATR1_TxOK statr1.bit._TxOK
#define STATR1_LEC2 statr1.bit._LEC2
#define STATR1_LEC1 statr1.bit._LEC1
#define STATR1_LEC0 statr1.bit._LEC0
#define STATR1_LEC statr1.bitc._LEC
__IO_EXTERN ERRCNT1STR errcnt1;  
#define ERRCNT1 errcnt1.word
#define ERRCNT1_RP errcnt1.bit._RP
#define ERRCNT1_REC6 errcnt1.bit._REC6
#define ERRCNT1_REC5 errcnt1.bit._REC5
#define ERRCNT1_REC4 errcnt1.bit._REC4
#define ERRCNT1_REC3 errcnt1.bit._REC3
#define ERRCNT1_REC2 errcnt1.bit._REC2
#define ERRCNT1_REC1 errcnt1.bit._REC1
#define ERRCNT1_REC0 errcnt1.bit._REC0
#define ERRCNT1_TEC7 errcnt1.bit._TEC7
#define ERRCNT1_TEC6 errcnt1.bit._TEC6
#define ERRCNT1_TEC5 errcnt1.bit._TEC5
#define ERRCNT1_TEC4 errcnt1.bit._TEC4
#define ERRCNT1_TEC3 errcnt1.bit._TEC3
#define ERRCNT1_TEC2 errcnt1.bit._TEC2
#define ERRCNT1_TEC1 errcnt1.bit._TEC1
#define ERRCNT1_TEC0 errcnt1.bit._TEC0
#define ERRCNT1_REC errcnt1.bitc._REC
#define ERRCNT1_TEC errcnt1.bitc._TEC
__IO_EXTERN BTR1STR btr1;  
#define BTR1 btr1.word
#define BTR1_Tseg22 btr1.bit._Tseg22
#define BTR1_Tseg21 btr1.bit._Tseg21
#define BTR1_Tseg20 btr1.bit._Tseg20
#define BTR1_Tseg13 btr1.bit._Tseg13
#define BTR1_Tseg12 btr1.bit._Tseg12
#define BTR1_Tseg11 btr1.bit._Tseg11
#define BTR1_Tseg10 btr1.bit._Tseg10
#define BTR1_SJW1 btr1.bit._SJW1
#define BTR1_SJW0 btr1.bit._SJW0
#define BTR1_BRP5 btr1.bit._BRP5
#define BTR1_BRP4 btr1.bit._BRP4
#define BTR1_BRP3 btr1.bit._BRP3
#define BTR1_BRP2 btr1.bit._BRP2
#define BTR1_BRP1 btr1.bit._BRP1
#define BTR1_BRP0 btr1.bit._BRP0
#define BTR1_Tseg2 btr1.bitc._Tseg2
#define BTR1_Tseg1 btr1.bitc._Tseg1
#define BTR1_SJW btr1.bitc._SJW
#define BTR1_BRP btr1.bitc._BRP
__IO_EXTERN IO_WORD intr1;  
#define INTR1 intr1
__IO_EXTERN TESTR1STR testr1;  
#define TESTR1 testr1.word
#define TESTR1_Rx testr1.bit._Rx
#define TESTR1_Tx1 testr1.bit._Tx1
#define TESTR1_Tx0 testr1.bit._Tx0
#define TESTR1_LBack testr1.bit._LBack
#define TESTR1_Silent testr1.bit._Silent
#define TESTR1_Basic testr1.bit._Basic
#define TESTR1_Tx testr1.bitc._Tx
__IO_EXTERN BRPER1STR brper1;  
#define BRPER1 brper1.word
#define BRPER1_BRPE3 brper1.bit._BRPE3
#define BRPER1_BRPE2 brper1.bit._BRPE2
#define BRPER1_BRPE1 brper1.bit._BRPE1
#define BRPER1_BRPE0 brper1.bit._BRPE0
#define BRPER1_BRPE brper1.bitc._BRPE
__IO_EXTERN BRPE1STR brpe1;  
#define BRPE1 brpe1.word
__IO_EXTERN IO_WORD cbsync1;  
#define CBSYNC1 cbsync1
__IO_EXTERN IF1CREQ1STR if1creq1;   /* CAN 1 IF 1 */
#define IF1CREQ1 if1creq1.word
#define IF1CREQ1_Busy if1creq1.bit._Busy
#define IF1CREQ1_MN5 if1creq1.bit._MN5
#define IF1CREQ1_MN4 if1creq1.bit._MN4
#define IF1CREQ1_MN3 if1creq1.bit._MN3
#define IF1CREQ1_MN2 if1creq1.bit._MN2
#define IF1CREQ1_MN1 if1creq1.bit._MN1
#define IF1CREQ1_MN0 if1creq1.bit._MN0
#define IF1CREQ1_MN if1creq1.bitc._MN
__IO_EXTERN IF1CMSK1STR if1cmsk1;  
#define IF1CMSK1 if1cmsk1.word
#define IF1CMSK1_WR if1cmsk1.bit._WR
#define IF1CMSK1_Mask if1cmsk1.bit._Mask
#define IF1CMSK1_Arb if1cmsk1.bit._Arb
#define IF1CMSK1_Control if1cmsk1.bit._Control
#define IF1CMSK1_CIP if1cmsk1.bit._CIP
#define IF1CMSK1_TxReq if1cmsk1.bit._TxReq
#define IF1CMSK1_DataA if1cmsk1.bit._DataA
#define IF1CMSK1_DataB if1cmsk1.bit._DataB
__IO_EXTERN IO_LWORD if1msk121;  
#define IF1MSK121 if1msk121
__IO_EXTERN IF1MSK21STR if1msk21;  
#define IF1MSK21 if1msk21.word
#define IF1MSK21_MXtd if1msk21.bit._MXtd
#define IF1MSK21_MDir if1msk21.bit._MDir
__IO_EXTERN IO_WORD if1msk11;  
#define IF1MSK11 if1msk11
__IO_EXTERN IO_LWORD if1arb121;  
#define IF1ARB121 if1arb121
__IO_EXTERN IF1ARB21STR if1arb21;  
#define IF1ARB21 if1arb21.word
#define IF1ARB21_MsgVal if1arb21.bit._MsgVal
#define IF1ARB21_Xtd if1arb21.bit._Xtd
#define IF1ARB21_DIR if1arb21.bit._DIR
__IO_EXTERN IO_WORD if1arb11;  
#define IF1ARB11 if1arb11
__IO_EXTERN IF1MCTR1STR if1mctr1;  
#define IF1MCTR1 if1mctr1.word
#define IF1MCTR1_NewDat if1mctr1.bit._NewDat
#define IF1MCTR1_MsgLst if1mctr1.bit._MsgLst
#define IF1MCTR1_IntPnd if1mctr1.bit._IntPnd
#define IF1MCTR1_UMask if1mctr1.bit._UMask
#define IF1MCTR1_TxIE if1mctr1.bit._TxIE
#define IF1MCTR1_RxIE if1mctr1.bit._RxIE
#define IF1MCTR1_RmtEn if1mctr1.bit._RmtEn
#define IF1MCTR1_TxRqst if1mctr1.bit._TxRqst
#define IF1MCTR1_EoB if1mctr1.bit._EoB
#define IF1MCTR1_DLC3 if1mctr1.bit._DLC3
#define IF1MCTR1_DLC2 if1mctr1.bit._DLC2
#define IF1MCTR1_DLC1 if1mctr1.bit._DLC1
#define IF1MCTR1_DLC0 if1mctr1.bit._DLC0
#define IF1MCTR1_DLC if1mctr1.bitc._DLC
__IO_EXTERN IO_LWORD if1dta121;  
#define IF1DTA121 if1dta121
__IO_EXTERN IO_WORD if1dta11;  
#define IF1DTA11 if1dta11
__IO_EXTERN IO_WORD if1dta21;  
#define IF1DTA21 if1dta21
__IO_EXTERN IO_LWORD if1dtb121;  
#define IF1DTB121 if1dtb121
__IO_EXTERN IO_WORD if1dtb11;  
#define IF1DTB11 if1dtb11
__IO_EXTERN IO_WORD if1dtb21;  
#define IF1DTB21 if1dtb21
__IO_EXTERN IO_LWORD if1dta_swp121;  
#define IF1DTA_SWP121 if1dta_swp121
__IO_EXTERN IO_WORD if1dta_swp21;  
#define IF1DTA_SWP21 if1dta_swp21
__IO_EXTERN IO_WORD if1dta_swp11;  
#define IF1DTA_SWP11 if1dta_swp11
__IO_EXTERN IO_LWORD if1dtb_swp121;  
#define IF1DTB_SWP121 if1dtb_swp121
__IO_EXTERN IO_WORD if1dtb_swp21;  
#define IF1DTB_SWP21 if1dtb_swp21
__IO_EXTERN IO_WORD if1dtb_swp11;  
#define IF1DTB_SWP11 if1dtb_swp11
__IO_EXTERN IF2CREQ1STR if2creq1;   /* CAN 1 IF 2 */
#define IF2CREQ1 if2creq1.word
#define IF2CREQ1_Busy if2creq1.bit._Busy
#define IF2CREQ1_MN5 if2creq1.bit._MN5
#define IF2CREQ1_MN4 if2creq1.bit._MN4
#define IF2CREQ1_MN3 if2creq1.bit._MN3
#define IF2CREQ1_MN2 if2creq1.bit._MN2
#define IF2CREQ1_MN1 if2creq1.bit._MN1
#define IF2CREQ1_MN0 if2creq1.bit._MN0
#define IF2CREQ1_MN if2creq1.bitc._MN
__IO_EXTERN IF2CMSK1STR if2cmsk1;  
#define IF2CMSK1 if2cmsk1.word
#define IF2CMSK1_WR if2cmsk1.bit._WR
#define IF2CMSK1_Mask if2cmsk1.bit._Mask
#define IF2CMSK1_Arb if2cmsk1.bit._Arb
#define IF2CMSK1_Control if2cmsk1.bit._Control
#define IF2CMSK1_CIP if2cmsk1.bit._CIP
#define IF2CMSK1_TxReq if2cmsk1.bit._TxReq
#define IF2CMSK1_DataA if2cmsk1.bit._DataA
#define IF2CMSK1_DataB if2cmsk1.bit._DataB
__IO_EXTERN IO_LWORD if2msk121;  
#define IF2MSK121 if2msk121
__IO_EXTERN IF2MSK21STR if2msk21;  
#define IF2MSK21 if2msk21.word
#define IF2MSK21_MXtd if2msk21.bit._MXtd
#define IF2MSK21_MDir if2msk21.bit._MDir
__IO_EXTERN IO_WORD if2msk11;  
#define IF2MSK11 if2msk11
__IO_EXTERN IO_LWORD if2arb121;  
#define IF2ARB121 if2arb121
__IO_EXTERN IF2ARB21STR if2arb21;  
#define IF2ARB21 if2arb21.word
#define IF2ARB21_MsgVal if2arb21.bit._MsgVal
#define IF2ARB21_Xtd if2arb21.bit._Xtd
#define IF2ARB21_DIR if2arb21.bit._DIR
__IO_EXTERN IO_WORD if2arb11;  
#define IF2ARB11 if2arb11
__IO_EXTERN IF2MCTR1STR if2mctr1;  
#define IF2MCTR1 if2mctr1.word
#define IF2MCTR1_NewDat if2mctr1.bit._NewDat
#define IF2MCTR1_MsgLst if2mctr1.bit._MsgLst
#define IF2MCTR1_IntPnd if2mctr1.bit._IntPnd
#define IF2MCTR1_UMask if2mctr1.bit._UMask
#define IF2MCTR1_TxIE if2mctr1.bit._TxIE
#define IF2MCTR1_RxIE if2mctr1.bit._RxIE
#define IF2MCTR1_RmtEn if2mctr1.bit._RmtEn
#define IF2MCTR1_TxRqst if2mctr1.bit._TxRqst
#define IF2MCTR1_EoB if2mctr1.bit._EoB
#define IF2MCTR1_DLC3 if2mctr1.bit._DLC3
#define IF2MCTR1_DLC2 if2mctr1.bit._DLC2
#define IF2MCTR1_DLC1 if2mctr1.bit._DLC1
#define IF2MCTR1_DLC0 if2mctr1.bit._DLC0
#define IF2MCTR1_DLC if2mctr1.bitc._DLC
__IO_EXTERN IO_LWORD if2dta121;  
#define IF2DTA121 if2dta121
__IO_EXTERN IO_WORD if2dta11;  
#define IF2DTA11 if2dta11
__IO_EXTERN IO_WORD if2dta21;  
#define IF2DTA21 if2dta21
__IO_EXTERN IO_LWORD if2dtb121;  
#define IF2DTB121 if2dtb121
__IO_EXTERN IO_WORD if2dtb11;  
#define IF2DTB11 if2dtb11
__IO_EXTERN IO_WORD if2dtb21;  
#define IF2DTB21 if2dtb21
__IO_EXTERN IO_LWORD if2dta_swp121;  
#define IF2DTA_SWP121 if2dta_swp121
__IO_EXTERN IO_WORD if2dta_swp21;  
#define IF2DTA_SWP21 if2dta_swp21
__IO_EXTERN IO_WORD if2dta_swp11;  
#define IF2DTA_SWP11 if2dta_swp11
__IO_EXTERN IO_LWORD if2dtb_swp121;  
#define IF2DTB_SWP121 if2dtb_swp121
__IO_EXTERN IO_WORD if2dtb_swp21;  
#define IF2DTB_SWP21 if2dtb_swp21
__IO_EXTERN IO_WORD if2dtb_swp11;  
#define IF2DTB_SWP11 if2dtb_swp11
__IO_EXTERN IO_LWORD treqr121;   /* CAN 1 Status Flags */
#define TREQR121 treqr121
__IO_EXTERN IO_WORD treqr21;  
#define TREQR21 treqr21
__IO_EXTERN IO_WORD treqr11;  
#define TREQR11 treqr11
__IO_EXTERN IO_LWORD newdt121;  
#define NEWDT121 newdt121
__IO_EXTERN IO_WORD newdt21;  
#define NEWDT21 newdt21
__IO_EXTERN IO_WORD newdt11;  
#define NEWDT11 newdt11
__IO_EXTERN IO_LWORD intpnd121;  
#define INTPND121 intpnd121
__IO_EXTERN IO_WORD intpnd21;  
#define INTPND21 intpnd21
__IO_EXTERN IO_WORD intpnd11;  
#define INTPND11 intpnd11
__IO_EXTERN IO_LWORD msgval121;  
#define MSGVAL121 msgval121
__IO_EXTERN IO_WORD msgval21;  
#define MSGVAL21 msgval21
__IO_EXTERN IO_WORD msgval11;  
#define MSGVAL11 msgval11
__IO_EXTERN CTRLR2STR ctrlr2;   /* CAN 2 Control Register */
#define CTRLR2 ctrlr2.word
#define CTRLR2_Test ctrlr2.bit._Test
#define CTRLR2_CCE ctrlr2.bit._CCE
#define CTRLR2_DAR ctrlr2.bit._DAR
#define CTRLR2_EIE ctrlr2.bit._EIE
#define CTRLR2_SIE ctrlr2.bit._SIE
#define CTRLR2_IE ctrlr2.bit._IE
#define CTRLR2_Init ctrlr2.bit._Init
__IO_EXTERN STATR2STR statr2;  
#define STATR2 statr2.word
#define STATR2_BOff statr2.bit._BOff
#define STATR2_EWarn statr2.bit._EWarn
#define STATR2_EPass statr2.bit._EPass
#define STATR2_RxOK statr2.bit._RxOK
#define STATR2_TxOK statr2.bit._TxOK
#define STATR2_LEC2 statr2.bit._LEC2
#define STATR2_LEC1 statr2.bit._LEC1
#define STATR2_LEC0 statr2.bit._LEC0
#define STATR2_LEC statr2.bitc._LEC
__IO_EXTERN ERRCNT2STR errcnt2;  
#define ERRCNT2 errcnt2.word
#define ERRCNT2_RP errcnt2.bit._RP
#define ERRCNT2_REC6 errcnt2.bit._REC6
#define ERRCNT2_REC5 errcnt2.bit._REC5
#define ERRCNT2_REC4 errcnt2.bit._REC4
#define ERRCNT2_REC3 errcnt2.bit._REC3
#define ERRCNT2_REC2 errcnt2.bit._REC2
#define ERRCNT2_REC1 errcnt2.bit._REC1
#define ERRCNT2_REC0 errcnt2.bit._REC0
#define ERRCNT2_TEC7 errcnt2.bit._TEC7
#define ERRCNT2_TEC6 errcnt2.bit._TEC6
#define ERRCNT2_TEC5 errcnt2.bit._TEC5
#define ERRCNT2_TEC4 errcnt2.bit._TEC4
#define ERRCNT2_TEC3 errcnt2.bit._TEC3
#define ERRCNT2_TEC2 errcnt2.bit._TEC2
#define ERRCNT2_TEC1 errcnt2.bit._TEC1
#define ERRCNT2_TEC0 errcnt2.bit._TEC0
#define ERRCNT2_REC errcnt2.bitc._REC
#define ERRCNT2_TEC errcnt2.bitc._TEC
__IO_EXTERN BTR2STR btr2;  
#define BTR2 btr2.word
#define BTR2_Tseg22 btr2.bit._Tseg22
#define BTR2_Tseg21 btr2.bit._Tseg21
#define BTR2_Tseg20 btr2.bit._Tseg20
#define BTR2_Tseg13 btr2.bit._Tseg13
#define BTR2_Tseg12 btr2.bit._Tseg12
#define BTR2_Tseg11 btr2.bit._Tseg11
#define BTR2_Tseg10 btr2.bit._Tseg10
#define BTR2_SJW1 btr2.bit._SJW1
#define BTR2_SJW0 btr2.bit._SJW0
#define BTR2_BRP5 btr2.bit._BRP5
#define BTR2_BRP4 btr2.bit._BRP4
#define BTR2_BRP3 btr2.bit._BRP3
#define BTR2_BRP2 btr2.bit._BRP2
#define BTR2_BRP1 btr2.bit._BRP1
#define BTR2_BRP0 btr2.bit._BRP0
#define BTR2_Tseg2 btr2.bitc._Tseg2
#define BTR2_Tseg1 btr2.bitc._Tseg1
#define BTR2_SJW btr2.bitc._SJW
#define BTR2_BRP btr2.bitc._BRP
__IO_EXTERN IO_WORD intr2;  
#define INTR2 intr2
__IO_EXTERN TESTR2STR testr2;  
#define TESTR2 testr2.word
#define TESTR2_Rx testr2.bit._Rx
#define TESTR2_Tx1 testr2.bit._Tx1
#define TESTR2_Tx0 testr2.bit._Tx0
#define TESTR2_LBack testr2.bit._LBack
#define TESTR2_Silent testr2.bit._Silent
#define TESTR2_Basic testr2.bit._Basic
#define TESTR2_Tx testr2.bitc._Tx
__IO_EXTERN BRPER2STR brper2;  
#define BRPER2 brper2.word
#define BRPER2_BRPE3 brper2.bit._BRPE3
#define BRPER2_BRPE2 brper2.bit._BRPE2
#define BRPER2_BRPE1 brper2.bit._BRPE1
#define BRPER2_BRPE0 brper2.bit._BRPE0
#define BRPER2_BRPE brper2.bitc._BRPE
__IO_EXTERN BRPE2STR brpe2;  
#define BRPE2 brpe2.word
__IO_EXTERN CBSYNC2STR cbsync2;  
#define CBSYNC2 cbsync2.word
__IO_EXTERN IF1CREQ2STR if1creq2;   /* CAN 2 IF 1 */
#define IF1CREQ2 if1creq2.word
#define IF1CREQ2_Busy if1creq2.bit._Busy
#define IF1CREQ2_MN5 if1creq2.bit._MN5
#define IF1CREQ2_MN4 if1creq2.bit._MN4
#define IF1CREQ2_MN3 if1creq2.bit._MN3
#define IF1CREQ2_MN2 if1creq2.bit._MN2
#define IF1CREQ2_MN1 if1creq2.bit._MN1
#define IF1CREQ2_MN0 if1creq2.bit._MN0
#define IF1CREQ2_MN if1creq2.bitc._MN
__IO_EXTERN IF1CMSK2STR if1cmsk2;  
#define IF1CMSK2 if1cmsk2.word
#define IF1CMSK2_WR if1cmsk2.bit._WR
#define IF1CMSK2_Mask if1cmsk2.bit._Mask
#define IF1CMSK2_Arb if1cmsk2.bit._Arb
#define IF1CMSK2_Control if1cmsk2.bit._Control
#define IF1CMSK2_CIP if1cmsk2.bit._CIP
#define IF1CMSK2_TxReq if1cmsk2.bit._TxReq
#define IF1CMSK2_DataA if1cmsk2.bit._DataA
#define IF1CMSK2_DataB if1cmsk2.bit._DataB
__IO_EXTERN IO_LWORD if1msk122;  
#define IF1MSK122 if1msk122
__IO_EXTERN IF1MSK22STR if1msk22;  
#define IF1MSK22 if1msk22.word
#define IF1MSK22_MXtd if1msk22.bit._MXtd
#define IF1MSK22_MDir if1msk22.bit._MDir
__IO_EXTERN IO_WORD if1msk12;  
#define IF1MSK12 if1msk12
__IO_EXTERN IO_LWORD if1arb122;  
#define IF1ARB122 if1arb122
__IO_EXTERN IF1ARB22STR if1arb22;  
#define IF1ARB22 if1arb22.word
#define IF1ARB22_MsgVal if1arb22.bit._MsgVal
#define IF1ARB22_Xtd if1arb22.bit._Xtd
#define IF1ARB22_DIR if1arb22.bit._DIR
__IO_EXTERN IO_WORD if1arb12;  
#define IF1ARB12 if1arb12
__IO_EXTERN IF1MCTR2STR if1mctr2;  
#define IF1MCTR2 if1mctr2.word
#define IF1MCTR2_NewDat if1mctr2.bit._NewDat
#define IF1MCTR2_MsgLst if1mctr2.bit._MsgLst
#define IF1MCTR2_IntPnd if1mctr2.bit._IntPnd
#define IF1MCTR2_UMask if1mctr2.bit._UMask
#define IF1MCTR2_TxIE if1mctr2.bit._TxIE
#define IF1MCTR2_RxIE if1mctr2.bit._RxIE
#define IF1MCTR2_RmtEn if1mctr2.bit._RmtEn
#define IF1MCTR2_TxRqst if1mctr2.bit._TxRqst
#define IF1MCTR2_EoB if1mctr2.bit._EoB
#define IF1MCTR2_DLC3 if1mctr2.bit._DLC3
#define IF1MCTR2_DLC2 if1mctr2.bit._DLC2
#define IF1MCTR2_DLC1 if1mctr2.bit._DLC1
#define IF1MCTR2_DLC0 if1mctr2.bit._DLC0
#define IF1MCTR2_DLC if1mctr2.bitc._DLC
__IO_EXTERN IO_LWORD if1dta122;  
#define IF1DTA122 if1dta122
__IO_EXTERN IO_WORD if1dta12;  
#define IF1DTA12 if1dta12
__IO_EXTERN IO_WORD if1dta22;  
#define IF1DTA22 if1dta22
__IO_EXTERN IO_LWORD if1dtb122;  
#define IF1DTB122 if1dtb122
__IO_EXTERN IO_WORD if1dtb12;  
#define IF1DTB12 if1dtb12
__IO_EXTERN IO_WORD if1dtb22;  
#define IF1DTB22 if1dtb22
__IO_EXTERN IO_LWORD if1dta_swp122;  
#define IF1DTA_SWP122 if1dta_swp122
__IO_EXTERN IO_WORD if1dta_swp22;  
#define IF1DTA_SWP22 if1dta_swp22
__IO_EXTERN IO_WORD if1dta_swp12;  
#define IF1DTA_SWP12 if1dta_swp12
__IO_EXTERN IO_LWORD if1dtb_swp122;  
#define IF1DTB_SWP122 if1dtb_swp122
__IO_EXTERN IO_WORD if1dtb_swp22;  
#define IF1DTB_SWP22 if1dtb_swp22
__IO_EXTERN IO_WORD if1dtb_swp12;  
#define IF1DTB_SWP12 if1dtb_swp12
__IO_EXTERN IF2CREQ2STR if2creq2;   /* CAN 2 IF 2 */
#define IF2CREQ2 if2creq2.word
#define IF2CREQ2_Busy if2creq2.bit._Busy
#define IF2CREQ2_MN5 if2creq2.bit._MN5
#define IF2CREQ2_MN4 if2creq2.bit._MN4
#define IF2CREQ2_MN3 if2creq2.bit._MN3
#define IF2CREQ2_MN2 if2creq2.bit._MN2
#define IF2CREQ2_MN1 if2creq2.bit._MN1
#define IF2CREQ2_MN0 if2creq2.bit._MN0
#define IF2CREQ2_MN if2creq2.bitc._MN
__IO_EXTERN IF2CMSK2STR if2cmsk2;  
#define IF2CMSK2 if2cmsk2.word
#define IF2CMSK2_WR if2cmsk2.bit._WR
#define IF2CMSK2_Mask if2cmsk2.bit._Mask
#define IF2CMSK2_Arb if2cmsk2.bit._Arb
#define IF2CMSK2_Control if2cmsk2.bit._Control
#define IF2CMSK2_CIP if2cmsk2.bit._CIP
#define IF2CMSK2_TxReq if2cmsk2.bit._TxReq
#define IF2CMSK2_DataA if2cmsk2.bit._DataA
#define IF2CMSK2_DataB if2cmsk2.bit._DataB
__IO_EXTERN IO_LWORD if2msk122;  
#define IF2MSK122 if2msk122
__IO_EXTERN IF2MSK22STR if2msk22;  
#define IF2MSK22 if2msk22.word
#define IF2MSK22_MXtd if2msk22.bit._MXtd
#define IF2MSK22_MDir if2msk22.bit._MDir
__IO_EXTERN IO_WORD if2msk12;  
#define IF2MSK12 if2msk12
__IO_EXTERN IO_LWORD if2arb122;  
#define IF2ARB122 if2arb122
__IO_EXTERN IF2ARB22STR if2arb22;  
#define IF2ARB22 if2arb22.word
#define IF2ARB22_MsgVal if2arb22.bit._MsgVal
#define IF2ARB22_Xtd if2arb22.bit._Xtd
#define IF2ARB22_DIR if2arb22.bit._DIR
__IO_EXTERN IO_WORD if2arb12;  
#define IF2ARB12 if2arb12
__IO_EXTERN IF2MCTR2STR if2mctr2;  
#define IF2MCTR2 if2mctr2.word
#define IF2MCTR2_NewDat if2mctr2.bit._NewDat
#define IF2MCTR2_MsgLst if2mctr2.bit._MsgLst
#define IF2MCTR2_IntPnd if2mctr2.bit._IntPnd
#define IF2MCTR2_UMask if2mctr2.bit._UMask
#define IF2MCTR2_TxIE if2mctr2.bit._TxIE
#define IF2MCTR2_RxIE if2mctr2.bit._RxIE
#define IF2MCTR2_RmtEn if2mctr2.bit._RmtEn
#define IF2MCTR2_TxRqst if2mctr2.bit._TxRqst
#define IF2MCTR2_EoB if2mctr2.bit._EoB
#define IF2MCTR2_DLC3 if2mctr2.bit._DLC3
#define IF2MCTR2_DLC2 if2mctr2.bit._DLC2
#define IF2MCTR2_DLC1 if2mctr2.bit._DLC1
#define IF2MCTR2_DLC0 if2mctr2.bit._DLC0
#define IF2MCTR2_DLC if2mctr2.bitc._DLC
__IO_EXTERN IO_LWORD if2dta122;  
#define IF2DTA122 if2dta122
__IO_EXTERN IO_WORD if2dta12;  
#define IF2DTA12 if2dta12
__IO_EXTERN IO_WORD if2dta22;  
#define IF2DTA22 if2dta22
__IO_EXTERN IO_LWORD if2dtb122;  
#define IF2DTB122 if2dtb122
__IO_EXTERN IO_WORD if2dtb12;  
#define IF2DTB12 if2dtb12
__IO_EXTERN IO_WORD if2dtb22;  
#define IF2DTB22 if2dtb22
__IO_EXTERN IO_LWORD if2dta_swp122;  
#define IF2DTA_SWP122 if2dta_swp122
__IO_EXTERN IO_WORD if2dta_swp22;  
#define IF2DTA_SWP22 if2dta_swp22
__IO_EXTERN IO_WORD if2dta_swp12;  
#define IF2DTA_SWP12 if2dta_swp12
__IO_EXTERN IO_LWORD if2dtb_swp122;  
#define IF2DTB_SWP122 if2dtb_swp122
__IO_EXTERN IO_WORD if2dtb_swp22;  
#define IF2DTB_SWP22 if2dtb_swp22
__IO_EXTERN IO_WORD if2dtb_swp12;  
#define IF2DTB_SWP12 if2dtb_swp12
__IO_EXTERN IO_LWORD treqr122;   /* CAN 2 Status Flags */
#define TREQR122 treqr122
__IO_EXTERN IO_WORD treqr22;  
#define TREQR22 treqr22
__IO_EXTERN IO_WORD treqr12;  
#define TREQR12 treqr12
__IO_EXTERN IO_LWORD newdt122;  
#define NEWDT122 newdt122
__IO_EXTERN IO_WORD newdt22;  
#define NEWDT22 newdt22
__IO_EXTERN IO_WORD newdt12;  
#define NEWDT12 newdt12
__IO_EXTERN IO_LWORD intpnd122;  
#define INTPND122 intpnd122
__IO_EXTERN IO_WORD intpnd22;  
#define INTPND22 intpnd22
__IO_EXTERN IO_WORD intpnd12;  
#define INTPND12 intpnd12
__IO_EXTERN IO_LWORD msgval122;  
#define MSGVAL122 msgval122
__IO_EXTERN IO_WORD msgval22;  
#define MSGVAL22 msgval22
__IO_EXTERN IO_WORD msgval12;  
#define MSGVAL12 msgval12
/* include : INC467_CAN.INC */
/*-------------------------------------------------------------------*/
/* INC467.CAN :  Old bit name of CAN Registers */

/* alias macro definition for CAN Bits */
#define BTR0_Tsg22 btr0.bit._Tseg22
#define BTR0_Tsg21 btr0.bit._Tseg21
#define BTR0_Tsg20 btr0.bit._Tseg20
#define BTR0_Tsg2 btr0.bitc._Tseg2
#define BTR0_Tsg13 btr0.bit._Tseg13
#define BTR0_Tsg12 btr0.bit._Tseg12
#define BTR0_Tsg11 btr0.bit._Tseg11
#define BTR0_Tsg10 btr0.bit._Tseg10
#define BTR0_Tsg1 btr0.bitc._Tseg1
#define IF1CMSK0_Contr if1cmsk0.bit._Control
#define IF2CMSK0_Contr if2cmsk0.bit._Control

#define BTR1_Tsg22 btr1.bit._Tseg22
#define BTR1_Tsg21 btr1.bit._Tseg21
#define BTR1_Tsg20 btr1.bit._Tseg20
#define BTR1_Tsg2 btr1.bitc._Tseg2
#define BTR1_Tsg13 btr1.bit._Tseg13
#define BTR1_Tsg12 btr1.bit._Tseg12
#define BTR1_Tsg11 btr1.bit._Tseg11
#define BTR1_Tsg10 btr1.bit._Tseg10
#define BTR1_Tsg1 btr1.bitc._Tseg1
#define IF1CMSK1_Contr if1cmsk1.bit._Control
#define IF2CMSK1_Contr if2cmsk1.bit._Control

#define BTR2_Tsg22 btr2.bit._Tseg22
#define BTR2_Tsg21 btr2.bit._Tseg21
#define BTR2_Tsg20 btr2.bit._Tseg20
#define BTR2_Tsg2 btr2.bitc._Tseg2
#define BTR2_Tsg13 btr2.bit._Tseg13
#define BTR2_Tsg12 btr2.bit._Tseg12
#define BTR2_Tsg11 btr2.bit._Tseg11
#define BTR2_Tsg10 btr2.bit._Tseg10
#define BTR2_Tsg1 btr2.bitc._Tseg1
#define IF1CMSK2_Contr if1cmsk2.bit._Control
#define IF2CMSK2_Contr if2cmsk2.bit._Control
/*-------------------------------------------------------------------*/
__IO_EXTERN BCTRLSTR bctrl;   /* EDSU/MPU Registers */
#define BCTRL bctrl.lword
#define BCTRL_SR bctrl.bit._SR
#define BCTRL_SW bctrl.bit._SW
#define BCTRL_SX bctrl.bit._SX
#define BCTRL_UR bctrl.bit._UR
#define BCTRL_UW bctrl.bit._UW
#define BCTRL_UX bctrl.bit._UX
#define BCTRL_FCPU bctrl.bit._FCPU
#define BCTRL_FDMA bctrl.bit._FDMA
#define BCTRL_EEMM bctrl.bit._EEMM
#define BCTRL_PFD bctrl.bit._PFD
#define BCTRL_SINT1 bctrl.bit._SINT1
#define BCTRL_SINT0 bctrl.bit._SINT0
#define BCTRL_EINT1 bctrl.bit._EINT1
#define BCTRL_EINT0 bctrl.bit._EINT0
#define BCTRL_EINTT bctrl.bit._EINTT
#define BCTRL_EINTR bctrl.bit._EINTR
#define BCTRL_SINT bctrl.bitc._SINT
#define BCTRL_EINT bctrl.bitc._EINT
__IO_EXTERN BSTATSTR bstat;  
#define BSTAT bstat.lword
#define BSTAT_IDX4 bstat.bit._IDX4
#define BSTAT_IDX3 bstat.bit._IDX3
#define BSTAT_IDX2 bstat.bit._IDX2
#define BSTAT_IDX1 bstat.bit._IDX1
#define BSTAT_IDX0 bstat.bit._IDX0
#define BSTAT_CDMA bstat.bit._CDMA
#define BSTAT_CSZ1 bstat.bit._CSZ1
#define BSTAT_CSZ0 bstat.bit._CSZ0
#define BSTAT_CRW1 bstat.bit._CRW1
#define BSTAT_CRW0 bstat.bit._CRW0
#define BSTAT_PV bstat.bit._PV
#define BSTAT_RST bstat.bit._RST
#define BSTAT_INT1 bstat.bit._INT1
#define BSTAT_INT0 bstat.bit._INT0
#define BSTAT_INTT bstat.bit._INTT
#define BSTAT_INTR bstat.bit._INTR
#define BSTAT_IDX bstat.bitc._IDX
#define BSTAT_CSZ bstat.bitc._CSZ
#define BSTAT_CRW bstat.bitc._CRW
#define BSTAT_INT bstat.bitc._INT
__IO_EXTERN IO_LWORD biac;  
#define BIAC biac
__IO_EXTERN IO_LWORD boac;  
#define BOAC boac
__IO_EXTERN BIRQSTR birq;  
#define BIRQ birq.lword
#define BIRQ_BD31 birq.bit._BD31
#define BIRQ_BD30 birq.bit._BD30
#define BIRQ_BD29 birq.bit._BD29
#define BIRQ_BD28 birq.bit._BD28
#define BIRQ_BD27 birq.bit._BD27
#define BIRQ_BD26 birq.bit._BD26
#define BIRQ_BD25 birq.bit._BD25
#define BIRQ_BD24 birq.bit._BD24
#define BIRQ_BD23 birq.bit._BD23
#define BIRQ_BD22 birq.bit._BD22
#define BIRQ_BD21 birq.bit._BD21
#define BIRQ_BD20 birq.bit._BD20
#define BIRQ_BD19 birq.bit._BD19
#define BIRQ_BD18 birq.bit._BD18
#define BIRQ_BD17 birq.bit._BD17
#define BIRQ_BD16 birq.bit._BD16
#define BIRQ_BD15 birq.bit._BD15
#define BIRQ_BD14 birq.bit._BD14
#define BIRQ_BD13 birq.bit._BD13
#define BIRQ_BD12 birq.bit._BD12
#define BIRQ_BD11 birq.bit._BD11
#define BIRQ_BD10 birq.bit._BD10
#define BIRQ_BD9 birq.bit._BD9
#define BIRQ_BD8 birq.bit._BD8
#define BIRQ_BD7 birq.bit._BD7
#define BIRQ_BD6 birq.bit._BD6
#define BIRQ_BD5 birq.bit._BD5
#define BIRQ_BD4 birq.bit._BD4
#define BIRQ_BD3 birq.bit._BD3
#define BIRQ_BD2 birq.bit._BD2
#define BIRQ_BD1 birq.bit._BD1
#define BIRQ_BD0 birq.bit._BD0
__IO_EXTERN BCR0STR bcr0;  
#define BCR0 bcr0.lword
#define BCR0_SRX1 bcr0.bit._SRX1
#define BCR0_SW1 bcr0.bit._SW1
#define BCR0_SRX0 bcr0.bit._SRX0
#define BCR0_SW0 bcr0.bit._SW0
#define BCR0_URX1 bcr0.bit._URX1
#define BCR0_UW1 bcr0.bit._UW1
#define BCR0_URX0 bcr0.bit._URX0
#define BCR0_UW0 bcr0.bit._UW0
#define BCR0_MPE bcr0.bit._MPE
#define BCR0_COMB bcr0.bit._COMB
#define BCR0_CTC1 bcr0.bit._CTC1
#define BCR0_CTC0 bcr0.bit._CTC0
#define BCR0_OBS1 bcr0.bit._OBS1
#define BCR0_OBS0 bcr0.bit._OBS0
#define BCR0_OBT1 bcr0.bit._OBT1
#define BCR0_OBT0 bcr0.bit._OBT0
#define BCR0_EP3 bcr0.bit._EP3
#define BCR0_EP2 bcr0.bit._EP2
#define BCR0_EP1 bcr0.bit._EP1
#define BCR0_EP0 bcr0.bit._EP0
#define BCR0_EM1 bcr0.bit._EM1
#define BCR0_EM0 bcr0.bit._EM0
#define BCR0_ER1 bcr0.bit._ER1
#define BCR0_ER0 bcr0.bit._ER0
#define BCR0_CTC bcr0.bitc._CTC
#define BCR0_OBS bcr0.bitc._OBS
#define BCR0_OBT bcr0.bitc._OBT
#define BCR0_EP bcr0.bitc._EP
#define BCR0_EM bcr0.bitc._EM
#define BCR0_ER bcr0.bitc._ER
__IO_EXTERN BCR1STR bcr1;  
#define BCR1 bcr1.lword
#define BCR1_SRX1 bcr1.bit._SRX1
#define BCR1_SW1 bcr1.bit._SW1
#define BCR1_SRX0 bcr1.bit._SRX0
#define BCR1_SW0 bcr1.bit._SW0
#define BCR1_URX1 bcr1.bit._URX1
#define BCR1_UW1 bcr1.bit._UW1
#define BCR1_URX0 bcr1.bit._URX0
#define BCR1_UW0 bcr1.bit._UW0
#define BCR1_MPE bcr1.bit._MPE
#define BCR1_COMB bcr1.bit._COMB
#define BCR1_CTC1 bcr1.bit._CTC1
#define BCR1_CTC0 bcr1.bit._CTC0
#define BCR1_OBS1 bcr1.bit._OBS1
#define BCR1_OBS0 bcr1.bit._OBS0
#define BCR1_OBT1 bcr1.bit._OBT1
#define BCR1_OBT0 bcr1.bit._OBT0
#define BCR1_EP3 bcr1.bit._EP3
#define BCR1_EP2 bcr1.bit._EP2
#define BCR1_EP1 bcr1.bit._EP1
#define BCR1_EP0 bcr1.bit._EP0
#define BCR1_EM1 bcr1.bit._EM1
#define BCR1_EM0 bcr1.bit._EM0
#define BCR1_ER1 bcr1.bit._ER1
#define BCR1_ER0 bcr1.bit._ER0
#define BCR1_CTC bcr1.bitc._CTC
#define BCR1_OBS bcr1.bitc._OBS
#define BCR1_OBT bcr1.bitc._OBT
#define BCR1_EP bcr1.bitc._EP
#define BCR1_EM bcr1.bitc._EM
#define BCR1_ER bcr1.bitc._ER
__IO_EXTERN BCR2STR bcr2;  
#define BCR2 bcr2.lword
#define BCR2_SRX1 bcr2.bit._SRX1
#define BCR2_SW1 bcr2.bit._SW1
#define BCR2_SRX0 bcr2.bit._SRX0
#define BCR2_SW0 bcr2.bit._SW0
#define BCR2_URX1 bcr2.bit._URX1
#define BCR2_UW1 bcr2.bit._UW1
#define BCR2_URX0 bcr2.bit._URX0
#define BCR2_UW0 bcr2.bit._UW0
#define BCR2_MPE bcr2.bit._MPE
#define BCR2_COMB bcr2.bit._COMB
#define BCR2_CTC1 bcr2.bit._CTC1
#define BCR2_CTC0 bcr2.bit._CTC0
#define BCR2_OBS1 bcr2.bit._OBS1
#define BCR2_OBS0 bcr2.bit._OBS0
#define BCR2_OBT1 bcr2.bit._OBT1
#define BCR2_OBT0 bcr2.bit._OBT0
#define BCR2_EP3 bcr2.bit._EP3
#define BCR2_EP2 bcr2.bit._EP2
#define BCR2_EP1 bcr2.bit._EP1
#define BCR2_EP0 bcr2.bit._EP0
#define BCR2_EM1 bcr2.bit._EM1
#define BCR2_EM0 bcr2.bit._EM0
#define BCR2_ER1 bcr2.bit._ER1
#define BCR2_ER0 bcr2.bit._ER0
#define BCR2_CTC bcr2.bitc._CTC
#define BCR2_OBS bcr2.bitc._OBS
#define BCR2_OBT bcr2.bitc._OBT
#define BCR2_EP bcr2.bitc._EP
#define BCR2_EM bcr2.bitc._EM
#define BCR2_ER bcr2.bitc._ER
__IO_EXTERN BCR3STR bcr3;  
#define BCR3 bcr3.lword
#define BCR3_SRX1 bcr3.bit._SRX1
#define BCR3_SW1 bcr3.bit._SW1
#define BCR3_SRX0 bcr3.bit._SRX0
#define BCR3_SW0 bcr3.bit._SW0
#define BCR3_URX1 bcr3.bit._URX1
#define BCR3_UW1 bcr3.bit._UW1
#define BCR3_URX0 bcr3.bit._URX0
#define BCR3_UW0 bcr3.bit._UW0
#define BCR3_MPE bcr3.bit._MPE
#define BCR3_COMB bcr3.bit._COMB
#define BCR3_CTC1 bcr3.bit._CTC1
#define BCR3_CTC0 bcr3.bit._CTC0
#define BCR3_OBS1 bcr3.bit._OBS1
#define BCR3_OBS0 bcr3.bit._OBS0
#define BCR3_OBT1 bcr3.bit._OBT1
#define BCR3_OBT0 bcr3.bit._OBT0
#define BCR3_EP3 bcr3.bit._EP3
#define BCR3_EP2 bcr3.bit._EP2
#define BCR3_EP1 bcr3.bit._EP1
#define BCR3_EP0 bcr3.bit._EP0
#define BCR3_EM1 bcr3.bit._EM1
#define BCR3_EM0 bcr3.bit._EM0
#define BCR3_ER1 bcr3.bit._ER1
#define BCR3_ER0 bcr3.bit._ER0
#define BCR3_CTC bcr3.bitc._CTC
#define BCR3_OBS bcr3.bitc._OBS
#define BCR3_OBT bcr3.bitc._OBT
#define BCR3_EP bcr3.bitc._EP
#define BCR3_EM bcr3.bitc._EM
#define BCR3_ER bcr3.bitc._ER
__IO_EXTERN BCR4STR bcr4;  
#define BCR4 bcr4.lword
#define BCR4_SRX1 bcr4.bit._SRX1
#define BCR4_SW1 bcr4.bit._SW1
#define BCR4_SRX0 bcr4.bit._SRX0
#define BCR4_SW0 bcr4.bit._SW0
#define BCR4_URX1 bcr4.bit._URX1
#define BCR4_UW1 bcr4.bit._UW1
#define BCR4_URX0 bcr4.bit._URX0
#define BCR4_UW0 bcr4.bit._UW0
#define BCR4_MPE bcr4.bit._MPE
#define BCR4_COMB bcr4.bit._COMB
#define BCR4_CTC1 bcr4.bit._CTC1
#define BCR4_CTC0 bcr4.bit._CTC0
#define BCR4_OBS1 bcr4.bit._OBS1
#define BCR4_OBS0 bcr4.bit._OBS0
#define BCR4_OBT1 bcr4.bit._OBT1
#define BCR4_OBT0 bcr4.bit._OBT0
#define BCR4_EP3 bcr4.bit._EP3
#define BCR4_EP2 bcr4.bit._EP2
#define BCR4_EP1 bcr4.bit._EP1
#define BCR4_EP0 bcr4.bit._EP0
#define BCR4_EM1 bcr4.bit._EM1
#define BCR4_EM0 bcr4.bit._EM0
#define BCR4_ER1 bcr4.bit._ER1
#define BCR4_ER0 bcr4.bit._ER0
#define BCR4_CTC bcr4.bitc._CTC
#define BCR4_OBS bcr4.bitc._OBS
#define BCR4_OBT bcr4.bitc._OBT
#define BCR4_EP bcr4.bitc._EP
#define BCR4_EM bcr4.bitc._EM
#define BCR4_ER bcr4.bitc._ER
__IO_EXTERN BCR5STR bcr5;  
#define BCR5 bcr5.lword
#define BCR5_SRX1 bcr5.bit._SRX1
#define BCR5_SW1 bcr5.bit._SW1
#define BCR5_SRX0 bcr5.bit._SRX0
#define BCR5_SW0 bcr5.bit._SW0
#define BCR5_URX1 bcr5.bit._URX1
#define BCR5_UW1 bcr5.bit._UW1
#define BCR5_URX0 bcr5.bit._URX0
#define BCR5_UW0 bcr5.bit._UW0
#define BCR5_MPE bcr5.bit._MPE
#define BCR5_COMB bcr5.bit._COMB
#define BCR5_CTC1 bcr5.bit._CTC1
#define BCR5_CTC0 bcr5.bit._CTC0
#define BCR5_OBS1 bcr5.bit._OBS1
#define BCR5_OBS0 bcr5.bit._OBS0
#define BCR5_OBT1 bcr5.bit._OBT1
#define BCR5_OBT0 bcr5.bit._OBT0
#define BCR5_EP3 bcr5.bit._EP3
#define BCR5_EP2 bcr5.bit._EP2
#define BCR5_EP1 bcr5.bit._EP1
#define BCR5_EP0 bcr5.bit._EP0
#define BCR5_EM1 bcr5.bit._EM1
#define BCR5_EM0 bcr5.bit._EM0
#define BCR5_ER1 bcr5.bit._ER1
#define BCR5_ER0 bcr5.bit._ER0
#define BCR5_CTC bcr5.bitc._CTC
#define BCR5_OBS bcr5.bitc._OBS
#define BCR5_OBT bcr5.bitc._OBT
#define BCR5_EP bcr5.bitc._EP
#define BCR5_EM bcr5.bitc._EM
#define BCR5_ER bcr5.bitc._ER
__IO_EXTERN BCR6STR bcr6;  
#define BCR6 bcr6.lword
#define BCR6_SRX1 bcr6.bit._SRX1
#define BCR6_SW1 bcr6.bit._SW1
#define BCR6_SRX0 bcr6.bit._SRX0
#define BCR6_SW0 bcr6.bit._SW0
#define BCR6_URX1 bcr6.bit._URX1
#define BCR6_UW1 bcr6.bit._UW1
#define BCR6_URX0 bcr6.bit._URX0
#define BCR6_UW0 bcr6.bit._UW0
#define BCR6_MPE bcr6.bit._MPE
#define BCR6_COMB bcr6.bit._COMB
#define BCR6_CTC1 bcr6.bit._CTC1
#define BCR6_CTC0 bcr6.bit._CTC0
#define BCR6_OBS1 bcr6.bit._OBS1
#define BCR6_OBS0 bcr6.bit._OBS0
#define BCR6_OBT1 bcr6.bit._OBT1
#define BCR6_OBT0 bcr6.bit._OBT0
#define BCR6_EP3 bcr6.bit._EP3
#define BCR6_EP2 bcr6.bit._EP2
#define BCR6_EP1 bcr6.bit._EP1
#define BCR6_EP0 bcr6.bit._EP0
#define BCR6_EM1 bcr6.bit._EM1
#define BCR6_EM0 bcr6.bit._EM0
#define BCR6_ER1 bcr6.bit._ER1
#define BCR6_ER0 bcr6.bit._ER0
#define BCR6_CTC bcr6.bitc._CTC
#define BCR6_OBS bcr6.bitc._OBS
#define BCR6_OBT bcr6.bitc._OBT
#define BCR6_EP bcr6.bitc._EP
#define BCR6_EM bcr6.bitc._EM
#define BCR6_ER bcr6.bitc._ER
__IO_EXTERN BCR7STR bcr7;  
#define BCR7 bcr7.lword
#define BCR7_SRX1 bcr7.bit._SRX1
#define BCR7_SW1 bcr7.bit._SW1
#define BCR7_SRX0 bcr7.bit._SRX0
#define BCR7_SW0 bcr7.bit._SW0
#define BCR7_URX1 bcr7.bit._URX1
#define BCR7_UW1 bcr7.bit._UW1
#define BCR7_URX0 bcr7.bit._URX0
#define BCR7_UW0 bcr7.bit._UW0
#define BCR7_MPE bcr7.bit._MPE
#define BCR7_COMB bcr7.bit._COMB
#define BCR7_CTC1 bcr7.bit._CTC1
#define BCR7_CTC0 bcr7.bit._CTC0
#define BCR7_OBS1 bcr7.bit._OBS1
#define BCR7_OBS0 bcr7.bit._OBS0
#define BCR7_OBT1 bcr7.bit._OBT1
#define BCR7_OBT0 bcr7.bit._OBT0
#define BCR7_EP3 bcr7.bit._EP3
#define BCR7_EP2 bcr7.bit._EP2
#define BCR7_EP1 bcr7.bit._EP1
#define BCR7_EP0 bcr7.bit._EP0
#define BCR7_EM1 bcr7.bit._EM1
#define BCR7_EM0 bcr7.bit._EM0
#define BCR7_ER1 bcr7.bit._ER1
#define BCR7_ER0 bcr7.bit._ER0
#define BCR7_CTC bcr7.bitc._CTC
#define BCR7_OBS bcr7.bitc._OBS
#define BCR7_OBT bcr7.bitc._OBT
#define BCR7_EP bcr7.bitc._EP
#define BCR7_EM bcr7.bitc._EM
#define BCR7_ER bcr7.bitc._ER
__IO_EXTERN IO_LWORD bad0;  
#define BAD0 bad0
__IO_EXTERN IO_LWORD bad1;  
#define BAD1 bad1
__IO_EXTERN IO_LWORD bad2;  
#define BAD2 bad2
__IO_EXTERN IO_LWORD bad3;  
#define BAD3 bad3
__IO_EXTERN IO_LWORD bad4;  
#define BAD4 bad4
__IO_EXTERN IO_LWORD bad5;  
#define BAD5 bad5
__IO_EXTERN IO_LWORD bad6;  
#define BAD6 bad6
__IO_EXTERN IO_LWORD bad7;  
#define BAD7 bad7
__IO_EXTERN IO_LWORD bad8;  
#define BAD8 bad8
__IO_EXTERN IO_LWORD bad9;  
#define BAD9 bad9
__IO_EXTERN IO_LWORD bad10;  
#define BAD10 bad10
__IO_EXTERN IO_LWORD bad11;  
#define BAD11 bad11
__IO_EXTERN IO_LWORD bad12;  
#define BAD12 bad12
__IO_EXTERN IO_LWORD bad13;  
#define BAD13 bad13
__IO_EXTERN IO_LWORD bad14;  
#define BAD14 bad14
__IO_EXTERN IO_LWORD bad15;  
#define BAD15 bad15
__IO_EXTERN IO_LWORD fsv1;   /* FSV & BSV Registers */
#define FSV1 fsv1
__IO_EXTERN IO_LWORD bsv1;  
#define BSV1 bsv1
__IO_EXTERN IO_LWORD fsv2;  
#define FSV2 fsv2
__IO_EXTERN IO_LWORD bsv2;  
#define BSV2 bsv2
/* include : INC467_BSYNC.INC */
/*-------------------------------------------------------------------*/
/* INC467.BSYNC :  Macros Bus Sync*/

#define RB_SYNC if(RBSYNC)
#define CB_SYNC0 if(CBSYNC0)
#define CB_SYNC1 if(CBSYNC1)
#define CB_SYNC2 if(CBSYNC2)
/*-------------------------------------------------------------------*/
#endif                   /* __FASM__    */
#endif                   /* __MB91XXX_H */
#endif                   /* __IO_DEFINE */
