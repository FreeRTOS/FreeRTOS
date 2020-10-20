/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of
* this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_rx_intrinsic_functions.h
* Description  : This is a file for integrating the definitions of built-in functions that differ for each compilers.
*                Replace different functions for each compiler.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 1.00     First Release
*         : 26.07.2019 1.10     Added the following function.
*                               - R_BSP_SINCOSF
*                               - R_BSP_ATAN2HYPOTF
*                               - R_BSP_CalcSine_Cosine
*                               - R_BSP_CalcAtan_SquareRoot
*         : 31.07.2019 1.11     Modified the compile condition of the below functions.
*                               - R_BSP_InitTFU
*                               - R_BSP_CalcSine_Cosine
*                               - R_BSP_CalcAtan_SquareRoot
*         : 08.10.2019 1.12     Modified the followind definition of intrinsic function of TFU for ICCRX.
*                               - R_BSP_INIT_TFU
*                               - R_BSP_SINCOSF
*                               - R_BSP_ATAN2HYPOTF
*         : 17.12.2019 1.13     Modified the comment of description.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef R_RX_INTRINSIC_FUNCTIONS_H
#define R_RX_INTRINSIC_FUNCTIONS_H

/* ---------- Maximum value and minimum value ---------- */
#if defined(__CCRX__)

/* signed long max(signed long data1, signed long data2) */
#define R_BSP_MAX(x, y)    max((signed long)(x), (signed long)(y))
/* signed long min(signed long data1, signed long data2) */
#define R_BSP_MIN(x, y)    min((signed long)(x), (signed long)(y))

#elif defined(__GNUC__)

/* signed long R_BSP_Max(signed long data1, signed long data2) (This macro uses API function of BSP.) */
#define R_BSP_MAX(x, y)    R_BSP_Max((signed long)(x), (signed long)(y))
/* signed long R_BSP_Min(signed long data1, signed long data2) (This macro uses API function of BSP.) */
#define R_BSP_MIN(x, y)    R_BSP_Min((signed long)(x), (signed long)(y))

#elif defined(__ICCRX__)

/* signed long   __MAX(signed long, signed long) */
#define R_BSP_MAX(x, y)    __MAX((signed long)(x), (signed long)(y))
/* signed long   __MIN(signed long, signed long) */
#define R_BSP_MIN(x, y)    __MIN((signed long)(x), (signed long)(y))

#endif

/* ---------- Byte switch ---------- */
#if defined(__CCRX__)

/* unsigned long revl(unsigned long data) */
#define R_BSP_REVL(x)    revl((unsigned long)(x))
/* unsigned long revw(unsigned long data) */
#define R_BSP_REVW(x)    revw((unsigned long)(x))

#elif defined(__GNUC__)

/* uint32_t __builtin_bswap32(uint32_t x) */
#define R_BSP_REVL(x)    __builtin_bswap32((uint32_t)(x))
/* int __builtin_rx_revw(int) */
#define R_BSP_REVW(x)    (unsigned long)__builtin_rx_revw((int)(x))

#elif defined(__ICCRX__)

/* unsigned long __REVL(unsigned long) */
#define R_BSP_REVL(x)    __REVL((unsigned long)(x))
/* unsigned long __REVW(unsigned long) */
#define R_BSP_REVW(x)    __REVW((unsigned long)(x))

#endif

/* ---------- Data Exchange ---------- */
#if defined(__CCRX__)

/* void xchg(signed long *data1, signed long *data2) */
#define R_BSP_EXCHANGE(x, y)    xchg((signed long *)(x), (signed long *)(y))

#elif defined(__GNUC__)

/* void __builtin_rx_xchg (int *, int *) */
#define R_BSP_EXCHANGE(x, y)    __builtin_rx_xchg((int *)(x), (int *)(y))

#elif defined(__ICCRX__)

/* void _builtin_xchg(signed long *, signed long *) */
#define R_BSP_EXCHANGE(x, y)    _builtin_xchg((signed long *)(x), (signed long *)(y))

#endif

/* ---------- Multiply-and-accumulate operation ---------- */
#if defined(__CCRX__)

/* long long rmpab(long long init, unsigned long count, signed char *addr1, signed char *addr2) */
#define R_BSP_RMPAB(w, x, y, z)    rmpab((long long)(w), (unsigned long)(x), (signed char *)(y), (signed char *)(z))
/* long long rmpaw(long long init, unsigned long count, short *addr1, short *addr2) */
#define R_BSP_RMPAW(w, x, y, z)    rmpaw((long long)(w), (unsigned long)(x), (short *)(y), (short *)(z))
/* long long rmpal(long long init, unsigned long count, long *addr1, long *addr2) */
#define R_BSP_RMPAL(w, x, y, z)    rmpal((long long)(w), (unsigned long)(x), (long *)(y), (long *)(z))

#elif defined(__GNUC__)

/* long long R_BSP_MulAndAccOperation_B(long long init, unsigned long count, signed char *addr1, signed char *addr2)
   (This macro uses API function of BSP.) */
#define R_BSP_RMPAB(w, x, y, z)    R_BSP_MulAndAccOperation_B((long long)(w), (unsigned long)(x), (signed char *)(y), (signed char *)(z))
/* long long R_BSP_MulAndAccOperation_W(long long init, unsigned long count, short *addr1, short *addr2)
   (This macro uses API function of BSP.) */
#define R_BSP_RMPAW(w, x, y, z)    R_BSP_MulAndAccOperation_W((long long)(w), (unsigned long)(x), (short *)(y), (short *)(z))
/* long long R_BSP_MulAndAccOperation_L(long long init, unsigned long count, long *addr1, long *addr2)
   (This macro uses API function of BSP.) */
#define R_BSP_RMPAL(w, x, y, z)    R_BSP_MulAndAccOperation_L((long long)(w), (unsigned long)(x), (long *)(y), (long *)(z))

#elif defined(__ICCRX__)

/* long long rmpab(long long init, unsigned long count, signed char *addr1, signed char *addr2) */
#define R_BSP_RMPAB(w, x, y, z)    rmpab((long long)(w), (unsigned long)(x), (signed char *)(y), (signed char *)(z))
/* long long rmpaw(long long init, unsigned long count, short *addr1, short *addr2) */
#define R_BSP_RMPAW(w, x, y, z)    rmpaw((long long)(w), (unsigned long)(x), (short *)(y), (short *)(z))
/* long long rmpal(long long init, unsigned long count, long *addr1, long *addr2) */
#define R_BSP_RMPAL(w, x, y, z)    rmpal((long long)(w), (unsigned long)(x), (long *)(y), (long *)(z))

#endif

/* ---------- Rotation ---------- */
#if defined(__CCRX__)

/* unsigned long rolc(unsigned long data) */
#define R_BSP_ROLC(x)    rolc((unsigned long)(x))
/* unsigned long rorc(unsigned long data) */
#define R_BSP_RORC(x)    rorc((unsigned long)(x))
/* unsigned long rotl(unsigned long data, unsigned long num) */
#define R_BSP_ROTL(x, y)    rotl((unsigned long)(x), (unsigned long)(y))
/* unsigned long rotr (unsigned long data, unsigned long num) */
#define R_BSP_ROTR(x, y)    rotr((unsigned long)(x), (unsigned long)(y))

#elif defined(__GNUC__)

/* unsigned long R_BSP_RotateLeftWithCarry(unsigned long data) (This macro uses API function of BSP.) */
#define R_BSP_ROLC(x)    R_BSP_RotateLeftWithCarry((unsigned long)(x))
/* unsigned long R_BSP_RotateRightWithCarry(unsigned long data) (This macro uses API function of BSP.) */
#define R_BSP_RORC(x)    R_BSP_RotateRightWithCarry((unsigned long)(x))
/* unsigned long R_BSP_RotateLeft(unsigned long data, unsigned long num) (This macro uses API function of BSP.) */
#define R_BSP_ROTL(x, y)    R_BSP_RotateLeft((unsigned long)(x), (unsigned long)(y))
/* unsigned long R_BSP_RotateRight (unsigned long data, unsigned long num) (This macro uses API function of BSP.) */
#define R_BSP_ROTR(x, y)    R_BSP_RotateRight((unsigned long)(x), (unsigned long)(y))

#elif defined(__ICCRX__)

/* unsigned long __ROLC(unsigned long) */
#define R_BSP_ROLC(x)    __ROLC((unsigned long)(x))
/* unsigned long __RORC(unsigned long) */
#define R_BSP_RORC(x)    __RORC((unsigned long)(x))
/* unsigned long __ROTL(unsigned long, unsigned long) */
#define R_BSP_ROTL(x, y)    __ROTL((unsigned long)(y), (unsigned long)(x))
/* unsigned long __ROTR(unsigned long, unsigned long) */
#define R_BSP_ROTR(x, y)    __ROTR((unsigned long)(y), (unsigned long)(x))

#endif

/* ---------- Special Instructions ---------- */
#if defined(__CCRX__)

/* void brk(void) */
#define R_BSP_BRK()    brk()
/* void int_exception(signed long num) */
#define R_BSP_INT(x)   int_exception((signed long)(x))
/* void wait(void) */
#define R_BSP_WAIT()   wait()
/* void nop(void) */
#define R_BSP_NOP()    nop()

#elif defined(__GNUC__)

/* void __builtin_rx_brk (void)  */
#define R_BSP_BRK()    __builtin_rx_brk()
/* void __builtin_rx_int (int) */
#define R_BSP_INT(x)   __builtin_rx_int((int)(x))
/* void __builtin_rx_wait (void) */
#define R_BSP_WAIT()   __builtin_rx_wait()
/* __asm("nop") */
#define R_BSP_NOP()    __asm("nop")

#elif defined(__ICCRX__)

/* void __break(void) */
#define R_BSP_BRK()    __break()
/* void __software_interrupt(unsigned char) */
#define R_BSP_INT(x)   __software_interrupt((unsigned char)(x))
/* void __wait_for_interrupt(void) */
#define R_BSP_WAIT()   __wait_for_interrupt()
/* void __no_operation(void) */
#define R_BSP_NOP()    __no_operation()

#endif

/* ---------- Processor interrupt priority level (IPL) ---------- */
#if defined(__CCRX__)

/* void set_ipl(signed long level) */
#define R_BSP_SET_IPL(x)    set_ipl((signed long)(x))
/* unsigned char get_ipl(void) */
#define R_BSP_GET_IPL()     get_ipl()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtipl (int) */
#define R_BSP_SET_IPL(x)    __builtin_rx_mvtipl((int)(x))
/* uint32_t R_BSP_CpuInterruptLevelRead (void) (This macro uses API function of BSP.) */
#define R_BSP_GET_IPL()     (unsigned char)R_BSP_CpuInterruptLevelRead()

#elif defined(__ICCRX__)

/* void __set_interrupt_level(__ilevel_t) */
#define R_BSP_SET_IPL(x)    __set_interrupt_level((__ilevel_t)(x))
/* __ilevel_t __get_interrupt_level(void) */
#define R_BSP_GET_IPL()     (unsigned char)__get_interrupt_level()

#endif

/* ---------- Processor status word (PSW) ---------- */
#if defined(__CCRX__)

/* void set_psw(unsigned long data) */
#define R_BSP_SET_PSW(x)    set_psw((unsigned long)(x))
/* unsigned long get_psw(void) */
#define R_BSP_GET_PSW()     get_psw()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_PSW(x)    __builtin_rx_mvtc(0x0, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_PSW()     (unsigned long)__builtin_rx_mvfc(0x0)

#elif defined(__ICCRX__)

/* void __set_PSW_register(unsigned long) */
#define R_BSP_SET_PSW(x)    __set_PSW_register((unsigned long)(x))
/* unsigned long __get_PSW_register(void) */
#define R_BSP_GET_PSW()     __get_PSW_register()

#endif

/* ---------- Floating-point status word (FPSW) ---------- */
#ifdef __FPU
#if defined(__CCRX__)

/* void set_fpsw(unsigned long data) */
#define R_BSP_SET_FPSW(x)    set_fpsw((unsigned long)(x))
/* unsigned long get_fpsw(void) */
#define R_BSP_GET_FPSW()     get_fpsw()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_FPSW(x)    __builtin_rx_mvtc(0x3, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_FPSW()    (unsigned long)__builtin_rx_mvfc(0x3)

#elif defined(__ICCRX__)

/* void __set_FPSW_register(unsigned long) */
#define R_BSP_SET_FPSW(x)    __set_FPSW_register((unsigned long)(x))
/* unsigned long __get_FPSW_register(void) */
#define R_BSP_GET_FPSW()     __get_FPSW_register()

#endif
#endif

/* ---------- User Stack Pointer (USP) ---------- */
#if defined(__CCRX__)

/* void set_usp(void *data) */
#define R_BSP_SET_USP(x)    set_usp((void *)(x))
/* void *get_usp(void) */
#define R_BSP_GET_USP()     get_usp()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_USP(x)    __builtin_rx_mvtc(0x2, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_USP()     (void *)__builtin_rx_mvfc(0x2)

#elif defined(__ICCRX__)

/* void __set_USP_register(unsigned long) */
#define R_BSP_SET_USP(x)    __set_USP_register((unsigned long)(x))
/* unsigned long __get_USP_register(void) */
#define R_BSP_GET_USP()     (void *)__get_USP_register()

#endif

/* ---------- Interrupt Stack Pointer (ISP) ---------- */
#if defined(__CCRX__)

/* void set_isp(void *data) */
#define R_BSP_SET_ISP(x)    set_isp((void *)(x))
/* void *get_isp(void) */
#define R_BSP_GET_ISP()     get_isp()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_ISP(x)    __builtin_rx_mvtc(0xA, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_ISP()     (void *)__builtin_rx_mvfc(0xA)

#elif defined(__ICCRX__)

/* void __set_ISP_register(unsigned long) */
#define R_BSP_SET_ISP(x)    __set_ISP_register((unsigned long)(x))
/* unsigned long __get_ISP_register(void) */
#define R_BSP_GET_ISP()     (void *)__get_ISP_register()

#endif

/* ---------- Interrupt Table Register (INTB) ---------- */
#if defined(__CCRX__)

/* void set_intb(void *data) */
#define R_BSP_SET_INTB(x)    set_intb((void *)(x))
/* void *get_intb(void) */
#define R_BSP_GET_INTB()     get_intb()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_INTB(x)    __builtin_rx_mvtc(0xC, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_INTB()     (void *)__builtin_rx_mvfc(0xC)

#elif defined(__ICCRX__)

/* void __set_interrupt_table(unsigned long address) */
#define R_BSP_SET_INTB(x)    __set_interrupt_table((unsigned long)(x))
/* unsigned long __get_interrupt_table(void); */
#define R_BSP_GET_INTB()     (void *)__get_interrupt_table()

#endif

/* ---------- Backup PSW (BPSW) ---------- */
#if defined(__CCRX__)

/* void set_bpsw(unsigned long data) */
#define R_BSP_SET_BPSW(x)    set_bpsw((unsigned long)(x))
/* unsigned long get_bpsw(void) */
#define R_BSP_GET_BPSW()     get_bpsw()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_BPSW(x)    __builtin_rx_mvtc(0x8, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_BPSW()     (unsigned long)__builtin_rx_mvfc(0x8)

#elif defined(__ICCRX__)

/* void R_BSP_SetBPSW(uint32_t data) (This macro uses API function of BSP.) */
#define R_BSP_SET_BPSW(x)    R_BSP_SetBPSW((uint32_t)(x))
/* uint32_t R_BSP_GetBPSW(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_BPSW()     R_BSP_GetBPSW()

#endif

/* ---------- Backup PC (BPC) ---------- */
#if defined(__CCRX__)

/* void set_bpc(void *data) */
#define R_BSP_SET_BPC(x)    set_bpc((void *)(x))
/* void *get_bpc(void) */
#define R_BSP_GET_BPC()     get_bpc()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_BPC(x)    __builtin_rx_mvtc(0x9, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_BPC()     (void *)__builtin_rx_mvfc(0x9)

#elif defined(__ICCRX__)

/* void R_BSP_SetBPC(void * data) (This macro uses API function of BSP.) */
#define R_BSP_SET_BPC(x)    R_BSP_SetBPC((void *)(x))
/* void *R_BSP_GetBPC(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_BPC()     R_BSP_GetBPC()

#endif

/* ---------- Fast Interrupt Vector Register (FINTV) ---------- */
#if defined(__CCRX__)

/* void set_fintv(void *data) */
#define R_BSP_SET_FINTV(x)    set_fintv((void *)(x))
/* void *get_fintv(void) */
#define R_BSP_GET_FINTV()     get_fintv()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_FINTV(x)    __builtin_rx_mvtc(0xB, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_FINTV()     (void *)__builtin_rx_mvfc(0xB)

#elif defined(__ICCRX__)

/* void __set_FINTV_register(__fast_int_f) */
#define R_BSP_SET_FINTV(x)    __set_FINTV_register((__fast_int_f)(x))
/* __fast_int_f __get_FINTV_register(void) */
#define R_BSP_GET_FINTV()     (void *)__get_FINTV_register()

#endif

/* ---------- Significant 64-bit multiplication ---------- */
#if defined(__CCRX__)

/* signed long long emul(signed long data1, signed long data2) */
#define R_BSP_EMUL(x, y)    emul((signed long)(x), (signed long)(y))
/* unsigned long long emulu(unsigned long data1, unsigned long data2) */
#define R_BSP_EMULU(x, y)   emulu((unsigned long)(x), (unsigned long)(y))

#elif defined(__GNUC__)

/* signed long long R_BSP_SignedMultiplication(signed long data1, signed long data2)
   (This macro uses API function of BSP.) */
#define R_BSP_EMUL(x, y)    R_BSP_SignedMultiplication((signed long)(x), (signed long)(y))
/* unsigned long long R_BSP_UnsignedMultiplication(unsigned long data1, unsigned long data2)
   (This macro uses API function of BSP.) */
#define R_BSP_EMULU(x, y)   R_BSP_UnsignedMultiplication((unsigned long)(x), (unsigned long)(y))

#elif defined(__ICCRX__)

/* signed long long R_BSP_SignedMultiplication(signed long data1, signed long data2)
   (This macro uses API function of BSP.) */
#define R_BSP_EMUL(x, y)    R_BSP_SignedMultiplication((signed long)(x), (signed long)(y))
/* unsigned long long R_BSP_UnsignedMultiplication(unsigned long data1, unsigned long data2)
   (This macro uses API function of BSP.) */
#define R_BSP_EMULU(x, y)   R_BSP_UnsignedMultiplication((unsigned long)(x), (unsigned long)(y))

#endif

/* ---------- Processor mode (PM) ---------- */
#if defined(__CCRX__)

/* void chg_pmusr(void) */
#define R_BSP_CHG_PMUSR()    chg_pmusr()

#elif defined(__GNUC__)

/* void R_BSP_ChangeToUserMode(void) (This macro uses API function of BSP.) */
#define R_BSP_CHG_PMUSR()    R_BSP_ChangeToUserMode()

#elif defined(__ICCRX__)

/* void R_BSP_ChangeToUserMode(void) (This macro uses API function of BSP.) */
#define R_BSP_CHG_PMUSR()    R_BSP_ChangeToUserMode()

#endif

/* ---------- Accumulator (ACC) ---------- */
#if defined(__CCRX__)

/* void set_acc(signed long long data) */
#define R_BSP_SET_ACC(x)    set_acc((signed long long)(x))
/* signed long long get_acc(void) */
#define R_BSP_GET_ACC()     get_acc()

#elif defined(__GNUC__)

/* void R_BSP_SetACC(signed long long data) (This macro uses API function of BSP.) */
#define R_BSP_SET_ACC(x)    R_BSP_SetACC((signed long long)(x))
/* signed long long R_BSP_GetACC(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_ACC()     R_BSP_GetACC()

#elif defined(__ICCRX__)

/* void R_BSP_SetACC(signed long long data) (This macro uses API function of BSP.) */
#define R_BSP_SET_ACC(x)    R_BSP_SetACC((signed long long)(x))
/* signed long long R_BSP_GetACC(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_ACC()     R_BSP_GetACC()

#endif

/* ---------- Control of the interrupt enable bits ---------- */
#if defined(__CCRX__)

/* void setpsw_i(void) */
#define R_BSP_SETPSW_I()    setpsw_i()
/* void clrpsw_i(void) */
#define R_BSP_CLRPSW_I()    clrpsw_i()

#elif defined(__GNUC__)

/* void __builtin_rx_setpsw (int) */
#define R_BSP_SETPSW_I()    __builtin_rx_setpsw('I')
/* void __builtin_rx_clrpsw (int) */
#define R_BSP_CLRPSW_I()    __builtin_rx_clrpsw('I')

#elif defined(__ICCRX__)

/* void __enable_interrupt(void) */
#define R_BSP_SETPSW_I()    __enable_interrupt()
/* void __disable_interrupt(void) */
#define R_BSP_CLRPSW_I()    __disable_interrupt()

#endif

/* ---------- Multiply-and-accumulate operation ---------- */
#if defined(__CCRX__)

/* long macl(short *data1, short *data2, unsigned long count) */
#define R_BSP_MACL(x, y, z)     macl((short *)(x), (short *)(y), (unsigned long)(z))
/* short macw1(short *data1, short *data2, unsigned long count) */
#define R_BSP_MACW1(x, y, z)    macw1((short *)(x), (short *)(y), (unsigned long)(z))
/* short macw2(short *data1, short *data2, unsigned long count) */
#define R_BSP_MACW2(x, y, z)    macw2((short *)(x), (short *)(y), (unsigned long)(z))

#elif defined(__GNUC__)

/* long R_BSP_MulAndAccOperation_2byte(short *data1, short *data2, unsigned long count)
   (This macro uses API function of BSP.) */
#define R_BSP_MACL(x, y, z)     R_BSP_MulAndAccOperation_2byte((short *)(x), (short *)(y), (unsigned long)(z))
/* short R_BSP_MulAndAccOperation_FixedPoint1(short *data1, short *data2, unsigned long count)
   (This macro uses API function of BSP.) */
#define R_BSP_MACW1(x, y, z)    R_BSP_MulAndAccOperation_FixedPoint1((short *)(x), (short *)(y), (unsigned long)(z))
/* short R_BSP_MulAndAccOperation_FixedPoint2(short *data1, short *data2, unsigned long count)
   (This macro uses API function of BSP.) */
#define R_BSP_MACW2(x, y, z)    R_BSP_MulAndAccOperation_FixedPoint2((short *)(x), (short *)(y), (unsigned long)(z))

#elif defined(__ICCRX__)

/* long __macl(short * data1, short * data2, unsigned long count) */
#define R_BSP_MACL(x, y, z)     __macl((short *)(x), (short *)(y), (unsigned long)(z))
/* short __macw1(short * data1, short * data2, unsigned long count) */
#define R_BSP_MACW1(x, y, z)    __macw1((short *)(x), (short *)(y), (unsigned long)(z))
/* short __macw2(short * data1, short * data2, unsigned long count) */
#define R_BSP_MACW2(x, y, z)    __macw2((short *)(x), (short *)(y), (unsigned long)(z))

#endif

/* ---------- Exception Table Register (EXTB) ---------- */
#ifdef BSP_MCU_EXCEPTION_TABLE
#if defined(__CCRX__)

/* void set_extb(void *data) */
#define R_BSP_SET_EXTB(x)    set_extb((void *)(x))
/* void *get_extb(void) */
#define R_BSP_GET_EXTB()     get_extb()

#elif defined(__GNUC__)

/* void __builtin_rx_mvtc (int reg, int val) */
#define R_BSP_SET_EXTB(x)    __builtin_rx_mvtc(0xD, (int)(x))
/* int __builtin_rx_mvfc (int) */
#define R_BSP_GET_EXTB()     (void *)__builtin_rx_mvfc(0xD)

#elif defined(__ICCRX__)

/* void R_BSP_SetEXTB(void * data) (This macro uses API function of BSP.) */
#define R_BSP_SET_EXTB(x)    R_BSP_SetEXTB((void *)(x))
/* void *R_BSP_GetEXTB(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_EXTB()     R_BSP_GetEXTB()

#endif
#endif

/* ---------- Bit Manipulation ---------- */
#if defined(__CCRX__)

/* void __bclr(unsigned char *data, unsigned long bit) */
#define R_BSP_BIT_CLEAR(x, y)      __bclr((unsigned char *)(x), (unsigned long)(y))
/* void __bset(unsigned char *data, unsigned long bit) */
#define R_BSP_BIT_SET(x, y)        __bset((unsigned char *)(x), (unsigned long)(y))
/* void __bnot(unsigned char *data, unsigned long bit) */
#define R_BSP_BIT_REVERSE(x, y)    __bnot((unsigned char *)(x), (unsigned long)(y))

#elif defined(__GNUC__)

/* void R_BSP_BitClear(uint8_t *data, uint32_t bit) (This macro uses API function of BSP.) */
#define R_BSP_BIT_CLEAR(x, y)      R_BSP_BitClear((uint8_t *)(x), (uint32_t)(y))
/* void R_BSP_BitSet(uint8_t *data, uint32_t bit) (This macro uses API function of BSP.) */
#define R_BSP_BIT_SET(x, y)        R_BSP_BitSet((uint8_t *)(x), (uint32_t)(y))
/* void R_BSP_BitReverse(uint8_t *data, uint32_t bit) (This macro uses API function of BSP.) */
#define R_BSP_BIT_REVERSE(x, y)    R_BSP_BitReverse((uint8_t *)(x), (uint32_t)(y))

#elif defined(__ICCRX__)

/* void R_BSP_BitClear(uint8_t *data, uint32_t bit) (This macro uses API function of BSP.) */
#define R_BSP_BIT_CLEAR(x, y)      R_BSP_BitClear((uint8_t *)(x), (uint32_t)(y))
/* void R_BSP_BitSet(uint8_t *data, uint32_t bit) (This macro uses API function of BSP.) */
#define R_BSP_BIT_SET(x, y)        R_BSP_BitSet((uint8_t *)(x), (uint32_t)(y))
/* void R_BSP_BitReverse(uint8_t *data, uint32_t bit) (This macro uses API function of BSP.) */
#define R_BSP_BIT_REVERSE(x, y)    R_BSP_BitReverse((uint8_t *)(x), (uint32_t)(y))

#endif

#ifdef BSP_MCU_DOUBLE_PRECISION_FLOATING_POINT
#ifdef __DPFPU
/* ---------- Double-Precision Floating-Point Status Word (DPSW) ---------- */
#if defined(__CCRX__)

/* void set_dpsw(unsigned long data) */
#define R_BSP_SET_DPSW(x)    __set_dpsw((unsigned long)(x))
/* unsigned long get_dpsw(void) */
#define R_BSP_GET_DPSW()     __get_dpsw()

#elif defined(__GNUC__)

/* void R_BSP_SetDPSW(uint32_t data) (This macro uses API function of BSP.) */
#define R_BSP_SET_DPSW(x)    R_BSP_SetDPSW((uint32_t)(x))
/* uint32_t R_BSP_GetDPSW(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_DPSW()     R_BSP_GetDPSW()

#elif defined(__ICCRX__)

/* void R_BSP_SetDPSW(uint32_t data) (This macro uses API function of BSP.) */
#define R_BSP_SET_DPSW(x)    R_BSP_SetDPSW((uint32_t)(x))
/* uint32_t R_BSP_GetDPSW(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_DPSW()     R_BSP_GetDPSW()

#endif

/* ---------- Double-precision floating-point exception handling operation control register (DECNT) ---------- */
#if defined(__CCRX__)

/* void __set_decnt(unsigned long data) */
#define R_BSP_SET_DECNT(x)    __set_decnt((unsigned long)(x))
/* unsigned long __get_decnt(void) */
#define R_BSP_GET_DECNT()     __get_decnt()

#elif defined(__GNUC__)

/* void R_BSP_SetDECNT(uint32_t data) (This macro uses API function of BSP.) */
#define R_BSP_SET_DECNT(x)    R_BSP_SetDECNT((uint32_t)(x))
/* uint32_t R_BSP_GetDECNT(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_DECNT()     R_BSP_GetDECNT()

#elif defined(__ICCRX__)

/* void R_BSP_SetDECNT(uint32_t data) (This macro uses API function of BSP.) */
#define R_BSP_SET_DECNT(x)    R_BSP_SetDECNT((uint32_t)(x))
/* uint32_t R_BSP_GetDECNT(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_DECNT()     R_BSP_GetDECNT()

#endif

/* ---------- Double-precision floating-point exception program counter (DEPC) ---------- */
#if defined(__CCRX__)

/* void *__get_depc(void) */
#define R_BSP_GET_DEPC()     __get_depc()

#elif defined(__GNUC__)

/* void *R_BSP_GetDEPC(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_DEPC()     R_BSP_GetDEPC()

#elif defined(__ICCRX__)

/* void *R_BSP_GetDEPC(void) (This macro uses API function of BSP.) */
#define R_BSP_GET_DEPC()     R_BSP_GetDEPC()

#endif
#endif /* __DPFPU */
#endif /* BSP_MCU_DOUBLE_PRECISION_FLOATING_POINT */

/* ---------- Initializing Arithmetic Unit for Trigonometric Functions ---------- */
#ifdef BSP_MCU_TRIGONOMETRIC
#if defined(__CCRX__)

/* void __init_tfu(void) */
#define R_BSP_INIT_TFU()      __init_tfu()

#elif defined(__GNUC__)

/* void R_BSP_InitTFU(void) (This macro uses API function of BSP.) */
#define R_BSP_INIT_TFU()      R_BSP_InitTFU()

#elif defined(__ICCRX__)

/* Invalid for ICCRX.
   Because the initilaze function of TFU is called automatically when the TFU function is called. */
#define R_BSP_INIT_TFU()      

#endif

/* ---------- Calculating the Sine and Cosine of an angle at the same time(single precision) ---------- */
#if defined(__CCRX__)

/* void __sincosf(float f, float *sin, float *cos) */
#define R_BSP_SINCOSF(x, y, z)    __sincosf((float)(x), (float *)(y), (float *)(z))

#elif defined(__GNUC__)

/* void R_BSP_CalcSine_Cosine(float f, float *sin, float *cos) (This macro uses API function of BSP.) */
#define R_BSP_SINCOSF(x, y, z)    R_BSP_CalcSine_Cosine((float)(x), (float *)(y), (float *)(z))

#elif defined(__ICCRX__)

/* void R_BSP_CalcSine_Cosine(float f, float *sin, float *cos) (This macro uses API function of BSP.) */
#define R_BSP_SINCOSF(x, y, z)    __sincosf((float)(x), (float *)(y), (float *)(z))

#endif

/* ---------- Initializing Arithmetic Unit for Trigonometric Functions ---------- */
#if defined(__CCRX__)

/* void __atan2hypotf(float y, float x, float *atan2, float *hypot) */
#define R_BSP_ATAN2HYPOTF(w, x, y, z)    __atan2hypotf((float)(w), (float)(x), (float *)(y), (float *)(z))

#elif defined(__GNUC__)

/* void R_BSP_CalcAtan_SquareRoot(float y, float x, float *atan2, float *hypot)
   (This macro uses API function of BSP.) */
#define R_BSP_ATAN2HYPOTF(w, x, y, z)    R_BSP_CalcAtan_SquareRoot((float)(w), (float)(x), (float *)(y), (float *)(z))

#elif defined(__ICCRX__)

/* void R_BSP_CalcAtan_SquareRoot(float y, float x, float *atan2, float *hypot)
   (This macro uses API function of BSP.) */
#define R_BSP_ATAN2HYPOTF(w, x, y, z)    __atan2hypotf((float)(w), (float)(x), (float *)(y), (float *)(z))

#endif
#endif /* BSP_MCU_TRIGONOMETRIC */

/***********************************************************************************************************************
Exported global variables
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global functions (to be accessed by other files)
***********************************************************************************************************************/
#if defined(__GNUC__)
signed long R_BSP_Max(signed long data1, signed long data2);
signed long R_BSP_Min(signed long data1, signed long data2);
long long R_BSP_MulAndAccOperation_B(long long init, unsigned long count, signed char *addr1, signed char *addr2);
long long R_BSP_MulAndAccOperation_W(long long init, unsigned long count, short *addr1, short *addr2);
long long R_BSP_MulAndAccOperation_L(long long init, unsigned long count, long *addr1, long *addr2);
unsigned long R_BSP_RotateLeftWithCarry(unsigned long data);
unsigned long R_BSP_RotateRightWithCarry(unsigned long data);
unsigned long R_BSP_RotateLeft(unsigned long data, unsigned long num);
unsigned long R_BSP_RotateRight(unsigned long data, unsigned long num);
long R_BSP_MulAndAccOperation_2byte(short* data1, short* data2, unsigned long count);
short R_BSP_MulAndAccOperation_FixedPoint1(short* data1, short* data2, unsigned long count);
short R_BSP_MulAndAccOperation_FixedPoint2(short* data1, short* data2, unsigned long count);
#endif /* defined(__GNUC__) */

#if defined(__GNUC__) || defined(__ICCRX__)
signed long long R_BSP_SignedMultiplication(signed long data1, signed long data2);
unsigned long long R_BSP_UnsignedMultiplication(unsigned long data1, unsigned long data2);
void R_BSP_SetACC(signed long long data);
signed long long R_BSP_GetACC(void);
#endif /* defined(__GNUC__) || defined(__ICCRX__)  */

R_BSP_ATTRIB_INLINE_ASM void R_BSP_ChangeToUserMode(void);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_SetBPSW(uint32_t data);
uint32_t R_BSP_GetBPSW(void);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_SetBPC(void * data);
void *R_BSP_GetBPC(void);
#ifdef BSP_MCU_EXCEPTION_TABLE
R_BSP_ATTRIB_INLINE_ASM void R_BSP_SetEXTB(void * data);
void *R_BSP_GetEXTB(void);
#endif /* BSP_MCU_EXCEPTION_TABLE */
R_BSP_ATTRIB_INLINE_ASM void R_BSP_BitSet(uint8_t *data, uint32_t bit);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_BitClear(uint8_t *data, uint32_t bit);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_BitReverse(uint8_t *data, uint32_t bit);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_MoveToAccHiLong(int32_t data);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_MoveToAccLoLong(int32_t data);
int32_t R_BSP_MoveFromAccHiLong(void);
int32_t R_BSP_MoveFromAccMiLong(void);
#ifdef BSP_MCU_DOUBLE_PRECISION_FLOATING_POINT
#ifdef __DPFPU
R_BSP_ATTRIB_INLINE_ASM void R_BSP_SetDPSW(uint32_t data);
uint32_t R_BSP_GetDPSW(void);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_SetDECNT(uint32_t data);
uint32_t R_BSP_GetDECNT(void);
void *R_BSP_GetDEPC(void);
#endif
#endif
#ifdef BSP_MCU_TRIGONOMETRIC
#ifdef __TFU
R_BSP_ATTRIB_INLINE_ASM void R_BSP_InitTFU(void);
#ifdef __FPU
R_BSP_ATTRIB_INLINE_ASM void R_BSP_CalcSine_Cosine(float f, float *sin, float *cos);
R_BSP_ATTRIB_INLINE_ASM void R_BSP_CalcAtan_SquareRoot(float y, float x, float *atan2, float *hypot);
#endif /* __FPU */
#endif /* __TFU */
#endif

/* End of multiple inclusion prevention macro */
#endif  /* R_RX_INTRINSIC_FUNCTIONS_H */

