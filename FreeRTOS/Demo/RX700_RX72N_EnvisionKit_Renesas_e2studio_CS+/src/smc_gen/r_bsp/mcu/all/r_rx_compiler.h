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
* File Name    : r_rx_compiler.h
* Description  : This is a file for integrating the definitions of different functions for each compilers.
*                Replace different functions for each compiler.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 1.00     First Release
*         : 08.10.2019 1.01     Modified definition of __RX_DPFPU_INSNS__ to __RX_DFPU_INSNS__ for GNUC.
*                               Modified definition of TFU for GNUC.
*                               Modified comment of TFU for ICCRX.
*                               Added include of r_bsp_config.h.
*                               Changed the following definitions for added support of Renesas RTOS(RI600V4 or RI600PX).
*                               - R_BSP_SECNAME_INTVECTTBL
*                               - R_BSP_SECNAME_EXCEPTVECTTBL
*                               - R_BSP_SECNAME_FIXEDVECTTBL
*                               - R_BSP_PRAGMA_INTERRUPT
*                               - R_BSP_PRAGMA_STATIC_INTERRUPT
*                               - R_BSP_PRAGMA_INTERRUPT_FUNCTION
*                               - R_BSP_ATTRIB_STATIC_INTERRUPT
*                               - R_BSP_PRAGMA_INTERRUPT_DEFAULT
*                               - R_BSP_PRAGMA_STATIC_INTERRUPT_DEFAULT
*                               Changed the following definitions to definition without __no_init for ICCRX so that 
*                               there is no warning when the initial value is specified.
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_C1
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_C2
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_C4
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_C8
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_D1
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_D2
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_D4
*                               - _R_BSP_ATTRIB_SECTION_CHANGE_D8
*         : 17.12.2019 1.02     Modified the comment of description.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "r_bsp_common.h"
#include "r_bsp_config.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef R_RX_COMPILER_H
#define R_RX_COMPILER_H

/* ========== Check Compiler ========== */
#if defined(__CCRX__)
    /* supported */
#elif defined(__GNUC__)
    /* supported */
#elif defined(__ICCRX__)
    /* supported */
#else
    #error "Unrecognized compiler"
#endif


/* ========== Macros ========== */
#if defined(__CCRX__)

/* #define __RX 1 */ /* This is automatically defined by CCRX. */
/* #define __LIT 1 */ /* This is automatically defined by CCRX. */
/* #define __BIG 1 */ /* This is automatically defined by CCRX. */
/* #define __FPU 1 */ /* This is automatically defined by CCRX. */
/* #define __RXV1 1 */ /* This is automatically defined by CCRX. */
/* #define __RXV2 1 */ /* This is automatically defined by CCRX. */
/* #define __RXV3 1 */ /* This is automatically defined by CCRX. */
/* #define __TFU 1 */ /* This is automatically defined by CCRX. */
/* #define __DPFPU 1 */ /* This is automatically defined by CCRX. */

#elif defined(__GNUC__)

#if !defined(__RX)
#define __RX 1
#endif

#if defined(__RX_LITTLE_ENDIAN__)
#if !defined(__LIT)
#define __LIT 1
#endif
#elif defined(__RX_BIG_ENDIAN__)
#if !defined(__BIG)
#define __BIG 1
#endif
#endif

#if defined(__RX_FPU_INSNS__)
#if !defined(__FPU)
#define __FPU 1
#endif
#endif

#if defined(__RXv1__)
#if !defined(__RXV1)
#define __RXV1 1
#endif
#endif

#if defined(__RXv2__)
#if !defined(__RXV2)
#define __RXV2 1
#endif
#endif

#if defined(__RXv3__)
#if !defined(__RXV3)
#define __RXV3 1
#endif
#endif

/* #define __TFU 1 */ /* This is automatically defined by GNUC. */

#if defined(__RX_DFPU_INSNS__)
#if !defined(__DPFPU)
#define __DPFPU 1
#endif
#endif

#elif defined(__ICCRX__)

#if !defined(__RX)
#define __RX 1
#endif

/* #define __LIT 1 */ /* This is automatically defined by ICCRX. */
/* #define __BIG 1 */ /* This is automatically defined by ICCRX. */
/* #define __FPU 1 */ /* This is automatically defined by ICCRX. */
/* #define __RXV1 1 */ /* This is automatically defined by ICCRX. */
/* #define __RXV2 1 */ /* This is automatically defined by ICCRX. */
/* #define __RXV3 1 */ /* This is automatically defined by ICCRX. */
/* #define __TFU 1 */ /* This is automatically defined by ICCRX. */
/* #define __DPFPU 1 */ /* Not yet supported. */

#endif


/* ========== Keywords ========== */
#if !(defined(__CCRX__) && defined(__cplusplus))
#define R_BSP_PRAGMA(...)    _Pragma(#__VA_ARGS__)
#else
/* CC-RX' C++ mode does not support Pragma operator and variadic macros */
#define R_BSP_PRAGMA(x)
#endif

#if defined(__CCRX__)

#define R_BSP_VOLATILE_EVENACCESS        volatile __evenaccess
#define R_BSP_EVENACCESS                 __evenaccess
#define R_BSP_EVENACCESS_SFR             __evenaccess
#define R_BSP_VOLATILE_SFR               volatile
#define R_BSP_SFR                        /* none */

#elif defined(__GNUC__)

#define R_BSP_VOLATILE_EVENACCESS        volatile
#define R_BSP_EVENACCESS                 /* none */
#define R_BSP_EVENACCESS_SFR             /* none */
#define R_BSP_VOLATILE_SFR               volatile
#define R_BSP_SFR                        /* none */

#elif defined(__ICCRX__)

#define R_BSP_VOLATILE_EVENACCESS        volatile
#define R_BSP_EVENACCESS                 volatile
#define R_BSP_EVENACCESS_SFR             __sfr
#define R_BSP_VOLATILE_SFR               volatile __sfr
#define R_BSP_SFR                        __sfr

#endif


/* ========== Sections ========== */

/* ---------- Operators ---------- */
#if defined(__CCRX__)

#define R_BSP_SECTOP(name)        __sectop(#name)
#define R_BSP_SECEND(name)        __secend(#name)
#define R_BSP_SECSIZE(name)       __secsize(#name)

#define R_BSP_SECTION_OPERATORS_INIT(name)    /* none */

#elif defined(__GNUC__)

#define R_BSP_SECTOP(name)        ((void *)name##_start)
#define R_BSP_SECEND(name)        ((void *)name##_end)
#define R_BSP_SECSIZE(name)       ((size_t)((uint8_t *)R_BSP_SECEND(name) - (uint8_t *)R_BSP_SECTOP(name)))

#define R_BSP_SECTION_OPERATORS_INIT(name)    extern uint8_t name##_start[], name##_end[];

#elif defined(__ICCRX__)

#define R_BSP_SECTOP(name)        __section_begin(#name)
#define R_BSP_SECEND(name)        __section_end(#name)
#define R_BSP_SECSIZE(name)       __section_size(#name)

#define R_BSP_SECTION_OPERATORS_INIT(name)    R_BSP_PRAGMA(section = #name);

#endif

/* ---------- Names ---------- */
#if defined(__CCRX__)

#if BSP_CFG_RTOS_USED == 4    /* Renesas RI600V4 & RI600PX */
#define R_BSP_SECNAME_INTVECTTBL       "INTERRUPT_VECTOR"
#else /* BSP_CFG_RTOS_USED != 4 */
#define R_BSP_SECNAME_INTVECTTBL       "C$VECT"
#endif /* BSP_CFG_RTOS_USED */

#if defined(__RXV2) || defined(__RXV3)
#if BSP_CFG_RTOS_USED == 4    /* Renesas RI600V4 & RI600PX */
#define R_BSP_SECNAME_EXCEPTVECTTBL    "FIX_INTERRUPT_VECTOR"
#else /* BSP_CFG_RTOS_USED != 4 */
#define R_BSP_SECNAME_EXCEPTVECTTBL    "EXCEPTVECT"
#endif /* BSP_CFG_RTOS_USED */
#define R_BSP_SECNAME_RESETVECT        "RESETVECT"
#else /* __RXV1 */
#if BSP_CFG_RTOS_USED == 4    /* Renesas RI600V4 & RI600PX */
#define R_BSP_SECNAME_FIXEDVECTTBL     "FIX_INTERRUPT_VECTOR"
#else /* BSP_CFG_RTOS_USED != 4 */
#define R_BSP_SECNAME_FIXEDVECTTBL     "FIXEDVECT"
#endif /* BSP_CFG_RTOS_USED */
#endif /* defined(__RXV2) || defined(__RXV3) */
#define R_BSP_SECNAME_UBSETTINGS       "UBSETTINGS"

#elif defined(__GNUC__)

#define R_BSP_SECNAME_INTVECTTBL       ".rvectors"
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_SECNAME_EXCEPTVECTTBL    ".exvectors"
#define R_BSP_SECNAME_RESETVECT        ".fvectors"
#else
#define R_BSP_SECNAME_FIXEDVECTTBL     ".fvectors"
#endif
#define R_BSP_SECNAME_UBSETTINGS       ".ubsettings"

#elif defined(__ICCRX__)

#define R_BSP_SECNAME_INTVECTTBL       ".inttable"
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_SECNAME_EXCEPTVECTTBL    ".exceptvect"
#define R_BSP_SECNAME_RESETVECT        ".resetvect"
#else
#define R_BSP_SECNAME_FIXEDVECTTBL     ".exceptvect"
#endif
#define R_BSP_SECNAME_UBSETTINGS       ".ubsettings"

#endif

/* ---------- Addresses ---------- */
#if defined(__CCRX__)

#define R_BSP_SECTOP_INTVECTTBL       __sectop(R_BSP_SECNAME_INTVECTTBL)
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_SECTOP_EXCEPTVECTTBL    __sectop(R_BSP_SECNAME_EXCEPTVECTTBL)
#endif

#elif defined(__GNUC__)

#define R_BSP_SECTOP_INTVECTTBL       ((void *)rvectors_start)
extern void * const                   rvectors_start[];
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_SECTOP_EXCEPTVECTTBL    ((void *)exvectors_start)
extern void * const                   exvectors_start[];
#endif

#elif defined(__ICCRX__)

#define R_BSP_SECTOP_INTVECTTBL       /* none */
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_SECTOP_EXCEPTVECTTBL    /* none */
#endif

#endif


/* ========== #pragma Directive ========== */

/* ---------- Stack Size ---------- */
#if defined(__CCRX__)

#define R_BSP_PRAGMA_STACKSIZE_SI(_size)     _R_BSP_PRAGMA_STACKSIZE_SI(_size) /* _size means '(size)' */
#define _R_BSP_PRAGMA_STACKSIZE_SI(_size)    __R_BSP_PRAGMA_STACKSIZE_SI##_size
#define __R_BSP_PRAGMA_STACKSIZE_SI(size)    R_BSP_PRAGMA(stacksize si=size)
#define R_BSP_PRAGMA_STACKSIZE_SU(_size)     _R_BSP_PRAGMA_STACKSIZE_SU(_size) /* _size means '(size)' */
#define _R_BSP_PRAGMA_STACKSIZE_SU(_size)    __R_BSP_PRAGMA_STACKSIZE_SU##_size
#define __R_BSP_PRAGMA_STACKSIZE_SU(size)    R_BSP_PRAGMA(stacksize su=size)

#elif defined(__GNUC__)

#define R_BSP_PRAGMA_STACKSIZE_SI(size)      static uint8_t istack_area[size] __attribute__((section(".r_bsp_istack"), used));
#define R_BSP_PRAGMA_STACKSIZE_SU(size)      static uint8_t ustack_area[size] __attribute__((section(".r_bsp_ustack"), used));

#elif defined(__ICCRX__)

#define R_BSP_PRAGMA_STACKSIZE_SI(size)      /* none */
#define R_BSP_PRAGMA_STACKSIZE_SU(size)      /* none */

#endif

/* ---------- Section Switch (part1) ---------- */
#if defined(__CCRX__)

#define R_BSP_ATTRIB_SECTION_CHANGE_UBSETTINGS                R_BSP_PRAGMA(section C UBSETTINGS)
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_ATTRIB_SECTION_CHANGE_EXCEPTVECT                R_BSP_PRAGMA(section C EXCEPTVECT)
#define R_BSP_ATTRIB_SECTION_CHANGE_RESETVECT                 R_BSP_PRAGMA(section C RESETVECT)
#else
#define R_BSP_ATTRIB_SECTION_CHANGE_FIXEDVECT                 R_BSP_PRAGMA(section C FIXEDVECT)
#endif

#elif defined(__GNUC__)

#define R_BSP_ATTRIB_SECTION_CHANGE_UBSETTINGS                __attribute__((section(R_BSP_SECNAME_UBSETTINGS)))
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_ATTRIB_SECTION_CHANGE_EXCEPTVECT                __attribute__((section(R_BSP_SECNAME_EXCEPTVECTTBL)))
#define R_BSP_ATTRIB_SECTION_CHANGE_RESETVECT                 __attribute__((section(R_BSP_SECNAME_RESETVECT)))
#else
#define R_BSP_ATTRIB_SECTION_CHANGE_FIXEDVECT                 __attribute__((section(R_BSP_SECNAME_FIXEDVECTTBL)))
#endif

#elif defined(__ICCRX__)

#define R_BSP_ATTRIB_SECTION_CHANGE_UBSETTINGS                R_BSP_PRAGMA(location=R_BSP_SECNAME_UBSETTINGS)
#if defined(__RXV2) || defined(__RXV3)
#define R_BSP_ATTRIB_SECTION_CHANGE_EXCEPTVECT                /* none */
#define R_BSP_ATTRIB_SECTION_CHANGE_RESETVECT                 /* none */
#else
#define R_BSP_ATTRIB_SECTION_CHANGE_FIXEDVECT                 /* none */
#endif
#endif

/* ---------- Section Switch (part2) ---------- */
#if defined(__CCRX__)

#define __R_BSP_ATTRIB_SECTION_CHANGE_V(type, section_name)    R_BSP_PRAGMA(section type section_name)
#define __R_BSP_ATTRIB_SECTION_CHANGE_F(type, section_name)    R_BSP_PRAGMA(section type section_name)

#define _R_BSP_ATTRIB_SECTION_CHANGE_B1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B, B##section_tag) /* The CC-RX adds postfix '_1' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_B2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B, B##section_tag) /* The CC-RX adds postfix '_2' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_B4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B, B##section_tag) /* The CC-RX does not add postfix '_4' */
#define _R_BSP_ATTRIB_SECTION_CHANGE_B8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B, B##section_tag) /* The CC-RX adds postfix '_8' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_C1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C, C##section_tag) /* The CC-RX adds postfix '_1' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_C2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C, C##section_tag) /* The CC-RX adds postfix '_2' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_C4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C, C##section_tag) /* The CC-RX does not add postfix '_4' */
#define _R_BSP_ATTRIB_SECTION_CHANGE_C8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C, C##section_tag) /* The CC-RX adds postfix '_8' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_D1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D, D##section_tag) /* The CC-RX adds postfix '_1' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_D2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D, D##section_tag) /* The CC-RX adds postfix '_2' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_D4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D, D##section_tag) /* The CC-RX does not add postfix '_4' */
#define _R_BSP_ATTRIB_SECTION_CHANGE_D8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D, D##section_tag) /* The CC-RX adds postfix '_8' automatically */
#define _R_BSP_ATTRIB_SECTION_CHANGE_P(section_tag)            __R_BSP_ATTRIB_SECTION_CHANGE_F(P, P##section_tag)

#if !defined(__cplusplus)
#define R_BSP_ATTRIB_SECTION_CHANGE(type, section_tag, ...)    _R_BSP_ATTRIB_SECTION_CHANGE_##type##__VA_ARGS__(section_tag)
#else
/* CC-RX' C++ mode does not support variadic macros */
#define R_BSP_ATTRIB_SECTION_CHANGE(type, section_tag, align)  _R_BSP_ATTRIB_SECTION_CHANGE_##type##align(section_tag)
#endif

#define R_BSP_ATTRIB_SECTION_CHANGE_END                        R_BSP_PRAGMA(section)

#elif defined(__GNUC__)

#define __R_BSP_ATTRIB_SECTION_CHANGE_V(section_name)          __attribute__((section(#section_name)))
#define __R_BSP_ATTRIB_SECTION_CHANGE_F(section_name)          __attribute__((section(#section_name)))

#define _R_BSP_ATTRIB_SECTION_CHANGE_B1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag##_1)
#define _R_BSP_ATTRIB_SECTION_CHANGE_B2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag##_2)
#define _R_BSP_ATTRIB_SECTION_CHANGE_B4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag) /* No postfix '_4' because the CC-RX does not add it */
#define _R_BSP_ATTRIB_SECTION_CHANGE_B8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag##_8)
#define _R_BSP_ATTRIB_SECTION_CHANGE_C1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C##section_tag##_1)
#define _R_BSP_ATTRIB_SECTION_CHANGE_C2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C##section_tag##_2)
#define _R_BSP_ATTRIB_SECTION_CHANGE_C4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C##section_tag) /* No postfix '_4' because the CC-RX does not add it */
#define _R_BSP_ATTRIB_SECTION_CHANGE_C8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(C##section_tag##_8)
#define _R_BSP_ATTRIB_SECTION_CHANGE_D1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D##section_tag##_1)
#define _R_BSP_ATTRIB_SECTION_CHANGE_D2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D##section_tag##_2)
#define _R_BSP_ATTRIB_SECTION_CHANGE_D4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D##section_tag) /* No postfix '_4' because the CC-RX does not add it */
#define _R_BSP_ATTRIB_SECTION_CHANGE_D8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(D##section_tag##_8)
#define _R_BSP_ATTRIB_SECTION_CHANGE_P(section_tag)            __R_BSP_ATTRIB_SECTION_CHANGE_F(P##section_tag)

#define R_BSP_ATTRIB_SECTION_CHANGE(type, section_tag, ...)    _R_BSP_ATTRIB_SECTION_CHANGE_##type##__VA_ARGS__(section_tag)
#define R_BSP_ATTRIB_SECTION_CHANGE_END                        /* none */

#elif defined(__ICCRX__)

#define __R_BSP_ATTRIB_SECTION_CHANGE_V(section_name)          R_BSP_PRAGMA(location=#section_name)\
                                                               __no_init
#define __R_BSP_ATTRIB_SECTION_CHANGE_F(section_name)          R_BSP_PRAGMA(location=#section_name)

#define _R_BSP_ATTRIB_SECTION_CHANGE_B1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag##_1)
#define _R_BSP_ATTRIB_SECTION_CHANGE_B2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag##_2)
#define _R_BSP_ATTRIB_SECTION_CHANGE_B4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag) /* No postfix '_4' because the CC-RX does not add it */
#define _R_BSP_ATTRIB_SECTION_CHANGE_B8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_V(B##section_tag##_8)
#define _R_BSP_ATTRIB_SECTION_CHANGE_C1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(C##section_tag##_1)
#define _R_BSP_ATTRIB_SECTION_CHANGE_C2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(C##section_tag##_2)
#define _R_BSP_ATTRIB_SECTION_CHANGE_C4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(C##section_tag) /* No postfix '_4' because the CC-RX does not add it */
#define _R_BSP_ATTRIB_SECTION_CHANGE_C8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(C##section_tag##_8)
#define _R_BSP_ATTRIB_SECTION_CHANGE_D1(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(D##section_tag##_1)
#define _R_BSP_ATTRIB_SECTION_CHANGE_D2(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(D##section_tag##_2)
#define _R_BSP_ATTRIB_SECTION_CHANGE_D4(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(D##section_tag) /* No postfix '_4' because the CC-RX does not add it */
#define _R_BSP_ATTRIB_SECTION_CHANGE_D8(section_tag)           __R_BSP_ATTRIB_SECTION_CHANGE_F(D##section_tag##_8)
#define _R_BSP_ATTRIB_SECTION_CHANGE_P(section_tag)            __R_BSP_ATTRIB_SECTION_CHANGE_F(P##section_tag)

#define R_BSP_ATTRIB_SECTION_CHANGE(type, section_tag, ...)    _R_BSP_ATTRIB_SECTION_CHANGE_##type##__VA_ARGS__(section_tag)
#define R_BSP_ATTRIB_SECTION_CHANGE_END                        /* none */

#endif

/* ---------- Interrupt Function Creation ---------- */
#if defined(__CCRX__)

/* Standard */
#if BSP_CFG_RTOS_USED == 4    /* Renesas RI600V4 & RI600PX */
#define R_BSP_PRAGMA_INTERRUPT(function_name, vector)                 extern void function_name(void);

#define R_BSP_PRAGMA_STATIC_INTERRUPT(function_name, vector)          void function_name(void);

#define R_BSP_PRAGMA_INTERRUPT_FUNCTION(function_name)                extern void function_name(void);

#else /* BSP_CFG_RTOS_USED != 4*/
#define R_BSP_PRAGMA_INTERRUPT(function_name, vector)                 R_BSP_PRAGMA(interrupt function_name(vect=vector))\
                                                                      extern void function_name(void);
#define R_BSP_PRAGMA_STATIC_INTERRUPT(function_name, vector)          R_BSP_PRAGMA(interrupt function_name(vect=vector))\
                                                                      static void function_name(void);

#define R_BSP_PRAGMA_INTERRUPT_FUNCTION(function_name)                R_BSP_PRAGMA(interrupt function_name)\
                                                                      extern void function_name(void);
#endif /* BSP_CFG_RTOS_USED */

#define R_BSP_PRAGMA_STATIC_INTERRUPT_FUNCTION(function_name)         R_BSP_PRAGMA(interrupt function_name)\
                                                                      static void function_name(void);

#define R_BSP_ATTRIB_INTERRUPT                                        extern /* only this one because of no corresponding keyword */

#if BSP_CFG_RTOS_USED == 4    /* Renesas RI600V4 & RI600PX */
#define R_BSP_ATTRIB_STATIC_INTERRUPT                                 
#else /* BSP_CFG_RTOS_USED !=4 */
#define R_BSP_ATTRIB_STATIC_INTERRUPT                                 static /* only this one because of no corresponding keyword */
#endif /* BSP_CFG_RTOS_USED */

/* Fast */
#define R_BSP_PRAGMA_FAST_INTERRUPT(function_name, vector)            R_BSP_PRAGMA(interrupt function_name(vect=vector, fint))\
                                                                      extern void function_name(void);
#define R_BSP_PRAGMA_STATIC_FAST_INTERRUPT(function_name, vector)     R_BSP_PRAGMA(interrupt function_name(vect=vector, fint))\
                                                                      static void function_name(void);

#define R_BSP_PRAGMA_FAST_INTERRUPT_FUNCTION(function_name)           R_BSP_PRAGMA(interrupt function_name(fint))\
                                                                      extern void function_name(void);
#define R_BSP_PRAGMA_STATIC_FAST_INTERRUPT_FUNCTION(function_name)    R_BSP_PRAGMA(interrupt function_name(fint))\
                                                                      static void function_name(void);

#define R_BSP_ATTRIB_FAST_INTERRUPT                                   extern /* only this one because of no corresponding keyword */
#define R_BSP_ATTRIB_STATIC_FAST_INTERRUPT                            static /* only this one because of no corresponding keyword */

/* Default */
#if BSP_CFG_RTOS_USED == 4    /* Renesas RI600V4 & RI600PX */
#define R_BSP_PRAGMA_INTERRUPT_DEFAULT(function_name)                 extern void function_name(void);

#define R_BSP_PRAGMA_STATIC_INTERRUPT_DEFAULT(function_name)          void function_name(void);
#else /* BSP_CFG_RTOS_USED != 4 */
#define R_BSP_PRAGMA_INTERRUPT_DEFAULT(function_name)                 R_BSP_PRAGMA(interrupt function_name)\
                                                                      extern void function_name(void);

#define R_BSP_PRAGMA_STATIC_INTERRUPT_DEFAULT(function_name)          R_BSP_PRAGMA(interrupt function_name)\
                                                                      static void function_name(void);
#endif /* BSP_CFG_RTOS_USED */

#elif defined(__GNUC__)

/* Standard */
#define R_BSP_PRAGMA_INTERRUPT(function_name, vector)                 extern void function_name(void) __attribute__((interrupt(R_BSP_SECNAME_INTVECTTBL, vector)));
#define R_BSP_PRAGMA_STATIC_INTERRUPT(function_name, vector)          static void function_name(void) __attribute__((interrupt(R_BSP_SECNAME_INTVECTTBL, vector), used));

#define R_BSP_PRAGMA_INTERRUPT_FUNCTION(function_name)                extern void function_name(void) __attribute__((interrupt));
#define R_BSP_PRAGMA_STATIC_INTERRUPT_FUNCTION(function_name)         static void function_name(void) __attribute__((interrupt, used));

#define R_BSP_ATTRIB_INTERRUPT                                        extern /* only this one because __attribute__((interrupt)) prevents GNURX from generating vector */
#define R_BSP_ATTRIB_STATIC_INTERRUPT                                 static /* only this one because __attribute__((interrupt, used)) prevents GNURX from generating vector */

/* Fast */
#define R_BSP_PRAGMA_FAST_INTERRUPT(function_name, vector)            extern void function_name(void) __attribute__((interrupt(R_BSP_SECNAME_INTVECTTBL, vector))) \
                                                                                                      __attribute__((fast_interrupt));
#define R_BSP_PRAGMA_STATIC_FAST_INTERRUPT(function_name, vector)     static void function_name(void) __attribute__((interrupt(R_BSP_SECNAME_INTVECTTBL, vector), used)) \
                                                                                                      __attribute__((fast_interrupt, used));

#define R_BSP_PRAGMA_FAST_INTERRUPT_FUNCTION(function_name)           extern void function_name(void) __attribute__((fast_interrupt));
#define R_BSP_PRAGMA_STATIC_FAST_INTERRUPT_FUNCTION(function_name)    static void function_name(void) __attribute__((fast_interrupt, used));

#define R_BSP_ATTRIB_FAST_INTERRUPT                                   extern /* __attribute__((interrupt(fast))) Not necessary,
                                                                                but Don't forget a R_BSP_PRAGMA_FAST_INTERRUPT() declaration */
#define R_BSP_ATTRIB_STATIC_FAST_INTERRUPT                            static /* __attribute__((interrupt(fast)), used) Not necessary, 
                                                                                but Don't forget a R_BSP_PRAGMA_STATIC_FAST_INTERRUPT() declaration */

/* Default */
#define R_BSP_PRAGMA_INTERRUPT_DEFAULT(function_name)                 extern void function_name(void) __attribute__((interrupt(R_BSP_SECNAME_INTVECTTBL, "$default")));
#define R_BSP_PRAGMA_STATIC_INTERRUPT_DEFAULT(function_name)          static void function_name(void) __attribute__((interrupt(R_BSP_SECNAME_INTVECTTBL, "$default"), used));

#elif defined(__ICCRX__)

/* Standard */
#define R_BSP_PRAGMA_INTERRUPT(function_name, vect)                   R_BSP_PRAGMA(vector=vect)\
                                                                      extern __interrupt void function_name(void);
#define R_BSP_PRAGMA_STATIC_INTERRUPT(function_name, vect)            R_BSP_PRAGMA(vector=vect)\
                                                                      static __interrupt void function_name(void);

#define R_BSP_PRAGMA_INTERRUPT_FUNCTION(function_name)                extern __interrupt void function_name(void);
#define R_BSP_PRAGMA_STATIC_INTERRUPT_FUNCTION(function_name)         static __interrupt void function_name(void);

#define R_BSP_ATTRIB_INTERRUPT                                        extern __interrupt /* ICCRX requires __interrupt not only at a function declaration but also at a function definition */
#define R_BSP_ATTRIB_STATIC_INTERRUPT                                 static __interrupt /* ICCRX requires __interrupt not only at a function declaration but also at a function definition */

/* Fast */
#define R_BSP_PRAGMA_FAST_INTERRUPT(function_name, vect)              R_BSP_PRAGMA(vector=vect)\
                                                                      extern __fast_interrupt void function_name(void);
#define R_BSP_PRAGMA_STATIC_FAST_INTERRUPT(function_name, vect)       R_BSP_PRAGMA(vector=vect)\
                                                                      static __fast_interrupt void function_name(void);

#define R_BSP_PRAGMA_FAST_INTERRUPT_FUNCTION(function_name)           extern __fast_interrupt void function_name(void);
#define R_BSP_PRAGMA_STATIC_FAST_INTERRUPT_FUNCTION(function_name)    static __fast_interrupt void function_name(void);

#define R_BSP_ATTRIB_FAST_INTERRUPT                                   extern __fast_interrupt /* ICCRX requires __interrupt not only at a function declaration but also at a function definition */
#define R_BSP_ATTRIB_STATIC_FAST_INTERRUPT                            static __fast_interrupt /* ICCRX requires __interrupt not only at a function declaration but also at a function definition */

/* Default */
#define R_BSP_PRAGMA_INTERRUPT_DEFAULT(function_name)                 extern __interrupt void function_name(void);
#define R_BSP_PRAGMA_STATIC_INTERRUPT_DEFAULT(function_name)          static __interrupt void function_name(void);

#endif

/* ---------- Inline Expansion of Function ---------- */
#if defined(__CCRX__)

#define R_BSP_PRAGMA_INLINE(function_name)           R_BSP_PRAGMA(inline function_name)\
                                                     extern
#define R_BSP_PRAGMA_STATIC_INLINE(function_name)    R_BSP_PRAGMA(inline function_name)\
                                                     static

#elif defined(__GNUC__)

#define R_BSP_PRAGMA_INLINE(function_name)           inline extern __attribute__((always_inline))
#define R_BSP_PRAGMA_STATIC_INLINE(function_name)    inline static __attribute__((always_inline))

#elif defined(__ICCRX__)

#define R_BSP_PRAGMA_INLINE(function_name)           R_BSP_PRAGMA(inline=forced)\
                                                     extern
#define R_BSP_PRAGMA_STATIC_INLINE(function_name)    R_BSP_PRAGMA(inline=forced)\
                                                     static

#endif

/* ---------- Inline Expansion of Assembly-Language Function (part1) ---------- */
#if defined(__CCRX__)

#define R_BSP_PRAGMA_INLINE_ASM(function_name)           R_BSP_PRAGMA(inline_asm function_name)\
                                                         extern
#define R_BSP_PRAGMA_STATIC_INLINE_ASM(function_name)    R_BSP_PRAGMA(inline_asm function_name)\
                                                         static

#define R_BSP_ATTRIB_INLINE_ASM                          extern /* only this one because of no corresponding keyword */
#define R_BSP_ATTRIB_STATIC_INLINE_ASM                   static /* only this one because of no corresponding keyword */

#elif defined(__GNUC__)

/* Using inline assembler without operands and clobbered resources is dangerous but using it with them is too difficult. */

#define R_BSP_PRAGMA_INLINE_ASM(function_name)           extern __attribute__((naked, noinline))
#define R_BSP_PRAGMA_STATIC_INLINE_ASM(function_name)    static __attribute__((naked, noinline))

#define R_BSP_ATTRIB_INLINE_ASM                          extern /* only this one because of no corresponding keyword */
#define R_BSP_ATTRIB_STATIC_INLINE_ASM                   static /* only this one because of no corresponding keyword */

#elif defined(__ICCRX__)

/* Using inline assembler without operands and clobbered resources is dangerous but using it with them is too difficult. */

#define R_BSP_PRAGMA_INLINE_ASM(function_name)           R_BSP_PRAGMA(inline=never)\
                                                         extern
#define R_BSP_PRAGMA_STATIC_INLINE_ASM(function_name)    R_BSP_PRAGMA(inline=never)\
                                                         static

#define R_BSP_ATTRIB_INLINE_ASM                          extern /* ICCRX requires __task not only at a function declaration but also at a function definition */
#define R_BSP_ATTRIB_STATIC_INLINE_ASM                   static /* ICCRX requires __task not only at a function declaration but also at a function definition */

#endif

/* ---------- Inline Expansion of Assembly-Language Function (part2) ---------- */
#if defined(__CDT_PARSER__)

#define R_BSP_ASM(...)            /* none */
#define R_BSP_ASM_LAB_NEXT(n)     /* none */
#define R_BSP_ASM_LAB_PREV(n)     /* none */
#define R_BSP_ASM_LAB(n_colon)    /* none */
#define R_BSP_ASM_BEGIN           /* none */
#define R_BSP_ASM_END             /* none */

#else

#if defined(__CCRX__)

#if !defined(__cplusplus)
#define R_BSP_ASM(...)            __VA_ARGS__
#else
/* CC-RX' C++ mode does not support variadic macros */
#endif
#define R_BSP_ASM_LAB_NEXT(n)     ?+
#define R_BSP_ASM_LAB_PREV(n)     ?-
#define R_BSP_ASM_LAB(n_colon)    R_BSP_ASM(?:)
#define R_BSP_ASM_BEGIN           /* none */
#define R_BSP_ASM_END             /* none */

#elif defined(__GNUC__)

#define _R_BSP_ASM(...)           #__VA_ARGS__
#define R_BSP_ASM(...)            _R_BSP_ASM(__VA_ARGS__\n)
#define R_BSP_ASM_LAB_NEXT(n)     ?+
#define R_BSP_ASM_LAB_PREV(n)     ?-
#define R_BSP_ASM_LAB(n_colon)    R_BSP_ASM(?:)
#define R_BSP_ASM_BEGIN           __asm__ volatile (
#define R_BSP_ASM_END             R_BSP_ASM(rts));

#elif defined(__ICCRX__)

#define _R_BSP_ASM(...)           #__VA_ARGS__
#define R_BSP_ASM(...)            _R_BSP_ASM(__VA_ARGS__\n)
#define R_BSP_ASM_LAB_NEXT(n)     _lab##n
#define R_BSP_ASM_LAB_PREV(n)     _lab##n
#define R_BSP_ASM_LAB(n_colon)    R_BSP_ASM(_lab##n_colon)
#define R_BSP_ASM_BEGIN           asm(
#define R_BSP_ASM_END             );

#endif

#endif /* defined(__CDT_PARSER__) */

/* ---------- Inline Expansion of Assembly-Language Function (part3) ---------- */
#if defined(__CCRX__)

#define R_BSP_ASM_INTERNAL_USED(p)        /* no way */
#define R_BSP_ASM_INTERNAL_NOT_USED(p)    /* no way */

#elif defined(__GNUC__)

#define R_BSP_ASM_INTERNAL_USED(p)        ((void)(p));
#define R_BSP_ASM_INTERNAL_NOT_USED(p)    ((void)(p));

#elif defined(__ICCRX__)

#define R_BSP_ASM_INTERNAL_USED(p)        ((void)(p));
#define R_BSP_ASM_INTERNAL_NOT_USED(p)    ((void)(p));

#endif

/* ---------- Bit Field Order Specification ---------- */

/* ---------- bit_order=left ---------- */
#if defined(__CCRX__)

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                           bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                           bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                           bf30, bf31)\
struct {\
R_BSP_PRAGMA(bit_order left)\
    struct {\
        bf0;\
        bf1;\
        bf2;\
        bf3;\
        bf4;\
        bf5;\
        bf6;\
        bf7;\
        bf8;\
        bf9;\
        bf10;\
        bf11;\
        bf12;\
        bf13;\
        bf14;\
        bf15;\
        bf16;\
        bf17;\
        bf18;\
        bf19;\
        bf20;\
        bf21;\
        bf22;\
        bf23;\
        bf24;\
        bf25;\
        bf26;\
        bf27;\
        bf28;\
        bf29;\
        bf30;\
        bf31;\
    };\
R_BSP_PRAGMA(bit_order)\
}

#elif defined(__GNUC__)

#if defined(__LIT)

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                           bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                           bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                           bf30, bf31)\
struct {\
    bf31;\
    bf30;\
    bf29;\
    bf28;\
    bf27;\
    bf26;\
    bf25;\
    bf24;\
    bf23;\
    bf22;\
    bf21;\
    bf20;\
    bf19;\
    bf18;\
    bf17;\
    bf16;\
    bf15;\
    bf14;\
    bf13;\
    bf12;\
    bf11;\
    bf10;\
    bf9;\
    bf8;\
    bf7;\
    bf6;\
    bf5;\
    bf4;\
    bf3;\
    bf2;\
    bf1;\
    bf0;\
}

#else /* defined(__LIT) */

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                           bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                           bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                           bf30, bf31)\
struct {\
    bf0;\
    bf1;\
    bf2;\
    bf3;\
    bf4;\
    bf5;\
    bf6;\
    bf7;\
    bf8;\
    bf9;\
    bf10;\
    bf11;\
    bf12;\
    bf13;\
    bf14;\
    bf15;\
    bf16;\
    bf17;\
    bf18;\
    bf19;\
    bf20;\
    bf21;\
    bf22;\
    bf23;\
    bf24;\
    bf25;\
    bf26;\
    bf27;\
    bf28;\
    bf29;\
    bf30;\
    bf31;\
}

#endif /* defined(__LIT) */

#elif defined(__ICCRX__)

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                           bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                           bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                           bf30, bf31)\
struct {\
R_BSP_PRAGMA(bitfields=reversed_disjoint_types)\
    struct {\
        bf0;\
        bf1;\
        bf2;\
        bf3;\
        bf4;\
        bf5;\
        bf6;\
        bf7;\
        bf8;\
        bf9;\
        bf10;\
        bf11;\
        bf12;\
        bf13;\
        bf14;\
        bf15;\
        bf16;\
        bf17;\
        bf18;\
        bf19;\
        bf20;\
        bf21;\
        bf22;\
        bf23;\
        bf24;\
        bf25;\
        bf26;\
        bf27;\
        bf28;\
        bf29;\
        bf30;\
        bf31;\
    };\
R_BSP_PRAGMA(bitfields=default)\
}

#endif /* defined(__ICCRX__) */

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_1(bf0)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_2(bf0, bf1)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_3(bf0, bf1, bf2)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_4(bf0, bf1, bf2, bf3)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_5(bf0, bf1, bf2, bf3, bf4)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_6(bf0, bf1, bf2, bf3, bf4, bf5)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_7(bf0, bf1, bf2, bf3, bf4, bf5, bf6)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_8(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_9(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_10(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_11(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_12(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_13(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_14(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_15(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_16(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_17(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_18(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_19(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_20(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_21(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_22(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_23(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_24(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_25(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_26(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_27(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_28(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_29(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_30(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, bf29, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_31(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                                bf30)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, bf29, bf30, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_32(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                                bf30, bf31)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, bf29, bf30, bf31) \

/* ---------- bit_order=right ---------- */
#if defined(__CCRX__)

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                            bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                            bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                            bf30, bf31)\
struct {\
R_BSP_PRAGMA(bit_order right)\
    struct {\
        bf0;\
        bf1;\
        bf2;\
        bf3;\
        bf4;\
        bf5;\
        bf6;\
        bf7;\
        bf8;\
        bf9;\
        bf10;\
        bf11;\
        bf12;\
        bf13;\
        bf14;\
        bf15;\
        bf16;\
        bf17;\
        bf18;\
        bf19;\
        bf20;\
        bf21;\
        bf22;\
        bf23;\
        bf24;\
        bf25;\
        bf26;\
        bf27;\
        bf28;\
        bf29;\
        bf30;\
        bf31;\
    };\
R_BSP_PRAGMA(bit_order)\
}

#elif defined(__GNUC__)

#if defined(__LIT)

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                            bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                            bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                            bf30, bf31)\
struct {\
    bf0;\
    bf1;\
    bf2;\
    bf3;\
    bf4;\
    bf5;\
    bf6;\
    bf7;\
    bf8;\
    bf9;\
    bf10;\
    bf11;\
    bf12;\
    bf13;\
    bf14;\
    bf15;\
    bf16;\
    bf17;\
    bf18;\
    bf19;\
    bf20;\
    bf21;\
    bf22;\
    bf23;\
    bf24;\
    bf25;\
    bf26;\
    bf27;\
    bf28;\
    bf29;\
    bf30;\
    bf31;\
}

#else /* defined(__LIT) */

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                            bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                            bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                            bf30, bf31)\
struct {\
    bf31;\
    bf30;\
    bf29;\
    bf28;\
    bf27;\
    bf26;\
    bf25;\
    bf24;\
    bf23;\
    bf22;\
    bf21;\
    bf20;\
    bf19;\
    bf18;\
    bf17;\
    bf16;\
    bf15;\
    bf14;\
    bf13;\
    bf12;\
    bf11;\
    bf10;\
    bf9;\
    bf8;\
    bf7;\
    bf6;\
    bf5;\
    bf4;\
    bf3;\
    bf2;\
    bf1;\
    bf0;\
}

#endif /* defined(__LIT) */

#elif defined(__ICCRX__)

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                            bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                            bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                            bf30, bf31)\
struct {\
R_BSP_PRAGMA(bitfields=disjoint_types)\
    struct {\
        bf0;\
        bf1;\
        bf2;\
        bf3;\
        bf4;\
        bf5;\
        bf6;\
        bf7;\
        bf8;\
        bf9;\
        bf10;\
        bf11;\
        bf12;\
        bf13;\
        bf14;\
        bf15;\
        bf16;\
        bf17;\
        bf18;\
        bf19;\
        bf20;\
        bf21;\
        bf22;\
        bf23;\
        bf24;\
        bf25;\
        bf26;\
        bf27;\
        bf28;\
        bf29;\
        bf30;\
        bf31;\
    };\
R_BSP_PRAGMA(bitfields=default)\
}

#endif /* defined(__ICCRX__) */

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_1(bf0)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_2(bf0, bf1)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_3(bf0, bf1, bf2)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_4(bf0, bf1, bf2, bf3)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_5(bf0, bf1, bf2, bf3, bf4)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_6(bf0, bf1, bf2, bf3, bf4, bf5)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_7(bf0, bf1, bf2, bf3, bf4, bf5, bf6)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_8(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_9(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_10(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_11(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_12(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_13(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_14(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_15(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_16(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_17(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_18(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_19(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_20(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_21(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, uint8_t :0, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_22(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, uint8_t :0, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_23(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, uint8_t :0, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_24(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_25(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_26(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_27(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_28(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, uint8_t :0, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_29(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, uint8_t :0, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_30(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, bf29, uint8_t :0, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_31(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                                bf30)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, bf29, bf30, uint8_t :0) \

#define R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT_32(bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, bf8, bf9, \
                                                bf10, bf11, bf12, bf13, bf14, bf15, bf16, bf17, bf18, bf19, \
                                                bf20, bf21, bf22, bf23, bf24, bf25, bf26, bf27, bf28, bf29, \
                                                bf30, bf31)\
 R_BSP_ATTRIB_STRUCT_BIT_ORDER_RIGHT( \
 bf0, bf1, bf2, bf3, bf4, bf5, bf6, bf7, \
 bf8, bf9, bf10, bf11, bf12, bf13, bf14, bf15, \
 bf16, bf17, bf18, bf19, bf20, bf21, bf22, bf23, \
 bf24, bf25, bf26, bf27, bf28, bf29, bf30, bf31) \

/* ---------- Alignment Value Specification for Structure Members and Class Members ---------- */
#if defined(__CCRX__)

#define R_BSP_PRAGMA_PACK          R_BSP_PRAGMA(pack)
#define R_BSP_PRAGMA_UNPACK        R_BSP_PRAGMA(unpack)
#define R_BSP_PRAGMA_PACKOPTION    R_BSP_PRAGMA(packoption)

#elif defined(__GNUC__)

#define R_BSP_PRAGMA_PACK          R_BSP_PRAGMA(pack(1))
#define R_BSP_PRAGMA_UNPACK        R_BSP_PRAGMA(pack(4))
#define R_BSP_PRAGMA_PACKOPTION    R_BSP_PRAGMA(pack())

#elif defined(__ICCRX__)

#define R_BSP_PRAGMA_PACK          R_BSP_PRAGMA(pack(1))
#define R_BSP_PRAGMA_UNPACK        R_BSP_PRAGMA(pack(4))
#define R_BSP_PRAGMA_PACKOPTION    R_BSP_PRAGMA(pack())

#endif

/* ========== Rename Functions ========== */

#if defined(__CCRX__)

#define R_BSP_POR_FUNCTION(name)            extern void name(void)
#define R_BSP_POWER_ON_RESET_FUNCTION       PowerON_Reset_PC
#define R_BSP_STARTUP_FUNCTION              PowerON_Reset_PC

#define R_BSP_UB_POR_FUNCTION(name)         extern void name(void)
#define R_BSP_UB_POWER_ON_RESET_FUNCTION    PowerON_Reset_PC

#define R_BSP_MAIN_FUNCTION                 main

/* #define _INITSCT */
/* #define excep_supervisor_inst_isr */
/* #define excep_access_isr */
/* #define excep_undefined_inst_isr */
/* #define excep_floating_point_isr */
/* #define non_maskable_isr */
/* #define undefined_interrupt_source_isr */

#elif defined(__GNUC__)

#define R_BSP_POR_FUNCTION(name)            extern void name(void)
#define R_BSP_POWER_ON_RESET_FUNCTION       PowerON_Reset_PC
#define R_BSP_STARTUP_FUNCTION              PowerON_Reset_PC_Prg

#define R_BSP_UB_POR_FUNCTION(name)         extern void name(void)
#define R_BSP_UB_POWER_ON_RESET_FUNCTION    PowerON_Reset_PC

#define R_BSP_MAIN_FUNCTION                 main

/* #define _INITSCT */
/* #define excep_supervisor_inst_isr */
/* #define excep_access_isr */
/* #define excep_undefined_inst_isr */
/* #define excep_floating_point_isr */
/* #define non_maskable_isr */
/* #define undefined_interrupt_source_isr */

#elif defined(__ICCRX__)

#define R_BSP_POR_FUNCTION(name)            extern int name(void)
#define R_BSP_POWER_ON_RESET_FUNCTION       _iar_program_start
#define R_BSP_STARTUP_FUNCTION              __low_level_init

#define R_BSP_UB_POR_FUNCTION(name)         extern int name(void)
#define R_BSP_UB_POWER_ON_RESET_FUNCTION    _iar_program_start

#define R_BSP_MAIN_FUNCTION                 _iar_main_call

#define _INITSCT                            __iar_data_init2
#define excep_supervisor_inst_isr           __privileged_handler
#define excep_access_isr                    __excep_access_inst
#define excep_undefined_inst_isr            __undefined_handler
#define excep_floating_point_isr            _float_placeholder
#define non_maskable_isr                    __NMI_handler
#define undefined_interrupt_source_isr      __undefined_interrupt_source_handler

#endif

#endif /* R_RX_COMPILER_H */

