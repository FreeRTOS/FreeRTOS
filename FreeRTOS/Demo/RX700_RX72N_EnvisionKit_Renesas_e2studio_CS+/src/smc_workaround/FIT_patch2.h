#ifndef FIT_PATCH2_H
#define FIT_PATCH2_H

#if defined(__ICCRX__)

/* Workaround to reduce the following remark messages caused in the r_rx_compiler.h.
 *
 *   #define R_BSP_ASM(...)            _R_BSP_ASM(__VA_ARGS__\n)
 *                                                           ^
 * "XXX\r_rx_compiler.h",NNN  Remark[Pe007]: unrecognized token
 *
 * Turn on the remark messages here.
 */
#pragma diag_default = Pe007

/* Workaround to reduce the following remark messages. (The following is example.)
 *
 *   #define R_BSP_ASM(...)            _R_BSP_ASM(__VA_ARGS__\n)
 *                                                           ^
 * "XXX\r_rx_compiler.h",NNN  Remark[Pe007]: unrecognized token
 *
 *       R_BSP_ASM(    SUB     #01H, R1                  )
 *                             ^
 * "XXX\r_bsp_common.c",NNN  Remark[Pe010]: "#" not expected here
 *
 *       R_BSP_ASM_BEGIN
 *       ^
 * "XXX\r_bsp_common.c",NNN  Remark[Pa174]: inline assembler statement has no declared
 * side-effect. All optimizations around it will be disabled. Either add side-effect
 * declarations or add volatile.
 *
 * Now redefine the following macros.
 */
#if !defined(__CDT_PARSER__)

#undef _R_BSP_ASM
#undef R_BSP_ASM
/* #undef R_BSP_ASM_LAB_NEXT */ /* no change */
/* #undef R_BSP_ASM_LAB_PREV */ /* no change */
/* #undef R_BSP_ASM_LAB */ /* no change */
#undef R_BSP_ASM_BEGIN
#undef R_BSP_ASM_END

#define _R_BSP_ASM(...)           #__VA_ARGS__ "\n"
#define R_BSP_ASM(...)            _R_BSP_ASM(__VA_ARGS__)
/* #define R_BSP_ASM_LAB_NEXT(n)     _lab##n */ /* no change */
/* #define R_BSP_ASM_LAB_PREV(n)     _lab##n */ /* no change */
/* #define R_BSP_ASM_LAB(n_colon)    R_BSP_ASM(_lab##n_colon) */ /* no change */
#define R_BSP_ASM_BEGIN           R_BSP_PRAGMA(diag_suppress = Pa174)\
                                  R_BSP_PRAGMA(diag_suppress = Pe010)\
                                  __asm volatile(
#define R_BSP_ASM_END             );\
                                  R_BSP_PRAGMA(diag_default = Pe010)\
                                  R_BSP_PRAGMA(diag_default = Pa174)

#endif /* !defined(__CDT_PARSER__) */

#endif /* defined(__ICCRX__) */

#endif /* FIT_PATCH2_H */
