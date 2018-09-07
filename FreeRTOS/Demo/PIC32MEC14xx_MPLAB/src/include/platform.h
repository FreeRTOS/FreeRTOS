/*****************************************************************************
* © 2014 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/

/** @file platform.h
 *MEC14xx platform/cpu abstractions
 */
/** @defgroup MEC14xx
 */

#ifndef _PLATFORM_H
#define _PLATFORM_H

#if defined(__GNUC__) && defined(__mips__)

#if defined(__XC32__)  // Microchip XC32 GCC

/* Pull in MIPS32 specific special instructions instrinsics for
 * interrupt control, NOP, Wait-for-Interrupt and accessing
 * MSR's.
 * Issue: MPLAB-X IDE editor and the CPU macros in xc.h & cp0defs.h.
 * The IDE editor will show red ! on every line of code using the above
 * macros due to a bug in the IDE's C language preprocessor.
 */
#include <xc.h>

#define CPU_DISABLE_INTERRUPTS() __builtin_disable_interrupts()
#define CPU_GET_DISABLE_INTERRUPTS(x) { x=_CP0_GET_STATUS()&0x1ul; __builtin_disable_interrupts() }
#define CPU_ENABLE_INTERRUPTS() __builtin_enable_interrupts()
#define CPU_RESTORE_INTERRUPTS(x) { if (x) { __builtin_enable_interrupts(); } }

#define Disable_Irq()   CPU_DISABLE_INTERRUPTS()
#define Enable_Irq()    CPU_ENABLE_INTERRUPTS()

#define __CLZ(x) __builtin_clz(x)
#define __CTZ(x) __builtin_ctz (x)
#define __CLO(x) _clo(x)

#define __INS(tgt,val,pos,sz) _ins(tgt,val,pos,sz)
#define __EXT(x,pos,sz) _ext(x,pos,sz)

#define CPU_NOP() __asm__ __volatile ("%(ssnop%)" : :)

#define CPU_WAIT_FOR_INTR() __asm__ __volatile ("wait")

#define __REV(x) _bswapw(x)

#define __EHB() _ehb()

#else

/* Include MIPS specific inline assembly functions for accessing
 * MIPS CP0 registers, NOP, WAIT, ASET, ACLR, byte-reverse, etc.
 */
#include "mipscpu.h"


#define CPU_DISABLE_INTERRUPTS()  	mips32r2_dis_intr()
#define CPU_GET_DISABLE_INTERRUPTS(x) x=mips32r2_dis_intr()
#define CPU_ENABLE_INTERRUPTS() mips32r2_en_intr()
#define CPU_RESTORE_INTERRUPTS(x) mips32r2_restore_intr(x)

#define Disable_Irq()   CPU_DISABLE_INTERRUPTS()
#define Enable_Irq()    CPU_ENABLE_INTERRUPTS()

#define __CLZ(x) __builtin_clz(x)
#define __CTZ(x) __builtin_ctz (x)

#define __CLO(x) __extension__({ \
    unsigned int __x = (x); \
    unsigned int __v; \
    __asm__ ("clo %0,%1" : "=d" (__v) : "d" (__x)); \
    __v; \
})

/* MIPS32r2 insert bits */
#define __INS(tgt,val,pos,sz) __extension__({ \
    unsigned int __t = (tgt), __v = (val); \
    __asm__ ("ins %0,%z1,%2,%3" \
             : "+d" (__t) \
             : "dJ" (__v), "I" (pos), "I" (sz)); \
    __t; \
})

/* MIPS32r2 extract bits */
#define __EXT(x,pos,sz) __extension__({ \
    unsigned int __x = (x), __v; \
    __asm__ ("ext %0,%z1,%2,%3" \
             : "=d" (__v) \
             : "dJ" (__x), "I" (pos), "I" (sz)); \
    __v; \
})

#define CPU_NOP() __asm__ __volatile ("%(ssnop%)" : :)

#define CPU_WAIT_FOR_INTR() __asm__ __volatile ("wait")

#define __REV(x) mips32r2_rev_word(x)

#define __EHB() __asm__ __volatile__ ("%(ehb%)" : :)

#define _CP0_GET_BADVADDR() mips32r2_cp0_badvaddr_get()

#define _CP0_GET_COUNT() mips32r2_cp0_count_get()
#define _CP0_SET_COUNT(val) mips32r2_cp0_count_set((unsigned long)val)

#define _CP0_GET_COMPARE() mips32r2_cp0_compare_get()
#define _CP0_SET_COMPARE(val) mips32r2_cp0_compare_set((unsigned long)val)

#define _CP0_GET_STATUS() mips32r2_cp0_status_get()
#define _CP0_SET_STATUS(val) mips32r2_cp0_status_set((unsigned long)val)
#define _CP0_BIC_STATUS(val) mips32r2_cp0_status_bic(val)
#define _CP0_BIS_STATUS(val) mips32r2_cp0_status_bis(val)

#define _CP0_GET_INTCTL() mips32r2_cp0_intctl_get()
#define _CP0_SET_INTCTL(val)  mips32r2_cp0_intctl_set((unsigned long)val)

#define _CP0_GET_VIEW_IPL() mips32r2_cp0_view_ipl_get()
#define _CP0_SET_VIEW_IPL(val)  mips32r2_cp0_view_ipl_set((unsigned long)val)

#define _CP0_GET_CAUSE() mips32r2_cp0_cause_get()
#define _CP0_SET_CAUSE(val) mips32r2_cp0_cause_set((unsigned long)val)
#define _CP0_BIC_CAUSE(val) mips32r2_cp0_cause_bic((unsigned long)val)
#define _CP0_BIS_CAUSE(val) mips32r2_cp0_cause_bis((unsigned long)val)

#define _CP0_GET_VIEW_RIPL() mips32r2_cp0_view_ripl_get()
#define _CP0_SET_VIEW_RIPL(val) mips32r2_cp0_view_ripl_set((unsigned long)val)

#define _CP0_GET_EPC() mips32r2_cp0_epc_get()
#define _CP0_SET_EPC(val) mips32r2_cp0_epc_set((unsigned long)val)

#define _CP0_GET_EBASE() mips32r2_cp0_ebase_get()
#define _CP0_SET_EBASE(val)  mips32r2_cp0_ebase_set((unsigned long)val)

#define _CP0_GET_CONFIG() mips32r2_cp0_config_get()
#define _CP0_GET_CONFIG3() mips32r2_cp0_config3_get()

#define _CP0_GET_DEPC() mips32r2_cp0_depc_get()

#endif

#else  // Any other compiler

#error "FORCED BUILD ERROR: Unknown compiler"

#endif

/*
Need to define NULL
*/
#ifndef NULL
    #ifdef __CPLUSPLUS__
    #define NULL            0
    #else
    #define NULL            ((void *)0)
    #endif
#endif

#endif // #ifndef _PLATFORM_H
/**   @}
 */
