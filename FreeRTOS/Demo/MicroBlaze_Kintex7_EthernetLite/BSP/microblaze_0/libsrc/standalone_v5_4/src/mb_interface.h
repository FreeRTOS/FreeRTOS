/******************************************************************************
*
* Copyright (C) 2004 - 2015 Xilinx, Inc. All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

#ifndef _MICROBLAZE_INTERFACE_H_
#define _MICROBLAZE_INTERFACE_H_

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_exception.h"

#ifdef __cplusplus
extern "C" {
#endif
extern void microblaze_enable_interrupts(void);                 /* Enable Interrupts */
extern void microblaze_disable_interrupts(void);                /* Disable Interrupts */
extern void microblaze_enable_icache(void);                     /* Enable Instruction Cache */
extern void microblaze_disable_icache(void);                    /* Disable Instruction Cache */
extern void microblaze_enable_dcache(void);                     /* Enable Instruction Cache */
extern void microblaze_disable_dcache(void);                    /* Disable Instruction Cache */
extern void microblaze_enable_exceptions(void);                 /* Enable hardware exceptions */
extern void microblaze_disable_exceptions(void);                /* Disable hardware exceptions */
extern void microblaze_register_handler(XInterruptHandler Handler, void *DataPtr); /* Register top level interrupt handler */
extern void microblaze_register_exception_handler(u32 ExceptionId, Xil_ExceptionHandler Handler, void *DataPtr); /* Register exception handler */

extern void microblaze_invalidate_icache(void);         /* Invalidate the entire icache */
extern void microblaze_invalidate_dcache(void);         /* Invalidate the entire dcache */
extern void microblaze_flush_dcache(void);              /* Flush the whole dcache */
extern void microblaze_invalidate_icache_range(u32 cacheaddr, u32 len);   /* Invalidate a part of the icache */
extern void microblaze_invalidate_dcache_range(u32 cacheaddr, u32 len);   /* Invalidate a part of the dcache */
extern void microblaze_flush_dcache_range(u32 cacheaddr, u32 len);        /* Flush a part of the dcache */
extern void microblaze_scrub(void);                     /* Scrub LMB and internal BRAM */
extern void microblaze_invalidate_cache_ext(void);         /* Invalidate cache ext */
extern void microblaze_flush_cache_ext(void);         /* Flush cache ext */
extern void microblaze_flush_cache_ext_range(u32 cacheaddr,
			u32 len); /* Flush cache ext range */
extern void microblaze_invalidate_cache_ext_range(u32 cacheaddr,
			u32 len); /* Invalidate cache ext range */

/* Deprecated */
extern void microblaze_update_icache (s32 , s32 , s32 ) __attribute__((deprecated));
extern void microblaze_init_icache_range (s32 , s32 )  __attribute__((deprecated));
extern void microblaze_update_dcache (s32 , s32 , s32 )  __attribute__((deprecated));
extern void microblaze_init_dcache_range (s32 , s32 )  __attribute__((deprecated));

/* necessary for pre-processor */
#define stringify(s)    tostring(s)
#define tostring(s)     #s

/* FSL Access Macros */

/* Blocking Data Read and Write to FSL no. id */
#define getfsl(val, id)         asm volatile ("get\t%0,rfsl" stringify(id) : "=d" (val))
#define putfsl(val, id)         asm volatile ("put\t%0,rfsl" stringify(id) :: "d" (val))

/* Non-blocking Data Read and Write to FSL no. id */
#define ngetfsl(val, id)        asm volatile ("nget\t%0,rfsl" stringify(id) : "=d" (val))
#define nputfsl(val, id)        asm volatile ("nput\t%0,rfsl" stringify(id) :: "d" (val))

/* Blocking Control Read and Write to FSL no. id */
#define cgetfsl(val, id)        asm volatile ("cget\t%0,rfsl" stringify(id) : "=d" (val))
#define cputfsl(val, id)        asm volatile ("cput\t%0,rfsl" stringify(id) :: "d" (val))

/* Non-blocking Control Read and Write to FSL no. id */
#define ncgetfsl(val, id)       asm volatile ("ncget\t%0,rfsl" stringify(id) : "=d" (val))
#define ncputfsl(val, id)       asm volatile ("ncput\t%0,rfsl" stringify(id) :: "d" (val))

/* Polling versions of FSL access macros. This makes the FSL access interruptible */
#define getfsl_interruptible(val, id)       asm volatile ("\n1:\n\tnget\t%0,rfsl" stringify(id) "\n\t"   \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                           : "=d" (val) :: "r18")

#define putfsl_interruptible(val, id)       asm volatile ("\n1:\n\tnput\t%0,rfsl" stringify(id) "\n\t"   \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                          :: "d" (val) : "r18")

#define cgetfsl_interruptible(val, id)      asm volatile ("\n1:\n\tncget\t%0,rfsl" stringify(id) "\n\t"  \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                          : "=d" (val) :: "r18")

#define cputfsl_interruptible(val, id)      asm volatile ("\n1:\n\tncput\t%0,rfsl" stringify(id) "\n\t"  \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                          :: "d" (val) : "r18")
/* FSL valid and error check macros. */
#define fsl_isinvalid(result)               asm volatile ("addic\t%0,r0,0"  : "=d" (result))
#define fsl_iserror(error)                  asm volatile ("mfs\t%0,rmsr\n\t"  \
                                                              "andi\t%0,%0,0x10" : "=d" (error))

/* Pseudo assembler instructions */
#define clz(v)          ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "clz\t%0,%1\n" : "=d"(_rval): "d" (v) \
                            );                          \
                            _rval;                      \
                        })

#define mbar(mask)      ({  __asm__ __volatile__ ("mbar\t" stringify(mask) ); })
#define mb_sleep()     	({  __asm__ __volatile__ ("sleep\t"); })

#define mb_swapb(v)		({	u32 _rval;         \
							__asm__ __volatile__ (      \
								"swapb\t%0,%1\n" : "=d"(_rval) : "d" (v) \
							 );                          \
							 _rval;                      \
						})

#define mb_swaph(v)		({	u32 _rval;         \
							__asm__ __volatile__ (      \
								"swaph\t%0,%1\n" : "=d"(_rval) : "d" (v) \
							 );                          \
							 _rval;                      \
						})

#define mfgpr(rn)       ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "or\t%0,r0," stringify(rn) "\n" : "=d"(_rval) \
                            );                          \
                            _rval;                      \
                        })

#define mfmsr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "mfs\t%0,rmsr\n" : "=d"(_rval) \
                            );                          \
                            _rval;                      \
                        })

#define mfear()         ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "mfs\t%0,rear\n" : "=d"(_rval) \
                            );                          \
                            _rval;                      \
                        })

#define mfeare()        ({  u32 _rval; \
                            __asm__ __volatile__ ( \
                                "mfse\t%0,rear\n" : "=d"(_rval) \
                            ); \
                            _rval; \
                          })

#define mfesr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "mfs\t%0,resr\n" : "=d"(_rval) \
                            );                          \
                            _rval;                      \
                        })

#define mffsr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "mfs\t%0,rfsr\n" : "=d"(_rval) \
                            );                          \
                            _rval;                      \
                        })

#define mfpvr(rn)       ({  u32 _rval;         \
                            __asm__ __volatile__ (                          \
                                "mfs\t%0,rpvr" stringify(rn) "\n" : "=d"(_rval) \
                            );                                              \
                            _rval;                                          \
                        })

#define mfpvre(rn)      ({  u32 _rval; \
                            __asm__ __volatile__ ( \
                                "mfse\t%0,rpvr" stringify(rn) "\n" : "=d"(_rval) \
                            ); \
                            _rval; \
                          })

#define mfbtr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "mfs\t%0,rbtr\n" : "=d"(_rval)  \
                            );                                  \
                            _rval;                              \
                        })

#define mfedr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (      \
                                "mfs\t%0,redr\n" : "=d"(_rval)  \
                            );                                  \
                            _rval;                              \
                        })

#define mfpid()         ({  u32 _rval;         \
                            __asm__ __volatile__ (            \
                                "mfs\t%0,rpid\n" : "=d"(_rval)\
                            );                                \
                            _rval;                            \
                        })

#define mfzpr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (                  \
                                "mfs\t%0,rzpr\n" : "=d"(_rval)      \
                            );                                      \
                            _rval;                                  \
                        })

#define mftlbx()        ({  u32 _rval;         \
                            __asm__ __volatile__ (                  \
                                "mfs\t%0,rtlbx\n" : "=d"(_rval)     \
                            );                                      \
                            _rval;                                  \
                        })

#define mftlblo()       ({  u32 _rval;                     \
                            __asm__ __volatile__ (                  \
                                "mfs\t%0,rtlblo\n" : "=d"(_rval)    \
                            );                                      \
                            _rval;                                  \
                        })

#define mftlbhi()       ({  u32 _rval;         \
                            __asm__ __volatile__ (                  \
                                "mfs\t%0,rtlbhi\n" : "=d"(_rval)    \
                            );                                      \
                            _rval;                                  \
                        })

#define mfslr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (                  \
                                "mfs\t%0,rslr\n" : "=d"(_rval)    \
                            );                                      \
                            _rval;                                  \
                        })

#define mfshr()         ({  u32 _rval;         \
                            __asm__ __volatile__ (                  \
                                "mfs\t%0,rshr\n" : "=d"(_rval)    \
                            );                                      \
                            _rval;                                  \
                        })

#define mtgpr(rn, v)    ({  __asm__ __volatile__ (                      \
                                "or\t" stringify(rn) ",r0,%0\n" :: "d" (v) \
                            );                          \
                        })

#define mtmsr(v)        ({  __asm__ __volatile__ (      \
                                "mts\trmsr,%0\n\tnop\n" :: "d" (v)      \
                            );                          \
                        })


#define mtfsr(v)        ({  __asm__ __volatile__ (      \
                                "mts\trfsr,%0\n\tnop\n" :: "d" (v)  \
                            );                                      \
                        })

#define mtpid(v)        ({  __asm__ __volatile__ (      \
                                "mts\trpid,%0\n\tnop\n" :: "d" (v)      \
                            );                                      \
                        })

#define mtzpr(v)        ({  __asm__ __volatile__ (                  \
                                "mts\trzpr,%0\n\tnop\n" :: "d" (v)      \
                            );                                      \
                        })

#define mttlbx(v)       ({  __asm__ __volatile__ (      \
                                "mts\trtlbx,%0\n\tnop\n" :: "d" (v)     \
                            );                                      \
                        })

#define mttlblo(v)      ({  __asm__ __volatile__ (      \
                                "mts\trtlblo,%0\n\tnop\n" :: "d" (v)    \
                            );                                      \
                        })

#define mttlbhi(v)      ({  __asm__ __volatile__ (      \
                                "mts\trtlbhi,%0\n\tnop\n" :: "d" (v)    \
                            );                                      \
                        })

#define mttlbsx(v)      ({  __asm__ __volatile__ (      \
                                "mts\trtlbsx,%0\n\tnop\n" :: "d" (v)    \
                            );                                      \
                        })

#define mtslr(v)        ({  __asm__ __volatile__ (      \
                                "mts\trslr,%0\n\tnop\n" :: "d" (v)  \
                            );                                      \
                        })

#define mtshr(v)        ({  __asm__ __volatile__ (      \
                                "mts\trshr,%0\n\tnop\n" :: "d" (v)  \
                            );                                      \
                        })

#define lwx(address)	({  u32 _rval; \
                              __asm__ __volatile__ ( \
                             "lwx\t%0,%1,r0\n" : "=d"(_rval) : "d" (address) \
                              ); \
                              _rval; \
                          })

#define lwr(address)	({  u32 _rval; \
                              __asm__ __volatile__ ( \
                             "lwr\t%0,%1,r0\n" : "=d"(_rval) : "d" (address) \
                              ); \
                              _rval; \
                          })


#define lwea(lladdr)	({  u32 _rval; \
                              __asm__ __volatile__ ( \
                             "lwea\t%0,%M1,%L1\n" : "=d"(_rval) : "d" (lladdr) \
                              ); \
                              _rval; \
                          })

#define lhur(address)	({  u32 _rval; \
                              __asm__ __volatile__ ( \
                             "lhur\t%0,%1,r0\n" : "=d"(_rval) : "d" (address) \
                              ); \
                              _rval; \
                          })

#define lhuea(lladdr)	({  u32 _rval; \
                              __asm__ __volatile__ ( \
                             "lhuea\t%0,%M1,%L1\n" : "=d"(_rval) : "d" (lladdr) \
                              ); \
                              _rval; \
                          })

#define lbur(address)	({  u32 _rval; \
                              __asm__ __volatile__ ( \
                             "lbur\t%0,%1,r0\n" : "=d"(_rval) : "d" (address) \
                              ); \
                              _rval; \
                          })

#define lbuea(lladdr)	({  u32 _rval; \
                              __asm__ __volatile__ ( \
                             "lbuea\t%0,%M1,%L1\n" : "=d"(_rval) : "d" (lladdr) \
                              ); \
                              _rval; \
                          })

#define swx(address, data) ({  __asm__ __volatile__ ( \
                                "swx\t%0,%1,r0\n" :: "d" (data), "d" (address) \
                               ); \
                           })

#define swr(address, data) ({  __asm__ __volatile__ ( \
                                "swr\t%0,%1,r0\n" :: "d" (data), "d" (address) \
                               ); \
                           })

#define swea(lladdr, data) ({  __asm__ __volatile__ ( \
                                "swea\t%0,%M1,%L1\n" :: "d" (data), "d" (lladdr) \
                               ); \
                           })

#define shr(address, data) ({  __asm__ __volatile__ ( \
                                "shr\t%0,%1,r0\n" :: "d" (data), "d" (address) \
                               ); \
                           })

#define shea(lladdr, data) ({  __asm__ __volatile__ ( \
                                "shea\t%0,%M1,%L1\n" :: "d" (data), "d" (lladdr) \
                               ); \
                           })

#define sbr(address, data) ({  __asm__ __volatile__ ( \
                                "sbr\t%0,%1,r0\n" :: "d" (data), "d" (address) \
                               ); \
                           })

#define sbea(lladdr, data) ({  __asm__ __volatile__ ( \
                                "sbea\t%0,%M1,%L1\n" :: "d" (data), "d" (lladdr) \
                               ); \
                           })

#define microblaze_getfpex_operand_a()     ({          \
                                    extern u32 mb_fpex_op_a;   \
                                    mb_fpex_op_a;                       \
                                })

#define microblaze_getfpex_operand_b()     ({          \
                                    extern u32 mb_fpex_op_b;   \
                                    mb_fpex_op_b;                       \
                                })

/* Deprecated MicroBlaze FSL macros */
#define microblaze_bread_datafsl(val, id)       getfsl(val,id)
#define microblaze_bwrite_datafsl(val, id)      putfsl(val,id)
#define microblaze_nbread_datafsl(val, id)      ngetfsl(val,id)
#define microblaze_nbwrite_datafsl(val, id)     nputfsl(val,id)
#define microblaze_bread_cntlfsl(val, id)       cgetfsl(val,id)
#define microblaze_bwrite_cntlfsl(val, id)      cputfsl(val,id)
#define microblaze_nbread_cntlfsl(val, id)      ncgetfsl(val,id)
#define microblaze_nbwrite_cntlfsl(val, id)     ncputfsl(val,id)

#ifdef __cplusplus
}
#endif
#endif // _MICROBLAZE_INTERFACE_H_
