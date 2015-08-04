#ifndef _FSL_H
#define _FSL_H

#include "mb_interface.h"       /* Legacy reasons. We just have to include this guy who defines the FSL stuff */

#ifdef __cplusplus
extern "C" {
#endif

/* Extended FSL macros. These now replace all of the previous FSL macros */
#define FSL_DEFAULT                             
#define FSL_NONBLOCKING                          n
#define FSL_EXCEPTION                            e
#define FSL_CONTROL                              c
#define FSL_ATOMIC                               a

#define FSL_NONBLOCKING_EXCEPTION                ne
#define FSL_NONBLOCKING_CONTROL                  nc
#define FSL_NONBLOCKING_ATOMIC                   na
#define FSL_EXCEPTION_CONTROL                    ec
#define FSL_EXCEPTION_ATOMIC                     ea
#define FSL_CONTROL_ATOMIC                       ca

#define FSL_NONBLOCKING_EXCEPTION_CONTROL        nec
#define FSL_NONBLOCKING_EXCEPTION_ATOMIC         nea
#define FSL_NONBLOCKING_CONTROL_ATOMIC           nca
#define FSL_EXCEPTION_CONTROL_ATOMIC             eca

#define FSL_NONBLOCKING_EXCEPTION_CONTROL_ATOMIC neca

#define getfslx(val, id, flags)      asm volatile (stringify(flags) "get\t%0,rfsl" stringify(id) : "=d" (val))
#define putfslx(val, id, flags)      asm volatile (stringify(flags) "put\t%0,rfsl" stringify(id) :: "d" (val))

#define tgetfslx(val, id, flags)     asm volatile ("t" stringify(flags) "get\t%0,rfsl" stringify(id) : "=d" (val))
#define tputfslx(id, flags)          asm volatile ("t" stringify(flags) "put\trfsl" stringify(id))

#define getdfslx(val, var, flags)    asm volatile (stringify(flags) "getd\t%0,%1" : "=d" (val) : "d" (var))
#define putdfslx(val, var, flags)    asm volatile (stringify(flags) "putd\t%0,%1" :: "d" (val), "d" (var))

#define tgetdfslx(val, var, flags)   asm volatile ("t" stringify(flags) "getd\t%0,%1" : "=d" (val) : "d" (var))
#define tputdfslx(var, flags)        asm volatile ("t" stringify(flags) "putd\t%0" :: "d" (var))


#ifdef __cplusplus
}
#endif
#endif /* _FSL_H */

