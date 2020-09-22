#ifndef SMC_WORKAROUND_H
#define SMC_WORKAROUND_H

#include "CC_patch.h"
#include "IDE_patch.h"
#include "CG_patch.h"
#include "FIT_patch.h"

#if defined(__GNUC__)

/* Just for convenience.
 */
#define brk()               R_BSP_BRK()
#define int_exception(x)    R_BSP_INT(x)
#define wait()              R_BSP_WAIT()
#define nop()               R_BSP_NOP()

#endif /* defined(__GNUC__) */

#if defined(__GNUC__) || defined(__ICCRX__)

/* Just for convenience.
 */
#define setpsw_i()  R_BSP_SETPSW_I()
#define clrpsw_i()  R_BSP_CLRPSW_I()

#endif /* defined(__GNUC__) || defined(__ICCRX__) */

/* Just for convenience. For example, memcmp(), memcpy(), memset(), and so on.
 */
#include <string.h>

#endif /* SMC_WORKAROUND_H */
