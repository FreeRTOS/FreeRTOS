#ifndef PLATFORM_PATCH_H
#define PLATFORM_PATCH_H

#include "../smc_gen/r_bsp/platform.h"

/* In case of stand alone Smart Configurator and CS+, generating source code places
 * the /src/smc_gen/r_bsp folder prior to the /src/smc_workaround/r_bsp_patch folder
 * in the include folder list so that including patch files here is not recommended
 * when CC-RX is used.
 */
#if defined(__GNUC__) || defined(__ICCRX__)

#include "FIT_patch2.h"

#endif /* defined(__GNUC__) || defined(__ICCRX__) */

#endif /* PLATFORM_PATCH_H */
