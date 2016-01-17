/***************************************************************************//**
 * @file em_version.h
 * @brief Assign correct part number for include file
 * @version 4.0.0
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Silicon Labs has no
 * obligation to support this Software. Silicon Labs is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Silicon Labs will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 ******************************************************************************/


#ifndef __SILICON_LABS_EM_VERSION_H_
#define __SILICON_LABS_EM_VERSION_H_

#include "em_device.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup Version
 * @{
 ******************************************************************************/

/** Version number of emlib peripheral API. */
#define _EMLIB_VERSION 4.0.0

/** Major version of emlib. Bumped when incompatible API changes introduced. */
#define _EMLIB_VERSION_MAJOR 4

/** Minor version of emlib. Bumped when functionality is added in a backwards-
    compatible manner. */
#define _EMLIB_VERSION_MINOR 0

/** Patch revision of emlib. Bumped when adding backwards-compatible bug
    fixes.*/
#define _EMLIB_VERSION_PATCH 0


/** Version number of targeted CMSIS package. */
#define _CMSIS_VERSION 4.2.0

/** Major version of CMSIS. */
#define _CMSIS_VERSION_MAJOR 4

/** Minor version of CMSIS. */
#define _CMSIS_VERSION_MINOR 2

/** Patch revision of CMSIS. */
#define _CMSIS_VERSION_PATCH 0

/** @} (end addtogroup Version) */
/** @} (end addtogroup EM_Library) */

#ifdef __cplusplus
}
#endif

#endif /* __SILICON_LABS_EM_VERSION_H_ */
