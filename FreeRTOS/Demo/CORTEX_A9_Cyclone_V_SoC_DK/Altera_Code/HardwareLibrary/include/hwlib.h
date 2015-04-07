/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
* 
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
* 
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
* 
******************************************************************************/

#ifndef __HWLIB_H__
#define __HWLIB_H__

#ifdef __cplusplus
#include <cstddef>
#include <cstdbool>
#include <cstdint>
#else   /* __cplusplus */
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#endif  /* __cplusplus */

#include "alt_hwlibs_ver.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*!
 * The type definition for status codes returned by the HWLIB.
 */
typedef int32_t             ALT_STATUS_CODE;

/*! Definitions of status codes returned by the HWLIB. */

/*! The operation was successful. */
#define ALT_E_SUCCESS               0

/*! The operation failed. */
#define ALT_E_ERROR                 (-1)
/*! FPGA configuration error detected.*/
#define ALT_E_FPGA_CFG              (-2)
/*! FPGA CRC error detected. */
#define ALT_E_FPGA_CRC              (-3)
/*! An error occurred on the FPGA configuration bitstream input source. */
#define ALT_E_FPGA_CFG_STM          (-4)
/*! The FPGA is powered off. */
#define ALT_E_FPGA_PWR_OFF          (-5)
/*! The SoC does not currently control the FPGA. */
#define ALT_E_FPGA_NO_SOC_CTRL      (-6)
/*! The FPGA is not in USER mode. */
#define ALT_E_FPGA_NOT_USER_MODE    (-7)
/*! An argument violates a range constraint. */
#define ALT_E_ARG_RANGE             (-8)
/*! A bad argument value was passed. */
#define ALT_E_BAD_ARG               (-9)
/*! The operation is invalid or illegal. */
#define ALT_E_BAD_OPERATION         (-10)
/*! An invalid option was selected. */
#define ALT_E_INV_OPTION            (-11)
/*! An operation or response timeout period expired. */
#define ALT_E_TMO                   (-12)
/*! The argument value is reserved or unavailable. */
#define ALT_E_RESERVED              (-13)
/*! A clock is not enabled or violates an operational constraint. */
#define ALT_E_BAD_CLK               (-14)
/*! The version ID is invalid. */
#define ALT_E_BAD_VERSION           (-15)
/*! The buffer does not contain enough free space for the operation. */
#define ALT_E_BUF_OVF               (-20)

/*!
 * Indicates a FALSE condition.
 */
#define ALT_E_FALSE                 (0)
/*!
 * Indicates a TRUE condition.
 */
#define ALT_E_TRUE                  (1)

/* Note, additional positive status codes may be defined to return
 * a TRUE condition with additional information */


/* Some other useful definitions */

/*!
 * Specifies the current major and minor revision of the HWLibs. The
 * MS four decimal digits specify the Altera ACDS release number, the
 * LS two decimal digits specify minor revisions of the HWLibs, if any.
 *
 * A typical use is:
 * \code
 * #if  ALTERA_HWLIBS_VERSION_CODE >= ALT_HWLIBS_VERSION(13, 1, 0)
 * \endcode
 *     for a dependency on the major or minor ACDS revision
 *   or
 * \code
 * #if  ALTERA_HWLIBS_VERSION_CODE == ALT_HWLIBS_VERSION(13, 0, 12)
 * \endcode
 *     for a dependency on the hwlibs revision
 *
 */
#define ALT_HWLIBS_VERSION(a,b,c)   (((a)*10000)+((b)*100)+(c))

#define ALTERA_HWLIBS_VERSION_CODE   ALT_HWLIBS_VERSION(ALTERA_ACDS_MAJOR_REV, \
                                    ALTERA_ACDS_MINOR_REV, ALTERA_HWLIBS_REV)

/*!
 * Allow some parts of the documentation to be hidden by setting to zero
 */
#define ALTERA_INTERNAL_ONLY_DOCS   1


/*!
 * Provide base address of MPU address space
 */

#ifndef ALT_HPS_ADDR
#define ALT_HPS_ADDR            0
#endif

/*!
 * These constants are sometimes useful:
 */
#define ALT_MILLISECS_IN_A_SEC      1000
#define ALT_MICROSECS_IN_A_SEC      1000000
#define ALT_NANOSECS_IN_A_SEC       1000000000

#define ALT_TWO_TO_POW0             (1)
#define ALT_TWO_TO_POW1             (1<<1)
#define ALT_TWO_TO_POW2             (1<<2)
#define ALT_TWO_TO_POW3             (1<<3)
#define ALT_TWO_TO_POW4             (1<<4)
#define ALT_TWO_TO_POW5             (1<<5)
#define ALT_TWO_TO_POW6             (1<<6)
#define ALT_TWO_TO_POW7             (1<<7)
#define ALT_TWO_TO_POW8             (1<<8)
#define ALT_TWO_TO_POW9             (1<<9)
#define ALT_TWO_TO_POW10            (1<<10)
#define ALT_TWO_TO_POW11            (1<<11)
#define ALT_TWO_TO_POW12            (1<<12)
#define ALT_TWO_TO_POW13            (1<<13)
#define ALT_TWO_TO_POW14            (1<<14)
#define ALT_TWO_TO_POW15            (1<<15)
#define ALT_TWO_TO_POW16            (1<<16)
#define ALT_TWO_TO_POW17            (1<<17)
#define ALT_TWO_TO_POW18            (1<<18)
#define ALT_TWO_TO_POW19            (1<<19)
#define ALT_TWO_TO_POW20            (1<<20)
#define ALT_TWO_TO_POW21            (1<<21)
#define ALT_TWO_TO_POW22            (1<<22)
#define ALT_TWO_TO_POW23            (1<<23)
#define ALT_TWO_TO_POW24            (1<<24)
#define ALT_TWO_TO_POW25            (1<<25)
#define ALT_TWO_TO_POW26            (1<<26)
#define ALT_TWO_TO_POW27            (1<<27)
#define ALT_TWO_TO_POW28            (1<<28)
#define ALT_TWO_TO_POW29            (1<<29)
#define ALT_TWO_TO_POW30            (1<<30)
#define ALT_TWO_TO_POW31            (1<<31)

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __HWLIB_H__ */

