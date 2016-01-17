/**************************************************************************//**
 * @file
 * @brief SWO Trace API (for eAProfiler)
 * @version 4.0.0
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/

#ifndef __BSP_TRACE_H
#define __BSP_TRACE_H

#include "em_device.h"
#if (defined( BSP_ETM_TRACE ) && defined( ETM_PRESENT )) || \
     defined( GPIO_ROUTE_SWOPEN ) || \
     defined( GPIO_ROUTEPEN_SWVPEN )

#include <stdint.h>
#include <stdbool.h>
#include "em_msc.h"
#include "traceconfig.h"

/***************************************************************************//**
 * @addtogroup BSP
 * @{
 ******************************************************************************/
/***************************************************************************//**
 * @addtogroup BSPCOMMON API common for all kits
 * @{
 ******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

#if defined(BSP_ETM_TRACE) && defined( ETM_PRESENT )
void BSP_TraceEtmSetup(void);
#endif

#if defined( GPIO_ROUTE_SWOPEN ) || defined( _GPIO_ROUTEPEN_SWVPEN_MASK )
bool BSP_TraceProfilerSetup(void);
void BSP_TraceSwoSetup(void);
#endif

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */
#define USER_PAGE    0x0FE00000UL /* Address to flash memory */
/** @endcond */

/**************************************************************************//**
 * @brief Set or clear word in user page which enables or disables SWO
 *        in BSP_TraceProfilerSetup. If BSP_TraceProfilerEnable(false) has been run,
 *        no example project will enable SWO trace.
 * @param[in] enable
 * @note Add "em_msc.c" to build to use this function.
 *****************************************************************************/
__STATIC_INLINE void BSP_TraceProfilerEnable(bool enable)
{
  uint32_t          data;
  volatile uint32_t *userpage = (uint32_t *) USER_PAGE;

  /* Check that configuration needs to change */
  data = *userpage;
  if (enable)
  {
    if (data == 0xFFFFFFFF)
    {
      return;
    }
  }
  else
  {
    if (data == 0x00000000)
    {
      return;
    }
  }

  /* Initialize MSC */
  MSC_Init();

  /* Write enable or disable trigger word into flash */
  if (enable)
  {
    data = 0xFFFFFFFF;
    MSC_ErasePage((uint32_t *) USER_PAGE);
    MSC_WriteWord((uint32_t *) USER_PAGE, (void *) &data, 4);
  }
  else
  {
    data = 0x00000000;
    MSC_ErasePage((uint32_t *) USER_PAGE);
    MSC_WriteWord((uint32_t *) USER_PAGE, (void *) &data, 4);
  }
}

#ifdef __cplusplus
}
#endif

/** @} (end group BSP) */
/** @} (end group BSP) */

#endif  /* (defined(BSP_ETM_TRACE) && defined( ETM_PRESENT )) || defined( GPIO_ROUTE_SWOPEN ) */
#endif  /* __BSP_TRACE_H */
