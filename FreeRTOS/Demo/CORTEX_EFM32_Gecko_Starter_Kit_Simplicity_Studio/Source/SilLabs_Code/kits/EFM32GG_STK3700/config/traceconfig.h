/***************************************************************************//**
 * @file
 * @brief Provide SWO/ETM TRACE configuration parameters.
 * @version 4.0.0
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/

#ifndef __TRACECONFIG_H
#define __TRACECONFIG_H

#define BSP_TRACE_SWO_LOCATION GPIO_ROUTE_SWLOCATION_LOC0

/* Enable output on pin - GPIO Port F, Pin 2. */
#define TRACE_ENABLE_PINS()                        \
  GPIO->P[5].MODEL &= ~(_GPIO_P_MODEL_MODE2_MASK); \
  GPIO->P[5].MODEL |= GPIO_P_MODEL_MODE2_PUSHPULL

#endif
