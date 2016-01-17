/***************************************************************************//**
 * @file
 * @brief Provide BSP (board support package) configuration parameters.
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

#ifndef __BSPCONFIG_H
#define __BSPCONFIG_H

#define BSP_STK
#define BSP_STK_2200

#define BSP_BCC_USART       UART0
#define BSP_BCC_CLK         cmuClock_UART0
#define BSP_BCC_LOCATION    UART_ROUTE_LOCATION_LOC1
#define BSP_BCC_TXPORT      gpioPortE
#define BSP_BCC_TXPIN       0
#define BSP_BCC_RXPORT      gpioPortE
#define BSP_BCC_RXPIN       1
#define BSP_BCC_ENABLE_PORT gpioPortF
#define BSP_BCC_ENABLE_PIN  7

#define BSP_GPIO_LEDS
#define BSP_NO_OF_LEDS  2
#define BSP_GPIO_LEDARRAY_INIT {{gpioPortE,2},{gpioPortE,3}}

#define BSP_STK_USE_EBI

#define BSP_INIT_DEFAULT  0

#define BSP_BCP_VERSION 2
#include "bsp_bcp.h"

#endif
