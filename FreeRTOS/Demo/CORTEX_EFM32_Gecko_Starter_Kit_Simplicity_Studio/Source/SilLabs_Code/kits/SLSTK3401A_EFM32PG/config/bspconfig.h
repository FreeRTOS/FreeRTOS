/***************************************************************************//**
 * @file
 * @brief Provide BSP (board support package) configuration parameters.
 * @version 4.2.1
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

#ifndef __SILICON_LABS_BSPCONFIG_H__
#define __SILICON_LABS_BSPCONFIG_H__

#define BSP_STK
#define BSP_STK_BRD2500

#define BSP_BCC_USART         USART0
#define BSP_BCC_CLK           cmuClock_USART0
#define BSP_BCC_TX_LOCATION   USART_ROUTELOC0_TXLOC_LOC0
#define BSP_BCC_RX_LOCATION   USART_ROUTELOC0_RXLOC_LOC0
#define BSP_BCC_TXPORT        gpioPortA
#define BSP_BCC_TXPIN         0
#define BSP_BCC_RXPORT        gpioPortA
#define BSP_BCC_RXPIN         1
#define BSP_BCC_ENABLE_PORT   gpioPortA
#define BSP_BCC_ENABLE_PIN    5                 /* VCOM_ENABLE */

#define BSP_DISP_ENABLE_PORT  gpioPortD
#define BSP_DISP_ENABLE_PIN   15                /* MemLCD display enable */

#define BSP_GPIO_LEDS
#define BSP_NO_OF_LEDS  2
#define BSP_GPIO_LEDARRAY_INIT {{gpioPortF,4},{gpioPortF,5}}

#define BSP_GPIO_BUTTONS
#define BSP_NO_OF_BUTTONS       2
#define BSP_GPIO_PB0_PORT       gpioPortF
#define BSP_GPIO_PB0_PIN        6
#define BSP_GPIO_PB1_PORT       gpioPortF
#define BSP_GPIO_PB1_PIN        7

#define BSP_GPIO_BUTTONARRAY_INIT {{BSP_GPIO_PB0_PORT, BSP_GPIO_PB0_PIN}, {BSP_GPIO_PB1_PORT, BSP_GPIO_PB1_PIN}}

#define BSP_INIT_DEFAULT  0

#if !defined( EMU_DCDCINIT_STK_DEFAULT )
/* Use emlib defaults */
#define EMU_DCDCINIT_STK_DEFAULT          EMU_DCDCINIT_DEFAULT
#endif

#if !defined(CMU_HFXOINIT_STK_DEFAULT)
#define CMU_HFXOINIT_STK_DEFAULT                                                \
{                                                                               \
  true,         /* Low-power mode for EFM32 */                                  \
  false,        /* Disable auto-start on EM0/1 entry */                         \
  false,        /* Disable auto-select on EM0/1 entry */                        \
  false,        /* Disable auto-start and select on RAC wakeup */               \
  _CMU_HFXOSTARTUPCTRL_CTUNE_DEFAULT,                                           \
  0x142,        /* Steady-state CTUNE for STK boards without load caps */       \
  _CMU_HFXOSTARTUPCTRL_REGISHWARM_DEFAULT,                                      \
  _CMU_HFXOSTEADYSTATECTRL_REGISH_DEFAULT,                                      \
  _CMU_HFXOSTARTUPCTRL_IBTRIMXOCORE_DEFAULT,                                    \
  0x7,          /* Recommended steady-state osc core bias current */            \
  0x6,          /* Recommended peak detection threshold */                      \
  _CMU_HFXOTIMEOUTCTRL_SHUNTOPTTIMEOUT_DEFAULT,                                 \
  0xA,          /* Recommended peak detection timeout  */                       \
  _CMU_HFXOTIMEOUTCTRL_WARMSTEADYTIMEOUT_DEFAULT,                               \
  _CMU_HFXOTIMEOUTCTRL_STEADYTIMEOUT_DEFAULT,                                   \
  _CMU_HFXOTIMEOUTCTRL_STARTUPTIMEOUT_DEFAULT,                                  \
}
#endif

#define BSP_BCP_VERSION 2
#include "bsp_bcp.h"

#endif /* __SILICON_LABS_BSPCONFIG_H__ */
