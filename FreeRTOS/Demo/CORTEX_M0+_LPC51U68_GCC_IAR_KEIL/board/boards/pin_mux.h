/*
 * Copyright 2018 NXP.
 * All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef _PIN_MUX_H_
#define _PIN_MUX_H_


/*******************************************************************************
 * Definitions
 ******************************************************************************/  

/*! @brief Direction type  */
typedef enum _pin_mux_direction
{
  kPIN_MUX_DirectionInput = 0U,         /* Input direction */
  kPIN_MUX_DirectionOutput = 1U,        /* Output direction */
  kPIN_MUX_DirectionInputOrOutput = 2U  /* Input or output direction */
} pin_mux_direction_t;

/*!
 * @addtogroup pin_mux
 * @{
 */

/*******************************************************************************
 * API
 ******************************************************************************/

#if defined(__cplusplus)
extern "C" {
#endif

/*!
 * @brief Calls initialization functions.
 *
 */
void BOARD_InitBootPins(void);

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitPins(void); /* Function assigned for the Cortex-M0P */

/* FC1_RTS_SCL_SSEL1 (number 1), J4[9]/JS3[1]/JS4[3]/U10[7]/U12[D6]/BRIDGE_SCL */
#define BOARD_LINK2MCU_SCL_PERIPHERAL                                  FLEXCOMM1   /*!< Device name: FLEXCOMM1 */
#define BOARD_LINK2MCU_SCL_SIGNAL                                  RTS_SCL_SSEL1   /*!< FLEXCOMM1 signal: RTS_SCL_SSEL1 */
#define BOARD_LINK2MCU_SCL_PIN_NAME                            FC1_RTS_SCL_SSEL1   /*!< Pin name */
#define BOARD_LINK2MCU_SCL_LABEL "J4[9]/JS3[1]/JS4[3]/U10[7]/U12[D6]/BRIDGE_SCL"   /*!< Label */
#define BOARD_LINK2MCU_SCL_NAME                                   "LINK2MCU_SCL"   /*!< Identifier name */

/* FC1_CTS_SDA_SSEL0 (number 2), J4[10]/JS2[1]/JS5[3]/U10[5]/U12[E6]/SW1/BRIDGE_SDA-WAKEUP */
#define BOARD_LINK2MCU_SDA_PERIPHERAL                                  FLEXCOMM1   /*!< Device name: FLEXCOMM1 */
#define BOARD_LINK2MCU_SDA_SIGNAL                                  CTS_SDA_SSEL0   /*!< FLEXCOMM1 signal: CTS_SDA_SSEL0 */
#define BOARD_LINK2MCU_SDA_PIN_NAME                            FC1_CTS_SDA_SSEL0   /*!< Pin name */
#define BOARD_LINK2MCU_SDA_LABEL "J4[10]/JS2[1]/JS5[3]/U10[5]/U12[E6]/SW1/BRIDGE_SDA-WAKEUP" /*!< Label */
#define BOARD_LINK2MCU_SDA_NAME                                   "LINK2MCU_SDA"   /*!< Identifier name */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitLink2MCUPins(void); /* Function assigned for the Cortex-M0P */

/* PIO0_24 (number 2), J4[10]/JS2[1]/JS5[3]/U10[5]/U12[E6]/SW1/BRIDGE_SDA-WAKEUP */
#define BOARD_SW1_GPIO                                                      GPIO   /*!< GPIO device name: GPIO */
#define BOARD_SW1_PORT                                                        0U   /*!< PORT device index: 0 */
#define BOARD_SW1_GPIO_PIN                                                   24U   /*!< PIO0 pin index: 24 */
#define BOARD_SW1_PIN_NAME                                               PIO0_24   /*!< Pin name */
#define BOARD_SW1_LABEL "J4[10]/JS2[1]/JS5[3]/U10[5]/U12[E6]/SW1/BRIDGE_SDA-WAKEUP" /*!< Label */
#define BOARD_SW1_NAME                                                     "SW1"   /*!< Identifier name */
#define BOARD_SW1_DIRECTION                              kPIN_MUX_DirectionInput   /*!< Direction */

/* PIO0_31 (number 13), J2[17]/J3[2]/P1[7]/U3[4]/SW2/P0_31-PDM0_CLK-ISP0_EN */
#define BOARD_SW2_GPIO                                                      GPIO   /*!< GPIO device name: GPIO */
#define BOARD_SW2_PORT                                                        0U   /*!< PORT device index: 0 */
#define BOARD_SW2_GPIO_PIN                                                   31U   /*!< PIO0 pin index: 31 */
#define BOARD_SW2_PIN_NAME                                               PIO0_31   /*!< Pin name */
#define BOARD_SW2_LABEL    "J2[17]/J3[2]/P1[7]/U3[4]/SW2/P0_31-PDM0_CLK-ISP0_EN"   /*!< Label */
#define BOARD_SW2_NAME                                                     "SW2"   /*!< Identifier name */
#define BOARD_SW2_DIRECTION                              kPIN_MUX_DirectionInput   /*!< Direction */

/* PIO0_4 (number 38), J4[7]/U9[12]/SW3/BRIDGE_T_INTR-ISP1 */
#define BOARD_SW3_GPIO                                                      GPIO   /*!< GPIO device name: GPIO */
#define BOARD_SW3_PORT                                                        0U   /*!< PORT device index: 0 */
#define BOARD_SW3_GPIO_PIN                                                    4U   /*!< PIO0 pin index: 4 */
#define BOARD_SW3_PIN_NAME                                                PIO0_4   /*!< Pin name */
#define BOARD_SW3_LABEL                    "J4[7]/U9[12]/SW3/BRIDGE_T_INTR-ISP1"   /*!< Label */
#define BOARD_SW3_NAME                                                     "SW3"   /*!< Identifier name */
#define BOARD_SW3_DIRECTION                              kPIN_MUX_DirectionInput   /*!< Direction */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitBUTTONsPins(void); /* Function assigned for the Cortex-M0P */

/* PIO1_9 (number 29), J9[5]/D2[3]/P1_9-BLUE_LED */
#define BOARD_LED_BLUE_GPIO                                                 GPIO   /*!< GPIO device name: GPIO */
#define BOARD_LED_BLUE_PORT                                                   1U   /*!< PORT device index: 1 */
#define BOARD_LED_BLUE_GPIO_PIN                                               9U   /*!< PIO1 pin index: 9 */
#define BOARD_LED_BLUE_PIN_NAME                                           PIO1_9   /*!< Pin name */
#define BOARD_LED_BLUE_LABEL                         "J9[5]/D2[3]/P1_9-BLUE_LED"   /*!< Label */
#define BOARD_LED_BLUE_NAME                                           "LED_BLUE"   /*!< Identifier name */
#define BOARD_LED_BLUE_DIRECTION                        kPIN_MUX_DirectionOutput   /*!< Direction */

/* PIO1_10 (number 30), J9[8]/D2[4]/P1_10-SCT4-LED_GREEN */
#define BOARD_LED_GREEN_GPIO                                                GPIO   /*!< GPIO device name: GPIO */
#define BOARD_LED_GREEN_PORT                                                  1U   /*!< PORT device index: 1 */
#define BOARD_LED_GREEN_GPIO_PIN                                             10U   /*!< PIO1 pin index: 10 */
#define BOARD_LED_GREEN_PIN_NAME                                         PIO1_10   /*!< Pin name */
#define BOARD_LED_GREEN_LABEL                 "J9[8]/D2[4]/P1_10-SCT4-LED_GREEN"   /*!< Label */
#define BOARD_LED_GREEN_NAME                                         "LED_GREEN"   /*!< Identifier name */
#define BOARD_LED_GREEN_DIRECTION                       kPIN_MUX_DirectionOutput   /*!< Direction */

/* PIO0_29 (number 11), J2[5]/D2[1]/P0_29-CT32B0_MAT3-RED */
#define BOARD_LED_RED_GPIO                                                  GPIO   /*!< GPIO device name: GPIO */
#define BOARD_LED_RED_PORT                                                    0U   /*!< PORT device index: 0 */
#define BOARD_LED_RED_GPIO_PIN                                               29U   /*!< PIO0 pin index: 29 */
#define BOARD_LED_RED_PIN_NAME                                           PIO0_29   /*!< Pin name */
#define BOARD_LED_RED_LABEL                  "J2[5]/D2[1]/P0_29-CT32B0_MAT3-RED"   /*!< Label */
#define BOARD_LED_RED_NAME                                             "LED_RED"   /*!< Identifier name */
#define BOARD_LED_RED_DIRECTION                         kPIN_MUX_DirectionOutput   /*!< Direction */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitLEDsPins(void); /* Function assigned for the Cortex-M0P */

/* FC4_RTS_SCL_SSEL1 (number 3), J1[1]/JS4[1]/U10[7]/P0_25-FC4_SCLX */
#define BOARD_FC4_SCLX_PERIPHERAL                                      FLEXCOMM4   /*!< Device name: FLEXCOMM4 */
#define BOARD_FC4_SCLX_SIGNAL                                      RTS_SCL_SSEL1   /*!< FLEXCOMM4 signal: RTS_SCL_SSEL1 */
#define BOARD_FC4_SCLX_PIN_NAME                                FC4_RTS_SCL_SSEL1   /*!< Pin name */
#define BOARD_FC4_SCLX_LABEL                "J1[1]/JS4[1]/U10[7]/P0_25-FC4_SCLX"   /*!< Label */
#define BOARD_FC4_SCLX_NAME                                           "FC4_SCLX"   /*!< Identifier name */

/* FC4_CTS_SDA_SSEL0 (number 4), J1[3]/JS5[1]/U10[5]/P0_26-FC4_SDAX */
#define BOARD_FC4_SDAX_PERIPHERAL                                      FLEXCOMM4   /*!< Device name: FLEXCOMM4 */
#define BOARD_FC4_SDAX_SIGNAL                                      CTS_SDA_SSEL0   /*!< FLEXCOMM4 signal: CTS_SDA_SSEL0 */
#define BOARD_FC4_SDAX_PIN_NAME                                FC4_CTS_SDA_SSEL0   /*!< Pin name */
#define BOARD_FC4_SDAX_LABEL                "J1[3]/JS5[1]/U10[5]/P0_26-FC4_SDAX"   /*!< Label */
#define BOARD_FC4_SDAX_NAME                                           "FC4_SDAX"   /*!< Identifier name */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitSecureMCUPins(void); /* Function assigned for the Cortex-M0P */

/* FC5_TXD_SCL_MISO (number 58), J1[11]/U5[2]/P0_18-FC5_TXD_SCL_MISO */
#define BOARD_SPI_FLASH_MISO_PERIPHERAL                                FLEXCOMM5   /*!< Device name: FLEXCOMM5 */
#define BOARD_SPI_FLASH_MISO_SIGNAL                                 TXD_SCL_MISO   /*!< FLEXCOMM5 signal: TXD_SCL_MISO */
#define BOARD_SPI_FLASH_MISO_PIN_NAME                           FC5_TXD_SCL_MISO   /*!< Pin name */
#define BOARD_SPI_FLASH_MISO_LABEL         "J1[11]/U5[2]/P0_18-FC5_TXD_SCL_MISO"   /*!< Label */
#define BOARD_SPI_FLASH_MISO_NAME                               "SPI_FLASH_MISO"   /*!< Identifier name */

/* FC5_SCK (number 59), J1[9]/J2[8]/U5[6]/P0_19-FC5_SCK-SPIFI_CSn */
#define BOARD_SPI_FLASH_SCK_PERIPHERAL                                 FLEXCOMM5   /*!< Device name: FLEXCOMM5 */
#define BOARD_SPI_FLASH_SCK_SIGNAL                                           SCK   /*!< FLEXCOMM5 signal: SCK */
#define BOARD_SPI_FLASH_SCK_PIN_NAME                                     FC5_SCK   /*!< Pin name */
#define BOARD_SPI_FLASH_SCK_LABEL    "J1[9]/J2[8]/U5[6]/P0_19-FC5_SCK-SPIFI_CSn"   /*!< Label */
#define BOARD_SPI_FLASH_SCK_NAME                                 "SPI_FLASH_SCK"   /*!< Identifier name */

/* FC5_RXD_SDA_MOSI (number 60), J1[13]/U5[5]/P0_20-FC5_RXD_SDA_MOSI */
#define BOARD_SPI_FLASH_MOSI_PERIPHERAL                                FLEXCOMM5   /*!< Device name: FLEXCOMM5 */
#define BOARD_SPI_FLASH_MOSI_SIGNAL                                 RXD_SDA_MOSI   /*!< FLEXCOMM5 signal: RXD_SDA_MOSI */
#define BOARD_SPI_FLASH_MOSI_PIN_NAME                           FC5_RXD_SDA_MOSI   /*!< Pin name */
#define BOARD_SPI_FLASH_MOSI_LABEL         "J1[13]/U5[5]/P0_20-FC5_RXD_SDA_MOSI"   /*!< Label */
#define BOARD_SPI_FLASH_MOSI_NAME                               "SPI_FLASH_MOSI"   /*!< Identifier name */

/* FC5_SSEL3 (number 16), J9[7]/JS8[1]/U5[1]/P1_2-FC5_SSEL3 */
#define BOARD_FC5_SSEL3_PERIPHERAL                                     FLEXCOMM5   /*!< Device name: FLEXCOMM5 */
#define BOARD_FC5_SSEL3_SIGNAL                                             SSEL3   /*!< FLEXCOMM5 signal: SSEL3 */
#define BOARD_FC5_SSEL3_PIN_NAME                                       FC5_SSEL3   /*!< Pin name */
#define BOARD_FC5_SSEL3_LABEL                "J9[7]/JS8[1]/U5[1]/P1_2-FC5_SSEL3"   /*!< Label */
#define BOARD_FC5_SSEL3_NAME                                         "FC5_SSEL3"   /*!< Identifier name */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitSPI_FLASHPins(void); /* Function assigned for the Cortex-M0P */

/* PIO0_4 (number 38), J4[7]/U9[12]/SW3/BRIDGE_T_INTR-ISP1 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_INTR_GPIO                GPIO   /*!< GPIO device name: GPIO */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_INTR_PORT                  0U   /*!< PORT device index: 0 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_INTR_GPIO_PIN              4U   /*!< PIO0 pin index: 4 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_INTR_PIN_NAME          PIO0_4   /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_INTR_LABEL "J4[7]/U9[12]/SW3/BRIDGE_T_INTR-ISP1" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_INTR_NAME     "BRIDGE_T_INTR"   /*!< Identifier name */

/* FC3_SCK (number 46), J4[4]/U9[13]/BRIDGE_T_SCK */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SCK_PERIPHERAL      FLEXCOMM3   /*!< Device name: FLEXCOMM3 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SCK_SIGNAL                SCK   /*!< FLEXCOMM3 signal: SCK */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SCK_PIN_NAME          FC3_SCK   /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SCK_LABEL "J4[4]/U9[13]/BRIDGE_T_SCK" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SCK_NAME       "BRIDGE_T_SCK"   /*!< Identifier name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SCK_DIRECTION kPIN_MUX_DirectionOutput /*!< Direction */

/* FC3_RXD_SDA_MOSI (number 47), J4[2]/U9[11]/BRIDGE_T_MOSI */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MOSI_PERIPHERAL     FLEXCOMM3   /*!< Device name: FLEXCOMM3 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MOSI_SIGNAL      RXD_SDA_MOSI   /*!< FLEXCOMM3 signal: RXD_SDA_MOSI */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MOSI_PIN_NAME FC3_RXD_SDA_MOSI  /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MOSI_LABEL "J4[2]/U9[11]/BRIDGE_T_MOSI" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MOSI_NAME     "BRIDGE_T_MOSI"   /*!< Identifier name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MOSI_DIRECTION kPIN_MUX_DirectionOutput /*!< Direction */

/* FC3_TXD_SCL_MISO (number 48), J4[3]/U15[4]/BRIDGE_T_MISO */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MISO_PERIPHERAL     FLEXCOMM3   /*!< Device name: FLEXCOMM3 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MISO_SIGNAL      TXD_SCL_MISO   /*!< FLEXCOMM3 signal: TXD_SCL_MISO */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MISO_PIN_NAME FC3_TXD_SCL_MISO  /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MISO_LABEL "J4[3]/U15[4]/BRIDGE_T_MISO" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MISO_NAME     "BRIDGE_T_MISO"   /*!< Identifier name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_MISO_DIRECTION kPIN_MUX_DirectionInput /*!< Direction */

/* FC3_CTS_SDA_SSEL0 (number 49), J2[12]/J4[1]/U9[14]/BRIDGE_T_SSEL-SPIFI_IO3 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SSEL_PERIPHERAL     FLEXCOMM3   /*!< Device name: FLEXCOMM3 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SSEL_SIGNAL     CTS_SDA_SSEL0   /*!< FLEXCOMM3 signal: CTS_SDA_SSEL0 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SSEL_PIN_NAME FC3_CTS_SDA_SSEL0 /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SSEL_LABEL "J2[12]/J4[1]/U9[14]/BRIDGE_T_SSEL-SPIFI_IO3" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SSEL_NAME     "BRIDGE_T_SSEL"   /*!< Identifier name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_T_SSEL_DIRECTION kPIN_MUX_DirectionOutput /*!< Direction */

/* PIO0_22 (number 63), J4[8]/P0_22-BRIDGE_GPIO */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_GPIO_GPIO                  GPIO   /*!< GPIO device name: GPIO */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_GPIO_PORT                    0U   /*!< PORT device index: 0 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_GPIO_GPIO_PIN               22U   /*!< PIO0 pin index: 22 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_GPIO_PIN_NAME           PIO0_22   /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_GPIO_LABEL "J4[8]/P0_22-BRIDGE_GPIO" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_GPIO_NAME         "BRIDGE_GPIO"   /*!< Identifier name */

/* FC1_RTS_SCL_SSEL1 (number 1), J4[9]/JS3[1]/JS4[3]/U10[7]/U12[D6]/BRIDGE_SCL */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SCL_PERIPHERAL        FLEXCOMM1   /*!< Device name: FLEXCOMM1 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SCL_SIGNAL        RTS_SCL_SSEL1   /*!< FLEXCOMM1 signal: RTS_SCL_SSEL1 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SCL_PIN_NAME  FC1_RTS_SCL_SSEL1   /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SCL_LABEL "J4[9]/JS3[1]/JS4[3]/U10[7]/U12[D6]/BRIDGE_SCL" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SCL_NAME           "BRIDGE_SCL"   /*!< Identifier name */

/* FC1_CTS_SDA_SSEL0 (number 2), J4[10]/JS2[1]/JS5[3]/U10[5]/U12[E6]/SW1/BRIDGE_SDA-WAKEUP */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SDA_WAKEUP_PERIPHERAL FLEXCOMM1   /*!< Device name: FLEXCOMM1 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SDA_WAKEUP_SIGNAL CTS_SDA_SSEL0   /*!< FLEXCOMM1 signal: CTS_SDA_SSEL0 */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SDA_WAKEUP_PIN_NAME FC1_CTS_SDA_SSEL0 /*!< Pin name */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SDA_WAKEUP_LABEL "J4[10]/JS2[1]/JS5[3]/U10[5]/U12[E6]/SW1/BRIDGE_SDA-WAKEUP" /*!< Label */
#define BOARD_INITPMOD_SPI_I2C_BRIDGEPINS_BRIDGE_SDA_WAKEUP_NAME "BRIDGE_SDA_WAKEUP" /*!< Identifier name */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitPMod_SPI_I2C_BRIDGEPins(void); /* Function assigned for the Cortex-M0P */

/* USB0_DP (number 5), J5[3]/U7[2]/USB_DP */
#define BOARD_USB_DP_PERIPHERAL                                             USB0   /*!< Device name: USB0 */
#define BOARD_USB_DP_SIGNAL                                               USB_DP   /*!< USB0 signal: USB_DP */
#define BOARD_USB_DP_PIN_NAME                                            USB0_DP   /*!< Pin name */
#define BOARD_USB_DP_LABEL                                  "J5[3]/U7[2]/USB_DP"   /*!< Label */
#define BOARD_USB_DP_NAME                                               "USB_DP"   /*!< Identifier name */

/* USB0_DM (number 6), J5[2]/U7[3]/USB_DM */
#define BOARD_USB_DM_PERIPHERAL                                             USB0   /*!< Device name: USB0 */
#define BOARD_USB_DM_SIGNAL                                               USB_DM   /*!< USB0 signal: USB_DM */
#define BOARD_USB_DM_PIN_NAME                                            USB0_DM   /*!< Pin name */
#define BOARD_USB_DM_LABEL                                  "J5[2]/U7[3]/USB_DM"   /*!< Label */
#define BOARD_USB_DM_NAME                                               "USB_DM"   /*!< Identifier name */

/* USB0_VBUS (number 26), J1[14]/J5[1]/JP10[2]/P1_6-FC7_SCK-USB_VBUS */
#define BOARD_USB_VBUS_PERIPHERAL                                           USB0   /*!< Device name: USB0 */
#define BOARD_USB_VBUS_SIGNAL                                           USB_VBUS   /*!< USB0 signal: USB_VBUS */
#define BOARD_USB_VBUS_PIN_NAME                                        USB0_VBUS   /*!< Pin name */
#define BOARD_USB_VBUS_LABEL        "J1[14]/J5[1]/JP10[2]/P1_6-FC7_SCK-USB_VBUS"   /*!< Label */
#define BOARD_USB_VBUS_NAME                                           "USB_VBUS"   /*!< Identifier name */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitUSBPins(void); /* Function assigned for the Cortex-M0P */

/* FC0_TXD_SCL_MISO (number 32), U6[4]/U22[3]/P0_1-ISP_TX */
#define BOARD_DEBUG_UART_TX_PERIPHERAL                                 FLEXCOMM0   /*!< Device name: FLEXCOMM0 */
#define BOARD_DEBUG_UART_TX_SIGNAL                                  TXD_SCL_MISO   /*!< FLEXCOMM0 signal: TXD_SCL_MISO */
#define BOARD_DEBUG_UART_TX_PIN_NAME                            FC0_TXD_SCL_MISO   /*!< Pin name */
#define BOARD_DEBUG_UART_TX_LABEL                     "U6[4]/U22[3]/P0_1-ISP_TX"   /*!< Label */
#define BOARD_DEBUG_UART_TX_NAME                                 "DEBUG_UART_TX"   /*!< Identifier name */
#define BOARD_DEBUG_UART_TX_DIRECTION                   kPIN_MUX_DirectionOutput   /*!< Direction */

/* FC0_RXD_SDA_MOSI (number 31), U18[4]/TO_MUX_P0_0-ISP_RX */
#define BOARD_DEBUG_UART_RX_PERIPHERAL                                 FLEXCOMM0   /*!< Device name: FLEXCOMM0 */
#define BOARD_DEBUG_UART_RX_SIGNAL                                  RXD_SDA_MOSI   /*!< FLEXCOMM0 signal: RXD_SDA_MOSI */
#define BOARD_DEBUG_UART_RX_PIN_NAME                            FC0_RXD_SDA_MOSI   /*!< Pin name */
#define BOARD_DEBUG_UART_RX_LABEL                    "U18[4]/TO_MUX_P0_0-ISP_RX"   /*!< Label */
#define BOARD_DEBUG_UART_RX_NAME                                 "DEBUG_UART_RX"   /*!< Identifier name */
#define BOARD_DEBUG_UART_RX_DIRECTION                    kPIN_MUX_DirectionInput   /*!< Direction */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitDEBUG_UARTPins(void); /* Function assigned for the Cortex-M0P */

/* SWDIO (number 53), J2[6]/P1[2]/U2[5]/U14[4]/IF_TMS_SWDIO-SPIFI_IO0 */
#define BOARD_DEBUG_SWD_SWDIO_PERIPHERAL                                     SWD   /*!< Device name: SWD */
#define BOARD_DEBUG_SWD_SWDIO_SIGNAL                                       SWDIO   /*!< SWD signal: SWDIO */
#define BOARD_DEBUG_SWD_SWDIO_PIN_NAME                                     SWDIO   /*!< Pin name */
#define BOARD_DEBUG_SWD_SWDIO_LABEL "J2[6]/P1[2]/U2[5]/U14[4]/IF_TMS_SWDIO-SPIFI_IO0" /*!< Label */
#define BOARD_DEBUG_SWD_SWDIO_NAME                             "DEBUG_SWD_SWDIO"   /*!< Identifier name */

/* SWCLK (number 52), J2[4]/JS28/U4[4]/TCK-SWDCLK_TRGT-SPIFI_IO1 */
#define BOARD_DEBUG_SWD_SWDCLK_PERIPHERAL                                    SWD   /*!< Device name: SWD */
#define BOARD_DEBUG_SWD_SWDCLK_SIGNAL                                      SWCLK   /*!< SWD signal: SWCLK */
#define BOARD_DEBUG_SWD_SWDCLK_PIN_NAME                                    SWCLK   /*!< Pin name */
#define BOARD_DEBUG_SWD_SWDCLK_LABEL "J2[4]/JS28/U4[4]/TCK-SWDCLK_TRGT-SPIFI_IO1"  /*!< Label */
#define BOARD_DEBUG_SWD_SWDCLK_NAME                           "DEBUG_SWD_SWDCLK"   /*!< Identifier name */

/*!
 * @brief Configures pin routing and optionally pin electrical features.
 *
 */
void BOARD_InitSWD_DEBUGPins(void); /* Function assigned for the Cortex-M0P */

#if defined(__cplusplus)
}
#endif

/*!
 * @}
 */
#endif /* _PIN_MUX_H_ */

/*******************************************************************************
 * EOF
 ******************************************************************************/
