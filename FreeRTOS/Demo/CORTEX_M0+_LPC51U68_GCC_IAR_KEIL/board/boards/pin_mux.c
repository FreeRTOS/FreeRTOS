/*
 * Copyright 2018 NXP.
 * All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
!!GlobalInfo
product: Pins v4.1
processor: LPC51U68
package_id: LPC51U68JBD64
mcu_data: ksdk2_0
processor_version: 3.0.1
board: LPCXpresso51u68
pin_labels:
- {pin_num: '1', pin_signal: PIO0_23/FC1_RTS_SCL_SSEL1/CTIMER0_CAP0/UTICK_CAP1, label: 'J4[9]/JS3[1]/JS4[3]/U10[7]/U12[D6]/BRIDGE_SCL', identifier: BRIDGE_SCL;LINK2MCU_SCL}
- {pin_num: '2', pin_signal: PIO0_24/FC1_CTS_SDA_SSEL0/CTIMER0_CAP1/CTIMER0_MAT0, label: 'J4[10]/JS2[1]/JS5[3]/U10[5]/U12[E6]/SW1/BRIDGE_SDA-WAKEUP', identifier: SW1;BRIDGE_SDA_WAKEUP;LINK2MCU_SDA}
- {pin_num: '13', pin_signal: PIO0_31/FC2_CTS_SDA_SSEL0/CTIMER0_CAP3/CTIMER0_MAT3/ADC0_2, label: 'J2[17]/J3[2]/P1[7]/U3[4]/SW2/P0_31-PDM0_CLK-ISP0_EN', identifier: SW2}
- {pin_num: '38', pin_signal: PIO0_4/FC0_SCK/FC3_SSEL2/CTIMER0_CAP2, label: 'J4[7]/U9[12]/SW3/BRIDGE_T_INTR-ISP1', identifier: SW3;BRIDGE_T_INTR}
- {pin_num: '29', pin_signal: PIO1_9/FC3_RXD_SDA_MOSI/CTIMER0_CAP2/USB0_UP_LED, label: 'J9[5]/D2[3]/P1_9-BLUE_LED', identifier: LED_BLUE}
- {pin_num: '30', pin_signal: PIO1_10/FC6_TXD_SCL_MISO_WS/SCT0_OUT4/FC1_SCK/USB0_FRAME, label: 'J9[8]/D2[4]/P1_10-SCT4-LED_GREEN', identifier: LED_GREEN}
- {pin_num: '11', pin_signal: PIO0_29/FC1_RXD_SDA_MOSI/SCT0_OUT2/CTIMER0_MAT3/CTIMER0_CAP1/CTIMER0_MAT1/ADC0_0, label: 'J2[5]/D2[1]/P0_29-CT32B0_MAT3-RED', identifier: LED_RED}
- {pin_num: '3', pin_signal: PIO0_25/FC4_RTS_SCL_SSEL1/FC6_CTS_SDA_SSEL0/CTIMER0_CAP2/CTIMER1_CAP1, label: 'J1[1]/JS4[1]/U10[7]/P0_25-FC4_SCLX', identifier: FC4_SCLX}
- {pin_num: '4', pin_signal: PIO0_26/FC4_CTS_SDA_SSEL0/CTIMER0_CAP3, label: 'J1[3]/JS5[1]/U10[5]/P0_26-FC4_SDAX', identifier: FC4_SDAX}
- {pin_num: '58', pin_signal: PIO0_18/FC5_TXD_SCL_MISO/SCT0_OUT0/CTIMER0_MAT0, label: 'J1[11]/U5[2]/P0_18-FC5_TXD_SCL_MISO', identifier: SPI_FLASH_MISO}
- {pin_num: '59', pin_signal: PIO0_19/FC5_SCK/SCT0_OUT1/CTIMER0_MAT1, label: 'J1[9]/J2[8]/U5[6]/P0_19-FC5_SCK-SPIFI_CSn', identifier: SPI_FLASH_SCK}
- {pin_num: '60', pin_signal: PIO0_20/FC5_RXD_SDA_MOSI/FC0_SCK/CTIMER3_CAP0, label: 'J1[13]/U5[5]/P0_20-FC5_RXD_SDA_MOSI', identifier: SPI_FLASH_MOSI}
- {pin_num: '16', pin_signal: PIO1_2/MCLK/FC7_SSEL3/SCT0_OUT5/FC5_SSEL3/FC4_RXD_SDA_MOSI/ADC0_5, label: 'J9[7]/JS8[1]/U5[1]/P1_2-FC5_SSEL3', identifier: FC5_SSEL3}
- {pin_num: '46', pin_signal: PIO0_11/FC3_SCK/FC6_RXD_SDA_MOSI_DATA, label: 'J4[4]/U9[13]/BRIDGE_T_SCK', identifier: BRIDGE_T_SCK}
- {pin_num: '47', pin_signal: PIO0_12/FC3_RXD_SDA_MOSI/FC6_TXD_SCL_MISO_WS, label: 'J4[2]/U9[11]/BRIDGE_T_MOSI', identifier: BRIDGE_T_MOSI}
- {pin_num: '48', pin_signal: PIO0_13/FC3_TXD_SCL_MISO/SCT0_OUT4, label: 'J4[3]/U15[4]/BRIDGE_T_MISO', identifier: BRIDGE_T_MISO}
- {pin_num: '63', pin_signal: PIO0_22/CLKIN/FC0_RXD_SDA_MOSI/CTIMER3_MAT3, label: 'J4[8]/P0_22-BRIDGE_GPIO', identifier: BRIDGE_GPIO}
- {pin_num: '31', pin_signal: PIO0_0/FC0_RXD_SDA_MOSI/FC3_CTS_SDA_SSEL0/CTIMER0_CAP0/SCT0_OUT3, label: 'U18[4]/TO_MUX_P0_0-ISP_RX', identifier: DEBUG_UART_RX}
- {pin_num: '5', pin_signal: USB0_DP, label: 'J5[3]/U7[2]/USB_DP', identifier: USB_DP}
- {pin_num: '6', pin_signal: USB0_DM, label: 'J5[2]/U7[3]/USB_DM', identifier: USB_DM}
- {pin_num: '32', pin_signal: PIO0_1/FC0_TXD_SCL_MISO/FC3_RTS_SCL_SSEL1/CTIMER0_CAP1/SCT0_OUT1, label: 'U6[4]/U22[3]/P0_1-ISP_TX', identifier: DEBUG_UART_TX}
- {pin_num: '53', pin_signal: PIO0_17/FC3_SSEL3/FC6_RTS_SCL_SSEL1/CTIMER3_MAT2/SWDIO, label: 'J2[6]/P1[2]/U2[5]/U14[4]/IF_TMS_SWDIO-SPIFI_IO0', identifier: DEBUG_SWD_SWDIO}
- {pin_num: '52', pin_signal: PIO0_16/FC3_SSEL2/FC6_CTS_SDA_SSEL0/CTIMER3_MAT1/SWCLK, label: 'J2[4]/JS28/U4[4]/TCK-SWDCLK_TRGT-SPIFI_IO1', identifier: DEBUG_SWD_SWDCLK}
- {pin_num: '50', pin_signal: PIO0_15/FC3_RTS_SCL_SSEL1/FC4_SCK, label: 'J2[10]/JS30/U4[12]/TDO-SWO_TRGT-SPIFI_IO2', identifier: DEBUG_SWD_SWO}
- {pin_num: '49', pin_signal: PIO0_14/FC3_CTS_SDA_SSEL0/SCT0_OUT5/FC1_SCK, label: 'J2[12]/J4[1]/U9[14]/BRIDGE_T_SSEL-SPIFI_IO3', identifier: BRIDGE_T_SSEL}
- {pin_num: '26', pin_signal: PIO1_6/FC7_SCK/CTIMER1_CAP2/CTIMER1_MAT2/USB0_VBUS/ADC0_9, label: 'J1[14]/J5[1]/JP10[2]/P1_6-FC7_SCK-USB_VBUS', identifier: USB_VBUS}
- {pin_num: '7', pin_signal: PIO1_16/CTIMER0_MAT0/CTIMER0_CAP0/FC7_RTS_SCL_SSEL1, label: 'J1[19]/P1_16-CT32B0_MAT0-GYRO_INT1'}
- {pin_num: '8', pin_signal: VDD8, label: VDD_LPC54u68_IC}
- {pin_num: '9', pin_signal: VSS9, label: GND}
- {pin_num: '10', pin_signal: PIO1_17/MCLK/UTICK_CAP3, label: 'J9[9]/P1_17-IR_LEARN_EN'}
- {pin_num: '12', pin_signal: PIO0_30/FC1_TXD_SCL_MISO/SCT0_OUT3/CTIMER0_MAT2/CTIMER0_CAP2/ADC0_1, label: 'J9[2]/P0_30-ADC1'}
- {pin_num: '14', pin_signal: PIO1_0/FC2_RTS_SCL_SSEL1/CTIMER3_MAT1/CTIMER0_CAP0/ADC0_3, label: 'J2[3]/P1_0-PDM0_DATA-CT32B3_MAT1'}
- {pin_num: '15', pin_signal: PIO1_1/SCT0_OUT4/FC5_SSEL2/FC4_TXD_SCL_MISO/ADC0_4, label: 'J1[15]/P1_1-FC5_SSEL2'}
- {pin_num: '17', pin_signal: PIO1_3/FC7_SSEL2/SCT0_OUT6/FC3_SCK/CTIMER0_CAP1/USB0_UP_LED/ADC0_6, label: 'J2[20]/P1_3-FC7_SSEL2-CT32B0_CAP1'}
- {pin_num: '18', pin_signal: PIO1_4/FC7_RTS_SCL_SSEL1/SCT0_OUT7/FC3_TXD_SCL_MISO/CTIMER0_MAT1/ADC0_7, label: 'J2[18]/J9[10]/P1_4-ADC7-PDM1_CLK-FC7_RTS-FC3_TXD'}
- {pin_num: '19', pin_signal: PIO1_5/FC7_CTS_SDA_SSEL0/CTIMER1_CAP0/CTIMER1_MAT3/USB0_FRAME/ADC0_8, label: 'J2[16]/J9[12]/P1_5-ADC8-PDM1_DAT-FC7_CTS'}
- {pin_num: '20', pin_signal: VSSA, label: GND}
- {pin_num: '21', pin_signal: VREFN, label: 'SJ1[2]/P4[3]/GND'}
- {pin_num: '22', pin_signal: VREFP, label: 'SJ2[2]/P4[1]/VDD_LPC541u68_IC'}
- {pin_num: '23', pin_signal: VDDA, label: VDD_LPC54u68_IC}
- {pin_num: '24', pin_signal: VDD24, label: VDD_LPC54u68_IC}
- {pin_num: '25', pin_signal: VSS25, label: GND}
- {pin_num: '27', pin_signal: PIO1_7/FC7_RXD_SDA_MOSI_DATA/CTIMER1_MAT2/CTIMER1_CAP2/ADC0_10, label: 'J1[10]/P1_7-FC7_RXD_SDA_MOSI_DATA'}
- {pin_num: '28', pin_signal: PIO1_8/FC7_TXD_SCL_MISO_WS/CTIMER1_MAT3/CTIMER1_CAP3/ADC0_11, label: 'J1[12]/J9[6]/P1_8-ADC11-FC7_TXD_SCL_MISO_FRAME'}
- {pin_num: '33', pin_signal: RTCXIN, label: 'JS18[2]/Y1/RTCXIN'}
- {pin_num: '34', pin_signal: VDD34, label: VDD_LPC54u68_IC}
- {pin_num: '35', pin_signal: RTCXOUT, label: JS17/Y1/RTCXOUT}
- {pin_num: '36', pin_signal: PIO0_2/FC0_CTS_SDA_SSEL0/FC2_SSEL3, label: 'J9[1]/P0_2-GPIO_SPI_CS'}
- {pin_num: '37', pin_signal: PIO0_3/FC0_RTS_SCL_SSEL1/FC2_SSEL2/CTIMER1_MAT3, label: 'J9[3]/P0_3-GPIO_SPI_CS'}
- {pin_num: '39', pin_signal: PIO0_5/FC6_RXD_SDA_MOSI_DATA/SCT0_OUT6/CTIMER0_MAT0, label: 'J1[20]/P0_5-FC6_RXD_SDA_MOSI_DATA'}
- {pin_num: '40', pin_signal: PIO0_6/FC6_TXD_SCL_MISO_WS/CTIMER0_MAT1/UTICK_CAP0, label: 'J1[18]/P0_6-FC6_TXD_SCL_MISO_FRAME'}
- {pin_num: '41', pin_signal: PIO0_7/FC6_SCK/SCT0_OUT0/CTIMER0_MAT2/CTIMER0_CAP2, label: 'J1[16]/P0_7-FC6_SCK'}
- {pin_num: '42', pin_signal: PIO1_11/FC6_RTS_SCL_SSEL1/CTIMER1_CAP0/FC4_SCK/USB0_VBUS, label: 'J2[19]/P1_11-FC6_RTS_SSEL1-MAG_DRDY'}
- {pin_num: '43', pin_signal: PIO0_8/FC2_RXD_SDA_MOSI/SCT0_OUT1/CTIMER0_MAT3, label: 'J2[15]/P0_8-FC2_RXD_SDA_MOSI'}
- {pin_num: '44', pin_signal: PIO0_9/FC2_TXD_SCL_MISO/SCT0_OUT2/CTIMER3_CAP0/FC3_CTS_SDA_SSEL0, label: 'J2[13]/P0_9-FC2_TXD_SCL_MISO'}
- {pin_num: '45', pin_signal: PIO0_10/FC2_SCK/SCT0_OUT3/CTIMER3_MAT0, label: 'J2[11]/P0_10-FC2_SCK-CT32B3_MAT0'}
- {pin_num: '51', pin_signal: PIO1_12/FC5_RXD_SDA_MOSI/CTIMER1_MAT0/FC7_SCK/UTICK_CAP2, label: 'J2[9]/P1_12-CT32B1_MAT0-ACCl_INT1'}
- {pin_num: '54', pin_signal: PIO1_13/FC5_TXD_SCL_MISO/CTIMER1_MAT1/FC7_RXD_SDA_MOSI_DATA, label: 'J2[7]/P1_13-CT32B1_MAT1'}
- {pin_num: '55', pin_signal: VSS55, label: GND}
- {pin_num: '56', pin_signal: VDD56, label: VDD_LPC54u68_IC}
- {pin_num: '57', pin_signal: PIO1_14/FC2_RXD_SDA_MOSI/SCT0_OUT7/FC7_TXD_SCL_MISO_WS, label: 'J2[1]/P1_14-SCTO7'}
- {pin_num: '61', pin_signal: PIO0_21/CLKOUT/FC0_TXD_SCL_MISO/CTIMER3_MAT0, label: 'J2[2]/P0_21-CLKOUT-SPIFI_CLK'}
- {pin_num: '62', pin_signal: PIO1_15/SCT0_OUT5/CTIMER1_CAP3/FC7_CTS_SDA_SSEL0, label: 'J1[17]/P1_15-SCTO5-FC7_CTS'}
- {pin_num: '64', pin_signal: RESET, label: 'J3[1]/J8[9]/J8[10]/JP7[1]/JS9[1]/JS12[1]/JS29/D4[1]/U4[8]/U5[7]/U10[22]/SW4/nRESET_TRGT', identifier: RESET}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

#include "fsl_common.h"
#include "pin_mux.h"

/*FUNCTION**********************************************************************
 * 
 * Function Name : BOARD_InitBootPins
 * Description   : Calls initialization functions.
 * 
 *END**************************************************************************/
void BOARD_InitBootPins(void) {
    BOARD_InitPins();
    BOARD_InitDEBUG_UARTPins();
}

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitPins:
- options: {callFromInitBoot: 'true', prefix: BOARD_, coreID: core0, enableClock: 'true'}
- pin_list: []
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitPins(void) { /* Function assigned for the Cortex-M0P */
}


#define PIO023_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO023_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO023_I2CSLEW_I2C_MODE       0x00u   /*!< Controls slew rate of I2C pin.: I2C mode. */
#define PIO024_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO024_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO024_I2CSLEW_I2C_MODE       0x00u   /*!< Controls slew rate of I2C pin.: I2C mode. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitLink2MCUPins:
- options: {prefix: BOARD_, coreID: core0, enableClock: 'false'}
- pin_list:
  - {pin_num: '1', peripheral: FLEXCOMM1, signal: RTS_SCL_SSEL1, pin_signal: PIO0_23/FC1_RTS_SCL_SSEL1/CTIMER0_CAP0/UTICK_CAP1, identifier: LINK2MCU_SCL, i2c_slew: i2c}
  - {pin_num: '2', peripheral: FLEXCOMM1, signal: CTS_SDA_SSEL0, pin_signal: PIO0_24/FC1_CTS_SDA_SSEL0/CTIMER0_CAP1/CTIMER0_MAT0, identifier: LINK2MCU_SDA, i2c_slew: i2c}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitLink2MCUPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitLink2MCUPins(void) { /* Function assigned for the Cortex-M0P */
  IOCON->PIO[0][23] = ((IOCON->PIO[0][23] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_I2CSLEW_MASK | IOCON_PIO_DIGIMODE_MASK))) /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO023_FUNC_ALT1)                     /* Selects pin function.: PORT023 (pin 1) is configured as FC1_RTS_SCL_SSEL1 */
      | IOCON_PIO_I2CSLEW(PIO023_I2CSLEW_I2C_MODE)           /* Controls slew rate of I2C pin.: I2C mode. */
      | IOCON_PIO_DIGIMODE(PIO023_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][24] = ((IOCON->PIO[0][24] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_I2CSLEW_MASK | IOCON_PIO_DIGIMODE_MASK))) /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO024_FUNC_ALT1)                     /* Selects pin function.: PORT024 (pin 2) is configured as FC1_CTS_SDA_SSEL0 */
      | IOCON_PIO_I2CSLEW(PIO024_I2CSLEW_I2C_MODE)           /* Controls slew rate of I2C pin.: I2C mode. */
      | IOCON_PIO_DIGIMODE(PIO024_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO024_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO024_FUNC_ALT0              0x00u   /*!< Selects pin function.: Alternative connection 0. */
#define PIO031_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO031_FUNC_ALT0              0x00u   /*!< Selects pin function.: Alternative connection 0. */
#define PIO04_DIGIMODE_DIGITAL        0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO04_FUNC_ALT0               0x00u   /*!< Selects pin function.: Alternative connection 0. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitBUTTONsPins:
- options: {prefix: BOARD_, coreID: core0, enableClock: 'true'}
- pin_list:
  - {pin_num: '2', peripheral: GPIO, signal: 'PIO0, 24', pin_signal: PIO0_24/FC1_CTS_SDA_SSEL0/CTIMER0_CAP1/CTIMER0_MAT0, identifier: SW1, direction: INPUT}
  - {pin_num: '13', peripheral: GPIO, signal: 'PIO0, 31', pin_signal: PIO0_31/FC2_CTS_SDA_SSEL0/CTIMER0_CAP3/CTIMER0_MAT3/ADC0_2, direction: INPUT}
  - {pin_num: '38', peripheral: GPIO, signal: 'PIO0, 4', pin_signal: PIO0_4/FC0_SCK/FC3_SSEL2/CTIMER0_CAP2, identifier: SW3, direction: INPUT}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitBUTTONsPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitBUTTONsPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[0][24] = ((IOCON->PIO[0][24] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO024_FUNC_ALT0)                     /* Selects pin function.: PORT024 (pin 2) is configured as PIO0_24 */
      | IOCON_PIO_DIGIMODE(PIO024_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][31] = ((IOCON->PIO[0][31] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO031_FUNC_ALT0)                     /* Selects pin function.: PORT031 (pin 13) is configured as PIO0_31 */
      | IOCON_PIO_DIGIMODE(PIO031_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][4] = ((IOCON->PIO[0][4] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO04_FUNC_ALT0)                      /* Selects pin function.: PORT04 (pin 38) is configured as PIO0_4 */
      | IOCON_PIO_DIGIMODE(PIO04_DIGIMODE_DIGITAL)           /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO029_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO029_FUNC_ALT0              0x00u   /*!< Selects pin function.: Alternative connection 0. */
#define PIO110_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO110_FUNC_ALT0              0x00u   /*!< Selects pin function.: Alternative connection 0. */
#define PIO19_DIGIMODE_DIGITAL        0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO19_FUNC_ALT0               0x00u   /*!< Selects pin function.: Alternative connection 0. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitLEDsPins:
- options: {prefix: BOARD_, coreID: core0, enableClock: 'true'}
- pin_list:
  - {pin_num: '29', peripheral: GPIO, signal: 'PIO1, 9', pin_signal: PIO1_9/FC3_RXD_SDA_MOSI/CTIMER0_CAP2/USB0_UP_LED, direction: OUTPUT}
  - {pin_num: '30', peripheral: GPIO, signal: 'PIO1, 10', pin_signal: PIO1_10/FC6_TXD_SCL_MISO_WS/SCT0_OUT4/FC1_SCK/USB0_FRAME, direction: OUTPUT}
  - {pin_num: '11', peripheral: GPIO, signal: 'PIO0, 29', pin_signal: PIO0_29/FC1_RXD_SDA_MOSI/SCT0_OUT2/CTIMER0_MAT3/CTIMER0_CAP1/CTIMER0_MAT1/ADC0_0, direction: OUTPUT}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitLEDsPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitLEDsPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[0][29] = ((IOCON->PIO[0][29] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO029_FUNC_ALT0)                     /* Selects pin function.: PORT029 (pin 11) is configured as PIO0_29 */
      | IOCON_PIO_DIGIMODE(PIO029_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[1][10] = ((IOCON->PIO[1][10] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO110_FUNC_ALT0)                     /* Selects pin function.: PORT110 (pin 30) is configured as PIO1_10 */
      | IOCON_PIO_DIGIMODE(PIO110_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[1][9] = ((IOCON->PIO[1][9] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO19_FUNC_ALT0)                      /* Selects pin function.: PORT19 (pin 29) is configured as PIO1_9 */
      | IOCON_PIO_DIGIMODE(PIO19_DIGIMODE_DIGITAL)           /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO025_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO025_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO025_I2CSLEW_I2C_MODE       0x00u   /*!< Controls slew rate of I2C pin.: I2C mode. */
#define PIO026_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO026_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO026_I2CSLEW_I2C_MODE       0x00u   /*!< Controls slew rate of I2C pin.: I2C mode. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitSecureMCUPins:
- options: {prefix: BOARD_, coreID: core0, enableClock: 'true'}
- pin_list:
  - {pin_num: '3', peripheral: FLEXCOMM4, signal: RTS_SCL_SSEL1, pin_signal: PIO0_25/FC4_RTS_SCL_SSEL1/FC6_CTS_SDA_SSEL0/CTIMER0_CAP2/CTIMER1_CAP1, i2c_slew: i2c}
  - {pin_num: '4', peripheral: FLEXCOMM4, signal: CTS_SDA_SSEL0, pin_signal: PIO0_26/FC4_CTS_SDA_SSEL0/CTIMER0_CAP3, i2c_slew: i2c}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitSecureMCUPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitSecureMCUPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[0][25] = ((IOCON->PIO[0][25] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_I2CSLEW_MASK | IOCON_PIO_DIGIMODE_MASK))) /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO025_FUNC_ALT1)                     /* Selects pin function.: PORT025 (pin 3) is configured as FC4_RTS_SCL_SSEL1 */
      | IOCON_PIO_I2CSLEW(PIO025_I2CSLEW_I2C_MODE)           /* Controls slew rate of I2C pin.: I2C mode. */
      | IOCON_PIO_DIGIMODE(PIO025_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][26] = ((IOCON->PIO[0][26] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_I2CSLEW_MASK | IOCON_PIO_DIGIMODE_MASK))) /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO026_FUNC_ALT1)                     /* Selects pin function.: PORT026 (pin 4) is configured as FC4_CTS_SDA_SSEL0 */
      | IOCON_PIO_I2CSLEW(PIO026_I2CSLEW_I2C_MODE)           /* Controls slew rate of I2C pin.: I2C mode. */
      | IOCON_PIO_DIGIMODE(PIO026_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO018_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO018_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO019_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO019_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO020_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO020_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO12_DIGIMODE_DIGITAL        0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO12_FUNC_ALT4               0x04u   /*!< Selects pin function.: Alternative connection 4. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitSPI_FLASHPins:
- options: {prefix: BOARD_, coreID: core0, enableClock: 'true'}
- pin_list:
  - {pin_num: '58', peripheral: FLEXCOMM5, signal: TXD_SCL_MISO, pin_signal: PIO0_18/FC5_TXD_SCL_MISO/SCT0_OUT0/CTIMER0_MAT0}
  - {pin_num: '59', peripheral: FLEXCOMM5, signal: SCK, pin_signal: PIO0_19/FC5_SCK/SCT0_OUT1/CTIMER0_MAT1}
  - {pin_num: '60', peripheral: FLEXCOMM5, signal: RXD_SDA_MOSI, pin_signal: PIO0_20/FC5_RXD_SDA_MOSI/FC0_SCK/CTIMER3_CAP0}
  - {pin_num: '16', peripheral: FLEXCOMM5, signal: SSEL3, pin_signal: PIO1_2/MCLK/FC7_SSEL3/SCT0_OUT5/FC5_SSEL3/FC4_RXD_SDA_MOSI/ADC0_5}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitSPI_FLASHPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitSPI_FLASHPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[0][18] = ((IOCON->PIO[0][18] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO018_FUNC_ALT1)                     /* Selects pin function.: PORT018 (pin 58) is configured as FC5_TXD_SCL_MISO */
      | IOCON_PIO_DIGIMODE(PIO018_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][19] = ((IOCON->PIO[0][19] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO019_FUNC_ALT1)                     /* Selects pin function.: PORT019 (pin 59) is configured as FC5_SCK */
      | IOCON_PIO_DIGIMODE(PIO019_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][20] = ((IOCON->PIO[0][20] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO020_FUNC_ALT1)                     /* Selects pin function.: PORT020 (pin 60) is configured as FC5_RXD_SDA_MOSI */
      | IOCON_PIO_DIGIMODE(PIO020_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[1][2] = ((IOCON->PIO[1][2] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO12_FUNC_ALT4)                      /* Selects pin function.: PORT12 (pin 16) is configured as FC5_SSEL3 */
      | IOCON_PIO_DIGIMODE(PIO12_DIGIMODE_DIGITAL)           /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO011_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO011_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO012_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO012_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO013_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO013_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO014_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO014_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO022_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO022_FUNC_ALT0              0x00u   /*!< Selects pin function.: Alternative connection 0. */
#define PIO023_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO023_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO023_I2CSLEW_I2C_MODE       0x00u   /*!< Controls slew rate of I2C pin.: I2C mode. */
#define PIO024_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO024_FUNC_ALT1              0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO024_I2CSLEW_I2C_MODE       0x00u   /*!< Controls slew rate of I2C pin.: I2C mode. */
#define PIO04_DIGIMODE_DIGITAL        0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO04_FUNC_ALT0               0x00u   /*!< Selects pin function.: Alternative connection 0. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitPMod_SPI_I2C_BRIDGEPins:
- options: {coreID: core0, enableClock: 'true'}
- pin_list:
  - {pin_num: '38', peripheral: GPIO, signal: 'PIO0, 4', pin_signal: PIO0_4/FC0_SCK/FC3_SSEL2/CTIMER0_CAP2, identifier: BRIDGE_T_INTR}
  - {pin_num: '46', peripheral: FLEXCOMM3, signal: SCK, pin_signal: PIO0_11/FC3_SCK/FC6_RXD_SDA_MOSI_DATA, direction: OUTPUT}
  - {pin_num: '47', peripheral: FLEXCOMM3, signal: RXD_SDA_MOSI, pin_signal: PIO0_12/FC3_RXD_SDA_MOSI/FC6_TXD_SCL_MISO_WS, direction: OUTPUT}
  - {pin_num: '48', peripheral: FLEXCOMM3, signal: TXD_SCL_MISO, pin_signal: PIO0_13/FC3_TXD_SCL_MISO/SCT0_OUT4, direction: INPUT}
  - {pin_num: '49', peripheral: FLEXCOMM3, signal: CTS_SDA_SSEL0, pin_signal: PIO0_14/FC3_CTS_SDA_SSEL0/SCT0_OUT5/FC1_SCK, direction: OUTPUT}
  - {pin_num: '63', peripheral: GPIO, signal: 'PIO0, 22', pin_signal: PIO0_22/CLKIN/FC0_RXD_SDA_MOSI/CTIMER3_MAT3}
  - {pin_num: '1', peripheral: FLEXCOMM1, signal: RTS_SCL_SSEL1, pin_signal: PIO0_23/FC1_RTS_SCL_SSEL1/CTIMER0_CAP0/UTICK_CAP1, identifier: BRIDGE_SCL, i2c_slew: i2c}
  - {pin_num: '2', peripheral: FLEXCOMM1, signal: CTS_SDA_SSEL0, pin_signal: PIO0_24/FC1_CTS_SDA_SSEL0/CTIMER0_CAP1/CTIMER0_MAT0, identifier: BRIDGE_SDA_WAKEUP, i2c_slew: i2c}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitPMod_SPI_I2C_BRIDGEPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitPMod_SPI_I2C_BRIDGEPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[0][11] = ((IOCON->PIO[0][11] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO011_FUNC_ALT1)                     /* Selects pin function.: PORT011 (pin 46) is configured as FC3_SCK */
      | IOCON_PIO_DIGIMODE(PIO011_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][12] = ((IOCON->PIO[0][12] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO012_FUNC_ALT1)                     /* Selects pin function.: PORT012 (pin 47) is configured as FC3_RXD_SDA_MOSI */
      | IOCON_PIO_DIGIMODE(PIO012_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][13] = ((IOCON->PIO[0][13] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO013_FUNC_ALT1)                     /* Selects pin function.: PORT013 (pin 48) is configured as FC3_TXD_SCL_MISO */
      | IOCON_PIO_DIGIMODE(PIO013_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][14] = ((IOCON->PIO[0][14] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO014_FUNC_ALT1)                     /* Selects pin function.: PORT014 (pin 49) is configured as FC3_CTS_SDA_SSEL0 */
      | IOCON_PIO_DIGIMODE(PIO014_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][22] = ((IOCON->PIO[0][22] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO022_FUNC_ALT0)                     /* Selects pin function.: PORT022 (pin 63) is configured as PIO0_22 */
      | IOCON_PIO_DIGIMODE(PIO022_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][23] = ((IOCON->PIO[0][23] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_I2CSLEW_MASK | IOCON_PIO_DIGIMODE_MASK))) /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO023_FUNC_ALT1)                     /* Selects pin function.: PORT023 (pin 1) is configured as FC1_RTS_SCL_SSEL1 */
      | IOCON_PIO_I2CSLEW(PIO023_I2CSLEW_I2C_MODE)           /* Controls slew rate of I2C pin.: I2C mode. */
      | IOCON_PIO_DIGIMODE(PIO023_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][24] = ((IOCON->PIO[0][24] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_I2CSLEW_MASK | IOCON_PIO_DIGIMODE_MASK))) /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO024_FUNC_ALT1)                     /* Selects pin function.: PORT024 (pin 2) is configured as FC1_CTS_SDA_SSEL0 */
      | IOCON_PIO_I2CSLEW(PIO024_I2CSLEW_I2C_MODE)           /* Controls slew rate of I2C pin.: I2C mode. */
      | IOCON_PIO_DIGIMODE(PIO024_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][4] = ((IOCON->PIO[0][4] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO04_FUNC_ALT0)                      /* Selects pin function.: PORT04 (pin 38) is configured as PIO0_4 */
      | IOCON_PIO_DIGIMODE(PIO04_DIGIMODE_DIGITAL)           /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO16_DIGIMODE_DIGITAL        0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO16_FUNC_ALT7               0x07u   /*!< Selects pin function.: Alternative connection 7. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitUSBPins:
- options: {prefix: BOARD_, coreID: core0, enableClock: 'true'}
- pin_list:
  - {pin_num: '5', peripheral: USB0, signal: USB_DP, pin_signal: USB0_DP}
  - {pin_num: '6', peripheral: USB0, signal: USB_DM, pin_signal: USB0_DM}
  - {pin_num: '26', peripheral: USB0, signal: USB_VBUS, pin_signal: PIO1_6/FC7_SCK/CTIMER1_CAP2/CTIMER1_MAT2/USB0_VBUS/ADC0_9}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitUSBPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitUSBPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[1][6] = ((IOCON->PIO[1][6] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO16_FUNC_ALT7)                      /* Selects pin function.: PORT16 (pin 26) is configured as USB0_VBUS */
      | IOCON_PIO_DIGIMODE(PIO16_DIGIMODE_DIGITAL)           /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO00_DIGIMODE_DIGITAL        0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO00_FUNC_ALT1               0x01u   /*!< Selects pin function.: Alternative connection 1. */
#define PIO01_DIGIMODE_DIGITAL        0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO01_FUNC_ALT1               0x01u   /*!< Selects pin function.: Alternative connection 1. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitDEBUG_UARTPins:
- options: {callFromInitBoot: 'true', prefix: BOARD_, coreID: core0, enableClock: 'false'}
- pin_list:
  - {pin_num: '32', peripheral: FLEXCOMM0, signal: TXD_SCL_MISO, pin_signal: PIO0_1/FC0_TXD_SCL_MISO/FC3_RTS_SCL_SSEL1/CTIMER0_CAP1/SCT0_OUT1, direction: OUTPUT}
  - {pin_num: '31', peripheral: FLEXCOMM0, signal: RXD_SDA_MOSI, pin_signal: PIO0_0/FC0_RXD_SDA_MOSI/FC3_CTS_SDA_SSEL0/CTIMER0_CAP0/SCT0_OUT3, direction: INPUT}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitDEBUG_UARTPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitDEBUG_UARTPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[0][0] = ((IOCON->PIO[0][0] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO00_FUNC_ALT1)                      /* Selects pin function.: PORT00 (pin 31) is configured as FC0_RXD_SDA_MOSI */
      | IOCON_PIO_DIGIMODE(PIO00_DIGIMODE_DIGITAL)           /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][1] = ((IOCON->PIO[0][1] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO01_FUNC_ALT1)                      /* Selects pin function.: PORT01 (pin 32) is configured as FC0_TXD_SCL_MISO */
      | IOCON_PIO_DIGIMODE(PIO01_DIGIMODE_DIGITAL)           /* Select Analog/Digital mode.: Digital mode. */
    );
}


#define PIO016_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO016_FUNC_ALT5              0x05u   /*!< Selects pin function.: Alternative connection 5. */
#define PIO017_DIGIMODE_DIGITAL       0x01u   /*!< Select Analog/Digital mode.: Digital mode. */
#define PIO017_FUNC_ALT5              0x05u   /*!< Selects pin function.: Alternative connection 5. */

/*
 * TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
BOARD_InitSWD_DEBUGPins:
- options: {prefix: BOARD_, coreID: core0, enableClock: 'true'}
- pin_list:
  - {pin_num: '53', peripheral: SWD, signal: SWDIO, pin_signal: PIO0_17/FC3_SSEL3/FC6_RTS_SCL_SSEL1/CTIMER3_MAT2/SWDIO}
  - {pin_num: '52', peripheral: SWD, signal: SWCLK, pin_signal: PIO0_16/FC3_SSEL2/FC6_CTS_SDA_SSEL0/CTIMER3_MAT1/SWCLK}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS ***********
 */

/*FUNCTION**********************************************************************
 *
 * Function Name : BOARD_InitSWD_DEBUGPins
 * Description   : Configures pin routing and optionally pin electrical features.
 *
 *END**************************************************************************/
void BOARD_InitSWD_DEBUGPins(void) { /* Function assigned for the Cortex-M0P */
  CLOCK_EnableClock(kCLOCK_Iocon);                           /* Enables the clock for the IOCON block. 0 = Disable; 1 = Enable.: 0x01u */

  IOCON->PIO[0][16] = ((IOCON->PIO[0][16] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO016_FUNC_ALT5)                     /* Selects pin function.: PORT016 (pin 52) is configured as SWCLK */
      | IOCON_PIO_DIGIMODE(PIO016_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
  IOCON->PIO[0][17] = ((IOCON->PIO[0][17] &
    (~(IOCON_PIO_FUNC_MASK | IOCON_PIO_DIGIMODE_MASK)))      /* Mask bits to zero which are setting */
      | IOCON_PIO_FUNC(PIO017_FUNC_ALT5)                     /* Selects pin function.: PORT017 (pin 53) is configured as SWDIO */
      | IOCON_PIO_DIGIMODE(PIO017_DIGIMODE_DIGITAL)          /* Select Analog/Digital mode.: Digital mode. */
    );
}

/*******************************************************************************
 * EOF
 ******************************************************************************/
